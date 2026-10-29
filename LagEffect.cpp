// LagEffect.cpp - hold (or toggle) a hotkey to loop the last chunk of your mic.
// Windows app with a settings window and tray icon. Settings save to LagEffect.ini.
// Built for Discord / OBS: send to a virtual cable, hear yourself on headphones,
// built-in noise gate, auto-reconnect, separate pitch/speed, dark mode, GitHub updater.
//
// Build:
//   1. Put miniaudio.h (https://github.com/mackron/miniaudio) next to this file.
//   2. Visual Studio (Developer Command Prompt):
//        rc LagEffect.rc
//        cl /O2 LagEffect.cpp LagEffect.res /link /SUBSYSTEM:WINDOWS
//      MinGW / MSYS2:
//        windres LagEffect.rc -O coff -o LagEffect_res.o
//        g++ -O2 LagEffect.cpp LagEffect_res.o -o LagEffect.exe -mwindows -lcomctl32 -lwinhttp -static
//
// Releasing an update: bump APP_VERSION below, build, then create a GitHub release whose tag
// is the version (e.g. v1.2.0) and attach LagEffect.exe. The app's "Check now" button finds it.

#define APP_VERSION L"1.1.0"

#define UNICODE
#define _UNICODE
#define NOMINMAX
#define MINIAUDIO_IMPLEMENTATION
#include "miniaudio.h"

#include <windows.h>
#include <commctrl.h>
#include <shellapi.h>
#include <winhttp.h>
#include <string.h>
#include <math.h>

#ifdef _MSC_VER
#pragma comment(lib, "comctl32.lib")
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "advapi32.lib")
#pragma comment(lib, "winhttp.lib")
#pragma comment(linker, "\"/manifestdependency:type='win32' name='Microsoft.Windows.Common-Controls' version='6.0.0.0' processorArchitecture='*' publicKeyToken='6595b64144ccf1df' language='*'\"")
#endif

static int Imin(int a, int b) { return a < b ? a : b; }
static int Imax(int a, int b) { return a > b ? a : b; }
static int Iclamp(int v, int lo, int hi) { return Imax(lo, Imin(hi, v)); }

// ======================= audio =======================
#define RATE     48000
#define HIST     (RATE * 2)                    // loops up to 2 seconds long
#define MON_SIZE 16384                         // monitor ring buffer (power of two)
#define MAXGRAIN (RATE * 40 / 1000)            // 40 ms grains for pitch/speed
static const int BUFFERS[] = { 32, 64, 128, 256, 512 };

enum { MON_OFF = 0, MON_EFFECT = 1, MON_ALL = 2 };

// Settings shared with the audio threads (plain ints/floats are safe to read on x86/x64).
static volatile int   gLoopMs = 500, gSpeedPct = 100, gPitchPct = 100, gVolPct = 100, gFadeMs = 3;
static volatile int   gGateDb = 50, gMonVolPct = 100, gMonMode = MON_OFF;
static volatile int   gHotkey = VK_F8;
static volatile bool  gToggleMode = false, gPassThrough = true, gGateOn = false;
static volatile bool  gCapturingKey = false, gLooping = false;
static volatile float gGateLin = 0.00316f;     // -50 dB

static float  hist[HIST], frozen[HIST], hann[MAXGRAIN];
static size_t wpos = 0, frozenLen = 1;
static bool   looping = false, prevDown = false, toggled = false;
static double loopPos = 0, grainStart[2];
static int    grainAge[2], grainLen = 2;
static float  gateEnv = 0, gateGain = 1;
static int    gateHold = 0;

static float  monRing[MON_SIZE];
static volatile unsigned monW = 0, monR = 0;
static volatile bool     monActive = false;

static void UpdateGateLin()
{
    float v = 1.0f;
    for (int i = 0; i < gGateDb; i++) v *= 0.891250938f;   // -1 dB per step
    gGateLin = v;
}

static inline double WrapPos(double p, double len)
{
    while (p >= len) p -= len;
    while (p < 0) p += len;
    return p;
}

static void AudioCallback(ma_device*, void* output, const void* input, ma_uint32 frames)
{
    float* out = (float*)output;                // stereo
    const float* in = (const float*)input;      // mono

    bool down = !gCapturingKey && (GetAsyncKeyState(gHotkey) & 0x8000) != 0;
    bool active;
    if (gToggleMode) { if (down && !prevDown) toggled = !toggled; active = toggled; }
    else             { toggled = false; active = down; }
    prevDown = down;

    if (active && !looping) {                  // freeze the most recent audio
        size_t len = (size_t)gLoopMs * RATE / 1000;
        if (len < 1) len = 1;
        if (len > (size_t)HIST) len = HIST;
        size_t start = (wpos + HIST - len) % HIST;
        for (size_t k = 0; k < len; k++) frozen[k] = hist[(start + k) % HIST];
        frozenLen = len;

        // Two overlapping grains (Hann windows at 50% overlap sum to 1) let speed and pitch differ.
        int g = len < (size_t)MAXGRAIN ? (int)len : MAXGRAIN;
        g &= ~1;
        if (g < 32) g = 32;
        grainLen = g;
        for (int i = 0; i < g; i++) hann[i] = 0.5f - 0.5f * (float)cos(6.283185307179586 * i / g);
        loopPos = 0;
        grainStart[0] = 0;                     grainAge[0] = 0;
        grainStart[1] = WrapPos(-(double)g / 2, (double)len); grainAge[1] = g / 2;
        looping = true;
    } else if (!active) {
        looping = false;
    }
    gLooping = looping;

    const float  vol    = gVolPct / 100.0f;
    const float  monVol = gMonVolPct / 100.0f;
    const int    mode   = monActive ? gMonMode : MON_OFF;
    const bool   gateOn = gGateOn;
    const float  thr    = gGateLin;
    const double speed  = gSpeedPct / 100.0;
    const double pitch  = gPitchPct / 100.0;
    const double len    = (double)frozenLen;
    double fade = (double)gFadeMs * RATE / 1000.0;
    if (fade * 2 > len) fade = len / 2.0;

    unsigned w = monW, r = monR;

    for (ma_uint32 f = 0; f < frames; f++) {
        float s = in ? in[f] : 0.0f;

        if (gateOn) {                           // noise gate: 1 ms open, 150 ms hold, 80 ms close
            float a = s < 0 ? -s : s;
            gateEnv = a > gateEnv ? a : gateEnv * 0.99948f;
            if (gateEnv > thr) gateHold = RATE * 150 / 1000;
            else if (gateHold > 0) gateHold--;
            float target = gateHold > 0 ? 1.0f : 0.0f;
            gateGain += (target - gateGain) * (target > gateGain ? 0.0206f : 0.00026f);
            s *= gateGain;
        }

        float o;
        if (looping) {
            float v = 0.0f;
            for (int k = 0; k < 2; k++) {
                double rp = WrapPos(grainStart[k] + grainAge[k] * pitch, len);
                size_t i0 = (size_t)rp, i1 = (i0 + 1) % frozenLen;
                float t = (float)(rp - (double)i0);
                float smp = frozen[i0] * (1 - t) + frozen[i1] * t;
                if (fade >= 1) {                // soften the click at the loop seam
                    double d = len - rp;
                    if (rp < d) d = rp;
                    if (d < fade) smp *= (float)(d / fade);
                }
                v += smp * hann[grainAge[k]];
                if (++grainAge[k] >= grainLen) { grainAge[k] = 0; grainStart[k] = WrapPos(loopPos + speed, len); }
            }
            loopPos = WrapPos(loopPos + speed, len);
            o = v * vol;
        } else {
            hist[wpos] = s;
            wpos = (wpos + 1) % HIST;
            o = gPassThrough ? s * vol : 0.0f;
        }

        if (o > 1.0f) o = 1.0f; else if (o < -1.0f) o = -1.0f;   // never clip harshly into Discord/OBS
        out[f * 2] = o;
        out[f * 2 + 1] = o;

        if (mode != MON_OFF && (w - r) < MON_SIZE) {
            float m = (mode == MON_ALL || looping) ? o * monVol : 0.0f;
            if (m > 1.0f) m = 1.0f; else if (m < -1.0f) m = -1.0f;
            monRing[w & (MON_SIZE - 1)] = m;
            w++;
        }
    }
    MemoryBarrier();
    monW = w;
}

static void MonitorCallback(ma_device* dev, void* output, const void*, ma_uint32 frames)
{
    float* out = (float*)output;                // stereo
    unsigned w = monW;
    MemoryBarrier();
    unsigned r = monR;
    unsigned avail = w - r;

    // The two devices run on separate clocks; drop old audio so delay never builds up.
    unsigned maxLag = dev->playback.internalPeriodSizeInFrames * 3 + 512;
    if (avail > maxLag) { r = w - dev->playback.internalPeriodSizeInFrames; avail = w - r; }

    for (ma_uint32 f = 0; f < frames; f++) {
        float m = 0.0f;
        if (avail) { m = monRing[r & (MON_SIZE - 1)]; r++; avail--; }
        out[f * 2] = m;
        out[f * 2 + 1] = m;
    }
    monR = r;
}

// ======================= app state =======================
enum {
    IDC_MIC = 101, IDC_OUT, IDC_MON, IDC_MONMODE, IDC_VBCABLE,
    IDC_LOOP, IDC_SPEED, IDC_PITCH, IDC_VOL, IDC_FADE, IDC_GATE, IDC_MONVOL,
    IDC_GATEON, IDC_PASS, IDC_HOTKEY, IDC_HOLD, IDC_TOGGLE, IDC_BUFFER, IDC_EXCL,
    IDC_STATUS, IDC_START, IDC_TRAY, IDC_HELPBTN, IDC_AUTO,
    IDC_THEME, IDC_REPO, IDC_CHECKUPD, IDC_UPDSTART,
    ID_TRAY_OPEN = 900, ID_TRAY_RUN, ID_TRAY_EXIT
};
#define WM_TRAY            (WM_APP + 1)
#define WM_DEVICE_LOST     (WM_APP + 2)
#define WM_UPDATE_CHECKED  (WM_APP + 3)
#define WM_UPDATE_DOWNLOAD (WM_APP + 4)
#define TIMER_STATUS    1
#define TIMER_KEY       2
#define TIMER_RECONNECT 3
#define TIMER_CLEANUP   4

static HINSTANCE gInst; static HWND gWnd, gStatus; static HFONT gFont; static HICON gIcon;
static ma_context gCtx; static ma_device gDev, gMonDev;
static bool gCtxOk = false, gRunning = false, gMonRunning = false, gWantRunning = false, gStopping = false;
static ma_device_info *gOuts = nullptr, *gIns = nullptr; static ma_uint32 gOutCount = 0, gInCount = 0;
static int  gBufIdx = 2;
static bool gExclusive = false, gAutoStart = false, gInTray = false, gUiReady = false;
static wchar_t gMicName[512], gOutName[512], gMonName[512], gIni[MAX_PATH];
static bool gKeyWasDown[256];
static int  gWaitRelease = 0;

struct Range { int id, lo, hi; volatile int* var; const wchar_t* key; };
static Range gRanges[] = {
    { IDC_LOOP,   10, 2000, &gLoopMs,    L"loop_ms"        },
    { IDC_SPEED,  10, 400,  &gSpeedPct,  L"speed"          },
    { IDC_PITCH,  25, 400,  &gPitchPct,  L"pitch"          },
    { IDC_VOL,    0,  200,  &gVolPct,    L"volume"         },
    { IDC_FADE,   0,  50,   &gFadeMs,    L"smoothing_ms"   },
    { IDC_GATE,   20, 90,   &gGateDb,    L"gate_db"        },
    { IDC_MONVOL, 0,  200,  &gMonVolPct, L"monitor_volume" },
};

static void Widen(const char* s, wchar_t* out, int cap)
{
    if (MultiByteToWideChar(CP_UTF8, 0, s, -1, out, cap) == 0) out[0] = 0;
}

static bool ContainsNoCase(const wchar_t* hay, const wchar_t* needle)
{
    wchar_t a[512], b[128];
    lstrcpynW(a, hay, 512); lstrcpynW(b, needle, 128);
    CharLowerW(a); CharLowerW(b);
    return wcsstr(a, b) != nullptr;
}

static void KeyName(int vk, wchar_t* buf, int cap)
{
    switch (vk) {
        case VK_RBUTTON:  lstrcpynW(buf, L"Right mouse", cap);  return;
        case VK_MBUTTON:  lstrcpynW(buf, L"Middle mouse", cap); return;
        case VK_XBUTTON1: lstrcpynW(buf, L"Mouse 4", cap);      return;
        case VK_XBUTTON2: lstrcpynW(buf, L"Mouse 5", cap);      return;
    }
    UINT sc = MapVirtualKeyW(vk, MAPVK_VK_TO_VSC);
    if ((vk >= VK_PRIOR && vk <= VK_DOWN) || vk == VK_INSERT || vk == VK_DELETE ||
        vk == VK_DIVIDE || vk == VK_NUMLOCK || vk == VK_RCONTROL || vk == VK_RMENU)
        sc |= 0x100;                            // extended key flag
    if (sc && GetKeyNameTextW((LONG)(sc << 16), buf, cap) > 0) return;
    wsprintfW(buf, L"Key %d", vk);
}

// ======================= theme (light / dark) =======================
enum { THEME_SYSTEM = 0, THEME_LIGHT = 1, THEME_DARK = 2 };
static int    gThemeMode = THEME_SYSTEM;
static bool   gDark = false;
static HBRUSH gBrBg, gBrCtl;
#define DK_BG   RGB(32, 32, 32)
#define DK_CTL  RGB(50, 50, 50)
#define DK_TEXT RGB(232, 232, 232)

typedef HRESULT (WINAPI* PFN_SetWindowTheme)(HWND, LPCWSTR, LPCWSTR);
typedef HRESULT (WINAPI* PFN_DwmSetWindowAttribute)(HWND, DWORD, LPCVOID, DWORD);
typedef int     (WINAPI* PFN_SetPreferredAppMode)(int);
typedef void    (WINAPI* PFN_FlushMenuThemes)(void);
static PFN_SetWindowTheme        pSetWindowTheme;
static PFN_DwmSetWindowAttribute pDwmSetWindowAttribute;
static PFN_SetPreferredAppMode   pSetPreferredAppMode;
static PFN_FlushMenuThemes       pFlushMenuThemes;

static DWORD WindowsBuild()
{
    typedef LONG (WINAPI* PFN_RtlGetVersion)(OSVERSIONINFOW*);
    OSVERSIONINFOW v = {}; v.dwOSVersionInfoSize = sizeof(v);
    PFN_RtlGetVersion f = (PFN_RtlGetVersion)(void*)GetProcAddress(GetModuleHandleW(L"ntdll.dll"), "RtlGetVersion");
    return (f && f(&v) == 0) ? v.dwBuildNumber : 0;
}

static void LoadThemeApis()
{
    HMODULE ux = LoadLibraryW(L"uxtheme.dll");
    if (ux) {
        pSetWindowTheme = (PFN_SetWindowTheme)(void*)GetProcAddress(ux, "SetWindowTheme");
        if (WindowsBuild() >= 18362) {          // undocumented, but stable since Windows 10 1903
            pSetPreferredAppMode = (PFN_SetPreferredAppMode)(void*)GetProcAddress(ux, MAKEINTRESOURCEA(135));
            pFlushMenuThemes     = (PFN_FlushMenuThemes)(void*)GetProcAddress(ux, MAKEINTRESOURCEA(136));
        }
    }
    HMODULE dwm = LoadLibraryW(L"dwmapi.dll");
    if (dwm) pDwmSetWindowAttribute = (PFN_DwmSetWindowAttribute)(void*)GetProcAddress(dwm, "DwmSetWindowAttribute");
    gBrBg  = CreateSolidBrush(DK_BG);
    gBrCtl = CreateSolidBrush(DK_CTL);
}

static bool SystemUsesDark()
{
    DWORD v = 1, sz = sizeof(v);
    if (RegGetValueW(HKEY_CURRENT_USER, L"Software\\Microsoft\\Windows\\CurrentVersion\\Themes\\Personalize",
                     L"AppsUseLightTheme", RRF_RT_REG_DWORD, nullptr, &v, &sz) != ERROR_SUCCESS) return false;
    return v == 0;
}

static void SetTheme(HWND h, LPCWSTR app, LPCWSTR id) { if (pSetWindowTheme) pSetWindowTheme(h, app, id); }

static BOOL CALLBACK ThemeChild(HWND h, LPARAM)
{
    wchar_t cls[32];
    GetClassNameW(h, cls, 32);
    if (!lstrcmpiW(cls, L"Button")) {
        LONG type = GetWindowLongW(h, GWL_STYLE) & BS_TYPEMASK;
        if (type == BS_PUSHBUTTON || type == BS_DEFPUSHBUTTON) SetTheme(h, gDark ? L"DarkMode_Explorer" : nullptr, nullptr);
        else if (gDark) SetTheme(h, L"", L"");  // unthemed so checkbox / group text can be light
        else            SetTheme(h, nullptr, nullptr);
    } else if (!lstrcmpiW(cls, L"ComboBox") || !lstrcmpiW(cls, L"Edit")) {
        SetTheme(h, gDark ? L"DarkMode_CFD" : nullptr, nullptr);
    } else if (!lstrcmpiW(cls, UPDOWN_CLASSW)) {
        SetTheme(h, gDark ? L"DarkMode_Explorer" : nullptr, nullptr);
    }
    return TRUE;
}

static void ApplyTheme()
{
    gDark = gThemeMode == THEME_DARK || (gThemeMode == THEME_SYSTEM && SystemUsesDark());
    if (pDwmSetWindowAttribute) {
        BOOL d = gDark;
        if (FAILED(pDwmSetWindowAttribute(gWnd, 20, &d, sizeof(d))))    // DWMWA_USE_IMMERSIVE_DARK_MODE
            pDwmSetWindowAttribute(gWnd, 19, &d, sizeof(d));            // older Windows 10 builds
    }
    if (pSetPreferredAppMode) {                 // dark tray menu
        pSetPreferredAppMode(gDark ? 2 : 3);
        if (pFlushMenuThemes) pFlushMenuThemes();
    }
    EnumChildWindows(gWnd, ThemeChild, 0);
    RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_ALLCHILDREN | RDW_FRAME);
}

// ======================= settings =======================
static wchar_t gUpdateRepo[200];
static bool    gUpdateOnStart = false;

static void LoadSettings()
{
    GetModuleFileNameW(nullptr, gIni, MAX_PATH);
    wchar_t* slash = wcsrchr(gIni, L'\\');
    if (slash) slash[1] = 0; else gIni[0] = 0;
    lstrcatW(gIni, L"LagEffect.ini");

    #define INI_INT(k, d) (int)GetPrivateProfileIntW(L"settings", k, d, gIni)
    for (Range& r : gRanges) *r.var = Iclamp(INI_INT(r.key, *r.var), r.lo, r.hi);
    gHotkey        = INI_INT(L"hotkey", VK_F8);
    gToggleMode    = INI_INT(L"toggle", 0) != 0;
    gPassThrough   = INI_INT(L"passthrough", 1) != 0;
    gGateOn        = INI_INT(L"gate", 0) != 0;
    gMonMode       = Iclamp(INI_INT(L"monitor_mode", MON_OFF), 0, 2);
    gBufIdx        = Iclamp(INI_INT(L"buffer", 2), 0, 4);
    gExclusive     = INI_INT(L"exclusive", 0) != 0;
    gAutoStart     = INI_INT(L"autostart", 0) != 0;
    gThemeMode     = Iclamp(INI_INT(L"theme", THEME_SYSTEM), 0, 2);
    gUpdateOnStart = INI_INT(L"update_on_start", 0) != 0;
    #undef INI_INT
    UpdateGateLin();

    GetPrivateProfileStringW(L"settings", L"mic",         L"", gMicName, 512, gIni);
    GetPrivateProfileStringW(L"settings", L"output",      L"", gOutName, 512, gIni);
    GetPrivateProfileStringW(L"settings", L"monitor",     L"", gMonName, 512, gIni);
    GetPrivateProfileStringW(L"settings", L"update_repo", L"", gUpdateRepo, 200, gIni);
}

static void SelectedName(int comboId, ma_device_info* list, ma_uint32 count, wchar_t* out, int cap)
{
    int i = (int)SendDlgItemMessageW(gWnd, comboId, CB_GETCURSEL, 0, 0) - 1;
    if (i >= 0 && i < (int)count) Widen(list[i].name, out, cap); else out[0] = 0;
}

static void SaveInt(const wchar_t* k, int v)
{
    wchar_t b[32]; wsprintfW(b, L"%d", v);
    WritePrivateProfileStringW(L"settings", k, b, gIni);
}

static void SaveSettings()
{
    for (Range& r : gRanges) SaveInt(r.key, *r.var);
    SaveInt(L"hotkey", gHotkey); SaveInt(L"toggle", gToggleMode); SaveInt(L"passthrough", gPassThrough);
    SaveInt(L"gate", gGateOn); SaveInt(L"monitor_mode", gMonMode);
    SaveInt(L"buffer", gBufIdx); SaveInt(L"exclusive", gExclusive); SaveInt(L"autostart", gAutoStart);
    SaveInt(L"theme", gThemeMode); SaveInt(L"update_on_start", gUpdateOnStart);
    WritePrivateProfileStringW(L"settings", L"update_repo", gUpdateRepo, gIni);
    wchar_t name[512];
    SelectedName(IDC_MIC, gIns, gInCount, name, 512);   WritePrivateProfileStringW(L"settings", L"mic", name, gIni);
    SelectedName(IDC_OUT, gOuts, gOutCount, name, 512); WritePrivateProfileStringW(L"settings", L"output", name, gIni);
    SelectedName(IDC_MON, gOuts, gOutCount, name, 512); WritePrivateProfileStringW(L"settings", L"monitor", name, gIni);
}

// ======================= audio start/stop =======================
static void NotifyCallback(const ma_device_notification* n)
{
    // A device was unplugged or disabled: let the window restart audio.
    if (n->type == ma_device_notification_type_stopped && !gStopping && gWantRunning)
        PostMessageW(gWnd, WM_DEVICE_LOST, 0, 0);
}

static int ComboIndex(int id) { return (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0) - 1; }

static bool StartMonitor()
{
    if (gMonMode == MON_OFF) return true;
    ma_device_config cfg = ma_device_config_init(ma_device_type_playback);
    cfg.playback.format    = ma_format_f32;
    cfg.playback.channels  = 2;
    cfg.sampleRate         = RATE;
    cfg.periodSizeInFrames = BUFFERS[gBufIdx];
    cfg.performanceProfile = ma_performance_profile_low_latency;
    cfg.dataCallback       = MonitorCallback;
    cfg.notificationCallback = NotifyCallback;
    int i = ComboIndex(IDC_MON);
    if (i >= 0 && i < (int)gOutCount) cfg.playback.pDeviceID = &gOuts[i].id;

    monW = monR = 0;
    if (ma_device_init(&gCtx, &cfg, &gMonDev) != MA_SUCCESS) return false;
    if (ma_device_start(&gMonDev) != MA_SUCCESS) { ma_device_uninit(&gMonDev); return false; }
    gMonRunning = true;
    monActive = true;
    return true;
}

static bool StartAudio(bool quiet)
{
    if (gRunning || !gCtxOk) return false;

    ma_device_config cfg = ma_device_config_init(ma_device_type_duplex);
    cfg.capture.format     = ma_format_f32;
    cfg.capture.channels   = 1;
    cfg.playback.format    = ma_format_f32;
    cfg.playback.channels  = 2;
    cfg.sampleRate         = RATE;
    cfg.periodSizeInFrames = BUFFERS[gBufIdx];
    cfg.performanceProfile = ma_performance_profile_low_latency;
    cfg.dataCallback       = AudioCallback;
    cfg.notificationCallback = NotifyCallback;
    if (gExclusive) {
        cfg.capture.shareMode  = ma_share_mode_exclusive;
        cfg.playback.shareMode = ma_share_mode_exclusive;
    }
    int mi = ComboIndex(IDC_MIC), oi = ComboIndex(IDC_OUT);
    if (mi >= 0 && mi < (int)gInCount)  cfg.capture.pDeviceID  = &gIns[mi].id;
    if (oi >= 0 && oi < (int)gOutCount) cfg.playback.pDeviceID = &gOuts[oi].id;

    memset(hist, 0, sizeof(hist));
    wpos = 0; frozenLen = 1; looping = false; toggled = false; prevDown = false;
    gateEnv = 0; gateGain = 1; gateHold = 0;
    monActive = false;

    gStopping = false;
    gWantRunning = true;
    if (!StartMonitor() && !quiet)
        MessageBoxW(gWnd, L"Couldn't open the \"Hear on\" device, so you won't hear yourself.\n\nThe effect is still being sent normally.",
                    L"Lag Effect", MB_ICONWARNING);

    const wchar_t* err = gExclusive
        ? L"Couldn't open the audio devices.\n\nTry turning off Exclusive mode or picking a bigger buffer."
        : L"Couldn't open the audio devices.\n\nCheck that the mic and output are plugged in.";
    bool ok = ma_device_init(&gCtx, &cfg, &gDev) == MA_SUCCESS;
    if (ok && ma_device_start(&gDev) != MA_SUCCESS) { ma_device_uninit(&gDev); ok = false; }
    if (!ok) {
        if (gMonRunning) { gStopping = true; ma_device_uninit(&gMonDev); gMonRunning = false; monActive = false; }
        if (!quiet) { gWantRunning = false; MessageBoxW(gWnd, err, L"Lag Effect", MB_ICONWARNING); }
        return false;
    }
    gRunning = true;
    return true;
}

static void StopDevices()
{
    gStopping = true;
    monActive = false;
    if (gRunning)    { ma_device_uninit(&gDev);    gRunning = false; }
    if (gMonRunning) { ma_device_uninit(&gMonDev); gMonRunning = false; }
    gLooping = false;
}

static void StopAudio()
{
    gWantRunning = false;
    KillTimer(gWnd, TIMER_RECONNECT);
    StopDevices();
}

// ======================= UI helpers =======================
static HWND Ctl(const wchar_t* cls, const wchar_t* text, DWORD style, int x, int y, int w, int h, int id, DWORD ex = 0)
{
    HWND c = CreateWindowExW(ex, cls, text, WS_CHILD | WS_VISIBLE | style, x, y, w, h,
                             gWnd, (HMENU)(INT_PTR)id, gInst, nullptr);
    SendMessageW(c, WM_SETFONT, (WPARAM)gFont, TRUE);
    return c;
}

static void Spin(int id, int x, int y, int lo, int hi, int val)
{
    HWND e = Ctl(L"EDIT", L"", WS_TABSTOP | ES_NUMBER | ES_RIGHT | ES_AUTOHSCROLL, x, y, 66, 23, id, WS_EX_CLIENTEDGE);
    HWND u = CreateWindowExW(0, UPDOWN_CLASSW, nullptr,
                             WS_CHILD | WS_VISIBLE | UDS_SETBUDDYINT | UDS_ALIGNRIGHT | UDS_ARROWKEYS | UDS_NOTHOUSANDS | UDS_HOTTRACK,
                             0, 0, 0, 0, gWnd, (HMENU)(INT_PTR)(id + 100), gInst, nullptr);
    SendMessageW(u, UDM_SETBUDDY, (WPARAM)e, 0);
    SendMessageW(u, UDM_SETRANGE32, lo, hi);
    SendMessageW(u, UDM_SETPOS32, 0, val);
}

static void FillCombo(int id, const wchar_t* defName, ma_device_info* list, ma_uint32 count, const wchar_t* want)
{
    HWND c = GetDlgItem(gWnd, id);
    SendMessageW(c, CB_RESETCONTENT, 0, 0);
    SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)defName);
    int sel = 0;
    wchar_t n[512];
    for (ma_uint32 i = 0; i < count; i++) {
        Widen(list[i].name, n, 512);
        SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)n);
        if (want[0] && lstrcmpW(n, want) == 0) sel = (int)i + 1;
    }
    SendMessageW(c, CB_SETCURSEL, sel, 0);
}

static void FillDevices()
{
    FillCombo(IDC_MIC, L"Default microphone", gIns,  gInCount,  gMicName);
    FillCombo(IDC_OUT, L"Default output",     gOuts, gOutCount, gOutName);
    FillCombo(IDC_MON, L"Default output",     gOuts, gOutCount, gMonName);
}

static void RefreshDevices()                    // re-scan, e.g. after installing VB-Cable
{
    if (!gCtxOk) return;
    SelectedName(IDC_MIC, gIns, gInCount, gMicName, 512);
    SelectedName(IDC_OUT, gOuts, gOutCount, gOutName, 512);
    SelectedName(IDC_MON, gOuts, gOutCount, gMonName, 512);
    bool was = gWantRunning;
    StopAudio();
    ma_context_get_devices(&gCtx, &gOuts, &gOutCount, &gIns, &gInCount);
    FillDevices();
    if (was) StartAudio(false);
}

static void UpdateStatus(bool force = false)
{
    static wchar_t last[160];
    static bool lastLoop = false;
    wchar_t s[160], key[64];
    if (gWantRunning && !gRunning) lstrcpynW(s, L"Audio device lost  -  reconnecting...", 160);
    else if (!gRunning)            lstrcpynW(s, L"Stopped  -  press Start", 160);
    else if (gLooping)             lstrcpynW(s, L"LOOPING", 160);
    else {
        KeyName(gHotkey, key, 64);
        wsprintfW(s, L"Live  -  %s %s to stutter", gToggleMode ? L"press" : L"hold", key);
    }
    if (force || lstrcmpW(s, last) != 0 || lastLoop != gLooping) {
        lstrcpynW(last, s, 160); lastLoop = gLooping;
        SetWindowTextW(gStatus, s);
        InvalidateRect(gStatus, nullptr, TRUE);
    }
}

static void UpdateUi()
{
    SetDlgItemTextW(gWnd, IDC_START, gWantRunning ? L"Stop" : L"Start");
    UpdateStatus(true);
}

static void RestartIfRunning()
{
    if (gWantRunning) { StopAudio(); StartAudio(false); UpdateUi(); }
}

// ======================= updater =======================
// Looks at https://api.github.com/repos/<user>/<repo>/releases/latest, compares the tag with
// APP_VERSION, downloads the attached .exe next to this one, swaps them and restarts.

struct UpdateJob {
    bool manual, ok, newer;
    wchar_t error[300], tag[64], url[1024], notes[700];
};

static void* MemAlloc(size_t n)            { return HeapAlloc(GetProcessHeap(), 0, n); }
static void* MemRealloc(void* p, size_t n) { return p ? HeapReAlloc(GetProcessHeap(), 0, p, n) : MemAlloc(n); }
static void  MemFree(void* p)              { if (p) HeapFree(GetProcessHeap(), 0, p); }

// Downloads a URL. Returns the body (NUL-terminated, caller frees) or null with an error message.
static char* HttpGet(const wchar_t* url, DWORD* outLen, wchar_t* err, int errCap)
{
    wchar_t host[256], path[2048], extra[1024];
    URL_COMPONENTS uc = {};
    uc.dwStructSize = sizeof(uc);
    uc.lpszHostName = host;   uc.dwHostNameLength = 256;
    uc.lpszUrlPath = path;    uc.dwUrlPathLength = 2048;
    uc.lpszExtraInfo = extra; uc.dwExtraInfoLength = 1024;
    if (!WinHttpCrackUrl(url, 0, 0, &uc)) { lstrcpynW(err, L"Bad update address.", errCap); return nullptr; }
    if (uc.nScheme != INTERNET_SCHEME_HTTPS) { lstrcpynW(err, L"Updates must come over HTTPS.", errCap); return nullptr; }
    lstrcatW(path, extra);

    char* data = nullptr; DWORD len = 0;
    HINTERNET s = WinHttpOpen(L"LagEffect-Updater/" APP_VERSION, WINHTTP_ACCESS_TYPE_DEFAULT_PROXY,
                              WINHTTP_NO_PROXY_NAME, WINHTTP_NO_PROXY_BYPASS, 0);
    HINTERNET c = s ? WinHttpConnect(s, host, uc.nPort, 0) : nullptr;
    HINTERNET r = nullptr;
    if (c) r = WinHttpOpenRequest(c, L"GET", path, nullptr, WINHTTP_NO_REFERER, WINHTTP_DEFAULT_ACCEPT_TYPES, WINHTTP_FLAG_SECURE);
    bool ok = r && WinHttpSendRequest(r, L"Accept: application/vnd.github+json, application/octet-stream\r\n", (DWORD)-1L,
                                      WINHTTP_NO_REQUEST_DATA, 0, 0, 0)
                && WinHttpReceiveResponse(r, nullptr);
    if (!ok) {
        lstrcpynW(err, L"Couldn't reach GitHub. Check your internet connection.", errCap);
    } else {
        DWORD status = 0, sz = sizeof(status);
        WinHttpQueryHeaders(r, WINHTTP_QUERY_STATUS_CODE | WINHTTP_QUERY_FLAG_NUMBER, WINHTTP_HEADER_NAME_BY_INDEX,
                            &status, &sz, WINHTTP_NO_HEADER_INDEX);
        if (status == 404) {
            lstrcpynW(err, L"No release found. Check the GitHub user/repo, and that the repo is public and has a release.", errCap);
            ok = false;
        } else if (status != 200) {
            wsprintfW(err, L"GitHub answered with error %u. Try again later.", status);
            ok = false;
        }
        while (ok) {
            DWORD avail = 0;
            if (!WinHttpQueryDataAvailable(r, &avail)) { ok = false; lstrcpynW(err, L"Download was interrupted.", errCap); break; }
            if (avail == 0) break;
            char* bigger = (char*)MemRealloc(data, len + avail + 1);
            if (!bigger) { ok = false; lstrcpynW(err, L"Out of memory.", errCap); break; }
            data = bigger;
            DWORD got = 0;
            if (!WinHttpReadData(r, data + len, avail, &got)) { ok = false; lstrcpynW(err, L"Download was interrupted.", errCap); break; }
            len += got;
        }
    }
    if (r) WinHttpCloseHandle(r);
    if (c) WinHttpCloseHandle(c);
    if (s) WinHttpCloseHandle(s);
    if (!ok) { MemFree(data); return nullptr; }
    if (!data) data = (char*)MemAlloc(1);
    data[len] = 0;
    *outLen = len;
    return data;
}

// Finds "key": "value" in JSON, starting at *pos. Unescapes the value into out (UTF-8).
static bool JsonString(const char* json, const char* key, const char** pos, char* out, int cap)
{
    char pat[64]; lstrcpynA(pat, "\"", 64); lstrcatA(pat, key); lstrcatA(pat, "\"");
    const char* p = strstr(*pos, pat);
    if (!p) return false;
    p += lstrlenA(pat);
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n' || *p == ':') p++;
    if (*p != '"') { *pos = p; return false; }
    p++;
    int n = 0;
    while (*p && *p != '"') {
        char ch = *p++;
        if (ch == '\\' && *p) {
            char e = *p++;
            ch = e == 'n' ? '\n' : e == 'r' ? '\r' : e == 't' ? ' ' : e;
            if (e == 'u') { for (int i = 0; i < 4 && *p; i++) p++; ch = '\''; }
        }
        if (n < cap - 1) out[n++] = ch;
    }
    out[n] = 0;
    *pos = p;
    (void)json;
    return true;
}

static void ParseVersion(const wchar_t* s, int v[3])
{
    v[0] = v[1] = v[2] = 0;
    while (*s && (*s < L'0' || *s > L'9')) s++;
    for (int i = 0; i < 3 && *s; i++) {
        while (*s >= L'0' && *s <= L'9') v[i] = v[i] * 10 + (*s++ - L'0');
        if (*s == L'.') s++; else break;
    }
}

static bool IsNewer(const wchar_t* tag)
{
    int a[3], b[3];
    ParseVersion(tag, a); ParseVersion(APP_VERSION, b);
    for (int i = 0; i < 3; i++) if (a[i] != b[i]) return a[i] > b[i];
    return false;
}

static bool RepoFromText(const wchar_t* text, wchar_t* repo, int cap)  // accepts "user/repo" or a github.com link
{
    wchar_t t[200]; lstrcpynW(t, text, 200);
    wchar_t* p = t;
    while (*p == L' ') p++;
    const wchar_t* prefixes[] = { L"https://github.com/", L"http://github.com/", L"github.com/" };
    for (const wchar_t* pre : prefixes) {
        int n = lstrlenW(pre);
        if (CompareStringOrdinal(p, Imin(n, lstrlenW(p)), pre, n, TRUE) == CSTR_EQUAL) { p += n; break; }
    }
    int slashes = 0, i = 0;
    for (; p[i] && p[i] != L' '; i++) {
        wchar_t ch = p[i];
        if (ch == L'/') { if (++slashes > 1) break; continue; }
        bool okc = (ch >= L'a' && ch <= L'z') || (ch >= L'A' && ch <= L'Z') || (ch >= L'0' && ch <= L'9') ||
                   ch == L'-' || ch == L'_' || ch == L'.';
        if (!okc) return false;
    }
    p[i] = 0;
    if (slashes != 1 || p[0] == L'/' || p[i - 1] == L'/') return false;
    lstrcpynW(repo, p, cap);
    return true;
}

static DWORD WINAPI CheckThread(LPVOID arg)
{
    UpdateJob* job = (UpdateJob*)arg;
    wchar_t repo[200], api[400];
    if (!RepoFromText(gUpdateRepo, repo, 200)) {
        lstrcpynW(job->error, L"Type your GitHub user/repo in the Updates box first (for example: yourname/LagEffect).", 300);
    } else {
        wsprintfW(api, L"https://api.github.com/repos/%s/releases/latest", repo);
        DWORD len = 0;
        char* json = HttpGet(api, &len, job->error, 300);
        if (json) {
            char tag[64] = "", notes[690] = "", url[1024] = "";
            const char* p = json;
            JsonString(json, "tag_name", &p, tag, 64);
            p = json;
            if (JsonString(json, "body", &p, notes, 690)) {} else notes[0] = 0;
            p = json;
            while (JsonString(json, "browser_download_url", &p, url, 1024)) {
                int n = lstrlenA(url);
                if (n > 4 && lstrcmpiA(url + n - 4, ".exe") == 0) break;
                url[0] = 0;
            }
            MemFree(json);
            Widen(tag, job->tag, 64);
            Widen(notes, job->notes, 700);
            Widen(url, job->url, 1024);
            if (!tag[0])      lstrcpynW(job->error, L"The latest release has no version tag.", 300);
            else if (!url[0]) lstrcpynW(job->error, L"The latest release has no .exe attached.", 300);
            else { job->ok = true; job->newer = IsNewer(job->tag); }
        }
    }
    PostMessageW(gWnd, WM_UPDATE_CHECKED, 0, (LPARAM)job);
    return 0;
}

static void ExePaths(wchar_t* exe, wchar_t* newer, wchar_t* older)
{
    GetModuleFileNameW(nullptr, exe, MAX_PATH);
    lstrcpynW(newer, exe, MAX_PATH); lstrcatW(newer, L".new");
    lstrcpynW(older, exe, MAX_PATH); lstrcatW(older, L".old");
}

static DWORD WINAPI DownloadThread(LPVOID arg)
{
    UpdateJob* job = (UpdateJob*)arg;
    job->ok = false;
    DWORD len = 0;
    char* data = HttpGet(job->url, &len, job->error, 300);
    if (data) {
        if (len < 50000 || data[0] != 'M' || data[1] != 'Z') {
            lstrcpynW(job->error, L"The downloaded file isn't a valid program.", 300);
        } else {
            wchar_t exe[MAX_PATH], nw[MAX_PATH + 8], old[MAX_PATH + 8];
            ExePaths(exe, nw, old);
            HANDLE f = CreateFileW(nw, GENERIC_WRITE, 0, nullptr, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, nullptr);
            DWORD wrote = 0;
            if (f != INVALID_HANDLE_VALUE && WriteFile(f, data, len, &wrote, nullptr) && wrote == len) job->ok = true;
            else lstrcpynW(job->error, L"Couldn't save the update. Move LagEffect.exe to a folder you can write to, like Documents.", 300);
            if (f != INVALID_HANDLE_VALUE) CloseHandle(f);
            if (!job->ok) DeleteFileW(nw);
        }
        MemFree(data);
    }
    PostMessageW(gWnd, WM_UPDATE_DOWNLOAD, 0, (LPARAM)job);
    return 0;
}

static bool gUpdateBusy = false;

static void StartUpdateCheck(bool manual)
{
    if (gUpdateBusy) return;
    UpdateJob* job = (UpdateJob*)MemAlloc(sizeof(UpdateJob));
    if (!job) return;
    memset(job, 0, sizeof(*job));
    job->manual = manual;
    gUpdateBusy = true;
    SetDlgItemTextW(gWnd, IDC_CHECKUPD, L"Checking...");
    HANDLE t = CreateThread(nullptr, 0, CheckThread, job, 0, nullptr);
    if (t) CloseHandle(t); else { gUpdateBusy = false; MemFree(job); SetDlgItemTextW(gWnd, IDC_CHECKUPD, L"Check now"); }
}

static void OnUpdateChecked(UpdateJob* job)
{
    SetDlgItemTextW(gWnd, IDC_CHECKUPD, L"Check now");
    if (!job->ok || !job->newer) {
        if (job->manual) {
            if (!job->ok) MessageBoxW(gWnd, job->error, L"Lag Effect - Updates", MB_ICONWARNING);
            else {
                wchar_t msg[200];
                wsprintfW(msg, L"You're up to date (version %s).", APP_VERSION);
                MessageBoxW(gWnd, msg, L"Lag Effect - Updates", MB_ICONINFORMATION);
            }
        }
        gUpdateBusy = false;
        MemFree(job);
        return;
    }
    wchar_t msg[1200];
    wsprintfW(msg, L"Version %s is available (you have %s).\n\n%s%sUpdate now? Lag Effect will restart.",
              job->tag, APP_VERSION, job->notes, job->notes[0] ? L"\n\n" : L"");
    if (MessageBoxW(gWnd, msg, L"Lag Effect - Update available", MB_YESNO | MB_ICONINFORMATION) != IDYES) {
        gUpdateBusy = false;
        MemFree(job);
        return;
    }
    SetDlgItemTextW(gWnd, IDC_CHECKUPD, L"Downloading...");
    HANDLE t = CreateThread(nullptr, 0, DownloadThread, job, 0, nullptr);
    if (t) CloseHandle(t); else { gUpdateBusy = false; MemFree(job); SetDlgItemTextW(gWnd, IDC_CHECKUPD, L"Check now"); }
}

static void SaveSettings();
static void StopAudio();
static void RemoveTray();

static void OnUpdateDownloaded(UpdateJob* job)
{
    SetDlgItemTextW(gWnd, IDC_CHECKUPD, L"Check now");
    gUpdateBusy = false;
    if (!job->ok) {
        MessageBoxW(gWnd, job->error, L"Lag Effect - Updates", MB_ICONWARNING);
        MemFree(job);
        return;
    }
    MemFree(job);

    wchar_t exe[MAX_PATH], nw[MAX_PATH + 8], old[MAX_PATH + 8], dir[MAX_PATH];
    ExePaths(exe, nw, old);
    DeleteFileW(old);
    // A running .exe can be renamed but not overwritten, so: current -> .old, .new -> current.
    if (!MoveFileExW(exe, old, MOVEFILE_REPLACE_EXISTING)) {
        DeleteFileW(nw);
        MessageBoxW(gWnd, L"Couldn't replace LagEffect.exe. Move it to a folder you can write to, like Documents.",
                    L"Lag Effect - Updates", MB_ICONWARNING);
        return;
    }
    if (!MoveFileExW(nw, exe, MOVEFILE_REPLACE_EXISTING)) {
        MoveFileExW(old, exe, 0);
        MessageBoxW(gWnd, L"Couldn't install the update. Your current version is unchanged.", L"Lag Effect - Updates", MB_ICONWARNING);
        return;
    }
    SaveSettings();
    StopAudio();
    RemoveTray();
    lstrcpynW(dir, exe, MAX_PATH);
    wchar_t* slash = wcsrchr(dir, L'\\');
    if (slash) *slash = 0;
    ShellExecuteW(nullptr, L"open", exe, L"--updated", dir, SW_SHOWNORMAL);
    DestroyWindow(gWnd);
}

static void CleanupOldExe()
{
    wchar_t exe[MAX_PATH], nw[MAX_PATH + 8], old[MAX_PATH + 8];
    ExePaths(exe, nw, old);
    DeleteFileW(nw);
    if (GetFileAttributesW(old) == INVALID_FILE_ATTRIBUTES || DeleteFileW(old)) KillTimer(gWnd, TIMER_CLEANUP);
}

// ======================= VB-Cable + help =======================
static void SetupVbCable()
{
    RefreshDevices();
    int cable = -1;
    wchar_t n[512];
    for (ma_uint32 i = 0; i < gOutCount; i++) {
        Widen(gOuts[i].name, n, 512);
        if (ContainsNoCase(n, L"CABLE Input")) { cable = (int)i; break; }
    }
    if (cable < 0) {
        if (MessageBoxW(gWnd,
                L"VB-Cable isn't installed.\n\nIt's a free virtual audio cable that lets Discord, OBS and games hear "
                L"Lag Effect. After installing it, restart your PC and click this button again.\n\nOpen the download page now?",
                L"Lag Effect", MB_YESNO | MB_ICONINFORMATION) == IDYES)
            ShellExecuteW(nullptr, L"open", L"https://vb-audio.com/Cable/", nullptr, nullptr, SW_SHOWNORMAL);
        return;
    }
    SendDlgItemMessageW(gWnd, IDC_OUT, CB_SETCURSEL, cable + 1, 0);
    SendDlgItemMessageW(gWnd, IDC_MON, CB_SETCURSEL, 0, 0);                 // hear on default output
    if (gMonMode == MON_OFF) {
        gMonMode = MON_EFFECT;
        SendDlgItemMessageW(gWnd, IDC_MONMODE, CB_SETCURSEL, MON_EFFECT, 0);
    }
    if (gExclusive) { gExclusive = false; CheckDlgButton(gWnd, IDC_EXCL, BST_UNCHECKED); }
    StopAudio();
    StartAudio(false);
    UpdateUi();
    MessageBoxW(gWnd,
        L"Lag Effect now sends to VB-Cable, and you'll hear the effect on your normal output.\n\n"
        L"Discord:  Settings > Voice & Video > Input Device = \"CABLE Output\".\n"
        L"Then turn Noise Suppression to None (or Standard), and turn off Echo Cancellation "
        L"and Automatic Gain Control. Use Lag Effect's noise gate instead.\n\n"
        L"OBS:  add an Audio Input Capture source set to \"CABLE Output\", and mute your normal mic source.",
        L"Lag Effect - VB-Cable ready", MB_ICONINFORMATION);
}

static void ShowHelp()
{
    MessageBoxW(gWnd,
        L"HOW IT WORKS\n"
        L"Your mic goes to \"Send to\". Hold (or toggle) your hotkey to repeat the last bit of audio.\n"
        L"Speed = how fast the loop plays through.  Pitch = how high or low it sounds.\n\n"
        L"DISCORD / GAMES\n"
        L"1. Install VB-Cable (free) and click \"Use VB-Cable\".\n"
        L"2. In Discord, set Input Device to \"CABLE Output\".\n"
        L"3. Set Noise Suppression to None or Standard (Krisp erases the effect), and turn off Echo "
        L"Cancellation and Automatic Gain Control.\n"
        L"4. Turn on Lag Effect's noise gate to keep background noise out.\n\n"
        L"OBS\n"
        L"With VB-Cable: add Audio Input Capture = \"CABLE Output\".\n"
        L"Without VB-Cable: add Application Audio Capture and pick LagEffect.exe.\n"
        L"Mute your normal mic source in OBS so you aren't heard twice.\n\n"
        L"UPDATES\n"
        L"Type the GitHub user/repo you publish releases to, then click \"Check now\".\n\n"
        L"TIPS\n"
        L"Use headphones. If a game runs as administrator, run Lag Effect as administrator too, "
        L"or the hotkey won't work while that game is focused.",
        L"Lag Effect " APP_VERSION L" - Help", MB_ICONINFORMATION);
}

// ======================= hotkey picker =======================
static void BeginKeyCapture()
{
    gCapturingKey = true;
    gWaitRelease = 0;
    for (int vk = 0; vk < 256; vk++) gKeyWasDown[vk] = (GetAsyncKeyState(vk) & 0x8000) != 0;
    SetDlgItemTextW(gWnd, IDC_HOTKEY, L"Press any key...  (Esc = cancel)");
    SetTimer(gWnd, TIMER_KEY, 15, nullptr);
}

static void PollKeyCapture()
{
    if (gWaitRelease) {                         // don't trigger the effect until the new key is let go
        if (!(GetAsyncKeyState(gWaitRelease) & 0x8000)) {
            gWaitRelease = 0;
            gCapturingKey = false;
            KillTimer(gWnd, TIMER_KEY);
        }
        return;
    }
    for (int vk = 2; vk < 256; vk++) {          // 1 = left mouse, skipped
        if (vk == VK_SHIFT || vk == VK_CONTROL || vk == VK_MENU) continue;   // use left/right versions
        bool d = (GetAsyncKeyState(vk) & 0x8000) != 0;
        bool pressed = d && !gKeyWasDown[vk];
        gKeyWasDown[vk] = d;
        if (!pressed) continue;
        if (vk != VK_ESCAPE) gHotkey = vk;
        wchar_t name[64]; KeyName(gHotkey, name, 64);
        SetDlgItemTextW(gWnd, IDC_HOTKEY, name);
        gWaitRelease = vk;
        UpdateStatus(true);
        return;
    }
}

// ======================= tray =======================
static void ToTray()
{
    NOTIFYICONDATAW nid = {};
    nid.cbSize = sizeof(nid);
    nid.hWnd = gWnd;
    nid.uID = 1;
    nid.uFlags = NIF_ICON | NIF_MESSAGE | NIF_TIP;
    nid.uCallbackMessage = WM_TRAY;
    nid.hIcon = gIcon;
    lstrcpynW(nid.szTip, L"Lag Effect", 128);
    if (!gInTray) Shell_NotifyIconW(NIM_ADD, &nid);
    gInTray = true;
    ShowWindow(gWnd, SW_HIDE);
}

static void RemoveTray()
{
    if (!gInTray) return;
    NOTIFYICONDATAW nid = {};
    nid.cbSize = sizeof(nid);
    nid.hWnd = gWnd;
    nid.uID = 1;
    Shell_NotifyIconW(NIM_DELETE, &nid);
    gInTray = false;
}

static void FromTray()
{
    RemoveTray();
    ShowWindow(gWnd, SW_SHOW);
    ShowWindow(gWnd, SW_RESTORE);
    SetForegroundWindow(gWnd);
}

static void TrayMenu()
{
    POINT p; GetCursorPos(&p);
    HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING, ID_TRAY_OPEN, L"Open");
    AppendMenuW(m, MF_STRING, ID_TRAY_RUN, gWantRunning ? L"Stop audio" : L"Start audio");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(m, MF_STRING, ID_TRAY_EXIT, L"Exit");
    SetForegroundWindow(gWnd);
    TrackPopupMenu(m, TPM_RIGHTBUTTON, p.x, p.y, 0, gWnd, nullptr);
    DestroyMenu(m);
}

// ======================= window =======================
#define CLIENT_W 430
#define CLIENT_H 534

static void CreateUI()
{
    const DWORD COMBO = CBS_DROPDOWNLIST | WS_VSCROLL | WS_TABSTOP;

    // Devices
    Ctl(L"BUTTON", L"Audio devices", BS_GROUPBOX, 10, 6, 410, 112, -1);
    Ctl(L"STATIC", L"Microphone:", 0, 22, 32, 80, 20, -1);
    Ctl(L"COMBOBOX", L"", COMBO, 105, 28, 303, 300, IDC_MIC);
    Ctl(L"STATIC", L"Send to:", 0, 22, 60, 80, 20, -1);
    Ctl(L"COMBOBOX", L"", COMBO, 105, 56, 210, 300, IDC_OUT);
    Ctl(L"BUTTON", L"Use VB-Cable", WS_TABSTOP, 320, 55, 88, 25, IDC_VBCABLE);
    Ctl(L"STATIC", L"Hear on:", 0, 22, 88, 80, 20, -1);
    Ctl(L"COMBOBOX", L"", COMBO, 105, 84, 210, 300, IDC_MON);
    HWND mm = Ctl(L"COMBOBOX", L"", COMBO, 320, 84, 88, 200, IDC_MONMODE);
    const wchar_t* monNames[] = { L"Off", L"Effect only", L"Everything" };
    for (const wchar_t* n : monNames) SendMessageW(mm, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(mm, CB_SETCURSEL, gMonMode, 0);
    FillDevices();

    // Effect
    Ctl(L"BUTTON", L"Effect", BS_GROUPBOX, 10, 124, 410, 150, -1);
    Ctl(L"STATIC", L"Loop length:", 0, 22, 151, 80, 20, -1);
    Spin(IDC_LOOP, 105, 148, 10, 2000, gLoopMs);
    Ctl(L"STATIC", L"ms", 0, 175, 151, 30, 20, -1);
    Ctl(L"STATIC", L"Speed:", 0, 222, 151, 76, 20, -1);
    Spin(IDC_SPEED, 300, 148, 10, 400, gSpeedPct);
    Ctl(L"STATIC", L"%", 0, 370, 151, 30, 20, -1);

    Ctl(L"STATIC", L"Pitch:", 0, 22, 181, 80, 20, -1);
    Spin(IDC_PITCH, 105, 178, 25, 400, gPitchPct);
    Ctl(L"STATIC", L"%", 0, 175, 181, 30, 20, -1);
    Ctl(L"STATIC", L"Smoothing:", 0, 222, 181, 76, 20, -1);
    Spin(IDC_FADE, 300, 178, 0, 50, gFadeMs);
    Ctl(L"STATIC", L"ms", 0, 370, 181, 30, 20, -1);

    Ctl(L"STATIC", L"Send volume:", 0, 22, 211, 80, 20, -1);
    Spin(IDC_VOL, 105, 208, 0, 200, gVolPct);
    Ctl(L"STATIC", L"%", 0, 175, 211, 30, 20, -1);
    Ctl(L"STATIC", L"Hear volume:", 0, 222, 211, 76, 20, -1);
    Spin(IDC_MONVOL, 300, 208, 0, 200, gMonVolPct);
    Ctl(L"STATIC", L"%", 0, 370, 211, 30, 20, -1);

    Ctl(L"BUTTON", L"Noise gate", BS_AUTOCHECKBOX | WS_TABSTOP, 22, 241, 80, 20, IDC_GATEON);
    CheckDlgButton(gWnd, IDC_GATEON, gGateOn ? BST_CHECKED : BST_UNCHECKED);
    Spin(IDC_GATE, 105, 238, 20, 90, gGateDb);
    Ctl(L"STATIC", L"-dB", 0, 175, 241, 30, 20, -1);
    Ctl(L"BUTTON", L"Send mic when not looping", BS_AUTOCHECKBOX | WS_TABSTOP, 222, 241, 190, 20, IDC_PASS);
    CheckDlgButton(gWnd, IDC_PASS, gPassThrough ? BST_CHECKED : BST_UNCHECKED);

    // Hotkey + latency
    wchar_t key[64]; KeyName(gHotkey, key, 64);
    Ctl(L"BUTTON", L"Hotkey", BS_GROUPBOX, 10, 280, 200, 84, -1);
    Ctl(L"BUTTON", key, WS_TABSTOP, 22, 302, 176, 28, IDC_HOTKEY);
    Ctl(L"BUTTON", L"Hold", BS_AUTORADIOBUTTON | WS_GROUP | WS_TABSTOP, 22, 336, 70, 20, IDC_HOLD);
    Ctl(L"BUTTON", L"Toggle", BS_AUTORADIOBUTTON, 100, 336, 90, 20, IDC_TOGGLE);
    CheckRadioButton(gWnd, IDC_HOLD, IDC_TOGGLE, gToggleMode ? IDC_TOGGLE : IDC_HOLD);

    Ctl(L"BUTTON", L"Latency", BS_GROUPBOX | WS_GROUP, 220, 280, 200, 84, -1);
    Ctl(L"STATIC", L"Buffer:", 0, 232, 307, 50, 20, -1);
    HWND buf = Ctl(L"COMBOBOX", L"", COMBO, 285, 303, 123, 200, IDC_BUFFER);
    const wchar_t* bufNames[] = { L"32 (fastest)", L"64", L"128 (default)", L"256", L"512 (safest)" };
    for (const wchar_t* n : bufNames) SendMessageW(buf, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(buf, CB_SETCURSEL, gBufIdx, 0);
    Ctl(L"BUTTON", L"Exclusive mode", BS_AUTOCHECKBOX | WS_TABSTOP, 232, 336, 170, 20, IDC_EXCL);
    CheckDlgButton(gWnd, IDC_EXCL, gExclusive ? BST_CHECKED : BST_UNCHECKED);

    // Status + buttons
    gStatus = Ctl(L"STATIC", L"", SS_CENTER | SS_CENTERIMAGE | SS_SUNKEN, 10, 372, 410, 22, IDC_STATUS);
    Ctl(L"BUTTON", L"Start", WS_TABSTOP, 10, 400, 134, 34, IDC_START);
    Ctl(L"BUTTON", L"Minimize to tray", WS_TABSTOP, 148, 400, 134, 34, IDC_TRAY);
    Ctl(L"BUTTON", L"Help / Discord && OBS", WS_TABSTOP, 286, 400, 134, 34, IDC_HELPBTN);

    // App options
    Ctl(L"BUTTON", L"App", BS_GROUPBOX, 10, 442, 410, 84, -1);
    Ctl(L"STATIC", L"Theme:", 0, 22, 467, 50, 20, -1);
    HWND th = Ctl(L"COMBOBOX", L"", COMBO, 72, 463, 82, 200, IDC_THEME);
    const wchar_t* themeNames[] = { L"System", L"Light", L"Dark" };
    for (const wchar_t* n : themeNames) SendMessageW(th, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(th, CB_SETCURSEL, gThemeMode, 0);
    Ctl(L"BUTTON", L"Start audio && hide in tray when opened", BS_AUTOCHECKBOX | WS_TABSTOP, 166, 466, 246, 20, IDC_AUTO);
    CheckDlgButton(gWnd, IDC_AUTO, gAutoStart ? BST_CHECKED : BST_UNCHECKED);

    Ctl(L"STATIC", L"Updates:", 0, 22, 497, 50, 20, -1);
    HWND repo = Ctl(L"EDIT", gUpdateRepo, WS_TABSTOP | ES_AUTOHSCROLL, 72, 494, 150, 23, IDC_REPO, WS_EX_CLIENTEDGE);
    SendMessageW(repo, EM_SETCUEBANNER, TRUE, (LPARAM)L"github-user/repo");
    Ctl(L"BUTTON", L"Check now", WS_TABSTOP, 228, 493, 86, 25, IDC_CHECKUPD);
    Ctl(L"BUTTON", L"On startup", BS_AUTOCHECKBOX | WS_TABSTOP, 322, 496, 92, 20, IDC_UPDSTART);
    CheckDlgButton(gWnd, IDC_UPDSTART, gUpdateOnStart ? BST_CHECKED : BST_UNCHECKED);

    gUiReady = true;
}

static bool Checked(int id) { return IsDlgButtonChecked(gWnd, id) == BST_CHECKED; }

static void OnCommand(int id, int code)
{
    switch (id) {
    case IDC_LOOP: case IDC_SPEED: case IDC_PITCH: case IDC_VOL: case IDC_FADE: case IDC_GATE: case IDC_MONVOL:
        if (!gUiReady) break;
        for (Range& r : gRanges) {
            if (r.id != id) continue;
            BOOL ok = FALSE;
            int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
            if (code == EN_CHANGE && ok) *r.var = Iclamp(v, r.lo, r.hi);
            else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)*r.var, FALSE);
        }
        if (id == IDC_GATE) UpdateGateLin();
        break;
    case IDC_REPO:
        if (code == EN_CHANGE && gUiReady) GetDlgItemTextW(gWnd, IDC_REPO, gUpdateRepo, 200);
        break;
    case IDC_GATEON:   gGateOn = Checked(IDC_GATEON); break;
    case IDC_PASS:     gPassThrough = Checked(IDC_PASS); break;
    case IDC_UPDSTART: gUpdateOnStart = Checked(IDC_UPDSTART); break;
    case IDC_CHECKUPD: if (code == BN_CLICKED) StartUpdateCheck(true); break;
    case IDC_HOLD:
    case IDC_TOGGLE:   gToggleMode = Checked(IDC_TOGGLE); UpdateStatus(true); break;
    case IDC_HOTKEY:   if (code == BN_CLICKED) BeginKeyCapture(); break;
    case IDC_THEME:
        if (code == CBN_SELCHANGE) {
            gThemeMode = (int)SendDlgItemMessageW(gWnd, IDC_THEME, CB_GETCURSEL, 0, 0);
            ApplyTheme();
        }
        break;
    case IDC_MIC: case IDC_OUT: case IDC_MON:
        if (code == CBN_SELCHANGE) RestartIfRunning();
        break;
    case IDC_MONMODE:
        if (code == CBN_SELCHANGE) {
            int newMode = (int)SendDlgItemMessageW(gWnd, IDC_MONMODE, CB_GETCURSEL, 0, 0);
            bool needDevice = (newMode == MON_OFF) != (gMonMode == MON_OFF);
            gMonMode = newMode;
            if (needDevice) RestartIfRunning();
        }
        break;
    case IDC_BUFFER:
        if (code == CBN_SELCHANGE) {
            gBufIdx = (int)SendDlgItemMessageW(gWnd, IDC_BUFFER, CB_GETCURSEL, 0, 0);
            RestartIfRunning();
        }
        break;
    case IDC_EXCL:    gExclusive = Checked(IDC_EXCL); RestartIfRunning(); break;
    case IDC_AUTO:    gAutoStart = Checked(IDC_AUTO); break;
    case IDC_VBCABLE: SetupVbCable(); break;
    case IDC_HELPBTN: ShowHelp(); break;
    case IDC_START:
    case ID_TRAY_RUN:
        if (gWantRunning) StopAudio(); else StartAudio(false);
        UpdateUi();
        break;
    case IDC_TRAY:     ToTray(); break;
    case ID_TRAY_OPEN: FromTray(); break;
    case ID_TRAY_EXIT: PostMessageW(gWnd, WM_CLOSE, 0, 0); break;
    }
}

static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_CREATE:
        gWnd = h;
        CreateUI();
        ApplyTheme();
        if (gAutoStart && !StartAudio(true)) SetTimer(h, TIMER_RECONNECT, 2000, nullptr);
        UpdateUi();
        SetTimer(h, TIMER_STATUS, 50, nullptr);
        SetTimer(h, TIMER_CLEANUP, 1000, nullptr);
        return 0;
    case WM_TIMER:
        if (w == TIMER_STATUS) UpdateStatus();
        else if (w == TIMER_KEY) PollKeyCapture();
        else if (w == TIMER_CLEANUP) CleanupOldExe();
        else if (w == TIMER_RECONNECT) {
            if (!gWantRunning || gRunning || StartAudio(true)) KillTimer(h, TIMER_RECONNECT);
            UpdateUi();
        }
        return 0;
    case WM_DEVICE_LOST:                        // unplugged headset etc: keep retrying quietly
        if (gWantRunning) {
            StopDevices();
            SetTimer(h, TIMER_RECONNECT, 1500, nullptr);
            UpdateUi();
        }
        return 0;
    case WM_UPDATE_CHECKED:
        OnUpdateChecked((UpdateJob*)l);
        return 0;
    case WM_UPDATE_DOWNLOAD:
        OnUpdateDownloaded((UpdateJob*)l);
        return 0;
    case WM_COMMAND:
        OnCommand(LOWORD(w), HIWORD(w));
        return 0;
    case WM_SYSCOMMAND:
        if ((w & 0xFFF0) == SC_MINIMIZE) { ToTray(); return 0; }   // minimize goes to the tray
        break;
    case WM_TRAY:
        if (l == WM_LBUTTONUP || l == WM_LBUTTONDBLCLK) FromTray();
        else if (l == WM_RBUTTONUP) TrayMenu();
        return 0;
    case WM_SETTINGCHANGE:
        if (gThemeMode == THEME_SYSTEM && l && lstrcmpW((LPCWSTR)l, L"ImmersiveColorSet") == 0) ApplyTheme();
        break;
    case WM_ERASEBKGND: {
        RECT rc; GetClientRect(h, &rc);
        FillRect((HDC)w, &rc, gDark ? gBrBg : GetSysColorBrush(COLOR_BTNFACE));
        return 1;
    }
    case WM_CTLCOLORSTATIC: case WM_CTLCOLORBTN: case WM_CTLCOLOREDIT: case WM_CTLCOLORLISTBOX: {
        HDC dc = (HDC)w;
        bool status = (HWND)l == gStatus;
        if (!gDark) {
            if (!status) break;
            SetBkMode(dc, TRANSPARENT);
            SetTextColor(dc, gLooping ? RGB(200, 30, 30) : GetSysColor(COLOR_WINDOWTEXT));
            return (LRESULT)GetSysColorBrush(COLOR_BTNFACE);
        }
        bool field = m == WM_CTLCOLOREDIT || m == WM_CTLCOLORLISTBOX;
        SetTextColor(dc, status && gLooping ? RGB(255, 95, 95) : DK_TEXT);
        SetBkColor(dc, field ? DK_CTL : DK_BG);
        return (LRESULT)(field ? gBrCtl : gBrBg);
    }
    case WM_CLOSE:
        SaveSettings();
        StopAudio();
        RemoveTray();
        DestroyWindow(h);
        return 0;
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(h, m, w, l);
}

int WINAPI WinMain(HINSTANCE hi, HINSTANCE, LPSTR, int show)
{
    gInst = hi;
    INITCOMMONCONTROLSEX icc = {};
    icc.dwSize = sizeof(icc);
    icc.dwICC = ICC_STANDARD_CLASSES | ICC_UPDOWN_CLASS;
    InitCommonControlsEx(&icc);

    bool justUpdated = wcsstr(GetCommandLineW(), L"--updated") != nullptr;

    LoadSettings();
    LoadThemeApis();
    gCtxOk = ma_context_init(nullptr, 0, nullptr, &gCtx) == MA_SUCCESS;
    if (gCtxOk) ma_context_get_devices(&gCtx, &gOuts, &gOutCount, &gIns, &gInCount);

    gFont = CreateFontW(-13, 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    gIcon = LoadIconW(hi, MAKEINTRESOURCEW(1));          // custom icon if built with LagEffect.rc
    if (!gIcon) gIcon = LoadIconW(nullptr, IDI_APPLICATION);

    WNDCLASSW wc = {};
    wc.lpfnWndProc   = WndProc;
    wc.hInstance     = hi;
    wc.hIcon         = gIcon;
    wc.hCursor       = LoadCursorW(nullptr, IDC_ARROW);
    wc.hbrBackground = nullptr;                          // painted in WM_ERASEBKGND (light or dark)
    wc.lpszClassName = L"LagEffectWnd";
    RegisterClassW(&wc);

    DWORD style = WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX;
    RECT r = { 0, 0, CLIENT_W, CLIENT_H };
    AdjustWindowRect(&r, style, FALSE);
    HWND h = CreateWindowExW(0, wc.lpszClassName, L"Lag Effect " APP_VERSION, style, CW_USEDEFAULT, CW_USEDEFAULT,
                             r.right - r.left, r.bottom - r.top, nullptr, nullptr, hi, nullptr);
    if (!h) return 1;

    if (!gCtxOk) MessageBoxW(h, L"Couldn't start the Windows audio system.", L"Lag Effect", MB_ICONERROR);
    if (gAutoStart && !justUpdated) ToTray();
    else { ShowWindow(h, show); UpdateWindow(h); }

    if (justUpdated)
        MessageBoxW(h, L"Lag Effect was updated to version " APP_VERSION L".", L"Lag Effect", MB_ICONINFORMATION);
    else if (gUpdateOnStart && gUpdateRepo[0])
        StartUpdateCheck(false);

    MSG msg;
    while (GetMessageW(&msg, nullptr, 0, 0) > 0) {
        if (!IsDialogMessageW(h, &msg)) {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
    }
    if (gCtxOk) ma_context_uninit(&gCtx);
    DeleteObject(gFont);
    return 0;
}
