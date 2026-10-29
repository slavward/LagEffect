// LagEffect.cpp - hold (or toggle) a hotkey to loop the last chunk of your mic.
// Windows app with a settings window and tray icon. Settings save to LagEffect.ini.
// Built for Discord / OBS: several outputs each playing Off / Effect only / Everything,
// built-in noise gate, auto-reconnect, separate pitch/speed, light/dark theme, GitHub updater,
// and a Voice FX page (pitch shift + reverb on your live voice, set with knobs).
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
// is the version (e.g. v1.4.0) and attach LagEffect.exe. The app's "Check now" button finds it.

#define APP_VERSION L"1.6.0"
#define DEFAULT_UPDATE_REPO L"slavward/LagEffect"

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
#include <stdlib.h>
#include <math.h>
#if defined(_M_X64) || defined(__x86_64__) || defined(_M_IX86) || defined(__i386__)
#include <xmmintrin.h>
#define HAVE_SSE_FLAGS 1
#endif

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
#define RATE      48000
#define HIST      (RATE * 2)                   // loops up to 2 seconds long
#define RING_SIZE 16384                        // per-output ring buffer (power of two)
#define MAXGRAIN  (RATE * 40 / 1000)           // 40 ms grains for pitch/speed
#define MAX_OUT   5                            // output rows
static const int BUFFERS[] = { 32, 64, 128, 256, 512 };

enum { MODE_OFF = 0, MODE_EFFECT = 1, MODE_ALL = 2 };

// Settings shared with the audio threads (plain ints/floats are safe to read on x86/x64).
static volatile int   gLoopMs = 500, gSpeedPct = 100, gPitchPct = 100, gFadeMs = 3;
static volatile int   gGateDb = 50, gTalkVolPct = 100;
#define MAX_KEYS 3                             // hotkey can be a combination of up to 3 keys
static volatile int   gHotkeys[MAX_KEYS] = { VK_F8, 0, 0 };
static volatile bool  gToggleMode = false, gGateOn = false, gTalkOver = false;
static volatile bool  gCapturingKey = false, gLooping = false;
static volatile float gGateLin = 0.00316f;     // -50 dB
static volatile int   gRowMode[MAX_OUT] = { MODE_ALL, MODE_EFFECT, MODE_EFFECT, MODE_EFFECT, MODE_EFFECT };
static volatile int   gRowVol[MAX_OUT]  = { 100, 100, 100, 100, 100 };

static float  hist[HIST], frozen[HIST], hann[MAXGRAIN];
static size_t wpos = 0, frozenLen = 1;
static bool   looping = false, prevDown = false, toggled = false;
static double loopPos = 0, grainStart[2];
static int    grainAge[2], grainLen = 2;
static float  gateEnv = 0, gateGain = 1;
static int    gateHold = 0;

// Output 1 plays straight from the main audio callback. Outputs 2-5 are separate devices
// fed through ring buffers.
static float             ring[MAX_OUT][RING_SIZE];
static volatile unsigned ringW[MAX_OUT], ringR[MAX_OUT];
static volatile bool     ringOn[MAX_OUT];

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

// Leaves normal levels untouched and gently rounds off peaks above 0.7 (voice + loop can add up).
static inline float SoftLimit(float x)
{
    float a = x < 0 ? -x : x;
    if (a <= 0.7f) return x;
    float y = 0.7f + 0.3f * tanhf((a - 0.7f) / 0.3f);
    return x < 0 ? -y : y;
}

static inline float RowSignal(int mode, float effect, float everything)
{
    return mode == MODE_EFFECT ? effect : mode == MODE_ALL ? everything : 0.0f;
}

// True while every key in a hotkey combination is held down (false if the combination is empty).
static bool KeysDown(const volatile int* keys)
{
    bool any = false;
    for (int i = 0; i < MAX_KEYS; i++) {
        int vk = keys[i];
        if (!vk) continue;
        any = true;
        if (!(GetAsyncKeyState(vk) & 0x8000)) return false;
    }
    return any;
}

static bool ComboDown() { return KeysDown(gHotkeys); }

// ======================= voice effects (Voice FX page) =======================
// Run on the live mic right after the noise gate, so they're on everything you send, and the
// stutter loop records them too. Each effect has its own on/off switch and knobs; to add one,
// write its Process function, call it in AudioCallback, and add a group + knobs to gFxGroups/gKnobs.
static volatile bool gFxOn = false;            // master switch at the top of the page
static volatile bool gFxPitchOn = true, gFxRevOn = true;
static volatile int  gFxSemi = 0, gFxCents = 0, gFxGrainMs = 50, gFxPitchMix = 100;
static volatile int  gFxRevMix = 30, gFxRevSize = 60, gFxRevDamp = 50, gFxPreMs = 20;
static volatile bool gFxResetReq = true;       // UI asks the audio thread to clear effect buffers

// Pitch shifter: two read taps glide through a short delay line at the new speed and crossfade
// (Hann windows, half a grain apart). Each new grain starts where the waveform best lines up with
// the one fading out, so the crossfade stays in phase: no warble, no level dips.
#define PS_SIZE   8192                         // > 100 ms grain span + search at 48 kHz
#define PS_SEARCH 720                          // 15 ms: covers voice pitch periods down to ~67 Hz
#define PS_CORR   192                          // samples compared when lining up a grain
static float  psBuf[PS_SIZE];
static int    psW = 0;
static double psDelay[2], psFrac[2];
static bool   psPrimed = false;

static inline float PsRead(double d)
{
    double rp = (double)psW - d;
    if (rp < 0) rp += PS_SIZE;
    int   i0 = (int)rp;
    float t  = (float)(rp - i0);
    float a = psBuf[i0 & (PS_SIZE - 1)], b = psBuf[(i0 + 1) & (PS_SIZE - 1)];
    return a + (b - a) * t;
}

static double PsGrainStart(int k, double ratio, int span)
{
    // Going up, the read point catches up with the input, so a grain starts a full span back.
    int base  = ratio > 1.0 ? 1 + span : 1;
    int other = (int)(psDelay[1 - k] + 0.5);
    float best = -1e30f; int bestD = 0;
    for (int d = 0; d < PS_SEARCH; d += 2) {
        int cand = base + d;
        float dot = 0, e = 0;
        for (int j = 0; j < PS_CORR; j += 2) {
            float x = psBuf[(psW - other - j) & (PS_SIZE - 1)];
            float y = psBuf[(psW - cand - j) & (PS_SIZE - 1)];
            dot += x * y; e += y * y;
        }
        float score = dot / sqrtf(e + 1e-9f);
        if (score > best) { best = score; bestD = d; }
    }
    return (double)(base + bestD);
}

static float PitchShift(float x, double ratio, int span, float mix)
{
    psBuf[psW] = x;
    float out = x;
    if (ratio != 1.0) {
        double grain = span / fabs(1.0 - ratio);           // one grain sweeps the whole span
        if (grain > RATE) grain = RATE;
        if (grain < 256)  grain = 256;
        if (!psPrimed) {
            psDelay[0] = psDelay[1] = ratio > 1.0 ? 1 + span : 1;
            psFrac[0] = 0.0; psFrac[1] = 0.5;
            psPrimed = true;
        }
        const double maxD = PS_SIZE - PS_CORR - 4;
        float wet = 0.0f;
        for (int k = 0; k < 2; k++) {
            if (psFrac[k] >= 1.0) { psFrac[k] -= 1.0; psDelay[k] = PsGrainStart(k, ratio, span); }
            if (psDelay[k] < 1.0)  psDelay[k] = 1.0;
            if (psDelay[k] > maxD) psDelay[k] = maxD;
            float s = (float)sin(3.141592653589793 * psFrac[k]);
            wet += PsRead(psDelay[k]) * s * s;
            psDelay[k] += 1.0 - ratio;
            psFrac[k]  += 1.0 / grain;
        }
        out = x + (wet - x) * mix;
    } else {
        psPrimed = false;
    }
    psW = (psW + 1) & (PS_SIZE - 1);
    return out;
}

// Reverb: Freeverb-style (8 damped comb filters into 4 allpasses), with a pre-delay in front.
static const int COMB_TUNE[8] = { 1116, 1188, 1277, 1356, 1422, 1491, 1557, 1617 };   // at 44.1 kHz
static const int AP_TUNE[4]   = { 556, 441, 341, 225 };
#define COMB_MAX 1800
#define AP_MAX   640
#define PRE_SIZE 16384                         // > 200 ms at 48 kHz
static float combBuf[8][COMB_MAX], combStore[8], apBuf[4][AP_MAX], preBuf[PRE_SIZE];
static int   combLen[8], combIdx[8], apLen[4], apIdx[4], preW = 0;

static float Reverb(float x, float size, float damp, float mix, int pre)
{
    preBuf[preW] = x;
    float in = preBuf[(preW - pre) & (PRE_SIZE - 1)] * 0.015f;
    preW = (preW + 1) & (PRE_SIZE - 1);

    const float fb = 0.7f + 0.28f * size, d1 = damp * 0.4f, d2 = 1.0f - d1;
    float acc = 0.0f;
    for (int i = 0; i < 8; i++) {
        float y = combBuf[i][combIdx[i]];
        combStore[i] = y * d2 + combStore[i] * d1;
        combBuf[i][combIdx[i]] = in + combStore[i] * fb;
        if (++combIdx[i] >= combLen[i]) combIdx[i] = 0;
        acc += y;
    }
    for (int i = 0; i < 4; i++) {
        float b = apBuf[i][apIdx[i]];
        apBuf[i][apIdx[i]] = acc + b * 0.5f;
        acc = b - acc;
        if (++apIdx[i] >= apLen[i]) apIdx[i] = 0;
    }
    return x + (acc * 3.0f - x) * mix;
}

static void FxReset()                          // audio thread only
{
    memset(psBuf, 0, sizeof(psBuf)); psW = 0; psPrimed = false;
    memset(combBuf, 0, sizeof(combBuf)); memset(combStore, 0, sizeof(combStore));
    memset(apBuf, 0, sizeof(apBuf)); memset(preBuf, 0, sizeof(preBuf)); preW = 0;
    for (int i = 0; i < 8; i++) { combLen[i] = Imin(COMB_TUNE[i] * RATE / 44100, COMB_MAX); combIdx[i] = 0; }
    for (int i = 0; i < 4; i++) { apLen[i] = Imin(AP_TUNE[i] * RATE / 44100, AP_MAX); apIdx[i] = 0; }
}

static void AudioCallback(ma_device*, void* output, const void* input, ma_uint32 frames)
{
#ifdef HAVE_SSE_FLAGS
    _mm_setcsr(_mm_getcsr() | 0x8040);         // flush denormals to zero: reverb tails stay cheap
#endif
    float* out = (float*)output;                // stereo
    const float* in = (const float*)input;      // mono

    bool down = !gCapturingKey && ComboDown();
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
        grainStart[0] = 0;                                      grainAge[0] = 0;
        grainStart[1] = WrapPos(-(double)g / 2, (double)len);   grainAge[1] = g / 2;
        looping = true;
    } else if (!active) {
        looping = false;
    }
    gLooping = looping;

    int      mode[MAX_OUT];
    float    vol[MAX_OUT];
    bool     on[MAX_OUT];
    unsigned w[MAX_OUT], r[MAX_OUT];
    for (int k = 0; k < MAX_OUT; k++) {
        mode[k] = gRowMode[k];
        vol[k]  = gRowVol[k] / 100.0f;
        on[k]   = k > 0 && ringOn[k];
        w[k]    = ringW[k];
        r[k]    = ringR[k];
    }

    const bool   gateOn  = gGateOn;
    const float  thr     = gGateLin;
    const bool   talk    = gTalkOver;
    const float  talkVol = gTalkVolPct / 100.0f;
    const double speed   = gSpeedPct / 100.0;
    const double pitch   = gPitchPct / 100.0;
    const double len     = (double)frozenLen;
    double fade = (double)gFadeMs * RATE / 1000.0;
    if (fade * 2 > len) fade = len / 2.0;

    if (gFxResetReq) { FxReset(); gFxResetReq = false; }
    const bool   fxPitch = gFxOn && gFxPitchOn;
    const bool   fxRev   = gFxOn && gFxRevOn;
    const double psRatio = pow(2.0, (gFxSemi + gFxCents / 100.0) / 12.0);
    const int    psGrain = Iclamp(gFxGrainMs * RATE / 1000, 64, PS_SIZE - PS_SEARCH - PS_CORR - 8);
    const float  psMix   = gFxPitchMix / 100.0f;
    const float  rvMix = gFxRevMix / 100.0f, rvSize = gFxRevSize / 100.0f, rvDamp = gFxRevDamp / 100.0f;
    const int    rvPre = Iclamp(gFxPreMs * RATE / 1000, 0, PRE_SIZE - 1);

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
        if (fxPitch) s = PitchShift(s, psRatio, psGrain, psMix);
        if (fxRev)   s = Reverb(s, rvSize, rvDamp, rvMix, rvPre);

        float effect = 0.0f, everything;
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
            effect = v;
            everything = v;
            if (talk) {                         // keep talking over the loop
                everything += s * talkVol;
                hist[wpos] = s;                 // and keep recording, so the next trigger grabs fresh audio
                wpos = (wpos + 1) % HIST;
            }
        } else {
            hist[wpos] = s;
            wpos = (wpos + 1) % HIST;
            everything = s;
        }

        float o = SoftLimit(RowSignal(mode[0], effect, everything) * vol[0]);
        out[f * 2] = o;
        out[f * 2 + 1] = o;

        for (int k = 1; k < MAX_OUT; k++) {
            if (!on[k] || (w[k] - r[k]) >= RING_SIZE) continue;
            ring[k][w[k] & (RING_SIZE - 1)] = SoftLimit(RowSignal(mode[k], effect, everything) * vol[k]);
            w[k]++;
        }
    }
    MemoryBarrier();
    for (int k = 1; k < MAX_OUT; k++) if (on[k]) ringW[k] = w[k];
}

static void ExtraOutputCallback(ma_device* dev, void* output, const void*, ma_uint32 frames)
{
    int k = (int)(INT_PTR)dev->pUserData;
    float* out = (float*)output;                // stereo
    unsigned w = ringW[k];
    MemoryBarrier();
    unsigned r = ringR[k];
    unsigned avail = w - r;

    // Each device runs on its own clock; drop old audio so delay never builds up.
    unsigned maxLag = dev->playback.internalPeriodSizeInFrames * 3 + 512;
    if (avail > maxLag) { r = w - dev->playback.internalPeriodSizeInFrames; avail = w - r; }

    for (ma_uint32 f = 0; f < frames; f++) {
        float m = 0.0f;
        if (avail) { m = ring[k][r & (RING_SIZE - 1)]; r++; avail--; }
        out[f * 2] = m;
        out[f * 2 + 1] = m;
    }
    ringR[k] = r;
}

// ======================= app state =======================
enum {
    IDC_MIC = 101, IDC_ADDOUT, IDC_VBCABLE,
    IDC_LOOP, IDC_SPEED, IDC_PITCH, IDC_FADE, IDC_GATE, IDC_TALKVOL,
    IDC_GATEON, IDC_TALKON, IDC_HOTKEY, IDC_HOLD, IDC_TOGGLE, IDC_BUFFER, IDC_EXCL,
    IDC_STATUS, IDC_START, IDC_TRAY, IDC_HELPBTN, IDC_AUTO,
    IDC_THEME, IDC_REPO, IDC_CHECKUPD, IDC_UPDSTART, IDC_HDR, IDC_TAB0, IDC_TAB1, IDC_TAB2, IDC_VERSION,
    IDC_FXON, IDC_FXKEY_MASTER,
    IDC_ROWLBL = 400, IDC_ROWDEV = 410, IDC_ROWMODE = 420, IDC_ROWVOL = 430, IDC_ROWDEL = 440,
    IDC_FXGRP_ON = 460, IDC_FXGRP_RESET = 470, IDC_KNOB = 480, IDC_FXGRP_KEY = 490,   // + group / knob index
    ID_TRAY_OPEN = 900, ID_TRAY_RUN, ID_TRAY_EXIT
};
#define SPIN_UD(id)        ((id) + 100)      // up-down control paired with a number box
#define WM_TRAY            (WM_APP + 1)
#define WM_DEVICE_LOST     (WM_APP + 2)
#define WM_UPDATE_CHECKED  (WM_APP + 3)
#define WM_UPDATE_DOWNLOAD (WM_APP + 4)
#define TIMER_STATUS    1
#define TIMER_KEY       2
#define TIMER_RECONNECT 3
#define TIMER_CLEANUP   4
#define TIMER_FXKEYS    5

static HINSTANCE gInst; static HWND gWnd, gStatus; static HFONT gFont, gFontBold; static HICON gIcon;
static ma_context gCtx; static ma_device gDev, gExtraDev[MAX_OUT];
static bool gCtxOk = false, gRunning = false, gWantRunning = false, gStopping = false;
static bool gExtraRunning[MAX_OUT];
static ma_device_info *gPlayDevs = nullptr, *gCapDevs = nullptr; static ma_uint32 gPlayCount = 0, gCapCount = 0;
static int  gRows = 1, gBufIdx = 2;
static bool gExclusive = false, gAutoStart = false, gInTray = false, gUiReady = false;
static wchar_t gMicName[512], gRowName[MAX_OUT][512], gIni[MAX_PATH];
static bool gKeyWasDown[256];
static int  gCapKeys[MAX_KEYS], gCapKeyCount = 0;

struct Range { int id, lo, hi; volatile int* var; const wchar_t* key; };
static Range gRanges[] = {
    { IDC_LOOP,    10, 2000, &gLoopMs,     L"loop_ms"         },
    { IDC_SPEED,   10, 400,  &gSpeedPct,   L"speed"           },
    { IDC_PITCH,   25, 400,  &gPitchPct,   L"pitch"           },
    { IDC_FADE,    0,  50,   &gFadeMs,     L"smoothing_ms"    },
    { IDC_GATE,    20, 90,   &gGateDb,     L"gate_db"         },
    { IDC_TALKVOL, 0,  200,  &gTalkVolPct, L"talkover_volume" },
};

// Voice FX page: one group (section) per effect, each with an on/off box and a row of knobs.
struct FxGroup { const wchar_t* title; volatile bool* on; const wchar_t* key; bool def; const wchar_t* hotkeyKey; };
static FxGroup gFxGroups[] = {
    { L"Pitch",  &gFxPitchOn, L"fx_pitch_on",  true, L"fx_pitch_hotkey"  },
    { L"Reverb", &gFxRevOn,   L"fx_reverb_on", true, L"fx_reverb_hotkey" },
};
#define FX_GROUPS ((int)(sizeof(gFxGroups) / sizeof(gFxGroups[0])))

// Optional hotkeys that switch Voice FX on/off: slot 0 = the whole page, slot 1+g = effect group g.
// Each is a combination of up to MAX_KEYS keys (0 = unused). Polled by the window (TIMER_FXKEYS).
#define FX_KEY_SLOTS (1 + FX_GROUPS)
static int  gFxKeys[FX_KEY_SLOTS][MAX_KEYS];
static bool gFxKeyWasDown[FX_KEY_SLOTS];

struct Knob { const wchar_t* label; const wchar_t* unit; int lo, hi, def; volatile int* var; const wchar_t* key; int group; bool bipolar; };
static Knob gKnobs[] = {
    { L"Pitch",     L" st", -12, 12,  0,   &gFxSemi,     L"fx_pitch_semitones", 0, true  },
    { L"Fine",      L" ct", -100, 100, 0,  &gFxCents,    L"fx_pitch_cents",     0, true  },
    { L"Grain",     L" ms", 20,  100, 50,  &gFxGrainMs,  L"fx_pitch_grain_ms",  0, false },
    { L"Mix",       L"%",   0,   100, 100, &gFxPitchMix, L"fx_pitch_mix",       0, false },
    { L"Mix",       L"%",   0,   100, 30,  &gFxRevMix,   L"fx_reverb_mix",      1, false },
    { L"Size",      L"%",   0,   100, 60,  &gFxRevSize,  L"fx_reverb_size",     1, false },
    { L"Damping",   L"%",   0,   100, 50,  &gFxRevDamp,  L"fx_reverb_damping",  1, false },
    { L"Pre-delay", L" ms", 0,   200, 20,  &gFxPreMs,    L"fx_reverb_predelay", 1, false },
};
#define KNOB_N ((int)(sizeof(gKnobs) / sizeof(gKnobs[0])))

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

static void ComboName(const int* keys, int count, wchar_t* buf, int cap)
{
    buf[0] = 0;
    for (int i = 0; i < count; i++) {
        if (!keys[i]) continue;
        wchar_t one[64];
        KeyName(keys[i], one, 64);
        if (buf[0] && lstrlenW(buf) + 3 < cap) lstrcatW(buf, L" + ");
        if (lstrlenW(buf) + lstrlenW(one) < cap) lstrcatW(buf, one);
    }
}

static void HotkeyName(wchar_t* buf, int cap)
{
    int keys[MAX_KEYS];
    for (int i = 0; i < MAX_KEYS; i++) keys[i] = gHotkeys[i];
    ComboName(keys, MAX_KEYS, buf, cap);
}

// ======================= theme (light / dark) =======================
enum { THEME_SYSTEM = 0, THEME_LIGHT = 1, THEME_DARK = 2 };
static int    gThemeMode = THEME_SYSTEM;
static bool   gDark = false;
static HBRUSH gBrDarkBg, gBrDarkCtl;

#define DK_BG      RGB(32, 32, 32)
#define DK_CTL     RGB(45, 45, 45)
#define DK_BORDER  RGB(78, 78, 78)
#define DK_SECTION RGB(64, 64, 64)
#define DK_TEXT    RGB(235, 235, 235)
#define DK_DIM     RGB(160, 160, 160)
#define ACCENT     RGB(76, 160, 255)

static COLORREF BgColor()  { return gDark ? DK_BG : GetSysColor(COLOR_BTNFACE); }
static HBRUSH   BgBrush()  { return gDark ? gBrDarkBg : GetSysColorBrush(COLOR_BTNFACE); }

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
    gBrDarkBg  = CreateSolidBrush(DK_BG);
    gBrDarkCtl = CreateSolidBrush(DK_CTL);
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
        // Push buttons use Windows' own dark style; checkboxes and radios are custom-drawn in dark mode.
        if (type == BS_PUSHBUTTON || type == BS_DEFPUSHBUTTON) SetTheme(h, gDark ? L"DarkMode_Explorer" : nullptr, nullptr);
    } else if (!lstrcmpiW(cls, L"ComboBox")) {
        SetTheme(h, gDark ? L"DarkMode_CFD" : nullptr, nullptr);
    } else if (!lstrcmpiW(cls, L"Edit")) {
        SetTheme(h, gDark ? L"DarkMode_CFD" : nullptr, nullptr);
        LONG ex = GetWindowLongW(h, GWL_EXSTYLE);          // flat border drawn by the window in dark mode
        LONG want = gDark ? (ex & ~WS_EX_CLIENTEDGE) : (ex | WS_EX_CLIENTEDGE);
        if (want != ex) {
            SetWindowLongW(h, GWL_EXSTYLE, want);
            SetWindowPos(h, nullptr, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE | SWP_FRAMECHANGED);
        }
    }
    InvalidateRect(h, nullptr, TRUE);
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

// Dark-mode checkbox / radio button, drawn from scratch (Windows has no dark version of these).
static LRESULT DrawDarkCheck(NMCUSTOMDRAW* cd)
{
    if (cd->dwDrawStage != CDDS_PREPAINT) return CDRF_DODEFAULT;
    HWND h = cd->hdr.hwndFrom;
    LONG type = GetWindowLongW(h, GWL_STYLE) & BS_TYPEMASK;
    bool radio = type == BS_AUTORADIOBUTTON || type == BS_RADIOBUTTON;
    if (!radio && type != BS_AUTOCHECKBOX && type != BS_CHECKBOX) return CDRF_DODEFAULT;

    HDC dc = cd->hdc;
    RECT rc = cd->rc;
    FillRect(dc, &rc, gBrDarkBg);
    bool checked = SendMessageW(h, BM_GETCHECK, 0, 0) == BST_CHECKED;
    bool hot = (cd->uItemState & CDIS_HOT) != 0;

    const int s = 15;
    int y = (rc.top + rc.bottom - s) / 2;
    HPEN   pen = CreatePen(PS_SOLID, 1, checked ? ACCENT : hot ? RGB(200, 200, 200) : RGB(135, 135, 135));
    HBRUSH br  = CreateSolidBrush(checked && !radio ? ACCENT : DK_CTL);
    HGDIOBJ oldPen = SelectObject(dc, pen), oldBr = SelectObject(dc, br);
    if (radio) Ellipse(dc, rc.left, y, rc.left + s, y + s);
    else       RoundRect(dc, rc.left, y, rc.left + s, y + s, 5, 5);
    SelectObject(dc, oldPen); SelectObject(dc, oldBr);
    DeleteObject(pen); DeleteObject(br);

    if (checked && radio) {
        HBRUSH dot = CreateSolidBrush(ACCENT);
        HPEN   none = CreatePen(PS_SOLID, 1, ACCENT);
        oldPen = SelectObject(dc, none); oldBr = SelectObject(dc, dot);
        Ellipse(dc, rc.left + 4, y + 4, rc.left + s - 4, y + s - 4);
        SelectObject(dc, oldPen); SelectObject(dc, oldBr);
        DeleteObject(dot); DeleteObject(none);
    } else if (checked) {
        HPEN tick = CreatePen(PS_SOLID, 2, RGB(255, 255, 255));
        oldPen = SelectObject(dc, tick);
        POINT pts[3] = { { rc.left + 4, y + 7 }, { rc.left + 6, y + 10 }, { rc.left + 11, y + 4 } };
        Polyline(dc, pts, 3);
        SelectObject(dc, oldPen);
        DeleteObject(tick);
    }

    wchar_t text[128];
    GetWindowTextW(h, text, 128);
    HGDIOBJ oldFont = SelectObject(dc, (HFONT)SendMessageW(h, WM_GETFONT, 0, 0));
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, DK_TEXT);
    RECT tr = rc; tr.left += s + 6;
    DrawTextW(dc, text, -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_LEFT);
    if (cd->uItemState & CDIS_FOCUS) {
        RECT fr = tr; DrawTextW(dc, text, -1, &fr, DT_SINGLELINE | DT_CALCRECT);
        fr.top = tr.top + 2; fr.bottom = tr.bottom - 2; InflateRect(&fr, 2, 0);
        SetTextColor(dc, DK_TEXT);
        DrawFocusRect(dc, &fr);
    }
    SelectObject(dc, oldFont);
    return CDRF_SKIPDEFAULT;
}

// Dark-mode up/down arrows for the number boxes.
static LRESULT CALLBACK UpDownProc(HWND h, UINT m, WPARAM w, LPARAM l, UINT_PTR, DWORD_PTR)
{
    if (gDark && m == WM_ERASEBKGND) return 1;
    if (gDark && m == WM_PAINT) {
        PAINTSTRUCT ps;
        HDC dc = BeginPaint(h, &ps);
        RECT rc; GetClientRect(h, &rc);
        int mid = (rc.top + rc.bottom) / 2;
        POINT cur; GetCursorPos(&cur); ScreenToClient(h, &cur);
        bool pressed = GetCapture() == h && (GetKeyState(VK_LBUTTON) & 0x8000);
        RECT top = rc, bot = rc;
        top.bottom = mid; bot.top = mid;
        FillRect(dc, &rc, gBrDarkCtl);
        if (pressed) {
            HBRUSH hi = CreateSolidBrush(RGB(70, 70, 70));
            FillRect(dc, cur.y < mid ? &top : &bot, hi);
            DeleteObject(hi);
        }
        HBRUSH arrow = CreateSolidBrush(RGB(200, 200, 200));
        HPEN   apen  = CreatePen(PS_SOLID, 1, RGB(200, 200, 200));
        HGDIOBJ op = SelectObject(dc, apen), ob = SelectObject(dc, arrow);
        int cx = (rc.left + rc.right) / 2;
        int ty = (top.top + top.bottom) / 2, by = (bot.top + bot.bottom) / 2;
        POINT up[3] = { { cx - 3, ty + 1 }, { cx + 3, ty + 1 }, { cx, ty - 2 } };
        POINT dn[3] = { { cx - 3, by - 1 }, { cx + 3, by - 1 }, { cx, by + 2 } };
        Polygon(dc, up, 3);
        Polygon(dc, dn, 3);
        SelectObject(dc, op); SelectObject(dc, ob);
        DeleteObject(arrow); DeleteObject(apen);
        EndPaint(h, &ps);
        return 0;
    }
    if (gDark && (m == WM_LBUTTONDOWN || m == WM_LBUTTONUP)) {
        LRESULT res = DefSubclassProc(h, m, w, l);
        InvalidateRect(h, nullptr, FALSE);
        return res;
    }
    return DefSubclassProc(h, m, w, l);
}

// ======================= settings =======================
static const wchar_t* FxKeyIniName(int slot) { return slot == 0 ? L"fx_hotkey" : gFxGroups[slot - 1].hotkeyKey; }

static wchar_t gUpdateRepo[200];
static bool    gUpdateOnStart = true;

static void LoadSettings()
{
    GetModuleFileNameW(nullptr, gIni, MAX_PATH);
    wchar_t* slash = wcsrchr(gIni, L'\\');
    if (slash) slash[1] = 0; else gIni[0] = 0;
    lstrcatW(gIni, L"LagEffect.ini");

    #define INI_INT(k, d) (int)GetPrivateProfileIntW(L"settings", k, d, gIni)
    for (Range& r : gRanges) *r.var = Iclamp(INI_INT(r.key, *r.var), r.lo, r.hi);
    gHotkeys[0]    = Iclamp(INI_INT(L"hotkey",  VK_F8), 0, 255);
    gHotkeys[1]    = Iclamp(INI_INT(L"hotkey2", 0), 0, 255);
    gHotkeys[2]    = Iclamp(INI_INT(L"hotkey3", 0), 0, 255);
    if (!gHotkeys[0]) gHotkeys[0] = VK_F8;
    gToggleMode    = INI_INT(L"toggle", 0) != 0;
    gGateOn        = INI_INT(L"gate", 0) != 0;
    gTalkOver      = INI_INT(L"talkover", 0) != 0;
    gBufIdx        = Iclamp(INI_INT(L"buffer", 2), 0, 4);
    gExclusive     = INI_INT(L"exclusive", 0) != 0;
    gAutoStart     = INI_INT(L"autostart", 0) != 0;
    gThemeMode     = Iclamp(INI_INT(L"theme", THEME_SYSTEM), 0, 2);
    gUpdateOnStart = INI_INT(L"update_on_start", 1) != 0;
    UpdateGateLin();

    gFxOn = INI_INT(L"fx_on", 0) != 0;
    for (int slot = 0; slot < FX_KEY_SLOTS; slot++) {
        wchar_t b[64];
        GetPrivateProfileStringW(L"settings", FxKeyIniName(slot), L"", b, 64, gIni);
        const wchar_t* q = b;
        for (int i = 0; i < MAX_KEYS; i++) {
            gFxKeys[slot][i] = *q ? Iclamp(_wtoi(q), 0, 255) : 0;
            while (*q && *q != L',') q++;
            if (*q == L',') q++;
        }
    }
    for (FxGroup& g : gFxGroups) *g.on = INI_INT(g.key, g.def) != 0;
    for (Knob& k : gKnobs) {                    // read as text: knob values can be negative
        wchar_t b[32];
        GetPrivateProfileStringW(L"settings", k.key, L"", b, 32, gIni);
        *k.var = Iclamp(b[0] ? _wtoi(b) : k.def, k.lo, k.hi);
    }

    GetPrivateProfileStringW(L"settings", L"mic",         L"", gMicName, 512, gIni);
    GetPrivateProfileStringW(L"settings", L"update_repo", DEFAULT_UPDATE_REPO, gUpdateRepo, 200, gIni);

    int rows = INI_INT(L"out_count", 0);
    if (rows < 1) {
        // Settings from 1.2 and older: "Send to" becomes output 1, "Hear on" becomes output 2.
        rows = 1;
        GetPrivateProfileStringW(L"settings", L"output", L"", gRowName[0], 512, gIni);
        gRowMode[0] = INI_INT(L"passthrough", 1) ? MODE_ALL : MODE_EFFECT;
        gRowVol[0]  = Iclamp(INI_INT(L"volume", 100), 0, 200);
        int mon = INI_INT(L"monitor_mode", MODE_OFF);
        if (mon != MODE_OFF) {
            rows = 2;
            GetPrivateProfileStringW(L"settings", L"monitor", L"", gRowName[1], 512, gIni);
            gRowMode[1] = Iclamp(mon, 0, 2);
            gRowVol[1]  = Iclamp(INI_INT(L"monitor_volume", 100), 0, 200);
        }
    } else {
        rows = Iclamp(rows, 1, MAX_OUT);
        for (int k = 0; k < rows; k++) {
            wchar_t key[32];
            wsprintfW(key, L"out%d_device", k + 1); GetPrivateProfileStringW(L"settings", key, L"", gRowName[k], 512, gIni);
            wsprintfW(key, L"out%d_mode", k + 1);   gRowMode[k] = Iclamp(INI_INT(key, k == 0 ? MODE_ALL : MODE_EFFECT), 0, 2);
            wsprintfW(key, L"out%d_volume", k + 1); gRowVol[k]  = Iclamp(INI_INT(key, 100), 0, 200);
        }
    }
    gRows = rows;
    #undef INI_INT
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
    SaveInt(L"hotkey", gHotkeys[0]); SaveInt(L"hotkey2", gHotkeys[1]); SaveInt(L"hotkey3", gHotkeys[2]);
    SaveInt(L"toggle", gToggleMode);
    SaveInt(L"gate", gGateOn); SaveInt(L"talkover", gTalkOver);
    SaveInt(L"buffer", gBufIdx); SaveInt(L"exclusive", gExclusive); SaveInt(L"autostart", gAutoStart);
    SaveInt(L"theme", gThemeMode); SaveInt(L"update_on_start", gUpdateOnStart);
    SaveInt(L"fx_on", gFxOn);
    for (int slot = 0; slot < FX_KEY_SLOTS; slot++) {
        wchar_t b[64];
        wsprintfW(b, L"%d,%d,%d", gFxKeys[slot][0], gFxKeys[slot][1], gFxKeys[slot][2]);
        WritePrivateProfileStringW(L"settings", FxKeyIniName(slot), b, gIni);
    }
    for (FxGroup& g : gFxGroups) SaveInt(g.key, *g.on);
    for (Knob& k : gKnobs) SaveInt(k.key, *k.var);
    WritePrivateProfileStringW(L"settings", L"update_repo", gUpdateRepo, gIni);
    wchar_t name[512], key[32];
    SelectedName(IDC_MIC, gCapDevs, gCapCount, name, 512);
    WritePrivateProfileStringW(L"settings", L"mic", name, gIni);
    SaveInt(L"out_count", gRows);
    for (int k = 0; k < gRows; k++) {
        SelectedName(IDC_ROWDEV + k, gPlayDevs, gPlayCount, name, 512);
        wsprintfW(key, L"out%d_device", k + 1); WritePrivateProfileStringW(L"settings", key, name, gIni);
        wsprintfW(key, L"out%d_mode", k + 1);   SaveInt(key, gRowMode[k]);
        wsprintfW(key, L"out%d_volume", k + 1); SaveInt(key, gRowVol[k]);
    }
}

// ======================= audio start/stop =======================
static void NotifyCallback(const ma_device_notification* n)
{
    // A device was unplugged or disabled: let the window restart audio.
    if (n->type == ma_device_notification_type_stopped && !gStopping && gWantRunning)
        PostMessageW(gWnd, WM_DEVICE_LOST, 0, 0);
}

static int ComboIndex(int id) { return (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0) - 1; }

static bool StartExtraOutput(int k)
{
    ma_device_config cfg = ma_device_config_init(ma_device_type_playback);
    cfg.playback.format    = ma_format_f32;
    cfg.playback.channels  = 2;
    cfg.sampleRate         = RATE;
    cfg.periodSizeInFrames = BUFFERS[gBufIdx];
    cfg.performanceProfile = ma_performance_profile_low_latency;
    cfg.dataCallback       = ExtraOutputCallback;
    cfg.notificationCallback = NotifyCallback;
    cfg.pUserData          = (void*)(INT_PTR)k;
    int i = ComboIndex(IDC_ROWDEV + k);
    if (i >= 0 && i < (int)gPlayCount) cfg.playback.pDeviceID = &gPlayDevs[i].id;

    ringW[k] = ringR[k] = 0;
    if (ma_device_init(&gCtx, &cfg, &gExtraDev[k]) != MA_SUCCESS) return false;
    if (ma_device_start(&gExtraDev[k]) != MA_SUCCESS) { ma_device_uninit(&gExtraDev[k]); return false; }
    gExtraRunning[k] = true;
    ringOn[k] = true;
    return true;
}

static void StopDevices()
{
    gStopping = true;
    for (int k = 0; k < MAX_OUT; k++) ringOn[k] = false;
    if (gRunning) { ma_device_uninit(&gDev); gRunning = false; }
    for (int k = 0; k < MAX_OUT; k++)
        if (gExtraRunning[k]) { ma_device_uninit(&gExtraDev[k]); gExtraRunning[k] = false; }
    gLooping = false;
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
    int mi = ComboIndex(IDC_MIC), oi = ComboIndex(IDC_ROWDEV);
    if (mi >= 0 && mi < (int)gCapCount)  cfg.capture.pDeviceID  = &gCapDevs[mi].id;
    if (oi >= 0 && oi < (int)gPlayCount) cfg.playback.pDeviceID = &gPlayDevs[oi].id;

    memset(hist, 0, sizeof(hist));
    wpos = 0; frozenLen = 1; looping = false; toggled = false; prevDown = false;
    gateEnv = 0; gateGain = 1; gateHold = 0;
    gFxResetReq = true;

    gStopping = false;
    gWantRunning = true;
    wchar_t failed[128] = L"";
    for (int k = 1; k < gRows; k++) {
        if (!StartExtraOutput(k)) {
            wchar_t n[8]; wsprintfW(n, failed[0] ? L", %d" : L"%d", k + 1);
            lstrcatW(failed, n);
        }
    }
    if (failed[0] && !quiet) {
        wchar_t msg[256];
        wsprintfW(msg, L"Couldn't open output %s, so nothing will play there.\n\nThe other outputs are working normally.", failed);
        MessageBoxW(gWnd, msg, L"Lag Effect", MB_ICONWARNING);
    }

    const wchar_t* err = gExclusive
        ? L"Couldn't open the microphone or output 1.\n\nTry turning off Exclusive mode or picking a bigger buffer."
        : L"Couldn't open the microphone or output 1.\n\nCheck that they're plugged in.";
    bool ok = ma_device_init(&gCtx, &cfg, &gDev) == MA_SUCCESS;
    if (ok && ma_device_start(&gDev) != MA_SUCCESS) { ma_device_uninit(&gDev); ok = false; }
    if (!ok) {
        StopDevices();
        if (!quiet) { gWantRunning = false; MessageBoxW(gWnd, err, L"Lag Effect", MB_ICONWARNING); }
        return false;
    }
    gRunning = true;
    return true;
}

static void StopAudio()
{
    gWantRunning = false;
    KillTimer(gWnd, TIMER_RECONNECT);
    StopDevices();
}

// ======================= layout helpers =======================
// Everything below the output list moves down as outputs are added, so controls created after
// the list are recorded with their starting position.
// Controls also belong to a page (tab): 0 = Main, 1 = Voice FX, 2 = Settings. Only the current page is shown.
#define CLIENT_W  560
#define BASE_H    592                          // window height with one output
#define ROW_Y0    134
#define ROW_H     30
#define TAB_COUNT 3
enum { PAGE_MAIN = 0, PAGE_FX = 1, PAGE_SETTINGS = 2 };

struct Shifted { HWND h; int x, y; };
struct Section { int x, y, w, h; const wchar_t* title; bool shifts; int page; };
struct Framed  { HWND edit, ud; };
struct Paged   { HWND h; int page; };
static Shifted gShift[96];   static int gShiftN = 0;
static Section gSections[12]; static int gSectionN = 0;
static Framed  gFramed[24];  static int gFramedN = 0;
static Paged   gPaged[160];  static int gPagedN = 0;
static bool    gRecordShift = false;
static int     gDevSectionIdx = 0;
static int     gBuildPage = -1;                // page new controls go on (-1 = always shown, e.g. the tabs)
static int     gPage = 0;                      // page being shown

static void RecordPage(HWND h) { if (gBuildPage >= 0 && gPagedN < 160) gPaged[gPagedN++] = { h, gBuildPage }; }

static int RowsDelta() { return ROW_H * (gRows - 1); }

static HWND Ctl(const wchar_t* cls, const wchar_t* text, DWORD style, int x, int y, int w, int h, int id, DWORD ex = 0)
{
    HWND c = CreateWindowExW(ex, cls, text, WS_CHILD | WS_VISIBLE | style, x, y, w, h,
                             gWnd, (HMENU)(INT_PTR)id, gInst, nullptr);
    SendMessageW(c, WM_SETFONT, (WPARAM)gFont, TRUE);
    if (gRecordShift && gShiftN < 96) gShift[gShiftN++] = { c, x, y };
    RecordPage(c);
    return c;
}

static HWND Spin(int id, int x, int y, int w, int lo, int hi, int val)
{
    HWND e = Ctl(L"EDIT", L"", WS_TABSTOP | ES_NUMBER | ES_RIGHT | ES_AUTOHSCROLL, x, y, w, 23, id, WS_EX_CLIENTEDGE);
    HWND u = CreateWindowExW(0, UPDOWN_CLASSW, nullptr,
                             WS_CHILD | WS_VISIBLE | UDS_SETBUDDYINT | UDS_ALIGNRIGHT | UDS_ARROWKEYS | UDS_NOTHOUSANDS | UDS_HOTTRACK,
                             0, 0, 0, 0, gWnd, (HMENU)(INT_PTR)SPIN_UD(id), gInst, nullptr);
    SendMessageW(u, UDM_SETBUDDY, (WPARAM)e, 0);
    SendMessageW(u, UDM_SETRANGE32, lo, hi);
    SendMessageW(u, UDM_SETPOS32, 0, val);
    SetWindowSubclass(u, UpDownProc, 1, 0);
    if (gRecordShift && gShiftN < 96) {
        RECT r; GetWindowRect(u, &r); MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2);
        gShift[gShiftN++] = { u, r.left, r.top };
    }
    if (gFramedN < 24) gFramed[gFramedN++] = { e, u };
    RecordPage(u);
    return u;
}

static void AddSection(int x, int y, int w, int h, const wchar_t* title)
{
    if (gSectionN < 12) gSections[gSectionN++] = { x, y, w, h, title, gRecordShift, gBuildPage };
}

// ======================= knob control (Voice FX page) =======================
// Drag up/down (Shift = fine), scroll the wheel, or use the arrow keys / Page Up/Down / Home / End.
// Double-click or Delete resets to the default. Writes straight into the knob's setting.
#define KNOB_W 96
#define KNOB_H 106
static int    gKnobLastY = 0;
static double gKnobAccum = 0;
static int    gWheelAccum = 0;

static bool KnobActive(int i) { return gFxOn && *gFxGroups[gKnobs[i].group].on; }
static int  KnobStep(int i)   { return Imax(1, (gKnobs[i].hi - gKnobs[i].lo) / 50); }

static void SetKnobValue(HWND h, int i, int v)
{
    Knob& k = gKnobs[i];
    v = Iclamp(v, k.lo, k.hi);
    if (v != *k.var) { *k.var = v; InvalidateRect(h, nullptr, FALSE); }
}

static void RedrawKnobs()
{
    for (int i = 0; i < KNOB_N; i++) InvalidateRect(GetDlgItem(gWnd, IDC_KNOB + i), nullptr, FALSE);
}

static void KnobPoint(int cx, int cy, int r, double deg, int* x, int* y)
{
    double a = deg * 3.14159265358979 / 180.0;
    *x = cx + (int)floor(r * cos(a) + 0.5);
    *y = cy - (int)floor(r * sin(a) + 0.5);
}

// Clockwise arc from angle 'from' down to angle 'to' (degrees, 0 = right, 90 = up).
static void KnobArc(HDC dc, int cx, int cy, int r, double from, double to, COLORREF c, int width)
{
    if (from - to < 1.0) return;
    LOGBRUSH lb = { BS_SOLID, c, 0 };
    HPEN p = ExtCreatePen(PS_GEOMETRIC | PS_SOLID | PS_ENDCAP_ROUND, width, &lb, 0, nullptr);
    HGDIOBJ op = SelectObject(dc, p);
    int x1, y1, x2, y2;
    KnobPoint(cx, cy, r, from, &x1, &y1);
    KnobPoint(cx, cy, r, to, &x2, &y2);
    SetArcDirection(dc, AD_CLOCKWISE);
    Arc(dc, cx - r, cy - r, cx + r, cy + r, x1, y1, x2, y2);
    SelectObject(dc, op);
    DeleteObject(p);
}

static void PaintKnob(HWND h, HDC dc)
{
    int i = GetDlgCtrlID(h) - IDC_KNOB;
    if (i < 0 || i >= KNOB_N) return;
    Knob& k = gKnobs[i];
    RECT rc; GetClientRect(h, &rc);
    FillRect(dc, &rc, BgBrush());

    const bool on = KnobActive(i), focus = GetFocus() == h;
    const int  cx = rc.right / 2, cy = 52, r = 26;
    double frac = (double)(*k.var - k.lo) / (double)(k.hi - k.lo);
    double ang  = 225.0 - 270.0 * frac;         // 225 = minimum (bottom left), -45 = maximum (bottom right)

    COLORREF track = gDark ? RGB(66, 66, 66) : RGB(212, 212, 212);
    COLORREF value = on ? ACCENT : (gDark ? RGB(112, 112, 112) : RGB(158, 158, 158));
    KnobArc(dc, cx, cy, r, 225.0, -45.0, track, 5);
    if (k.bipolar) {                            // fills from the middle (12 o'clock) toward the value
        if (ang < 90.0) KnobArc(dc, cx, cy, r, 90.0, ang, value, 5);
        else            KnobArc(dc, cx, cy, r, ang, 90.0, value, 5);
    } else {
        KnobArc(dc, cx, cy, r, 225.0, ang, value, 5);
    }

    HBRUSH body = CreateSolidBrush(gDark ? RGB(54, 54, 54) : RGB(252, 252, 252));
    HPEN   edge = CreatePen(PS_SOLID, 1, focus ? ACCENT : gDark ? RGB(88, 88, 88) : RGB(186, 186, 186));
    HGDIOBJ ob = SelectObject(dc, body), op = SelectObject(dc, edge);
    Ellipse(dc, cx - 18, cy - 18, cx + 19, cy + 19);
    SelectObject(dc, ob); SelectObject(dc, op);
    DeleteObject(body); DeleteObject(edge);

    int x1, y1, x2, y2;                         // pointer
    KnobPoint(cx, cy, 6, ang, &x1, &y1);
    KnobPoint(cx, cy, 15, ang, &x2, &y2);
    LOGBRUSH lb = { BS_SOLID, on ? (gDark ? DK_TEXT : RGB(40, 40, 40)) : (gDark ? DK_DIM : RGB(130, 130, 130)), 0 };
    HPEN ptr = ExtCreatePen(PS_GEOMETRIC | PS_SOLID | PS_ENDCAP_ROUND, 3, &lb, 0, nullptr);
    op = SelectObject(dc, ptr);
    MoveToEx(dc, x1, y1, nullptr); LineTo(dc, x2, y2);
    SelectObject(dc, op);
    DeleteObject(ptr);

    SetBkMode(dc, TRANSPARENT);
    HGDIOBJ of = SelectObject(dc, gFont);
    SetTextColor(dc, focus ? ACCENT : gDark ? DK_DIM : RGB(95, 95, 95));
    RECT lr = { 0, 0, rc.right, 18 };
    DrawTextW(dc, k.label, -1, &lr, DT_SINGLELINE | DT_CENTER | DT_VCENTER);

    wchar_t txt[32];
    wsprintfW(txt, k.bipolar && *k.var > 0 ? L"+%d%s" : L"%d%s", *k.var, k.unit);
    SelectObject(dc, gFontBold);
    SetTextColor(dc, on ? (gDark ? DK_TEXT : RGB(30, 30, 30)) : (gDark ? DK_DIM : RGB(130, 130, 130)));
    RECT vr = { 0, cy + 30, rc.right, rc.bottom };
    DrawTextW(dc, txt, -1, &vr, DT_SINGLELINE | DT_CENTER | DT_TOP);
    SelectObject(dc, of);
}

static LRESULT CALLBACK KnobProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    int i = GetDlgCtrlID(h) - IDC_KNOB;
    if (i < 0 || i >= KNOB_N) return DefWindowProcW(h, m, w, l);
    Knob& k = gKnobs[i];
    switch (m) {
    case WM_GETDLGCODE:
        return DLGC_WANTARROWS;
    case WM_LBUTTONDOWN:
        SetFocus(h);
        SetCapture(h);
        gKnobLastY = (short)HIWORD(l);
        gKnobAccum = *k.var;
        return 0;
    case WM_MOUSEMOVE:
        if (GetCapture() == h) {
            int y = (short)HIWORD(l);
            double perPixel = (k.hi - k.lo) / ((w & MK_SHIFT) ? 600.0 : 150.0);
            gKnobAccum += (gKnobLastY - y) * perPixel;
            gKnobAccum = gKnobAccum < k.lo ? k.lo : gKnobAccum > k.hi ? k.hi : gKnobAccum;
            gKnobLastY = y;
            SetKnobValue(h, i, (int)floor(gKnobAccum + 0.5));
        }
        return 0;
    case WM_LBUTTONUP:
        if (GetCapture() == h) ReleaseCapture();
        return 0;
    case WM_LBUTTONDBLCLK:
        SetFocus(h);
        SetKnobValue(h, i, k.def);
        return 0;
    case WM_MOUSEWHEEL: {
        gWheelAccum += GET_WHEEL_DELTA_WPARAM(w);
        int notches = gWheelAccum / WHEEL_DELTA;
        gWheelAccum -= notches * WHEEL_DELTA;
        int step = (GET_KEYSTATE_WPARAM(w) & MK_SHIFT) ? 1 : KnobStep(i);
        SetKnobValue(h, i, *k.var + notches * step);
        return 0;
    }
    case WM_KEYDOWN: {
        bool fine = (GetKeyState(VK_SHIFT) & 0x8000) != 0;
        int step = fine ? 1 : KnobStep(i);
        switch (w) {
        case VK_UP:    case VK_RIGHT: SetKnobValue(h, i, *k.var + step);     return 0;
        case VK_DOWN:  case VK_LEFT:  SetKnobValue(h, i, *k.var - step);     return 0;
        case VK_PRIOR: SetKnobValue(h, i, *k.var + step * 5);                return 0;
        case VK_NEXT:  SetKnobValue(h, i, *k.var - step * 5);                return 0;
        case VK_HOME:  SetKnobValue(h, i, k.lo);                             return 0;
        case VK_END:   SetKnobValue(h, i, k.hi);                             return 0;
        case VK_DELETE: case VK_BACK: SetKnobValue(h, i, k.def);             return 0;
        }
        break;
    }
    case WM_SETFOCUS: case WM_KILLFOCUS:
        InvalidateRect(h, nullptr, FALSE);
        return 0;
    case WM_ERASEBKGND:
        return 1;
    case WM_PAINT: {                            // double-buffered so dragging never flickers
        PAINTSTRUCT ps;
        HDC dc = BeginPaint(h, &ps);
        RECT rc; GetClientRect(h, &rc);
        HDC mem = CreateCompatibleDC(dc);
        HBITMAP bmp = CreateCompatibleBitmap(dc, rc.right, rc.bottom);
        HGDIOBJ old = SelectObject(mem, bmp);
        PaintKnob(h, mem);
        BitBlt(dc, 0, 0, rc.right, rc.bottom, mem, 0, 0, SRCCOPY);
        SelectObject(mem, old);
        DeleteObject(bmp);
        DeleteDC(mem);
        EndPaint(h, &ps);
        return 0;
    }
    }
    return DefWindowProcW(h, m, w, l);
}

// Master switch at the top of the Voice FX page: a card with an on/off pill.
static void DrawFxSwitch(DRAWITEMSTRUCT* d)
{
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    const bool on = gFxOn;

    HBRUSH card = CreateSolidBrush(gDark ? DK_CTL : RGB(252, 252, 252));
    HPEN   cpen = CreatePen(PS_SOLID, 1, on ? ACCENT : gDark ? DK_SECTION : RGB(206, 206, 206));
    HGDIOBJ ob = SelectObject(dc, card), op = SelectObject(dc, cpen);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 12, 12);
    SelectObject(dc, ob); SelectObject(dc, op);
    DeleteObject(card); DeleteObject(cpen);

    const int pw = 44, ph = 22, px = rc.left + 16, py = (rc.top + rc.bottom - ph) / 2;
    COLORREF pill = on ? ACCENT : gDark ? RGB(90, 90, 90) : RGB(170, 170, 170);
    HBRUSH pb = CreateSolidBrush(pill);
    HPEN   pp = CreatePen(PS_SOLID, 1, pill);
    ob = SelectObject(dc, pb); op = SelectObject(dc, pp);
    RoundRect(dc, px, py, px + pw, py + ph, ph, ph);
    SelectObject(dc, ob); SelectObject(dc, op);
    DeleteObject(pb); DeleteObject(pp);

    int kx = on ? px + pw - ph + 3 : px + 3;
    HBRUSH kb = CreateSolidBrush(RGB(255, 255, 255));
    HPEN   kp = CreatePen(PS_SOLID, 1, RGB(255, 255, 255));
    ob = SelectObject(dc, kb); op = SelectObject(dc, kp);
    Ellipse(dc, kx, py + 3, kx + ph - 6, py + ph - 3);
    SelectObject(dc, ob); SelectObject(dc, op);
    DeleteObject(kb); DeleteObject(kp);

    SetBkMode(dc, TRANSPARENT);
    HGDIOBJ of = SelectObject(dc, gFontBold);
    SetTextColor(dc, gDark ? DK_TEXT : RGB(30, 30, 30));
    RECT tr = { px + pw + 14, rc.top + 5, rc.right - 70, rc.top + 24 };
    DrawTextW(dc, L"Voice effects", -1, &tr, DT_SINGLELINE | DT_LEFT | DT_VCENTER);
    SelectObject(dc, gFont);
    SetTextColor(dc, gDark ? DK_DIM : RGB(105, 105, 105));
    RECT sr = { px + pw + 14, rc.top + 23, rc.right - 70, rc.bottom - 4 };
    DrawTextW(dc, L"Changes your live voice (and the loop).", -1, &sr,
              DT_SINGLELINE | DT_LEFT | DT_VCENTER | DT_END_ELLIPSIS);
    SelectObject(dc, gFontBold);
    SetTextColor(dc, on ? ACCENT : gDark ? DK_DIM : RGB(120, 120, 120));
    RECT st = { rc.right - 64, rc.top, rc.right - 16, rc.bottom };
    DrawTextW(dc, on ? L"ON" : L"OFF", -1, &st, DT_SINGLELINE | DT_RIGHT | DT_VCENTER);
    SelectObject(dc, of);

    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) {
        RECT fr = rc; InflateRect(&fr, -4, -4);
        SetTextColor(dc, gDark ? DK_TEXT : RGB(20, 20, 20));
        DrawFocusRect(dc, &fr);
    }
}

static void SetFxOn(bool on)
{
    if (on && !gFxOn) gFxResetReq = true;      // start clean, no stale reverb tail
    gFxOn = on;
    InvalidateRect(GetDlgItem(gWnd, IDC_FXON), nullptr, FALSE);
    RedrawKnobs();
}

static void UpdateStatus(bool force);

static void SetFxGroupOn(int g, bool on)
{
    if (on && !*gFxGroups[g].on) gFxResetReq = true;
    *gFxGroups[g].on = on;
    CheckDlgButton(gWnd, IDC_FXGRP_ON + g, on ? BST_CHECKED : BST_UNCHECKED);
    RedrawKnobs();
}

// Voice FX hotkeys: the page key flips the master switch; an effect's key flips that effect
// (and turns the master switch on with it, so the key always does something you can hear).
static void PollFxKeys()
{
    for (int slot = 0; slot < FX_KEY_SLOTS; slot++) {
        bool down = !gCapturingKey && KeysDown(gFxKeys[slot]);
        bool pressed = down && !gFxKeyWasDown[slot];
        gFxKeyWasDown[slot] = down;
        if (!pressed) continue;
        if (slot == 0) {
            SetFxOn(!gFxOn);
        } else {
            int g = slot - 1;
            bool on = !(*gFxGroups[g].on && gFxOn);
            SetFxGroupOn(g, on);
            if (on && !gFxOn) SetFxOn(true);
        }
        UpdateStatus(true);
    }
}

static void ResetFxGroup(int g)
{
    for (int i = 0; i < KNOB_N; i++)
        if (gKnobs[i].group == g) SetKnobValue(GetDlgItem(gWnd, IDC_KNOB + i), i, gKnobs[i].def);
}

// ======================= device lists =======================
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
    FillCombo(IDC_MIC, L"Default microphone", gCapDevs, gCapCount, gMicName);
    for (int k = 0; k < MAX_OUT; k++)
        FillCombo(IDC_ROWDEV + k, L"Default output", gPlayDevs, gPlayCount, k < gRows ? gRowName[k] : L"");
}

static void RememberDeviceNames()
{
    SelectedName(IDC_MIC, gCapDevs, gCapCount, gMicName, 512);
    for (int k = 0; k < MAX_OUT; k++) SelectedName(IDC_ROWDEV + k, gPlayDevs, gPlayCount, gRowName[k], 512);
}

static void RefreshDevices()                    // re-scan, e.g. after installing VB-Cable
{
    if (!gCtxOk) return;
    RememberDeviceNames();
    bool was = gWantRunning;
    StopAudio();
    ma_context_get_devices(&gCtx, &gPlayDevs, &gPlayCount, &gCapDevs, &gCapCount);
    FillDevices();
    if (was) StartAudio(false);
}

// ======================= status + layout =======================
static void UpdateStatus(bool force = false)
{
    static wchar_t last[200];
    static bool lastLoop = false;
    wchar_t s[200], key[120];
    if (gWantRunning && !gRunning) lstrcpynW(s, L"Audio device lost  -  reconnecting...", 160);
    else if (!gRunning)            lstrcpynW(s, L"Stopped  -  press Start", 160);
    else if (gLooping)             lstrcpynW(s, L"LOOPING", 160);
    else {
        HotkeyName(key, 120);
        wsprintfW(s, L"Live  -  %s %s to stutter", gToggleMode ? L"press" : L"hold", key);
    }
    if (gRunning && gFxOn) lstrcatW(s, L"   (Voice FX on)");
    if (force || lstrcmpW(s, last) != 0 || lastLoop != gLooping) {
        lstrcpynW(last, s, 200); lastLoop = gLooping;
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

// Which output row a control belongs to (-1 if none). Sets *isDel for the row's remove button.
static int RowOfId(int id, bool* isDel)
{
    *isDel = false;
    const int bases[] = { IDC_ROWLBL, IDC_ROWDEV, IDC_ROWMODE, IDC_ROWVOL, SPIN_UD(IDC_ROWVOL), IDC_ROWDEL };
    for (int b : bases)
        if (id >= b && id < b + MAX_OUT) { *isDel = b == IDC_ROWDEL; return id - b; }
    return -1;
}

static void Layout()
{
    for (int i = 0; i < gPagedN; i++) {
        bool del;
        int k = RowOfId(GetDlgCtrlID(gPaged[i].h), &del);
        bool vis = gPaged[i].page == gPage && (k < 0 || (k < gRows && !(del && k == 0)));
        ShowWindow(gPaged[i].h, vis ? SW_SHOWNA : SW_HIDE);
    }

    int by = ROW_Y0 + ROW_H * gRows + 6;
    SetWindowPos(GetDlgItem(gWnd, IDC_ADDOUT),  nullptr, 30,  by, 0, 0, SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);
    SetWindowPos(GetDlgItem(gWnd, IDC_VBCABLE), nullptr, 162, by, 0, 0, SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);
    EnableWindow(GetDlgItem(gWnd, IDC_ADDOUT), gRows < MAX_OUT);
    gSections[gDevSectionIdx].h = by + 28 + 14 - gSections[gDevSectionIdx].y;

    int d = RowsDelta();
    for (int i = 0; i < gShiftN; i++)
        SetWindowPos(gShift[i].h, nullptr, gShift[i].x, gShift[i].y + d, 0, 0, SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);

    DWORD style = (DWORD)GetWindowLongW(gWnd, GWL_STYLE);
    RECT r = { 0, 0, CLIENT_W, BASE_H + d };   // both pages share the window size, so switching never jumps
    AdjustWindowRect(&r, style, FALSE);
    SetWindowPos(gWnd, nullptr, 0, 0, r.right - r.left, r.bottom - r.top, SWP_NOMOVE | SWP_NOZORDER | SWP_NOACTIVATE);
    RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_ALLCHILDREN);
}

static void SetPage(int page)
{
    if (page < 0 || page >= TAB_COUNT || page == gPage) return;
    HWND focus = GetFocus();
    gPage = page;
    Layout();
    if (!focus || !IsWindowVisible(focus)) SetFocus(GetDlgItem(gWnd, IDC_TAB0 + page));
}

static void SetRowMode(int k, int mode)
{
    gRowMode[k] = mode;
    SendDlgItemMessageW(gWnd, IDC_ROWMODE + k, CB_SETCURSEL, mode, 0);
}

static void SetRowVol(int k, int vol)
{
    gRowVol[k] = vol;
    SendDlgItemMessageW(gWnd, SPIN_UD(IDC_ROWVOL + k), UDM_SETPOS32, 0, vol);
}

static void AddOutput()
{
    if (gRows >= MAX_OUT) return;
    int k = gRows;
    SendDlgItemMessageW(gWnd, IDC_ROWDEV + k, CB_SETCURSEL, 0, 0);
    SetRowMode(k, MODE_EFFECT);
    SetRowVol(k, 100);
    gRows++;
    Layout();
    RestartIfRunning();
}

static void RemoveOutput(int k)
{
    if (k <= 0 || k >= gRows) return;
    for (int j = k; j < gRows - 1; j++) {
        LRESULT sel = SendDlgItemMessageW(gWnd, IDC_ROWDEV + j + 1, CB_GETCURSEL, 0, 0);
        SendDlgItemMessageW(gWnd, IDC_ROWDEV + j, CB_SETCURSEL, sel, 0);
        SetRowMode(j, gRowMode[j + 1]);
        SetRowVol(j, gRowVol[j + 1]);
    }
    gRows--;
    Layout();
    RestartIfRunning();
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
static bool gResumeAudio = false;               // set when relaunched by the updater while audio was running

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
    bool wasRunning = gWantRunning;            // the new version picks up where this one left off
    SaveSettings();
    StopAudio();
    RemoveTray();
    lstrcpynW(dir, exe, MAX_PATH);
    wchar_t* slash = wcsrchr(dir, L'\\');
    if (slash) *slash = 0;
    ShellExecuteW(nullptr, L"open", exe, wasRunning ? L"--updated --resume" : L"--updated", dir, SW_SHOWNORMAL);
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
    for (ma_uint32 i = 0; i < gPlayCount; i++) {
        Widen(gPlayDevs[i].name, n, 512);
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
    StopAudio();
    SendDlgItemMessageW(gWnd, IDC_ROWDEV, CB_SETCURSEL, cable + 1, 0);     // output 1 -> VB-Cable, everything
    SetRowMode(0, MODE_ALL);
    if (gRows == 1) {                                                     // output 2 -> your headphones, effect only
        SendDlgItemMessageW(gWnd, IDC_ROWDEV + 1, CB_SETCURSEL, 0, 0);
        SetRowMode(1, MODE_EFFECT);
        SetRowVol(1, 100);
        gRows = 2;
        Layout();
    }
    if (gExclusive) { gExclusive = false; CheckDlgButton(gWnd, IDC_EXCL, BST_UNCHECKED); }
    StartAudio(false);
    UpdateUi();
    MessageBoxW(gWnd,
        L"Output 1 now goes to VB-Cable (Everything), and output 2 lets you hear the effect on your normal "
        L"speakers or headphones.\n\n"
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
        L"Hold (or toggle) your hotkey to repeat the last bit of your mic.\n"
        L"Speed = how fast the loop plays through.  Pitch = how high or low it sounds.\n"
        L"Tick \"Keep talking during the effect\" to speak over the loop; Voice level sets how loud you are.\n\n"
        L"PAGES\n"
        L"Main has the outputs, effect and hotkey. Voice FX adds pitch and reverb to your live voice. "
        L"Settings has latency, theme and updates. Ctrl+Tab switches between them.\n\n"
        L"VOICE FX\n"
        L"Flip the switch at the top, then tick the effects you want. Drag a knob up or down, scroll it, "
        L"or use the arrow keys (hold Shift for fine steps). Double-click a knob to reset it.\n"
        L"Hotkeys: click \"Set hotkey\" next to the switch, Pitch or Reverb and press a key or combo. "
        L"They work from anywhere, even in a game. Right-click a hotkey button (or press Backspace while setting it) to clear it.\n"
        L"Pitch: semitones + fine cents. Grain: longer = smoother, shorter = less delay.\n"
        L"Reverb: Mix = how much room, Size = how big, Damping = darker tail, Pre-delay = gap before the echo.\n\n"
        L"HOTKEY\n"
        L"Click the hotkey button, hold one key or up to 3 together (like Shift + F or Ctrl + Shift + 1), "
        L"then let go. Esc cancels. Mouse side buttons work too.\n\n"
        L"OUTPUTS\n"
        L"Add up to 5 with \"+ Add output\". Each one plays:\n"
        L"  Off - nothing\n"
        L"  Effect only - just the stutter, never your normal voice\n"
        L"  Everything - your voice plus the stutter (what others should hear)\n\n"
        L"DISCORD / GAMES\n"
        L"1. Install VB-Cable (free) and click \"Use VB-Cable\".\n"
        L"2. In Discord, set Input Device to \"CABLE Output\".\n"
        L"3. Set Noise Suppression to None or Standard (Krisp erases the effect), and turn off Echo "
        L"Cancellation and Automatic Gain Control.\n"
        L"4. Turn on Lag Effect's noise gate to keep background noise out.\n\n"
        L"OBS\n"
        L"With VB-Cable: add Audio Input Capture = \"CABLE Output\".\n"
        L"Without VB-Cable: add Application Audio Capture and pick LagEffect.exe.\n\n"
        L"TIPS\n"
        L"Use headphones. If a game runs as administrator, run Lag Effect as administrator too, "
        L"or the hotkey won't work while that game is focused.",
        L"Lag Effect " APP_VERSION L" - Help", MB_ICONINFORMATION);
}

// ======================= hotkey picker =======================
// One picker for every hotkey: the stutter hotkey (IDC_HOTKEY) and the Voice FX on/off keys.
static volatile int* gCapTarget = gHotkeys;    // where the captured combination is stored
static int           gCapButton = IDC_HOTKEY;  // button that shows it

static void FxKeyButtonText(int slot, wchar_t* buf, int cap)
{
    ComboName(gFxKeys[slot], MAX_KEYS, buf, cap);
    if (!buf[0]) lstrcpynW(buf, L"Set hotkey", cap);
}

static int FxKeyButtonId(int slot) { return slot == 0 ? IDC_FXKEY_MASTER : IDC_FXGRP_KEY + slot - 1; }

static void ShowCaptureTarget()
{
    wchar_t name[120];
    if (gCapButton == IDC_HOTKEY) HotkeyName(name, 120);
    else {
        int slot = gCapButton == IDC_FXKEY_MASTER ? 0 : gCapButton - IDC_FXGRP_KEY + 1;
        FxKeyButtonText(slot, name, 120);
    }
    SetDlgItemTextW(gWnd, gCapButton, name);
}

static void EndKeyCapture();

static void BeginKeyCapture(volatile int* target, int button)
{
    if (gCapturingKey) EndKeyCapture();         // only one picker at a time
    gCapTarget = target;
    gCapButton = button;
    gCapturingKey = true;
    gCapKeyCount = 0;
    for (int vk = 0; vk < 256; vk++) gKeyWasDown[vk] = (GetAsyncKeyState(vk) & 0x8000) != 0;
    SetDlgItemTextW(gWnd, button, button == IDC_HOTKEY ? L"Hold your key(s), then let go" : L"Press keys...");
    SetTimer(gWnd, TIMER_KEY, 15, nullptr);
}

static void EndKeyCapture()
{
    gCapturingKey = false;
    KillTimer(gWnd, TIMER_KEY);
    ShowCaptureTarget();
    for (int slot = 0; slot < FX_KEY_SLOTS; slot++) gFxKeyWasDown[slot] = KeysDown(gFxKeys[slot]);   // no instant toggle
    UpdateStatus(true);
}

static void ClearFxKey(int slot)
{
    if (gCapturingKey) EndKeyCapture();
    for (int i = 0; i < MAX_KEYS; i++) gFxKeys[slot][i] = 0;
    wchar_t name[120]; FxKeyButtonText(slot, name, 120);
    SetDlgItemTextW(gWnd, FxKeyButtonId(slot), name);
}

// Left/right Shift, Ctrl and Alt are stored as plain Shift/Ctrl/Alt so either side works.
static int NormalizeKey(int vk)
{
    switch (vk) {
        case VK_LSHIFT:   case VK_RSHIFT:   return VK_SHIFT;
        case VK_LCONTROL: case VK_RCONTROL: return VK_CONTROL;
        case VK_LMENU:    case VK_RMENU:    return VK_MENU;
    }
    return vk;
}

static int KeyRank(int vk)                      // modifiers are listed first: Ctrl + Shift + Alt + Win + key
{
    switch (vk) {
        case VK_CONTROL: return 0;
        case VK_SHIFT:   return 1;
        case VK_MENU:    return 2;
        case VK_LWIN: case VK_RWIN: return 3;
    }
    return 4;
}

// Records every key pressed while capturing (up to 3). The combination is saved once they're all let go.
static void PollKeyCapture()
{
    bool changed = false;
    for (int vk = 2; vk < 256; vk++) {          // 1 = left mouse, skipped
        if (vk == VK_SHIFT || vk == VK_CONTROL || vk == VK_MENU) continue;   // read left/right versions
        bool d = (GetAsyncKeyState(vk) & 0x8000) != 0;
        bool pressed = d && !gKeyWasDown[vk];
        gKeyWasDown[vk] = d;
        if (!pressed) continue;
        if (vk == VK_ESCAPE) { EndKeyCapture(); return; }    // cancel, keep the old hotkey
        if (vk == VK_BACK && gCapKeyCount == 0 && gCapButton != IDC_HOTKEY) {   // Backspace clears an FX hotkey
            for (int i = 0; i < MAX_KEYS; i++) gCapTarget[i] = 0;
            EndKeyCapture();
            return;
        }
        int key = NormalizeKey(vk);
        bool have = false;
        for (int i = 0; i < gCapKeyCount; i++) if (gCapKeys[i] == key) have = true;
        if (!have && gCapKeyCount < MAX_KEYS) { gCapKeys[gCapKeyCount++] = key; changed = true; }
    }
    if (gCapKeyCount == 0) return;

    if (changed) {                              // show the combination as it's being pressed
        int sorted[MAX_KEYS];
        for (int i = 0; i < gCapKeyCount; i++) sorted[i] = gCapKeys[i];
        for (int i = 1; i < gCapKeyCount; i++)
            for (int j = i; j > 0 && KeyRank(sorted[j]) < KeyRank(sorted[j - 1]); j--) {
                int t = sorted[j]; sorted[j] = sorted[j - 1]; sorted[j - 1] = t;
            }
        for (int i = 0; i < gCapKeyCount; i++) gCapKeys[i] = sorted[i];
        wchar_t name[140];
        ComboName(gCapKeys, gCapKeyCount, name, 120);
        lstrcatW(name, L" ...");
        SetDlgItemTextW(gWnd, gCapButton, name);
    }

    for (int i = 0; i < gCapKeyCount; i++)
        if (GetAsyncKeyState(gCapKeys[i]) & 0x8000) return;   // still holding: wait

    for (int i = 0; i < MAX_KEYS; i++) gCapTarget[i] = i < gCapKeyCount ? gCapKeys[i] : 0;
    EndKeyCapture();
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
static void CreateUI()
{
    const DWORD COMBO = CBS_DROPDOWNLIST | WS_VSCROLL | WS_TABSTOP;
    const wchar_t* modeNames[] = { L"Off", L"Effect only", L"Everything" };

    // Tabs (always visible). Drawn by DrawTab().
    gBuildPage = -1;
    Ctl(L"BUTTON", L"Main",     BS_OWNERDRAW | WS_TABSTOP, 14,  10, 100, 32, IDC_TAB0 + PAGE_MAIN);
    Ctl(L"BUTTON", L"Voice FX", BS_OWNERDRAW | WS_TABSTOP, 118, 10, 100, 32, IDC_TAB0 + PAGE_FX);
    Ctl(L"BUTTON", L"Settings", BS_OWNERDRAW | WS_TABSTOP, 222, 10, 100, 32, IDC_TAB0 + PAGE_SETTINGS);

    // ---------------- Main page ----------------
    // Grid: sections run from x 14 to 546, contents from x 30 to 530.
    // Effect section columns: label / number box / unit at 30 / 136 / 218 and 290 / 392 / 474.
    gBuildPage = PAGE_MAIN;

    // Audio: microphone + output list
    gDevSectionIdx = gSectionN;
    AddSection(14, 60, 532, 152, L"Audio");
    Ctl(L"STATIC", L"Microphone:", 0, 30, 85, 90, 20, -1);
    HWND mic = Ctl(L"COMBOBOX", L"", COMBO, 124, 82, 406, 300, IDC_MIC);
    SendMessageW(mic, CB_SETDROPPEDWIDTH, 420, 0);
    Ctl(L"STATIC", L"Output", 0, 80, 116, 200, 16, IDC_HDR);
    Ctl(L"STATIC", L"Plays", 0, 320, 116, 100, 16, IDC_HDR);
    Ctl(L"STATIC", L"Volume %", 0, 432, 116, 70, 16, IDC_HDR);
    for (int k = 0; k < MAX_OUT; k++) {
        int y = ROW_Y0 + ROW_H * k;
        wchar_t lbl[16]; wsprintfW(lbl, L"Out %d", k + 1);
        Ctl(L"STATIC", lbl, 0, 30, y + 4, 46, 20, IDC_ROWLBL + k);
        HWND dev = Ctl(L"COMBOBOX", L"", COMBO, 80, y, 234, 300, IDC_ROWDEV + k);
        SendMessageW(dev, CB_SETDROPPEDWIDTH, 420, 0);       // the open list shows full device names
        HWND mc = Ctl(L"COMBOBOX", L"", COMBO, 320, y, 106, 200, IDC_ROWMODE + k);
        for (const wchar_t* n : modeNames) SendMessageW(mc, CB_ADDSTRING, 0, (LPARAM)n);
        SendMessageW(mc, CB_SETCURSEL, gRowMode[k], 0);
        Spin(IDC_ROWVOL + k, 432, y, 68, 0, 200, gRowVol[k]);
        Ctl(L"BUTTON", L"×", WS_TABSTOP, 506, y, 24, 23, IDC_ROWDEL + k);
    }
    Ctl(L"BUTTON", L"+ Add output", WS_TABSTOP, 30, 170, 124, 28, IDC_ADDOUT);
    Ctl(L"BUTTON", L"Use VB-Cable", WS_TABSTOP, 162, 170, 124, 28, IDC_VBCABLE);
    FillDevices();

    gRecordShift = true;                        // everything below on this page moves with the output list

    // Effect
    AddSection(14, 232, 532, 165, L"Effect");
    Ctl(L"STATIC", L"Loop length:", 0, 30, 259, 104, 20, -1);
    Spin(IDC_LOOP, 136, 256, 76, 10, 2000, gLoopMs);
    Ctl(L"STATIC", L"ms", 0, 218, 259, 40, 20, -1);
    Ctl(L"STATIC", L"Speed:", 0, 290, 259, 100, 20, -1);
    Spin(IDC_SPEED, 392, 256, 76, 10, 400, gSpeedPct);
    Ctl(L"STATIC", L"%", 0, 474, 259, 40, 20, -1);

    Ctl(L"STATIC", L"Pitch:", 0, 30, 293, 104, 20, -1);
    Spin(IDC_PITCH, 136, 290, 76, 25, 400, gPitchPct);
    Ctl(L"STATIC", L"%", 0, 218, 293, 40, 20, -1);
    Ctl(L"STATIC", L"Smoothing:", 0, 290, 293, 100, 20, -1);
    Spin(IDC_FADE, 392, 290, 76, 0, 50, gFadeMs);
    Ctl(L"STATIC", L"ms", 0, 474, 293, 40, 20, -1);

    Ctl(L"BUTTON", L"Noise gate", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 327, 104, 20, IDC_GATEON);
    CheckDlgButton(gWnd, IDC_GATEON, gGateOn ? BST_CHECKED : BST_UNCHECKED);
    Spin(IDC_GATE, 136, 324, 76, 20, 90, gGateDb);
    Ctl(L"STATIC", L"-dB", 0, 218, 327, 40, 20, -1);

    Ctl(L"BUTTON", L"Keep talking during the effect", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 361, 250, 20, IDC_TALKON);
    CheckDlgButton(gWnd, IDC_TALKON, gTalkOver ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Voice level:", 0, 290, 361, 100, 20, -1);
    Spin(IDC_TALKVOL, 392, 358, 76, 0, 200, gTalkVolPct);
    Ctl(L"STATIC", L"%", 0, 474, 361, 40, 20, -1);

    // Hotkey
    wchar_t key[120]; HotkeyName(key, 120);
    AddSection(14, 417, 532, 69, L"Hotkey");
    Ctl(L"BUTTON", key, WS_TABSTOP, 30, 440, 260, 30, IDC_HOTKEY);
    Ctl(L"BUTTON", L"Hold", BS_AUTORADIOBUTTON | WS_GROUP | WS_TABSTOP, 310, 445, 80, 20, IDC_HOLD);
    Ctl(L"BUTTON", L"Toggle", BS_AUTORADIOBUTTON, 400, 445, 100, 20, IDC_TOGGLE);
    CheckRadioButton(gWnd, IDC_HOLD, IDC_TOGGLE, gToggleMode ? IDC_TOGGLE : IDC_HOLD);

    // Status + buttons
    gStatus = Ctl(L"STATIC", L"", SS_OWNERDRAW | WS_GROUP, 14, 504, 532, 30, IDC_STATUS);
    Ctl(L"BUTTON", L"Start", WS_TABSTOP, 14, 544, 172, 34, IDC_START);
    Ctl(L"BUTTON", L"Minimize to tray", WS_TABSTOP, 194, 544, 172, 34, IDC_TRAY);
    Ctl(L"BUTTON", L"Help / Discord && OBS", WS_TABSTOP, 374, 544, 172, 34, IDC_HELPBTN);

    gRecordShift = false;

    // ---------------- Voice FX page ----------------
    // Master switch, then one section per effect: knobs on the left, on/off + reset on the right.
    // Sections stack downward (FX_SEC_STEP apart); there's room below for more effects.
    gBuildPage = PAGE_FX;
    Ctl(L"BUTTON", L"Voice effects", BS_OWNERDRAW | WS_TABSTOP, 14, 56, 410, 48, IDC_FXON);
    {
        wchar_t kn[120]; FxKeyButtonText(0, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 432, 66, 114, 30, IDC_FXKEY_MASTER);
    }
    const int FX_SEC_Y0 = 126, FX_SEC_STEP = 146, FX_SEC_H = 126;
    for (int g = 0; g < FX_GROUPS; g++) {
        int y = FX_SEC_Y0 + FX_SEC_STEP * g;
        AddSection(14, y, 532, FX_SEC_H, gFxGroups[g].title);
        int col = 0;
        for (int i = 0; i < KNOB_N; i++) {
            if (gKnobs[i].group != g) continue;
            Ctl(L"LagKnob", L"", WS_TABSTOP | (col == 0 ? WS_GROUP : 0), 26 + col * 98, y + 14, KNOB_W, KNOB_H, IDC_KNOB + i);
            col++;
        }
        Ctl(L"BUTTON", L"On", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 430, y + 16, 100, 20, IDC_FXGRP_ON + g);
        CheckDlgButton(gWnd, IDC_FXGRP_ON + g, *gFxGroups[g].on ? BST_CHECKED : BST_UNCHECKED);
        wchar_t kn[120]; FxKeyButtonText(1 + g, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 428, y + 44, 104, 28, IDC_FXGRP_KEY + g);
        Ctl(L"BUTTON", L"Reset", WS_TABSTOP, 428, y + 80, 104, 28, IDC_FXGRP_RESET + g);
    }
    Ctl(L"STATIC", L"Drag a knob up/down or scroll it  -  Shift = fine steps  -  double-click resets.", 0,
        30, FX_SEC_Y0 + FX_SEC_STEP * FX_GROUPS - 4, 500, 18, IDC_HDR);
    Ctl(L"STATIC", L"Hotkeys switch an effect on/off from anywhere. Right-click one (or press Backspace) to clear it.", 0,
        30, FX_SEC_Y0 + FX_SEC_STEP * FX_GROUPS + 16, 516, 18, IDC_HDR);

    // ---------------- Settings page ----------------
    gBuildPage = PAGE_SETTINGS;

    AddSection(14, 60, 532, 87, L"Latency");
    Ctl(L"STATIC", L"Buffer:", 0, 30, 85, 90, 20, -1);
    HWND buf = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 124, 81, 168, 200, IDC_BUFFER);
    const wchar_t* bufNames[] = { L"32 (fastest)", L"64", L"128 (default)", L"256", L"512 (safest)" };
    for (const wchar_t* n : bufNames) SendMessageW(buf, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(buf, CB_SETCURSEL, gBufIdx, 0);
    Ctl(L"BUTTON", L"Exclusive mode", BS_AUTOCHECKBOX | WS_TABSTOP, 310, 84, 220, 20, IDC_EXCL);
    CheckDlgButton(gWnd, IDC_EXCL, gExclusive ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Smaller buffer = less delay. Pick a bigger one if you hear crackling.", 0, 30, 116, 500, 18, IDC_HDR);

    AddSection(14, 167, 532, 100, L"App");
    Ctl(L"STATIC", L"Theme:", 0, 30, 196, 60, 20, -1);
    HWND th = Ctl(L"COMBOBOX", L"", COMBO, 94, 192, 110, 200, IDC_THEME);
    const wchar_t* themeNames[] = { L"System", L"Light", L"Dark" };
    for (const wchar_t* n : themeNames) SendMessageW(th, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(th, CB_SETCURSEL, gThemeMode, 0);
    Ctl(L"BUTTON", L"Start audio && hide in tray when opened", BS_AUTOCHECKBOX | WS_TABSTOP, 222, 194, 300, 20, IDC_AUTO);
    CheckDlgButton(gWnd, IDC_AUTO, gAutoStart ? BST_CHECKED : BST_UNCHECKED);

    Ctl(L"STATIC", L"Updates:", 0, 30, 230, 60, 20, -1);
    HWND repo = Ctl(L"EDIT", gUpdateRepo, WS_TABSTOP | ES_AUTOHSCROLL, 94, 227, 200, 24, IDC_REPO, WS_EX_CLIENTEDGE);
    SendMessageW(repo, EM_SETCUEBANNER, TRUE, (LPARAM)L"github-user/repo");
    if (gFramedN < 24) gFramed[gFramedN++] = { repo, nullptr };
    Ctl(L"BUTTON", L"Check now", WS_TABSTOP, 302, 226, 100, 26, IDC_CHECKUPD);
    Ctl(L"BUTTON", L"On startup", BS_AUTOCHECKBOX | WS_TABSTOP, 412, 229, 118, 20, IDC_UPDSTART);
    CheckDlgButton(gWnd, IDC_UPDSTART, gUpdateOnStart ? BST_CHECKED : BST_UNCHECKED);

    Ctl(L"STATIC", L"Lag Effect " APP_VERSION, 0, 30, 283, 300, 18, IDC_HDR);

    gBuildPage = -1;
    gUiReady = true;
    Layout();
}

// Tab button: label, with an accent bar under the selected one.
static void DrawTab(DRAWITEMSTRUCT* d)
{
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    int idx = (int)d->CtlID - IDC_TAB0;
    bool active = idx == gPage;

    FillRect(dc, &rc, BgBrush());
    wchar_t text[32]; GetWindowTextW(d->hwndItem, text, 32);
    HGDIOBJ of = SelectObject(dc, active ? gFontBold : gFont);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, active ? (gDark ? DK_TEXT : RGB(20, 20, 20)) : (gDark ? DK_DIM : RGB(105, 105, 105)));
    RECT tr = rc; tr.bottom -= 3;
    DrawTextW(dc, text, -1, &tr, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(dc, of);
    if (active) {
        HBRUSH ab = CreateSolidBrush(ACCENT);
        RECT bar = { rc.left + 14, rc.bottom - 3, rc.right - 14, rc.bottom };
        FillRect(dc, &bar, ab);
        DeleteObject(ab);
    }
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) {
        RECT fr = rc; InflateRect(&fr, -4, -4);
        SetTextColor(dc, gDark ? DK_TEXT : RGB(20, 20, 20));
        DrawFocusRect(dc, &fr);
    }
}

static void PaintWindow(HDC dc)
{
    int d = RowsDelta();
    SetBkMode(dc, OPAQUE);
    HGDIOBJ oldFont = SelectObject(dc, gFontBold);
    HPEN border = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : RGB(206, 206, 206));
    HGDIOBJ oldPen = SelectObject(dc, border), oldBr = SelectObject(dc, GetStockObject(NULL_BRUSH));

    {                                           // line under the tabs
        HPEN sep = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : RGB(206, 206, 206));
        HGDIOBJ op = SelectObject(dc, sep);
        MoveToEx(dc, 14, 42, nullptr); LineTo(dc, CLIENT_W - 14, 42);
        SelectObject(dc, op);
        DeleteObject(sep);
    }

    for (int i = 0; i < gSectionN; i++) {       // rounded section frames with their title in the top edge
        Section& s = gSections[i];
        if (s.page >= 0 && s.page != gPage) continue;
        int y = s.y + (s.shifts ? d : 0);
        RoundRect(dc, s.x, y, s.x + s.w, y + s.h, 12, 12);
        SIZE sz; GetTextExtentPoint32W(dc, s.title, lstrlenW(s.title), &sz);
        RECT tr = { s.x + 10, y - sz.cy / 2, s.x + 18 + sz.cx, y + sz.cy / 2 + 1 };
        FillRect(dc, &tr, BgBrush());
        SetBkColor(dc, BgColor());
        SetTextColor(dc, gDark ? DK_TEXT : RGB(40, 40, 40));
        TextOutW(dc, s.x + 14, y - sz.cy / 2, s.title, lstrlenW(s.title));
    }

    if (gDark) {                                 // flat borders around number boxes and text boxes
        HPEN eb = CreatePen(PS_SOLID, 1, DK_BORDER);
        SelectObject(dc, eb);
        for (int i = 0; i < gFramedN; i++) {
            if (!IsWindowVisible(gFramed[i].edit)) continue;
            RECT r; GetWindowRect(gFramed[i].edit, &r);
            if (gFramed[i].ud) { RECT u; GetWindowRect(gFramed[i].ud, &u); UnionRect(&r, &r, &u); }
            MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2);
            InflateRect(&r, 1, 1);
            Rectangle(dc, r.left, r.top, r.right, r.bottom);
        }
        SelectObject(dc, border);
        DeleteObject(eb);
    }
    SelectObject(dc, oldPen); SelectObject(dc, oldBr); SelectObject(dc, oldFont);
    DeleteObject(border);
}

static void DrawStatus(DRAWITEMSTRUCT* d)
{
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    bool loop = gLooping, live = gRunning;
    COLORREF fill = loop ? (gDark ? RGB(92, 30, 34) : RGB(253, 224, 224)) : (gDark ? DK_CTL : RGB(228, 228, 228));
    COLORREF text = loop ? (gDark ? RGB(255, 125, 125) : RGB(185, 20, 20)) : (gDark ? DK_TEXT : RGB(40, 40, 40));
    COLORREF dotc = loop ? RGB(235, 60, 60) : live ? RGB(40, 190, 90) : RGB(150, 150, 150);

    HBRUSH br = CreateSolidBrush(fill);
    HPEN   pn = CreatePen(PS_SOLID, 1, fill);
    HGDIOBJ op = SelectObject(dc, pn), ob = SelectObject(dc, br);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 14, 14);
    SelectObject(dc, op); SelectObject(dc, ob);
    DeleteObject(br); DeleteObject(pn);

    wchar_t s[160]; GetWindowTextW(d->hwndItem, s, 160);
    HGDIOBJ of = SelectObject(dc, loop ? gFontBold : gFont);
    SIZE sz; GetTextExtentPoint32W(dc, s, lstrlenW(s), &sz);
    int total = sz.cx + 14;
    int x = (rc.left + rc.right - total) / 2, cy = (rc.top + rc.bottom) / 2;

    HBRUSH db = CreateSolidBrush(dotc);
    HPEN   dp = CreatePen(PS_SOLID, 1, dotc);
    op = SelectObject(dc, dp); ob = SelectObject(dc, db);
    Ellipse(dc, x, cy - 4, x + 8, cy + 4);
    SelectObject(dc, op); SelectObject(dc, ob);
    DeleteObject(db); DeleteObject(dp);

    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, text);
    TextOutW(dc, x + 14, cy - sz.cy / 2, s, lstrlenW(s));
    SelectObject(dc, of);
}

static bool Checked(int id) { return IsDlgButtonChecked(gWnd, id) == BST_CHECKED; }

static void OnCommand(int id, int code)
{
    if (id >= IDC_ROWDEV && id < IDC_ROWDEV + MAX_OUT) {
        if (code == CBN_SELCHANGE) RestartIfRunning();
        return;
    }
    if (id >= IDC_ROWMODE && id < IDC_ROWMODE + MAX_OUT) {
        if (code == CBN_SELCHANGE) gRowMode[id - IDC_ROWMODE] = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
        return;
    }
    if (id >= IDC_ROWVOL && id < IDC_ROWVOL + MAX_OUT) {
        if (!gUiReady) return;
        int k = id - IDC_ROWVOL;
        BOOL ok = FALSE;
        int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok) gRowVol[k] = Iclamp(v, 0, 200);
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gRowVol[k], FALSE);
        return;
    }
    if (id >= IDC_ROWDEL && id < IDC_ROWDEL + MAX_OUT) {
        if (code == BN_CLICKED) RemoveOutput(id - IDC_ROWDEL);
        return;
    }
    if (id >= IDC_FXGRP_ON && id < IDC_FXGRP_ON + FX_GROUPS) {
        SetFxGroupOn(id - IDC_FXGRP_ON, Checked(id));
        return;
    }
    if (id >= IDC_FXGRP_KEY && id < IDC_FXGRP_KEY + FX_GROUPS) {
        if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[1 + id - IDC_FXGRP_KEY], id);
        return;
    }
    if (id >= IDC_FXGRP_RESET && id < IDC_FXGRP_RESET + FX_GROUPS) {
        if (code == BN_CLICKED) ResetFxGroup(id - IDC_FXGRP_RESET);
        return;
    }

    switch (id) {
    case IDC_LOOP: case IDC_SPEED: case IDC_PITCH: case IDC_FADE: case IDC_GATE: case IDC_TALKVOL:
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
    case IDC_ADDOUT:   if (code == BN_CLICKED) AddOutput(); break;
    case IDC_TAB0: case IDC_TAB1: case IDC_TAB2:
        if (code == BN_CLICKED) SetPage(id - IDC_TAB0);
        break;
    case IDC_FXON:
        if (code == BN_CLICKED) { SetFxOn(!gFxOn); UpdateStatus(true); }
        break;
    case IDC_GATEON:   gGateOn = Checked(IDC_GATEON); break;
    case IDC_TALKON:   gTalkOver = Checked(IDC_TALKON); break;
    case IDC_UPDSTART: gUpdateOnStart = Checked(IDC_UPDSTART); break;
    case IDC_CHECKUPD: if (code == BN_CLICKED) StartUpdateCheck(true); break;
    case IDC_HOLD:
    case IDC_TOGGLE:   gToggleMode = Checked(IDC_TOGGLE); UpdateStatus(true); break;
    case IDC_HOTKEY:   if (code == BN_CLICKED) BeginKeyCapture(gHotkeys, IDC_HOTKEY); break;
    case IDC_FXKEY_MASTER:
        if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[0], IDC_FXKEY_MASTER);
        break;
    case IDC_THEME:
        if (code == CBN_SELCHANGE) {
            gThemeMode = (int)SendDlgItemMessageW(gWnd, IDC_THEME, CB_GETCURSEL, 0, 0);
            ApplyTheme();
        }
        break;
    case IDC_MIC:
        if (code == CBN_SELCHANGE) RestartIfRunning();
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
        // Keeps retrying quietly if the devices are still busy (e.g. the old version is closing).
        if ((gAutoStart || gResumeAudio) && !StartAudio(true)) SetTimer(h, TIMER_RECONNECT, 1000, nullptr);
        UpdateUi();
        SetTimer(h, TIMER_STATUS, 50, nullptr);
        SetTimer(h, TIMER_CLEANUP, 1000, nullptr);
        SetTimer(h, TIMER_FXKEYS, 20, nullptr);
        return 0;
    case WM_TIMER:
        if (w == TIMER_STATUS) UpdateStatus();
        else if (w == TIMER_KEY) PollKeyCapture();
        else if (w == TIMER_CLEANUP) CleanupOldExe();
        else if (w == TIMER_FXKEYS) PollFxKeys();
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
    case WM_NOTIFY: {
        NMHDR* nh = (NMHDR*)l;
        if (gDark && nh->code == NM_CUSTOMDRAW) {
            wchar_t cls[16];
            GetClassNameW(nh->hwndFrom, cls, 16);
            if (!lstrcmpiW(cls, L"Button")) return DrawDarkCheck((NMCUSTOMDRAW*)l);
        }
        break;
    }
    case WM_DRAWITEM:
        if (((DRAWITEMSTRUCT*)l)->hwndItem == gStatus) { DrawStatus((DRAWITEMSTRUCT*)l); return TRUE; }
        if (w >= IDC_TAB0 && w < IDC_TAB0 + TAB_COUNT) { DrawTab((DRAWITEMSTRUCT*)l); return TRUE; }
        if (w == IDC_FXON) { DrawFxSwitch((DRAWITEMSTRUCT*)l); return TRUE; }
        break;
    case WM_CONTEXTMENU: {                      // right-click a Voice FX hotkey button to clear it
        int id = GetDlgCtrlID((HWND)w);
        if (id == IDC_FXKEY_MASTER) { ClearFxKey(0); return 0; }
        if (id >= IDC_FXGRP_KEY && id < IDC_FXGRP_KEY + FX_GROUPS) { ClearFxKey(1 + id - IDC_FXGRP_KEY); return 0; }
        break;
    }
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
        FillRect((HDC)w, &rc, BgBrush());
        return 1;
    }
    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC dc = BeginPaint(h, &ps);
        PaintWindow(dc);
        EndPaint(h, &ps);
        return 0;
    }
    case WM_CTLCOLORSTATIC: case WM_CTLCOLORBTN: case WM_CTLCOLOREDIT: case WM_CTLCOLORLISTBOX: {
        HDC dc = (HDC)w;
        bool header = GetDlgCtrlID((HWND)l) == IDC_HDR;
        bool field  = m == WM_CTLCOLOREDIT || m == WM_CTLCOLORLISTBOX;
        if (!gDark) {
            if (!header) break;
            SetTextColor(dc, RGB(110, 110, 110));
            SetBkColor(dc, GetSysColor(COLOR_BTNFACE));
            return (LRESULT)GetSysColorBrush(COLOR_BTNFACE);
        }
        SetTextColor(dc, header ? DK_DIM : DK_TEXT);
        SetBkColor(dc, field ? DK_CTL : DK_BG);
        return (LRESULT)(field ? gBrDarkCtl : gBrDarkBg);
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
    gResumeAudio = justUpdated && wcsstr(GetCommandLineW(), L"--resume") != nullptr;

    LoadSettings();
    LoadThemeApis();
    gCtxOk = ma_context_init(nullptr, 0, nullptr, &gCtx) == MA_SUCCESS;
    if (gCtxOk) ma_context_get_devices(&gCtx, &gPlayDevs, &gPlayCount, &gCapDevs, &gCapCount);

    gFont     = CreateFontW(-13, 0, 0, 0, FW_NORMAL,   0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    gFontBold = CreateFontW(-13, 0, 0, 0, FW_SEMIBOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
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

    WNDCLASSW kc = {};                                   // knobs on the Voice FX page
    kc.style         = CS_DBLCLKS;
    kc.lpfnWndProc   = KnobProc;
    kc.hInstance     = hi;
    kc.hCursor       = LoadCursorW(nullptr, IDC_SIZENS);
    kc.lpszClassName = L"LagKnob";
    RegisterClassW(&kc);

    DWORD style = WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_CLIPCHILDREN;
    RECT r = { 0, 0, CLIENT_W, BASE_H };
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
        if (msg.message == WM_KEYDOWN && msg.wParam == VK_TAB && (GetKeyState(VK_CONTROL) & 0x8000) &&
            (msg.hwnd == h || IsChild(h, msg.hwnd))) {
            SetPage((gPage + 1) % TAB_COUNT);   // Ctrl+Tab: next page
            continue;
        }
        if (!IsDialogMessageW(h, &msg)) {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
    }
    if (gCtxOk) ma_context_uninit(&gCtx);
    DeleteObject(gFont);
    DeleteObject(gFontBold);
    return 0;
}
