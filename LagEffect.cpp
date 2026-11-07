// LagEffect.cpp - hold (or toggle) a hotkey to loop the last chunk of your mic.
// Windows app with a settings window and tray icon. Settings save to LagEffect.ini.
// Built for Discord / OBS: several outputs each playing Off / Effect only / Everything,
// built-in noise gate, auto-reconnect, separate pitch/speed, light/dark theme, GitHub updater,
// a Voice FX page (pitch shift, reverb and a Voloco-style vocoder on your live voice, set with knobs),
// and a Mic page (AI noise suppression, noise gate, voice quality).
//
// Build (GitHub Actions does this automatically, see .github/workflows/build.yml):
//   1. Put miniaudio.h (https://github.com/mackron/miniaudio, 0.11.25) next to this file.
//      RNNoise (noise suppression) is included in the rnnoise folder.
//   2. Visual Studio (Developer Command Prompt):
//        rc LagEffect.rc
//        cl /O2 /MT /utf-8 /D_USE_MATH_DEFINES /I rnnoise\\include LagEffect.cpp rnnoise\src\denoise.c rnnoise\src\rnn.c
//           rnnoise\src\rnn_data.c rnnoise\src\pitch.c rnnoise\src\kiss_fft.c rnnoise\src\celt_lpc.c
//           LagEffect.res /link /SUBSYSTEM:WINDOWS
//      MinGW / MSYS2:
//        windres LagEffect.rc -O coff -o LagEffect_res.o
//        gcc -O2 -Irnnoise/include -c rnnoise/src/{denoise,rnn,rnn_data,pitch,kiss_fft,celt_lpc}.c
//        g++ -O2 LagEffect.cpp *.o LagEffect_res.o -o LagEffect.exe -mwindows -lcomctl32 -lwinhttp -static
//
// Releasing an update: bump APP_VERSION below, build, then create a GitHub release whose tag
// is the version (e.g. v1.4.0) and attach LagEffect.exe. The app's "Check now" button finds it.

#define APP_VERSION L"1.35.0"
#define DEFAULT_UPDATE_REPO L"slavward/LagEffect"

#define UNICODE
#define _UNICODE
#define NOMINMAX
#include <winsock2.h>                           // (before anything pulls in windows.h: remote control's WebSocket server)
#include <ws2tcpip.h>
#define MINIAUDIO_IMPLEMENTATION
#include "miniaudio.h"
#include "rnnoise/include/rnnoise.h"           // AI noise suppression (BSD licence, see rnnoise/COPYING)

#include <windows.h>
#include <commctrl.h>
#include <shellapi.h>
#include <winhttp.h>
#include <mmdeviceapi.h>                        // listing apps that play sound (Vocode to song)
#include <audiopolicy.h>
#include <audioclient.h>                        // per-app sound capture (process loopback), done by hand
#include <tlhelp32.h>                           // process names without opening the process (browsers' audio helpers)
#include <commdlg.h>                            // "Audio file..." picker
#include <sapi.h>                               // text to speech (Windows' own voices)
#include <wctype.h>
#include <shlobj.h>                             // folder picker (Load a folder of sounds)
#include <mfapi.h>                              // MP3 export (Windows' own encoder, loaded at run time)
#include <mfidl.h>
#include <mfreadwrite.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#if defined(_M_X64) || defined(__x86_64__) || defined(_M_IX86) || defined(__i386__)
#include <xmmintrin.h>
#define HAVE_SSE_FLAGS 1
#endif

// Focus boxes (the dotted outline on the control you last used) only show once you move around with the
// keyboard (Tab / arrows), like most apps; clicking with the mouse hides them again.
static bool gKbdNav = false;
static inline int FocusRectIfKeys(HDC dc, const RECT* r) { return gKbdNav ? DrawFocusRect(dc, r) : TRUE; }
#define DrawFocusRect(dc, r) FocusRectIfKeys(dc, r)

#ifdef _MSC_VER
#pragma comment(lib, "comctl32.lib")
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "advapi32.lib")
#pragma comment(lib, "winhttp.lib")
#pragma comment(lib, "ole32.lib")
#pragma comment(lib, "comdlg32.lib")
#pragma comment(lib, "ws2_32.lib")
#pragma comment(linker, "\"/manifestdependency:type='win32' name='Microsoft.Windows.Common-Controls' version='6.0.0.0' processorArchitecture='*' publicKeyToken='6595b64144ccf1df' language='*'\"")
#endif

static int Imin(int a, int b) { return a < b ? a : b; }
static int Imax(int a, int b) { return a > b ? a : b; }
static int Iclamp(int v, int lo, int hi) { return Imax(lo, Imin(hi, v)); }

// ======================= audio =======================
#define RATE      48000
#define HIST      (RATE * 4)                   // loops up to 2 s; Rewind / Repeat word look back further
#define RING_SIZE 16384                        // per-output ring buffer (power of two), floats
#define RING_FRAMES (RING_SIZE / 2)             // ... as stereo frames
#define MAXGRAIN  (RATE * 40 / 1000)           // 40 ms grains for pitch/speed
#define MAX_OUT   5                            // output rows
static const int BUFFERS[] = { 32, 64, 128, 256, 512 };

enum { MODE_OFF = 0, MODE_EFFECT = 1, MODE_ALL = 2, MODE_CLEAN = 3, MODE_APPS = 4 };   // Clean: your voice without Voice FX or the stutter
                                                // Apps only: just the Mixer channels sent to it (no mic, no effects, no soundboard)

// Settings shared with the audio threads (plain ints/floats are safe to read on x86/x64).
static volatile int   gLoopMs = 500, gSpeedPct = 100, gPitchPct = 100, gFadeMs = 3;
static volatile int   gTalkVolPct = 100;
#define MAX_KEYS 3                             // hotkey can be a combination of up to 3 keys
static volatile int   gHotkeys[MAX_KEYS] = { VK_F8, 0, 0 };
static volatile bool  gToggleMode = false, gTalkOver = false;
static volatile bool  gCapturingKey = false, gLooping = false;
#define DEF_MODE0 MODE_ALL
#define DEF_MODEK MODE_EFFECT
static volatile int   gRowMode[MAX_OUT] = { DEF_MODE0, DEF_MODEK, DEF_MODEK, DEF_MODEK, DEF_MODEK };
static volatile int   gRowVol[MAX_OUT]  = { 100, 100, 100, 100, 100 };

static float  hist[HIST], frozen[HIST], hann[MAXGRAIN];
static size_t wpos = 0, frozenLen = 1;
static bool   looping = false, prevDown = false, toggled = false;
static double loopPos = 0, grainStart[2];
static int    grainAge[2], grainLen = 2;
static float  gateEnv = 0, gateGain = 1;
static volatile bool gMicMuted = false;          // Mute mic: button / hotkey / tray
static int gUiScale = 100;                      // Settings > UI size
static bool gOwnSize = false;                   // (resizing) the window is sizing itself
static bool gMoving = false;                    // you're dragging / resizing the window
static DWORD gOutNextTry[MAX_OUT], gOutWait[MAX_OUT];       // (extra outputs that failed: when to try again)
static int  gOrgX = 0;                          // pages sit centred when the window is wider than they are
static int  gExtraW = 0, gExtraH = 0;           // how much bigger than it needs to be you made the window (px)
static bool gOverlayOn = false, gBeeps = false, gCmdLine = false, gCompact = false;
static inline int SC(int v) { return gUiScale == 100 ? v : MulDiv(v, gUiScale, 100); }
static inline int UNSC(int v) { return gUiScale == 100 ? v : MulDiv(v, 100, gUiScale); }   // screen px -> design px   // UI size   // gCmdLine: hidden (right-click the version text)
static int  gOverlayX = INT_MIN, gOverlayY = INT_MIN;
static volatile int  gPttMode = 0;               // 0 off, 1 push-to-talk (mic only while held), 2 push-to-mute
static volatile bool gPttHeld = false;
static float         pttGain = 1;
static volatile float gOutPeak[8];               // per output, for the little meters on the Main tab
static float gOutShow[8] = { -80, -80, -80, -80, -80, -80, -80, -80 };
// Random lag: the stutter fires by itself now and then. Rewind / Repeat word: hotkey requests to the audio thread.
static volatile bool gRandLagOn = false, gRewindReq = false, gRepeatReq = false;
// Settings > Features: each of these is hidden and doesn't run at all while it's off (new installs: all off).
static volatile bool gFeatLag = false, gFeatFx = false, gFeatSound = false, gFeatClips = false;
// Remote control (Streamer.bot & co.): a WebSocket server on this PC only, and only while it's switched on.
static bool    gWsOn = false;
static int     gWsPort = 7600;
static wchar_t gWsPass[64] = L"";
static volatile DWORD gWsLagUntil = 0;          // {"do":"lag","ms":...}: stutter until then
enum { FEAT_LAG = 1, FEAT_FX = 2, FEAT_SOUND = 4, FEAT_CLIPS = 8 };
static bool FeatOn(int mask) { return (mask & FEAT_LAG && gFeatLag) || (mask & FEAT_FX && gFeatFx) || (mask & FEAT_SOUND && gFeatSound) || (mask & FEAT_CLIPS && gFeatClips); }
static int  gBuildFeat = 0;                     // (while building the window: which feature these controls belong to)
static volatile int  gRandLagSec = 8, gRewindMs = 2000, gRepeatN = 3;
static volatile int  gRewindTop = 350, gRewindRamp = 30, gRewindPitch = 0;   // Rewind: top speed %, % of it spent speeding up, semitones
static volatile bool gTapeReq = false, gDiveHeld = false, gBeatSync = false, gFxBypass = false;   // A/B: hear yourself dry
static volatile int  gDiveSemis = -12, gBpm = 120, gBeatDiv = 1;   // beat division: 0 = 1/4, 1 = 1/8, 2 = 1/16, 3 = 1/32
// Mic test: 5 s of exactly what Discord hears, recorded by the audio thread, played back on your speakers.
#define TEST_LEN (RATE * 5)
static short gTestBuf[TEST_LEN];
static volatile unsigned gTestPos = 0, gTestLen = 0;
static volatile bool gTestRec = false;
#define PADREC_LEN (RATE * 10)                  // "record a pad from your mic": up to 10 s
static short gPadRecBuf[PADREC_LEN];
static volatile unsigned gPadRecPos = 0;
static volatile bool gPadRec = false, gPadDuck = false, gPadChoke = false;
static volatile int  gHearOut = 0;              // always hear pads / clips / TTS on: 0 = no extra, 1..MAX_OUT = that output, MAX_OUT + 1 = every output
static int gPadRecSlot = -1;                    // pad being recorded from the mic

// ---- Soundboard: 8 pads of short clips, mixed into every output that isn't Off ----
// Not recorded into the stutter loop, not run through the voice effects, not silenced by Mute mic.
// The UI swaps clips in/out (data == nullptr while swapping); the audio thread only reads.
#define PADS  8                                 // soundboard pads on screen (one page)
#define PAD_BANKS 4                             // pages A-D
#define PAD_N (PADS * PAD_BANKS)                // every pad
#define CLIPS 8                                 // instant-replay clips on screen (one page)
#define CLIP_BANKS 4                            // clip pages A-D
#define CLIP_N (CLIPS * CLIP_BANKS)             // every clip slot
#define CLIP0 PAD_N                             // where clips start in gPads
#define TTS_SLOT (CLIP0 + CLIP_N)               // text-to-speech plays in this slot
#define SB_N  (TTS_SLOT + 1)                    // all share one mixer: pads, clips, then text-to-speech
struct Pad {
    short* volatile   data;                      // 48 kHz mono 16-bit
    volatile unsigned len;
    volatile int      vol;                       // percent
    volatile bool     trigger, stop;             // UI -> audio: (re)start / stop
    volatile bool     playing;                   // audio -> UI
    volatile unsigned pos;
    float             fade;                      // short fade-out when stopped or restarted (no clicks)
    unsigned          fadePos;
    // per-pad options (soundboard): play mode, speed (varispeed %), pitch (semitones), fades (ms)
    volatile int      mode, speed, pitch, fadeInMs, fadeOutMs;
    double            fpos;                      // play position (fractional when the speed isn't 100%)
    bool              stopping;                  // fading out after Stop
    float             outEnv;
    int               lastPitch; double ratio;
};
enum { PM_ONESHOT = 0, PM_LOOP, PM_HOLD, PM_TOGGLE };
template <class T> static inline T Min(T a, T b) { return a < b ? a : b; }
template <class T> static inline T Max(T a, T b) { return a > b ? a : b; }
static Pad gPads[SB_N];
static HWND gTrimWnd = nullptr;                 // clip trim editor, while open
static volatile int gPadMaster = 100, gClipMaster = 100;
static volatile bool gPadsFx = false, gClipsFx = false;   // play through the voice effects (as if you said it)
static int gPadBank = 0;                        // soundboard page on screen
static inline int PadSlot(int row) { return gPadBank * PADS + row; }

struct PShift;
static float PadPitch(int i, float x, double ratio);   // per-pad pitch shifter (defined with the DSP)
static inline float PadsMix(float& viaFx, int& padsPlaying)   // audio thread: one output sample of all playing pads
{                                               // (viaFx gets the ones that go through the voice effects)
    viaFx = 0; padsPlaying = 0;
    float sum = 0;
    const float padMaster = gPadMaster / 100.0f, clipMaster = gClipMaster / 100.0f;
    for (int i = 0; i < SB_N; i++) {
        Pad& p = gPads[i];
        const bool  isClip = i >= CLIP0 && i < CLIP0 + CLIP_N;
        const float master = isClip ? clipMaster : padMaster;
        float& acc = (isClip ? gClipsFx : gPadsFx) ? viaFx : sum;
        short* d = p.data; unsigned n = p.len;
        if (p.stop) {
            p.stop = false;
            if (p.playing) {
                if (p.fadeOutMs > 0 && !p.stopping) { p.stopping = true; p.outEnv = 1.0f; }   // fade out, then stop
                else if (!p.stopping) { p.fade = 1.0f; p.fadePos = (unsigned)p.fpos; p.playing = false; }
            }
        }
        if (p.trigger) {                         // (re)start: fade the old play-through out, start fresh
            p.trigger = false;
            if (p.playing) { p.fade = 1.0f; p.fadePos = (unsigned)p.fpos; }
            p.fpos = 0; p.pos = 0; p.playing = d && n; p.stopping = false; p.outEnv = 1.0f;
        }
        if (!d || !n) { p.playing = false; p.fade = 0; continue; }
        const float g = p.vol / 100.0f * master * (1.0f / 32768.0f);
        if (p.fade > 0) {                         // the tail of a stopped / restarted play-through
            if (p.fadePos < n) acc += d[p.fadePos++] * g * p.fade;
            p.fade -= 1.0f / 240.0f;              // 5 ms
        }
        if (p.playing) {
            if (!isClip && i < CLIP0) padsPlaying++;
            const double rate = p.speed > 0 && p.speed != 100 ? p.speed / 100.0 : 1.0;
            double fp = p.fpos;
            unsigned i0 = (unsigned)fp;
            float smp = d[i0];
            if (rate != 1.0) { float t = (float)(fp - i0); smp = smp * (1.0f - t) + (i0 + 1 < n ? d[i0 + 1] : 0) * t; }
            const double fin = p.fadeInMs > 1 ? p.fadeInMs * (RATE / 1000.0) : 48.0;
            float env = fp < fin ? (float)(fp / fin) : 1.0f;
            double left = (n - fp) / rate;
            if (p.mode != PM_LOOP && left < 240) env *= (float)(left / 240.0);   // 5 ms fade-out at the end
            if (p.stopping) {
                p.outEnv -= 1.0f / (Imax(1, (int)p.fadeOutMs) * (RATE / 1000.0f));
                if (p.outEnv <= 0) { p.outEnv = 0; p.playing = false; p.stopping = false; }
                env *= p.outEnv;
            }
            float v = smp * g * env;
            if (p.pitch != 0 && i < PAD_N) {
                if (p.lastPitch != p.pitch) { p.lastPitch = p.pitch; p.ratio = pow(2.0, p.pitch / 12.0); }
                v = PadPitch(i, v, p.ratio);
            }
            acc += v;
            fp += rate;
            if (fp >= n) { if (p.mode == PM_LOOP) fp -= n; else p.playing = false; }
            p.fpos = fp; p.pos = (unsigned)fp;
        }
    }
    return sum;
}
// Instant replay: the last REC_MAX_S seconds are always kept (in memory only) so "Clip it" can save them.
// Your voice is written by the audio thread; PC sound by its own loopback capture.
#define REC_MAX_S 60
#define REC_LEN   (RATE * (REC_MAX_S + 1))
struct RecRing { short* buf; volatile unsigned w, fill; };
static RecRing gRecVoice, gRecPc;
static volatile bool gRecVoiceOn = false;

static inline void RecPut(RecRing& r, float v)
{
    if (!r.buf) return;
    v = v > 1.0f ? 1.0f : v < -1.0f ? -1.0f : v;
    unsigned w = r.w;
    r.buf[w] = (short)(v * 32767.0f);
    r.w = w + 1 >= REC_LEN ? 0 : w + 1;
    if (r.fill < REC_LEN) r.fill = r.fill + 1;
}

static float  muteGain = 1;                      // ramps so muting never clicks
static float  talkEnv = 0, chDuck = 1;           // Mixer ducking: are you talking, and how far ducked channels are down
static int    talkHold = 0;
static int    gateHold = 0;

// Mic cleanup (Mic tab). Order: boost -> low cut -> AI noise suppression -> gate -> leveler.
enum { GATE_OFF = 0, GATE_VOLUME = 1, GATE_VOICE = 2, GATE_BOTH = 3 };
static volatile int   gMicBoostDb = 0, gLowCutHz = 80, gLevelerPct = 0;
static volatile bool  gNsOn = false;
static volatile int   gNsStrength = 100;
static volatile int   gGateMode = GATE_OFF, gGateLastMode = GATE_VOLUME;
static volatile int   gGateThrDb = -50, gGateVoicePct = 60, gGateHoldMs = 150, gGateReleaseMs = 80, gGateRangeDb = 80;
static volatile float gMeterPeak = 0, gMeterVad = 0;  // for the Mic tab meter (UI reads, then clears the peak)
static volatile bool  gMeterGateOpen = true;

// RNNoise works on 10 ms frames (480 samples at 48 kHz) and delays its output by one more frame,
// so the dry signal is delayed by the same 20 ms to stay lined up when blending.
#define NS_FRAME 480
#define NS_DELAY (NS_FRAME * 2)
#define DRY_RING 1024
static DenoiseState* gNs = nullptr;
static float nsIn[NS_FRAME], nsOut[NS_FRAME], dryRing[DRY_RING];
static int   nsIdx = 0, dryW = 0;
static float nsVad = 0;
static float hpX1, hpX2, hpY1, hpY2, hpB0 = 1, hpB1, hpB2, hpA1, hpA2;
static int   hpFc = -1;
static float lvEnv = 0;
static float limGain[MAX_OUT] = { 1, 1, 1, 1, 1 };
static volatile bool gLimHit[MAX_OUT];          // the limiter caught a peak (the Mixer's "Limit" light)

// 2nd-order Butterworth high-pass ("Low cut"), coefficients recomputed when the knob moves.
static void LowCutSetup(int fc)
{
    hpFc = fc;
    if (fc <= 0) return;
    double w = 2.0 * 3.141592653589793 * fc / RATE, c = cos(w), al = sin(w) / (2.0 * 0.7071067811865476);
    double a0 = 1.0 + al;
    hpB0 = (float)((1.0 + c) / 2.0 / a0); hpB1 = (float)(-(1.0 + c) / a0); hpB2 = hpB0;
    hpA1 = (float)(-2.0 * c / a0);         hpA2 = (float)((1.0 - al) / a0);
}

static inline float LowCut(float x)
{
    float y = hpB0 * x + hpB1 * hpX1 + hpB2 * hpX2 - hpA1 * hpY1 - hpA2 * hpY2;
    hpX2 = hpX1; hpX1 = x; hpY2 = hpY1; hpY1 = y;
    return y;
}

// Runs RNNoise one frame behind. Returns the denoised sample and, through *dry, the input from
// the same moment (20 ms ago). Updates nsVad (0..1 chance that the last frame was speech).
static inline float NoiseStage(float x, float* dry)
{
    dryRing[dryW] = x;
    *dry = dryRing[(dryW - NS_DELAY) & (DRY_RING - 1)];
    dryW = (dryW + 1) & (DRY_RING - 1);
    float den = nsOut[nsIdx];
    nsIn[nsIdx] = x * 32768.0f;                  // RNNoise expects 16-bit sample values
    if (++nsIdx == NS_FRAME) {
        nsIdx = 0;
        float frame[NS_FRAME];
        nsVad = gNs ? rnnoise_process_frame(gNs, frame, nsIn) : 1.0f;
        for (int i = 0; i < NS_FRAME; i++) nsOut[i] = gNs ? frame[i] * (1.0f / 32768.0f) : nsIn[i] * (1.0f / 32768.0f);
    }
    return den;
}

static void MicReset()                          // audio thread / before start
{
    gateEnv = 0; gateGain = 1; gateHold = 0;
    memset(nsIn, 0, sizeof(nsIn)); memset(nsOut, 0, sizeof(nsOut)); memset(dryRing, 0, sizeof(dryRing));
    nsIdx = 0; dryW = 0; nsVad = 0;
    hpX1 = hpX2 = hpY1 = hpY2 = 0; hpFc = -1;
    lvEnv = 0;
    for (int k = 0; k < MAX_OUT; k++) limGain[k] = 1;
}

// Output limiter: leaves everything under -1 dBFS untouched; louder peaks are turned down
// smoothly instead of being distorted (replaces the old soft clipper, which coloured loud voices).
static inline float Limit(int k, float x)
{
    const float ceil = 0.891f;                   // -1 dBFS
    float a = x < 0 ? -x : x;
    if (a * limGain[k] > ceil) limGain[k] = ceil / a;
    float y = x * limGain[k];
    limGain[k] += (1.0f - limGain[k]) * 0.00014f;   // ~150 ms recovery
    return y;
}

// The same, for a stereo pair: one gain for both sides, so the picture never leans when it limits.
static inline void LimitStereo(int k, float& l, float& r)
{
    const float ceil = 0.891f;
    float a = Max(fabsf(l), fabsf(r));
    if (a * limGain[k] > ceil) { limGain[k] = ceil / a; if (limGain[k] < 0.89f) gLimHit[k] = true; }   // (more than ~1 dB)
    l *= limGain[k]; r *= limGain[k];
    limGain[k] += (1.0f - limGain[k]) * 0.00014f;
}

// ======================= mixer channels (audio side) =======================
// Up to CH_MAX extra inputs: an app (its sound, captured on its own), or an input device (another mic, a
// line-in...). Each capture runs on its own thread and pushes stereo frames into its channel's ring; the main
// callback takes them out, applies the channel's volume / mute and adds them to the outputs it's sent to.
#define CH_MAX   8
#define CH_RING  16384                          // frames (stereo, interleaved), power of two
enum { CH_NONE = 0, CH_APP = 1, CH_DEV = 2, CH_OUT = 3 };   // app / input device / what an output device plays
struct ChanAudio {
    float buf[CH_RING * 2];
    volatile unsigned w, r;                     // frames written (capture thread) / read (audio callback)
    volatile bool live;                         // capturing
    volatile float peakL, peakR;                // loudest since the meter last looked
    bool primed;                                // (callback) enough buffered to play smoothly
};
static ChanAudio gChA[CH_MAX];
struct ChanSet {
    int type; wchar_t src[128];
    volatile int db10;                          // volume in tenths of a dB (-600 = off, max +60)
    volatile bool mute, solo, duck;             // solo: only this one on your listening output; duck: quieter while you talk
    volatile unsigned routes;
    wchar_t name[32];                           // your name for it ("" = the app's / input's)
    int color;
    int holdTalk;                               // its hold hotkey: 0 = silences it while held, 1 = only plays while held
    volatile bool held;                         // (that key is held / push-to-talk without the key: quiet)
};
static inline float DbGain10(int db10) { return db10 <= -600 ? 0.0f : powf(10.0f, db10 / 200.0f); }
static volatile int gDuckDb = 12;               // how much ducked channels drop while you talk
static int  gChW[CH_MAX], gOutW[MAX_OUT];       // Mixer strip widths (design px, 0 = the normal width)
static int  gMixStep = 2;                       // Mixer hotkeys: dB per press
static int  gMixSub = 0;                        // Mixer tab: 0 = the strips, 1 = its hotkeys
static void MixMemStore(int c);
static ChanSet gCh[CH_MAX];
static volatile bool gOutMute[MAX_OUT];
static wchar_t gOutName[MAX_OUT][32];           // your name for an output ("" = "Out 1"...)
static void OutName(int k, wchar_t* out, int cap)
{
    if (k >= 0 && k < MAX_OUT && gOutName[k][0]) lstrcpynW(out, gOutName[k], cap);
    else { wchar_t t[16]; wsprintfW(t, L"Out %d", k + 1); lstrcpynW(out, t, cap); }
}
static void ChanStartAll(); static void ChanStopAll(); static void ChanTick(); static bool ChanStart(int c); static void ChanStop(int c);
static void ChanPush(int c, const float* in, unsigned frames, int chans)   // (capture thread)
{
    ChanAudio& a = gChA[c];
    if (!a.live || !in) return;
    if (gCh[c].mute || (!gCh[c].routes && !gCh[c].solo)) {   // can't be heard: only the meter needs it
        float pl = 0, pr = 0;
        for (unsigned f = 0; f < frames; f++) {
            float l = fabsf(in[f * chans]), r = chans > 1 ? fabsf(in[f * chans + 1]) : l;
            if (l > pl) pl = l; if (r > pr) pr = r;
        }
        if (pl > a.peakL) a.peakL = pl; if (pr > a.peakR) a.peakR = pr;
        return;
    }
    unsigned w = a.w; const unsigned r = a.r;
    float pkL = 0, pkR = 0;
    for (unsigned f = 0; f < frames; f++) {
        if (w - r >= CH_RING - 1) break;        // (the callback isn't keeping up: drop, it skips ahead anyway)
        const float L = in[f * chans], R = chans > 1 ? in[f * chans + 1] : L;
        const unsigned i = (w & (CH_RING - 1)) * 2;
        a.buf[i] = L; a.buf[i + 1] = R;
        if (fabsf(L) > pkL) pkL = fabsf(L); if (fabsf(R) > pkR) pkR = fabsf(R);
        w++;
    }
    MemoryBarrier();
    a.w = w;
    if (pkL > a.peakL) a.peakL = pkL; if (pkR > a.peakR) a.peakR = pkR;
}

// 4-point Hermite interpolation: noticeably cleaner than straight lines when pitch/speed resample.
static inline float Hermite(float xm1, float x0, float x1, float x2, float t)
{
    float c1 = 0.5f * (x1 - xm1);
    float c2 = xm1 - 2.5f * x0 + 2.0f * x1 - 0.5f * x2;
    float c3 = 0.5f * (x2 - xm1) + 1.5f * (x0 - x1);
    return ((c3 * t + c2) * t + c1) * t + x0;
}

// Output 1 plays straight from the main audio callback. Outputs 2-5 are separate devices
// fed through ring buffers.
static float             ring[MAX_OUT][RING_SIZE];
static volatile unsigned ringW[MAX_OUT], ringR[MAX_OUT];
static volatile unsigned gMainFrames = 256;     // the main device's block size (extra outputs size their cushion by it)
static volatile bool     ringOn[MAX_OUT];

static inline double WrapPos(double p, double len)
{
    while (p >= len) p -= len;
    while (p < 0) p += len;
    return p;
}

static inline float RowSignal(int mode, float effect, float everything, float clean)
{
    return mode == MODE_EFFECT ? effect : mode == MODE_ALL ? everything : mode == MODE_CLEAN ? clean : 0.0f;
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
// Same, but each key is asked about once per poll however many hotkeys use it (cache: 0 unknown, 1 up, 2 down).
static bool KeysDownCached(const volatile int* keys, BYTE* cache)
{
    bool any = false;
    for (int i = 0; i < MAX_KEYS; i++) {
        int vk = keys[i] & 255;
        if (!vk) continue;
        any = true;
        if (!cache[vk]) cache[vk] = (GetAsyncKeyState(vk) & 0x8000) ? 2 : 1;
        if (cache[vk] != 2) return false;
    }
    return any;
}

// ======================= voice effects (Voice FX page) =======================
// Run on the live mic right after the noise gate, so they're on everything you send, and the
// stutter loop records them too. Each effect has its own on/off switch and knobs; to add one,
// write its Process function, call it in AudioCallback, and add a group + knobs to gFxGroups/gKnobs.
static volatile bool gFxOn = false;            // master switch at the top of the page
static volatile bool gFxPitchOn = true, gFxRevOn = true;
static volatile int  gFxSemi = 0, gFxCents = 0, gFxGrainMs = 50, gFxPitchMix = 100;
static volatile int  gFxRevMix = 30, gFxRevSize = 60, gFxRevDamp = 50, gFxPreMs = 20;
static volatile bool gFxResetReq = true;       // UI asks the audio thread to clear effect buffers
static volatile bool gFxVocOn = false;
// Vocoder (Voloco-style): style, key (0 = C .. 11 = B), scale, and knobs.
enum { VOC_TUNE = 0, VOC_HARMONY = 1, VOC_ROBOT = 2, VOC_CHOIR = 3, VOC_SONG = 4, VOC_STYLES };
static volatile int  gVocStyle = VOC_HARMONY, gVocKey = 0, gVocScale = 1;
enum { VR_AUTO = 0, VR_HIGH = 1, VR_LOW = 2 };     // voice range (Vocoder): who's singing
static volatile int  gVocRange = VR_AUTO;
static volatile int  gVocRetuneMs = 15, gVocSynth = 60, gVocMix = 100;
static volatile bool gFxRadioOn = false;
static volatile int  gRadioPreset = 0, gRadioDrive = 50, gRadioStatic = 50, gRadioSquelch = 70;

// Pitch shifter: two read taps glide through a short delay line at the new speed and crossfade
// (Hann windows, half a grain apart). Each new grain starts where the waveform best lines up with
// the one fading out, so the crossfade stays in phase: no warble, no level dips.
#define PS_SIZE   8192                         // > 100 ms grain span + search at 48 kHz
#define PS_SEARCH 720                          // 15 ms: covers voice pitch periods down to ~67 Hz
#define PS_CORR   192                          // samples compared when lining up a grain
// Each shifter keeps its own state, so several can run at once (Voice FX pitch, vocoder tuning).
struct PShift {
    float  buf[PS_SIZE];
    int    w;
    double delay[2], frac[2];
    bool   primed;
};
static PShift gPsFx, gPsTune;
static PShift* gPadPs[PAD_N];                    // created the first time a pad is pitched
static float PitchShift(PShift& p, float x, double ratio, int span, float mix, bool centered, int search, int corr);

static void PsReset(PShift& p) { memset(&p, 0, sizeof(p)); }

static inline float PsRead(const PShift& p, double d)
{
    double rp = (double)p.w - d;
    if (rp < 0) rp += PS_SIZE;
    int   i0 = (int)rp;
    float t  = (float)(rp - i0);
    return Hermite(p.buf[(i0 - 1) & (PS_SIZE - 1)], p.buf[i0 & (PS_SIZE - 1)],
                   p.buf[(i0 + 1) & (PS_SIZE - 1)], p.buf[(i0 + 2) & (PS_SIZE - 1)], t);
}

static double PsGrainStart(const PShift& p, int k, int base, int search = PS_SEARCH, int corr = PS_CORR)
{
    int other = (int)(p.delay[1 - k] + 0.5);
    float best = -1e30f; int bestD = 0;
    for (int d = 0; d < search; d += 2) {
        int cand = base + d;
        float dot = 0, e = 0;
        for (int j = 0; j < corr; j += 2) {
            float x = p.buf[(p.w - other - j) & (PS_SIZE - 1)];
            float y = p.buf[(p.w - cand - j) & (PS_SIZE - 1)];
            dot += x * y; e += y * y;
        }
        float score = dot / sqrtf(e + 1e-9f);
        if (score > best) { best = score; bestD = d; }
    }
    return (double)(base + bestD);
}

// centered = false: lowest delay; each grain sweeps the whole span in one direction (big shifts).
// centered = true: grains start mid-span and may drift either way, so the ratio can swing above
// and below 1 smoothly (used for auto-tune, where small corrections flip direction all the time).
static float PitchShift(PShift& p, float x, double ratio, int span, float mix, bool centered = false,
                        int search = PS_SEARCH, int corr = PS_CORR)
{
    p.buf[p.w] = x;
    float out = x;
    if (ratio != 1.0) {
        double grain = (centered ? span / 2 : span) / fabs(1.0 - ratio);   // one grain sweeps the (half) span
        if (grain > RATE) grain = RATE;
        if (grain < 256)  grain = 256;
        // Going up, the read point catches up with the input, so a grain starts a full span back.
        const int base = centered ? 2 + span / 2 : ratio > 1.0 ? 2 + span : 2;
        if (!p.primed) {
            p.delay[0] = p.delay[1] = base;
            p.frac[0] = 0.0; p.frac[1] = 0.5;
            p.primed = true;
        }
        const double maxD = PS_SIZE - corr - 4;
        float wet = 0.0f;
        for (int k = 0; k < 2; k++) {
            if (p.frac[k] >= 1.0) { p.frac[k] -= 1.0; p.delay[k] = PsGrainStart(p, k, base, search, corr); }
            if (p.delay[k] < 2.0)  p.delay[k] = 2.0;
            if (p.delay[k] > maxD) p.delay[k] = maxD;
            float sn = (float)sin(3.141592653589793 * p.frac[k]);
            wet += PsRead(p, p.delay[k]) * sn * sn;
            p.delay[k] += 1.0 - ratio;
            p.frac[k]  += 1.0 / grain;
        }
        out = x + (wet - x) * mix;
    } else if (!centered) {
        p.primed = false;
    } else if (p.primed) {                      // centered: keep the same delay at ratio 1, no jump
        float sn0 = (float)sin(3.141592653589793 * p.frac[0]), sn1 = (float)sin(3.141592653589793 * p.frac[1]);
        out = (PsRead(p, p.delay[0]) * sn0 * sn0 + PsRead(p, p.delay[1]) * sn1 * sn1);
        out = x + (out - x) * mix;
        p.frac[0] += 1.0 / RATE; p.frac[1] += 1.0 / RATE;
        for (int k = 0; k < 2; k++) if (p.frac[k] >= 1.0) { p.frac[k] -= 1.0; p.delay[k] = PsGrainStart(p, k, 2 + span / 2, search, corr); }
    }
    p.w = (p.w + 1) & (PS_SIZE - 1);
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

// ======================= vocoder (Voloco-style tune + harmony) =======================
// 1. Pitch detection: YIN on a 12 kHz copy of the voice, every 5 ms.
// 2. Tune: the detected note is snapped to the nearest note of the chosen key/scale; Retune sets
//    how fast it gets there (0 = instant, the hard "robot" auto-tune). The voice is shifted with
//    its own phase-aligned pitch shifter, which keeps its natural tone.
// 3. Synth: band-limited sawtooth voices (two slightly detuned oscillators each) play the tuned
//    note and/or a chord built from the scale, following your pitch.
// 4. Channel vocoder: 28 bands (4th-order filters, 110 Hz - 7.6 kHz) shape the synth with your
//    voice's tone, with the synth's own tilt flattened out so words stay clear; consonants
//    ("s", "t") above 5 kHz pass through directly.
// Room to grow: more styles (VOC_STYLES), scales (VOC_SCALES), and per-style voice lists (VocVoices).
#define VOC_SCALES 6
static const char VOC_SCALE_STEPS[VOC_SCALES][12] = {
    { 1,1,1,1,1,1,1,1,1,1,1,1 },               // Chromatic
    { 1,0,1,0,1,1,0,1,0,1,0,1 },               // Major
    { 1,0,1,1,0,1,0,1,1,0,1,0 },               // Minor (natural)
    { 1,0,1,0,1,0,0,1,0,1,0,0 },               // Major pentatonic
    { 1,0,0,1,0,1,0,1,0,0,1,0 },               // Minor pentatonic
    { 1,0,0,1,0,1,1,1,0,0,1,0 },               // Blues
};

#define PD_DS     4                            // detector runs at 48 kHz / 4 = 12 kHz
#define PD_RATE   (RATE / PD_DS)
#define PD_MAXLAG 240                          // lowest pitch it can hear: 12000 / 240 = 50 Hz
#define PD_WIN    480                          // longest analysis window (40 ms; low voices need a few cycles)
#define PD_BUF    1024
#define PD_HOP    64                           // analyse every ~5 ms
#define VOC_BANDS 28
#define VOC_OSC   8                            // synth voices (each = 2 detuned saws)
#define SONG_GAIN 1.17f                        // Song style level: about as loud as your voice (calibrated in testing)

struct Biquad { float b0, b1, b2, a1, a2, z1, z2; };
static inline float BqRun(Biquad& q, float x)
{
    float y = q.b0 * x + q.z1;
    q.z1 = q.b1 * x - q.a1 * y + q.z2;
    q.z2 = q.b2 * x - q.a2 * y;
    return y;
}
static void BqSet(Biquad& q, int type, double fc, double Q)   // 0 = low-pass, 1 = band-pass (0 dB peak), 2 = high-pass
{
    double w = 2.0 * 3.141592653589793 * fc / RATE, c = cos(w), al = sin(w) / (2.0 * Q), a0 = 1.0 + al;
    double b0, b1, b2;
    if (type == 0)      { b0 = (1 - c) / 2; b1 = 1 - c;    b2 = (1 - c) / 2; }
    else if (type == 1) { b0 = al;          b1 = 0;        b2 = -al; }
    else                { b0 = (1 + c) / 2; b1 = -(1 + c); b2 = (1 + c) / 2; }
    q.b0 = (float)(b0 / a0); q.b1 = (float)(b1 / a0); q.b2 = (float)(b2 / a0);
    q.a1 = (float)(-2 * c / a0); q.a2 = (float)((1 - al) / a0);
    q.z1 = q.z2 = 0;
}

static struct VocState {
    // pitch detection
    Biquad dsLp[2];
    float  pdBuf[PD_BUF];
    int    pdW, pdPhase, pdHop;
    float  pdD[PD_MAXLAG + 2];
    float  f0;                                 // detected pitch in Hz (0 = no clear pitch)
    float  level;                              // recent voice level, for the voicing decision
    int    unvoicedHops;
    // tuning
    int    targetNote;                         // MIDI note being tuned to (-1 = none yet)
    float  shift, wantShift;                   // correction in semitones (current, goal)
    float  outNote;                            // the note being sung after correction (MIDI, fractional)
    // synth
    double phase[VOC_OSC][2];
    float  oscFreq[VOC_OSC], oscGain[VOC_OSC];
    float  voiced;                             // 0..1, fades the synth in and out
    // vocoder
    Biquad modBp[VOC_BANDS][2], carBp[VOC_BANDS][2];
    float  modEnv[VOC_BANDS], carEnv[VOC_BANDS];
    Biquad sibHp[2];
    bool   ready;
    // voice range
    bool   low;                                // using the low-voice settings right now
    bool   bandsLow;                           // which band layout the vocoder filters are set to
    float  rangeAvg;                           // Auto: average sung note (MIDI), decides high/low
    float  jumpF; int jumpCount;               // octave-jump guard
    float  conf;                               // last detection's YIN dip (lower = more certain)
} gVoc;

// Vocoder bands: 28 bands from 110 Hz (or 70 Hz for low voices) to 7.6 kHz.
static void VocBands(bool low)
{
    const double lo = low ? 70.0 : 110.0, hi = 7600.0, r = pow(hi / lo, 1.0 / (VOC_BANDS - 1));
    const double Q = 1.0 / (sqrt(r) - 1.0 / sqrt(r));
    for (int b = 0; b < VOC_BANDS; b++) {
        double fc = lo * pow(r, b);
        for (int i = 0; i < 2; i++) { BqSet(gVoc.modBp[b][i], 1, fc, Q); BqSet(gVoc.carBp[b][i], 1, fc, Q); }
    }
    gVoc.bandsLow = low;
}

static void VocReset()                         // audio thread / before start
{
    memset(&gVoc, 0, sizeof(gVoc));
    for (int i = 0; i < 2; i++) BqSet(gVoc.dsLp[i], 0, 2600.0, i ? 1.3066 : 0.5412);   // 4th-order Butterworth
    VocBands(false);
    for (int i = 0; i < 2; i++) BqSet(gVoc.sibHp[i], 2, 5000.0, i ? 1.3066 : 0.5412);
    gVoc.targetNote = -1;
    gVoc.rangeAvg = 55.0f;                      // start in the middle (G3)
    gVoc.ready = true;
}

static inline float MidiToHz(float n) { return 440.0f * powf(2.0f, (n - 69.0f) / 12.0f); }

static bool VocInScale(int note, int key, int scale)
{
    int d = ((note - key) % 12 + 12) % 12;
    return VOC_SCALE_STEPS[scale][d] != 0;
}

static int VocNearest(float note, int key, int scale)   // nearest allowed note
{
    int best = -1; float bd = 99;
    for (int n = (int)floorf(note) - 3; n <= (int)ceilf(note) + 3; n++)
        if (VocInScale(n, key, scale) && fabsf(n - note) < bd) { bd = fabsf(n - note); best = n; }
    return best;
}

// Harmonies use the scale's parent: Chromatic and Major pentatonic -> Major; Minor pentatonic and Blues -> Minor.
static int VocHarmonyScale(int scale) { return scale == 0 || scale == 3 ? 1 : scale == 4 || scale == 5 ? 2 : scale; }

static int VocScaleStep(int note, int steps, int key, int scale)   // move up/down by scale notes
{
    scale = VocHarmonyScale(scale);
    int n = note, dir = steps > 0 ? 1 : -1;
    for (int k = 0; k != steps; k += dir) {
        do n += dir; while (!VocInScale(n, key, scale));
    }
    return n;
}

// YIN pitch detection on the newest `win` samples of the 12 kHz buffer, looking for periods
// between minLag and maxLag samples. Tolerant of real voices (jitter, breath, a weak fundamental):
//  - a clear dip below 0.2 wins, as in standard YIN;
//  - otherwise the first dip almost as deep as the deepest is accepted, if reasonably periodic (< 0.45);
//  - it prefers staying near the previous pitch; a guard in Vocoder() also stops one-off octave jumps.
static float VocDetect(int minLag, int maxLag, int win, float prevF0)
{
    float* d = gVoc.pdD;
    const int base = gVoc.pdW - win - maxLag;
    float energy = 0;
    for (int j = 0; j < win; j++) { float x = gVoc.pdBuf[(base + maxLag + j) & (PD_BUF - 1)]; energy += x * x; }
    gVoc.level = sqrtf(energy / win);
    if (gVoc.level < 0.002f) return 0;         // too quiet to have a pitch (about -54 dBFS)

    d[0] = 1; float run = 0;
    for (int tau = 1; tau <= maxLag; tau++) {
        float sum = 0;
        for (int j = 0; j < win; j++) {
            float a = gVoc.pdBuf[(base + maxLag + j) & (PD_BUF - 1)];
            float b = gVoc.pdBuf[(base + maxLag + j - tau) & (PD_BUF - 1)];
            sum += (a - b) * (a - b);
        }
        run += sum;
        d[tau] = run > 0 ? sum * tau / run : 1;   // cumulative mean normalised difference
    }
    int tau = -1;
    for (int t = minLag; t < maxLag; t++)
        if (d[t] < 0.2f) { while (t + 1 < maxLag && d[t + 1] < d[t]) t++; tau = t; break; }
    if (tau < 0) {                              // no clear dip (breathy voice): find the deepest one...
        int best = minLag;
        for (int t = minLag + 1; t < maxLag; t++) if (d[t] < d[best]) best = t;
        if (d[best] > 0.45f) return 0;          // no pitch: breath, "s", noise
        // ...but take the first dip that's nearly as deep: the deepest is often at twice the period
        for (int t = minLag + 1; t < best; t++)
            if (d[t] < d[best] + 0.06f && d[t] <= d[t - 1] && d[t] <= d[t + 1]) { best = t; break; }
        tau = best;
    }
    // Voices glide, they don't jump: if there's a dip almost as good near the last pitch, stay with it.
    // (Stops breathy voices flipping to a vowel resonance or to twice/three times the period.)
    if (prevF0 > 0) {
        float pp = (float)PD_RATE / prevF0;
        int lo = Imax(minLag, (int)(pp * 0.93f)), hi = Imin(maxLag - 1, (int)(pp * 1.07f) + 1);
        int nearT = -1;
        for (int t = lo; t <= hi; t++) if (nearT < 0 || d[t] < d[nearT]) nearT = t;
        if (nearT > 0 && nearT != tau && d[nearT] < d[tau] + 0.1f && d[nearT] < 0.45f) tau = nearT;
    }
    if (tau < 1 || tau >= maxLag) return 0;
    gVoc.conf = d[tau];
    float a = d[tau - 1], b = d[tau], c = d[tau + 1], den = a - 2 * b + c;
    float t = tau + (fabsf(den) > 1e-9f ? 0.5f * (a - c) / den : 0.0f);   // parabolic refinement
    return (float)PD_RATE / t;
}

// Which notes the synth plays, as offsets in scale steps from the tuned note (99 = unused).
static void VocVoices(int style, bool low, int* steps, float* gains, int* octaves)
{
    for (int i = 0; i < VOC_OSC; i++) { steps[i] = 99; gains[i] = 0; octaves[i] = 0; }
    switch (style) {
    case VOC_HARMONY:                           // third + fifth above, root an octave below
        steps[0] = 2; gains[0] = 0.8f;
        steps[1] = 4; gains[1] = 0.7f;
        steps[2] = 0; gains[2] = 0.6f; octaves[2] = -1;
        break;
    case VOC_ROBOT:                             // the tuned note, doubled an octave below
        steps[0] = 0; gains[0] = 1.0f;
        steps[1] = 0; gains[1] = 0.5f; octaves[1] = -1;
        break;
    case VOC_CHOIR:                             // full chord across two octaves
        steps[0] = 0; gains[0] = 1.0f;
        steps[1] = 2; gains[1] = 0.8f;
        steps[2] = 4; gains[2] = 0.8f;
        steps[3] = 0; gains[3] = 0.6f; octaves[3] = -1;
        steps[4] = 4; gains[4] = 0.4f; octaves[4] = -1;
        steps[5] = 0; gains[5] = 0.35f; octaves[5] = 1;
        break;
    }
    if (low)                                    // deep voices: an octave below gets muddy, so go above instead
        for (int i = 0; i < VOC_OSC; i++) if (octaves[i] < 0) { octaves[i] = 1; gains[i] *= 0.7f; }
}

static inline float PolyBlep(double t, double dt)   // removes the aliasing a plain sawtooth would have
{
    if (t < dt)       { t /= dt;             return (float)(t + t - t * t - 1.0); }
    if (t > 1.0 - dt) { t = (t - 1.0) / dt;  return (float)(t * t + t + t + 1.0); }
    return 0.0f;
}

// ---- Song style: music playing on the PC becomes the vocoder's sound ----
// A loopback capture (one app, or everything except Lag Effect) writes the music here from its own
// thread; the vocoder reads it as its carrier. Kept 20-100 ms fresh so it never lags behind.
#define SONG_RING 16384
static float             songRing[SONG_RING];
static volatile unsigned songW = 0, songR = 0;
static volatile float    gSongPeak = 0;         // loudest music sample lately (UI shows "hearing music")

static void SongCallback(ma_device*, void*, const void* input, ma_uint32 frames)
{
    const float* in = (const float*)input;      // stereo
    unsigned w = songW;
    float pk = 0;
    for (ma_uint32 f = 0; f < frames; f++) {
        float m = in ? (in[f * 2] + in[f * 2 + 1]) * 0.5f : 0.0f;
        songRing[w & (SONG_RING - 1)] = m;
        w++;
        float a = m < 0 ? -m : m; if (a > pk) pk = a;
    }
    MemoryBarrier();
    songW = w;
    if (pk > gSongPeak) gSongPeak = pk;
}

// Song from an audio file: decoded once to 48 kHz mono 16-bit, played on a loop while vocoding.
static short* volatile   gFileData = nullptr;
static volatile unsigned gFileLen = 0;
static volatile bool     gUseFile = false, gFileRestart = false;
static unsigned          gFilePos = 0;

static inline float SongRead()                  // audio thread
{
    if (gUseFile) {
        short* d = gFileData; unsigned n = gFileLen;
        if (!d || !n) return 0;
        if (gFileRestart) { gFilePos = 0; gFileRestart = false; }
        if (gFilePos >= n) gFilePos = 0;
        float x = d[gFilePos] * (1.0f / 32768.0f);
        if (++gFilePos >= n) gFilePos = 0;     // loops
        float a = x < 0 ? -x : x;
        if (a > gSongPeak) gSongPeak = a;
        return x;
    }
    unsigned w = songW;
    MemoryBarrier();
    unsigned r = songR, avail = w - r;
    if (avail > RATE / 10) { r = w - RATE / 50; avail = RATE / 50; }   // fell behind: jump to 20 ms ago
    float x = 0;
    if (avail) { x = songRing[r & (SONG_RING - 1)]; r++; }
    songR = r;
    return x;
}

// Per-block settings, read once per audio callback.
static struct VocParams { int style, key, scale, range; float retuneCoef, synth, mix; } gVp;

static void VocBlock()
{
    gVp.style = Iclamp(gVocStyle, 0, VOC_STYLES - 1);
    gVp.key   = Iclamp(gVocKey, 0, 11);
    gVp.scale = Iclamp(gVocScale, 0, VOC_SCALES - 1);
    float ms  = (float)gVocRetuneMs;
    gVp.retuneCoef = ms <= 0 ? 1.0f : 1.0f - expf(-1.0f / (ms * 0.001f * RATE));
    gVp.synth = gVocSynth / 100.0f;
    gVp.mix   = gVocMix / 100.0f;
    gVp.range = Iclamp(gVocRange, 0, 2);
}

// eps keeps silent carrier bands from blowing up; the synth styles were calibrated at 0.0005, the
// Song style uses a smaller one so quiet music (low browser volume) still comes through at full level.
static float VocodeBands(VocState& v, float mod, float car, float eps = 0.0005f)   // car shaped by mod
{
    float voc = 0;
    for (int b = 0; b < VOC_BANDS; b++) {
        float m = BqRun(v.modBp[b][1], BqRun(v.modBp[b][0], mod));
        float c = BqRun(v.carBp[b][1], BqRun(v.carBp[b][0], car));
        float am = m < 0 ? -m : m, ac = c < 0 ? -c : c;
        v.modEnv[b] += (am - v.modEnv[b]) * (am > v.modEnv[b] ? 0.007f : 0.0014f);   // ~3 ms attack, ~15 ms release
        v.carEnv[b] += (ac - v.carEnv[b]) * 0.0014f;
        voc += c * v.modEnv[b] / (v.carEnv[b] + eps);             // carrier flattened, voice's shape applied
    }
    return voc;
}

static float Vocoder(float x)
{
    VocState& v = gVoc;
    if (!v.ready) VocReset();

    if (gVp.style == VOC_SONG) {                // the music says your words: no tuning needed
        float song = SongRead();
        if (v.bandsLow) VocBands(false);
        float voc = VocodeBands(v, x, song, 0.00005f) * SONG_GAIN;
        voc += BqRun(v.sibHp[1], BqRun(v.sibHp[0], x)) * 0.15f;  // a hint of "s" / "t" for clarity, not your voice
        float a = gVp.synth * 1.5707963f;                         // Synth: how much of your voice the song replaces
        float out = x * cosf(a) + voc * sinf(a);
        return x + (out - x) * gVp.mix;
    }
    SongRead();                                 // keep the music buffer fresh even when not used

    // --- pitch detection (12 kHz) ---
    float lp = BqRun(v.dsLp[1], BqRun(v.dsLp[0], x));
    if (++v.pdPhase >= PD_DS) {
        v.pdPhase = 0;
        v.pdBuf[v.pdW & (PD_BUF - 1)] = lp;
        v.pdW++;
        if (++v.pdHop >= PD_HOP) {
            v.pdHop = 0;
            // High: 80-1000 Hz, 27 ms window. Low: 50-500 Hz, 40 ms window. Auto: listens to both.
            v.low = gVp.range == VR_LOW || (gVp.range == VR_AUTO && v.low);
            if (gVp.range == VR_HIGH) v.low = false;
            int minLag = gVp.range == VR_LOW ? PD_RATE / 500 : PD_RATE / 1000;
            int maxLag = gVp.range == VR_HIGH ? PD_RATE / 80 : PD_MAXLAG;
            int win    = gVp.range == VR_HIGH ? 320 : PD_WIN;
            float f = VocDetect(minLag, maxLag, win, v.f0);
            if (f > 0 && v.f0 > 0) {                // octave-jump guard: needs 3 readings in a row to jump
                float r = f / v.f0;
                bool jump = (r > 1.85f && r < 2.15f) || (r > 0.465f && r < 0.54f);
                if (jump && ++v.jumpCount < 3) f = v.f0;
                else if (!jump) v.jumpCount = 0;
            }
            if (f > 0) {
                v.f0 = f; v.unvoicedHops = 0;
                float note = 69.0f + 12.0f * log2f(f / 440.0f);
                int cand = VocNearest(note, gVp.key, gVp.scale);
                // stay on the current note unless the new one is clearly closer (no flutter between two notes)
                if (v.targetNote < 0 || !VocInScale(v.targetNote, gVp.key, gVp.scale) ||
                    fabsf(note - v.targetNote) > fabsf(note - cand) + 0.25f)
                    v.targetNote = cand;
                v.wantShift = (float)v.targetNote - note;
            } else if (++v.unvoicedHops > 8) {  // ~40 ms of no pitch (rides over short dropouts)
                v.f0 = 0;
                v.wantShift = 0;
            }
            if (f > 0 && v.conf < 0.2f && gVp.range == VR_AUTO) {   // Auto (confident readings only): low below ~D3 (147 Hz), high above ~F3 (175 Hz)
                v.rangeAvg += (69.0f + 12.0f * log2f(v.f0 / 440.0f) - v.rangeAvg) * 0.03f;
                if (v.rangeAvg < 50.0f) v.low = true; else if (v.rangeAvg > 53.0f) v.low = false;
            }
            if (v.low != v.bandsLow) VocBands(v.low);
        }
    }

    // --- tune ---
    v.shift += (v.wantShift - v.shift) * (v.f0 > 0 ? gVp.retuneCoef : 0.002f);
    // 20 ms grains for high voices; 42 ms with a wider search for low ones (a grain needs a few voice cycles)
    float tuned = v.low ? PitchShift(gPsTune, x, pow(2.0, v.shift / 12.0), 2000, 1.0f, true, 960, 384)
                        : PitchShift(gPsTune, x, pow(2.0, v.shift / 12.0), 960, 1.0f, true);
    if (v.f0 > 0) v.outNote = 69.0f + 12.0f * log2f(v.f0 / 440.0f) + v.shift;
    if (gVp.style == VOC_TUNE) return x + (tuned - x) * gVp.mix;

    // --- synth carrier ---
    v.voiced += ((v.f0 > 0 ? 1.0f : 0.0f) - v.voiced) * 0.002f;   // ~10 ms fade
    int steps[VOC_OSC], octs[VOC_OSC]; float gains[VOC_OSC];
    VocVoices(gVp.style, v.low, steps, gains, octs);
    float car = 0;
    if (v.targetNote >= 0) {
        float bend = v.outNote - (float)v.targetNote;              // follow vibrato and slides
        for (int i = 0; i < VOC_OSC; i++) {
            if (steps[i] == 99) continue;
            int n = VocScaleStep(v.targetNote, steps[i], gVp.key, gVp.scale) + 12 * octs[i];
            float fq = MidiToHz((float)n + bend);
            if (fq > 6000.0f) continue;
            v.oscFreq[i] += (fq - v.oscFreq[i]) * (v.oscFreq[i] > 0 ? 0.01f : 1.0f);
            for (int k = 0; k < 2; k++) {                          // two saws, +/- 7 cents
                double dt = v.oscFreq[i] * (k ? 1.00405 : 0.99597) / RATE;
                double& ph = v.phase[i][k];
                ph += dt; if (ph >= 1.0) ph -= 1.0;
                car += ((float)(2.0 * ph - 1.0) - PolyBlep(ph, dt)) * gains[i] * 0.5f;
            }
        }
    }
    static unsigned seed = 12345;                                  // a little noise fills gaps between harmonics
    seed = seed * 1664525u + 1013904223u;
    car = car * v.voiced + ((int)(seed >> 9) % 2000 - 1000) * 0.00002f;

    // --- channel vocoder ---
    float voc = VocodeBands(v, tuned, car);
    voc *= 1.5f;                                // calibrated: pure synth voice about as loud as your voice
    voc += BqRun(v.sibHp[1], BqRun(v.sibHp[0], tuned)) * 0.7f;    // keep "s" and "t" sounds clear

    float out;
    if (gVp.style == VOC_HARMONY) out = tuned + voc * gVp.synth;   // your tuned voice + harmonies
    else {                                                         // blend toward pure synth voice, equal loudness
        float a = gVp.synth * 1.5707963f;
        out = tuned * cosf(a) + voc * sinf(a);
    }
    return x + (out - x) * gVp.mix;
}

// ======================= radio (walkie-talkie, phone, megaphone...) =======================
// Each preset is a row in RADIO_PRESETS: the band the device lets through, a resonance (speaker
// or horn), how hard it distorts, digital crunch (phone codec / 8-bit), background noise, an echo,
// and the sounds it makes when you start/stop talking. Add a row to add a preset.
// The knobs scale the preset: Drive (distortion), Static (noise), Squelch (start/stop sounds).
enum { SQ_NONE = 0, SQ_WALKIE = 1, SQ_QUINDAR = 2, SQ_CLICK = 3 };
enum { CLIP_SOFT = 0, CLIP_HARD = 1, CLIP_RATTLE = 2 };
struct RadioPreset {
    const wchar_t* name;
    float hp, lp;                              // band edges in Hz (4th-order filters)
    float peakHz, peakDb, peakQ;               // speaker / horn resonance
    float driveDb; int clip;                   // distortion (at Drive 50%)
    float comp;                                // compression (0..1): radios and phones squash your voice
    int   srDiv, bits; bool mulaw;             // digital crunch: sample-rate divider, bit depth, phone codec curve
    float hiss, crackle, hum;                  // background noise (at Static 50%)
    float slapMs, slapGain;                    // echo off walls (megaphone)
    int   squelch;                             // start/stop sound
    float outDb;                               // level match: a normal voice (-22 dBFS) comes out as loud as it went in
                                               // (Megaphone +2 dB on purpose). Radios squash: quiet gets louder, loud quieter.
};
#define RADIO_N 8
static const RadioPreset RADIO_PRESETS[RADIO_N] = {
    //  name               hp    lp     peak   dB   Q    drive clip         comp  sr bits mulaw  hiss    crackle hum     slap  gain  squelch      out
    { L"Walkie-talkie",    450,  2800,  1800,  6,   1.0f, 14, CLIP_SOFT,   0.8f, 1, 0,  false, 0.012f, 0.0f,   0.0f,   0,    0,    SQ_WALKIE,   -4.4 },
    { L"Phone call",       320,  3400,  1500,  3,   0.8f, 6,  CLIP_SOFT,   0.5f, 6, 0,  true,  0.002f, 0.0f,   0.0f,   0,    0,    SQ_NONE,     1.8 },
    { L"Megaphone",        600,  4500,  1400,  9,   2.0f, 20, CLIP_HARD,   0.7f, 1, 0,  false, 0.0f,   0.0f,   0.0f,   70,   0.3f, SQ_NONE,     -9.6 },
    { L"Old radio",        250,  3800,  900,   3,   0.7f, 8,  CLIP_SOFT,   0.4f, 1, 0,  false, 0.006f, 0.5f,   0.004f, 0,    0,    SQ_NONE,     -1.8 },
    { L"Space radio",      400,  3000,  2000,  4,   1.0f, 10, CLIP_SOFT,   0.7f, 1, 0,  false, 0.010f, 0.0f,   0.0f,   0,    0,    SQ_QUINDAR,  -0.8 },
    { L"Drive-thru",       700,  2600,  1100,  8,   3.0f, 18, CLIP_RATTLE, 0.8f, 1, 0,  false, 0.006f, 0.0f,   0.0f,   0,    0,    SQ_CLICK,    -5.7 },
    { L"Lo-fi 8-bit",      150,  6000,  0,     0,   1.0f, 3,  CLIP_SOFT,   0.3f, 4, 7,  false, 0.0f,   0.0f,   0.0f,   0,    0,    SQ_NONE,     4.3 },
    { L"Next room",        60,   450,   200,   3,   0.7f, 0,  CLIP_SOFT,   0.2f, 1, 0,  false, 0.0f,   0.0f,   0.0f,   18,   0.25f,SQ_NONE,     2.6 },
};

static const wchar_t* RADIO_DESC[RADIO_N] = {
    L"Crackly two-way radio. \"Kssht\" when you stop talking.",
    L"Like you're on a phone call (8 kHz phone line).",
    L"Loud, distorted horn with an echo off the street.",
    L"1940s valve radio: warm, crackle and hum.",
    L"Mission control, with Apollo \"Quindar\" beeps.",
    L"Tinny, buzzy drive-thru speaker. Clicks on and off.",
    L"Crunchy 8-bit game console voice.",
    L"Muffled, like you're talking from the next room.",
};

static inline float SatSoft(float x)   { return tanhf(x); }
static void BqPeak(Biquad& q, double fc, double db, double Q)   // peaking EQ
{
    double A = pow(10.0, db / 40.0), w = 2.0 * 3.141592653589793 * fc / RATE, c = cos(w), al = sin(w) / (2.0 * Q);
    double a0 = 1 + al / A;
    q.b0 = (float)((1 + al * A) / a0); q.b1 = (float)(-2 * c / a0); q.b2 = (float)((1 - al * A) / a0);
    q.a1 = (float)(-2 * c / a0);        q.a2 = (float)((1 - al / A) / a0);
    q.z1 = q.z2 = 0;
}

#define RADIO_SLAP 8192
static struct RadioState {
    int    preset;                             // preset the filters are set up for (-1 = none)
    Biquad hp[2], lp[2], lpPost[2], peak, noiseBp[2], quindar;
    float  compEnv, keyEnv, keyed, holdLeft;   // talk detection: keyed = 0..1 "transmitting"
    bool   talking;
    int    quietFor;
    float  srHold; int srCount;                // sample-and-hold for the codec / 8-bit
    float  slap[RADIO_SLAP]; int slapW;
    // start/stop sounds
    int    sqLeft, sqLen, sqKind;              // samples left, length, which sound (1 = start, 2 = stop)
    double sqPhase;
    float  sqFlutter, sqFlutterTarget, sqTilt;  // walkie tail: slow level wobble, brighter "hiss" tilt
    Biquad sqThump[2];                          // drive-thru relay click: two short resonances
    float  crackleEnv;
    double humPhase;
    unsigned seed;
} gRadio;

static struct RadioParams { const RadioPreset* p; float drive, statik, squelch; } gRp;

static void RadioReset()
{
    memset(&gRadio, 0, sizeof(gRadio));
    gRadio.preset = -1;
    gRadio.seed = 0x1234567u;
}

static void RadioSetup(int idx)                // filters for a preset (audio thread)
{
    const RadioPreset& p = RADIO_PRESETS[idx];
    for (int i = 0; i < 2; i++) {
        BqSet(gRadio.hp[i], 2, p.hp, i ? 1.3066 : 0.5412);
        BqSet(gRadio.lp[i], 0, p.lp, i ? 1.3066 : 0.5412);
        BqSet(gRadio.lpPost[i], 0, p.lp, i ? 1.3066 : 0.5412);
        BqSet(gRadio.noiseBp[i], 1, 2500.0, 0.8);
    }
    if (p.peakDb != 0) BqPeak(gRadio.peak, p.peakHz, p.peakDb, p.peakQ);
    BqSet(gRadio.quindar, 1, 2500.0, 4.0);
    gRadio.preset = idx;
}

static void RadioBlock()
{
    int idx = Iclamp(gRadioPreset, 0, RADIO_N - 1);
    gRp.p       = &RADIO_PRESETS[idx];
    gRp.drive   = gRadioDrive / 50.0f;         // 50% = the preset as designed
    gRp.statik  = gRadioStatic / 50.0f;
    gRp.squelch = gRadioSquelch / 100.0f;
}

static inline float RadioNoise()                // white noise, -1..1
{
    gRadio.seed = gRadio.seed * 1664525u + 1013904223u;
    return (float)((int)(gRadio.seed >> 8) & 0xFFFF) / 32768.0f - 1.0f;
}

static float Radio(float x)
{
    RadioState& r = gRadio;
    const RadioPreset& p = *gRp.p;
    int idx = (int)(gRp.p - RADIO_PRESETS);
    if (r.preset != idx) RadioSetup(idx);

    // --- are you talking? (decides when the radio is "keyed", and when to play start/stop sounds) ---
    float a = x < 0 ? -x : x;
    r.keyEnv = a > r.keyEnv ? a : r.keyEnv * 0.998f;                // ~10 ms decay
    if (!r.talking && r.keyEnv > 0.008f) {                          // about -42 dBFS: you started
        r.talking = true;
        if (r.quietFor > RATE / 4 && p.squelch != SQ_NONE && gRp.squelch > 0) {   // only after a real pause
            r.sqKind = 1;
            r.sqLen = p.squelch == SQ_QUINDAR ? RATE / 4 : p.squelch == SQ_WALKIE ? RATE * 3 / 100 : RATE * 3 / 100;
            r.sqLeft = r.sqLen; r.sqPhase = 0;
            if (p.squelch == SQ_CLICK) { BqSet(r.sqThump[0], 1, 1300.0, 6.0); BqSet(r.sqThump[1], 1, 320.0, 3.0); }
        }
        r.quietFor = 0;
    }
    if (r.talking) {
        if (r.keyEnv < 0.003f) {                                    // -50 dBFS for ~0.22 s: you let go of the button
            if (++r.quietFor > RATE * 22 / 100) {
                r.talking = false;
                if (p.squelch != SQ_NONE && gRp.squelch > 0) {
                    r.sqKind = 2;
                    // a real squelch tail is 150-250 ms and never quite the same twice
                    r.sqLen = p.squelch == SQ_QUINDAR ? RATE / 4
                            : p.squelch == SQ_WALKIE  ? RATE * (16 + (int)((r.seed >> 10) % 9)) / 100
                            :                           RATE * 3 / 100;
                    r.sqLeft = r.sqLen; r.sqPhase = 0;
                    r.sqFlutter = 1.0f; r.sqFlutterTarget = 1.0f;
                    if (p.squelch == SQ_CLICK) { BqSet(r.sqThump[0], 1, 1100.0, 6.0); BqSet(r.sqThump[1], 1, 280.0, 3.0); }
                }
            }
        } else r.quietFor = 0;
    } else r.quietFor++;
    r.keyed += ((r.talking ? 1.0f : 0.0f) - r.keyed) * 0.0005f;     // noise fades in/out over ~40 ms

    // --- background noise, added before the filters so it sounds like it came through the device ---
    float n = 0;
    if (gRp.statik > 0 && r.keyed > 0.001f) {
        n += RadioNoise() * p.hiss;
        if (p.crackle > 0) {                                        // vinyl-like pops and crackle
            if ((r.seed & 0x3FFF) < (unsigned)(p.crackle * 6)) r.crackleEnv = RadioNoise() * 0.3f;
            n += r.crackleEnv; r.crackleEnv *= 0.9f;
        }
        n *= gRp.statik * r.keyed;
    }
    // --- start/stop sounds made *by the device*: they go through its speaker like your voice does ---
    float sqIn = 0, sqOut = 0;
    if (r.sqLeft > 0) {
        float t = 1.0f - (float)r.sqLeft / r.sqLen;
        int   done = r.sqLen - r.sqLeft, left = r.sqLeft;
        if (p.squelch == SQ_WALKIE) {
            float wn = RadioNoise();
            float hiss = wn - 0.55f * r.sqTilt; r.sqTilt = wn;       // FM receiver noise leans bright
            if (r.sqKind == 2) {                                    // "KSSHHT": full blast, a little wobble, hard cut
                if ((done & 511) == 0) r.sqFlutterTarget = 0.8f + 0.4f * (RadioNoise() * 0.5f + 0.5f);
                r.sqFlutter += (r.sqFlutterTarget - r.sqFlutter) * 0.004f;
                float env = fminf(1.0f, done / (0.002f * RATE))         // 2 ms snap on
                          * fminf(1.0f, left / (0.004f * RATE))         // 4 ms cut off
                          * (done < RATE / 50 ? 1.25f : 1.0f);          // the first instant is a touch louder
                sqIn = hiss * 0.55f * env * r.sqFlutter;
            } else {                                                // keying up: a click, then a 30 ms blip of static
                float click = done < 24 ? (done < 6 ? 0.9f : -0.5f) : 0.0f;
                float env = expf(-t * 5.0f) * fminf(1.0f, left / (0.003f * RATE));
                sqIn = click + hiss * 0.35f * env;
            }
        } else if (p.squelch == SQ_CLICK) {                         // relay / speaker thump
            float kick = done < 3 ? (r.sqKind == 1 ? 1.0f : 0.7f) : 0.0f;
            sqIn = (BqRun(r.sqThump[0], kick) * 2.5f + BqRun(r.sqThump[1], kick) * 2.0f)
                 + RadioNoise() * 0.05f * expf(-t * 12.0f);
        } else if (p.squelch == SQ_QUINDAR) {                       // NASA Apollo "Quindar" beeps: 2525 Hz in, 2475 Hz out
            r.sqPhase += (r.sqKind == 1 ? 2525.0 : 2475.0) / RATE;
            float env = fminf(1.0f, fminf((float)done, (float)left) / (0.004f * RATE));
            sqOut = (float)sin(6.283185307179586 * r.sqPhase) * 0.22f * env;   // a clean tone, added after the speaker
        }
        sqIn *= gRp.squelch; sqOut *= gRp.squelch;
        r.sqLeft--;
    }

    float s = x + n;

    // --- device: compression, band, resonance, distortion ---
    float pw = s * s;
    r.compEnv += (pw - r.compEnv) * (pw > r.compEnv ? 0.01f : 0.0003f);
    if (p.comp > 0) {
        float lvl = 10.0f * log10f(r.compEnv + 1e-12f);
        float gdb = lvl > -32.0f ? (-32.0f - lvl) * p.comp * 0.75f : 0.0f;   // up to 4:1 above -32 dBFS
        s *= powf(10.0f, (gdb + p.comp * 10.0f) / 20.0f);                    // + make-up
    }
    s += sqIn;                                  // squelch joins after the compressor, before the speaker
    s = BqRun(r.hp[0], s);
    if (p.peakDb != 0) s = BqRun(r.peak, s);

    float g = powf(10.0f, p.driveDb * gRp.drive / 20.0f);
    if (p.driveDb > 0 && g > 1.0f) {
        float v = s * g;
        if (p.clip == CLIP_HARD)        v = v > 0.5f ? 0.5f : v < -0.5f ? -0.5f : v;
        else if (p.clip == CLIP_RATTLE) v = SatSoft(v + 0.3f * v * v);  // lopsided: buzzy cheap speaker
        else                            v = SatSoft(v);
        s = v / (p.clip == CLIP_HARD ? 0.5f : 1.0f) * 0.5f;
    }
    s = BqRun(r.hp[1], s);                     // second half of the low cut, after distortion: removes rumble and DC it adds

    s = BqRun(r.lp[1], BqRun(r.lp[0], s));     // top cut, before the crunch (stops harsh aliasing)
    if (p.srDiv > 1 || p.bits > 0 || p.mulaw) {                     // digital crunch
        if (++r.srCount >= (p.srDiv > 1 ? p.srDiv : 1)) {
            r.srCount = 0;
            float v = s;
            if (p.mulaw) {                                          // G.711-style: 8-bit with the telephone curve
                float m = logf(1.0f + 255.0f * fminf(fabsf(v), 1.0f)) / logf(256.0f);
                m = floorf(m * 127.0f + 0.5f) / 127.0f;
                v = (v < 0 ? -1.0f : 1.0f) * (powf(256.0f, m) - 1.0f) / 255.0f;
            }
            if (p.bits > 0) { float q = (float)(1 << (p.bits - 1)); v = floorf(v * q + 0.5f) / q; }
            r.srHold = v;
        }
        s = BqRun(r.lpPost[1], BqRun(r.lpPost[0], r.srHold));   // and again after: smooths the steps
    }

    if (p.hum > 0 && r.keyed > 0.001f) {                            // mains hum (old valve radios)
        r.humPhase += 120.0 / RATE; if (r.humPhase >= 1) r.humPhase -= 1;
        s += (float)(sin(6.283185307179586 * r.humPhase) + 0.5 * sin(12.566370614359172 * r.humPhase)) * p.hum * gRp.statik * r.keyed;
    }
    if (p.slapGain > 0) {                                           // echo off walls
        int d = Iclamp((int)(p.slapMs * RATE / 1000), 1, RADIO_SLAP - 1);
        float e = r.slap[(r.slapW - d) & (RADIO_SLAP - 1)];
        r.slap[r.slapW] = s + e * 0.35f;
        r.slapW = (r.slapW + 1) & (RADIO_SLAP - 1);
        s += e * p.slapGain;
    }

    s += sqOut;
    return s * powf(10.0f, p.outDb / 20.0f);
}

// ======================= more voice effects (Voice FX sub-tabs) =======================
// Formant, Echo, Reverse ("Ghost"), Distortion, Chorus/flanger, Wobble, Muffle and Glitch.
// All run on the audio thread; their knob values are read once per block.
static volatile bool gFxFormantOn = false, gFxEchoOn = false, gFxRvsOn = false, gFxDistOn = false,
                     gFxChorusOn = false, gFxWobbleOn = false, gFxMuffleOn = false, gFxGlitchOn = false;
static volatile int  gFormantShift = 0, gFormantMix = 100;
static volatile int  gEchoStyle = 0, gEchoMs = 350, gEchoFb = 35, gEchoMix = 35;
static volatile int  gRvsLenMs = 400, gRvsMix = 60, gRvsDelayMs = 0;
static volatile int  gDistStyle = 0, gDistDrive = 50, gDistCrush = 0, gDistMix = 100;
static volatile int  gChoStyle = 0, gChoSpeed = 35, gChoDepth = 50, gChoMix = 50;
static volatile int  gWobSpeed = 6, gWobTrem = 50, gWobVib = 0;
static volatile int  gMufStyle = 0, gMufAmount = 70, gMufWarble = 45, gMufBubbles = 40;
static volatile int  gGlAmount = 30, gGlDrop = 50, gGlStutter = 50, gGlRobot = 50;

static unsigned gFxSeed = 0x9E3779B9u;
static inline float FxRand()                    // 0..1
{
    gFxSeed = gFxSeed * 1664525u + 1013904223u;
    return (float)((gFxSeed >> 8) & 0xFFFF) / 65536.0f;
}
static inline float FxOnePole(float hz) { return 1.0f - expf(-6.2831853f * hz / RATE); }

// Reads a delay line at a fractional delay (linear interpolation). size must be a power of two.
static inline float DlRead(const float* buf, int size, int w, double d)
{
    double rp = (double)w - d;
    while (rp < 0) rp += size;
    int i0 = (int)rp; float t = (float)(rp - i0);
    return buf[i0 & (size - 1)] * (1.0f - t) + buf[(i0 + 1) & (size - 1)] * t;
}

// Keeps an effect about as loud as what went into it (distortion changes level a lot).
struct AutoGain { float inE, outE, g; };
static inline float AutoGainRun(AutoGain& a, float in, float out, float maxGain = 4.0f)
{
    const float k = 0.0005f;                    // ~40 ms
    a.inE  += (in * in - a.inE) * k;
    a.outE += (out * out - a.outE) * k;
    if (a.inE < 1e-6f) return out * a.g;        // silence: hold the gain (no loud pop when you start talking)
    float want = a.outE > 1e-9f ? sqrtf((a.inE + 1e-9f) / a.outE) : 1.0f;
    if (want > maxGain) want = maxGain; if (want < 0.1f) want = 0.1f;
    a.g += (want - a.g) * (want < a.g ? 0.002f : 0.0005f);   // turning down is quicker than turning up
    return out * a.g;
}

// ---------------- Formant: changes how big your throat sounds, not your pitch ----------------
// Short-time FFT (1024, 75% overlap). The spectral envelope (cepstrum, smoothed) is stretched up or
// down and each frame is re-weighted by new envelope / old envelope; pitch and phases are untouched.
#define FM_N   1024
#define FM_HOP 256
#define FM_LIFTER 46                            // envelope detail: below any voice's pitch period
static float fmCos[FM_N / 2], fmSin[FM_N / 2], fmWin[FM_N];
static int   fmRev[FM_N];
static bool  fmReady = false;
static struct FormantState {
    float in[FM_N]; int w;                      // last FM_N input samples (ring)
    float acc[FM_N]; int pos;                   // overlap-add output (ring)
    int   hop;
    float re[FM_N], im[FM_N], cr[FM_N], ci[FM_N], env[FM_N / 2 + 1];
} gFm;

static void FftSetup()
{
    if (fmReady) return;
    for (int i = 0; i < FM_N / 2; i++) { fmCos[i] = (float)cos(2 * 3.141592653589793 * i / FM_N); fmSin[i] = (float)sin(2 * 3.141592653589793 * i / FM_N); }
    int bits = 0; while ((1 << bits) < FM_N) bits++;
    for (int i = 0; i < FM_N; i++) { int r = 0; for (int b = 0; b < bits; b++) if (i & (1 << b)) r |= 1 << (bits - 1 - b); fmRev[i] = r; }
    for (int i = 0; i < FM_N; i++) fmWin[i] = (float)sin(3.141592653589793 * (i + 0.5) / FM_N);   // sqrt-Hann
    fmReady = true;
}

static void Fft(float* re, float* im, bool inverse)
{
    for (int i = 0; i < FM_N; i++) if (i < fmRev[i]) { float t = re[i]; re[i] = re[fmRev[i]]; re[fmRev[i]] = t; t = im[i]; im[i] = im[fmRev[i]]; im[fmRev[i]] = t; }
    for (int len = 2; len <= FM_N; len <<= 1) {
        int half = len >> 1, step = FM_N / len;
        for (int i = 0; i < FM_N; i += len)
            for (int j = 0; j < half; j++) {
                float wr = fmCos[j * step], wi = inverse ? fmSin[j * step] : -fmSin[j * step];
                int a = i + j, b = a + half;
                float tr = re[b] * wr - im[b] * wi, ti = re[b] * wi + im[b] * wr;
                re[b] = re[a] - tr; im[b] = im[a] - ti;
                re[a] += tr;        im[a] += ti;
            }
    }
    if (inverse) { const float s = 1.0f / FM_N; for (int i = 0; i < FM_N; i++) { re[i] *= s; im[i] *= s; } }
}

static void FormantFrameOf(FormantState& f, float factor, int mode, float air)
{
    for (int i = 0; i < FM_N; i++) { f.re[i] = f.in[(f.w + i) & (FM_N - 1)] * fmWin[i]; f.im[i] = 0; }
    Fft(f.re, f.im, false);
    for (int k = 0; k <= FM_N / 2; k++) {       // log magnitude, mirrored -> real cepstrum
        float m = logf(sqrtf(f.re[k] * f.re[k] + f.im[k] * f.im[k]) + 1e-7f);
        f.cr[k] = m; if (k > 0 && k < FM_N / 2) f.cr[FM_N - k] = m;
    }
    memset(f.ci, 0, sizeof(f.ci));
    Fft(f.cr, f.ci, true);
    for (int q = FM_LIFTER; q <= FM_N - FM_LIFTER; q++) { f.cr[q] = 0; }
    for (int q = 0; q < FM_N; q++) f.ci[q] = 0;
    f.cr[FM_LIFTER - 1] *= 0.5f; f.cr[FM_N - FM_LIFTER + 1] *= 0.5f;   // soften the cut a little
    Fft(f.cr, f.ci, false);
    for (int k = 0; k <= FM_N / 2; k++) f.env[k] = f.cr[k];             // smooth log envelope
    if (mode == 1) {                            // whisper: the envelope, filled with noise (random phases)
        for (int k = 0; k <= FM_N / 2; k++) {
            float tilt = 1.0f + air * 2.0f * (k > FM_N / 24 ? 1.0f : (float)k / (FM_N / 24));   // brighter above ~2 kHz
            float m = expf(f.env[k]) * tilt, ph = FxRand() * 6.2831853f;
            f.re[k] = m * cosf(ph); f.im[k] = m * sinf(ph);
        }
        f.re[0] = 0; f.im[0] = 0; f.im[FM_N / 2] = 0;
        for (int k = 1; k < FM_N / 2; k++) { f.re[FM_N - k] = f.re[k]; f.im[FM_N - k] = -f.im[k]; }
        Fft(f.re, f.im, true);
        for (int i = 0; i < FM_N; i++) f.acc[(f.pos + i) & (FM_N - 1)] += f.re[i] * fmWin[i] * 0.5f;
        return;
    }
    for (int k = 0; k <= FM_N / 2; k++) {
        float src = k / factor, e2;
        if (src >= FM_N / 2) e2 = f.env[FM_N / 2] - 2.0f;
        else { int i0 = (int)src; float t = src - i0; e2 = f.env[i0] * (1 - t) + f.env[i0 + 1] * t; }
        float g = expf(e2 - f.env[k]);
        if (g > 24.0f) g = 24.0f; if (g < 0.04f) g = 0.04f;
        f.re[k] *= g; f.im[k] *= g;
    }
    for (int k = 1; k < FM_N / 2; k++) { f.re[FM_N - k] = f.re[k]; f.im[FM_N - k] = -f.im[k]; }
    Fft(f.re, f.im, true);
    const float norm = 0.5f;                    // sqrt-Hann in and out (= Hann) at 75% overlap adds up to 2
    for (int i = 0; i < FM_N; i++) f.acc[(f.pos + i) & (FM_N - 1)] += f.re[i] * fmWin[i] * norm;
}

static float Formant(float x, float factor, float mix)   // ~21 ms of delay while on
{
    FormantState& f = gFm;
    float dry = f.in[f.w];                      // the input from FM_N samples ago (lines up with the output)
    f.in[f.w] = x; f.w = (f.w + 1) & (FM_N - 1);
    float y = f.acc[f.pos]; f.acc[f.pos] = 0; f.pos = (f.pos + 1) & (FM_N - 1);
    if (++f.hop >= FM_HOP) { f.hop = 0; FormantFrameOf(f, factor, 0, 0); }
    return dry + (y - dry) * mix;
}

// ---------------- Echo ----------------
#define ECHO_SIZE 131072                        // 2.7 s
struct EchoStyle { const wchar_t* name; int ms, fb, mix; float lpHz, wow; bool sat; };
static const EchoStyle ECHO_STYLES[] = {
    { L"Echo",      350, 35, 35, 7000.0f, 0.0f, false },
    { L"Slapback",   95,  0, 45, 9000.0f, 0.0f, false },
    { L"Tape echo", 300, 45, 35, 2800.0f, 1.0f, true  },
    { L"Canyon",    650, 55, 30, 4500.0f, 0.0f, false },
};
#define ECHO_N ((int)(sizeof(ECHO_STYLES) / sizeof(ECHO_STYLES[0])))
static struct EchoState { float buf[ECHO_SIZE]; int w; double d; float lp; double wowPh; } gEcho;

static float Echo(float x, double targetD, float fb, float mix, float lpA, float wow, bool sat)
{
    EchoState& e = gEcho;
    if (e.d <= 0) e.d = targetD;
    e.d += (targetD - e.d) * 0.0003;            // turning Time glides, like a real delay
    double d = e.d;
    if (wow > 0) { e.wowPh += 2 * 3.141592653589793 * 0.55 / RATE; d += wow * 0.0022 * RATE * sin(e.wowPh) + wow * 0.0006 * RATE * sin(e.wowPh * 3.7); }
    float r = DlRead(e.buf, ECHO_SIZE, e.w, d);
    e.lp += (r - e.lp) * lpA;
    float back = e.lp * fb;
    if (sat) back = tanhf(back * 1.3f) / 1.3f;
    e.buf[e.w] = x + back;
    e.w = (e.w + 1) & (ECHO_SIZE - 1);
    return x + e.lp * mix;
}

// ---------------- Reverse ("Ghost"): backwards reverb swells ----------------
#define RVS_SIZE 131072
static const int MV_COMB[4] = { 1557, 1617, 1491, 1422 }, MV_AP[2] = { 556, 441 };
static struct RvsState {
    float buf[RVS_SIZE]; int w;                 // reverb-washed voice, read backwards
    float dry[RVS_SIZE]; int dw;                // optional voice delay
    double ph[2];                               // read heads: 0..1 through a chunk
    float comb[4][1800], combSt[4], ap[2][640];
    int   ci[4], ai[2];
} gRvs;

static float Reverse(float x, int lenS, float mix, int delayS)
{
    RvsState& r = gRvs;
    // a small dedicated reverb (separate from the Reverb effect) makes the wash that gets reversed
    float in = x * 0.02f, acc = 0;
    for (int i = 0; i < 4; i++) {
        int L = MV_COMB[i] * RATE / 44100;
        float y = r.comb[i][r.ci[i]];
        r.combSt[i] = y * 0.7f + r.combSt[i] * 0.3f;
        r.comb[i][r.ci[i]] = in + r.combSt[i] * 0.88f;
        if (++r.ci[i] >= L) r.ci[i] = 0;
        acc += y;
    }
    for (int i = 0; i < 2; i++) {
        int L = MV_AP[i] * RATE / 44100;
        float b = r.ap[i][r.ai[i]];
        r.ap[i][r.ai[i]] = acc + b * 0.5f;
        acc = b - acc;
        if (++r.ai[i] >= L) r.ai[i] = 0;
    }
    r.buf[r.w] = acc * 2.2f + x * 0.35f;        // mostly wash, a little backwards voice
    // two heads read backwards (delay grows by 2 per sample), half a chunk apart, Hann-crossfaded
    float ghost = 0;
    for (int k = 0; k < 2; k++) {
        double d = 1.0 + r.ph[k] * 2.0 * lenS;
        float s = (float)sin(3.141592653589793 * r.ph[k]);
        ghost += DlRead(r.buf, RVS_SIZE, r.w, d) * s * s;
        r.ph[k] += 1.0 / lenS;
        if (r.ph[k] >= 1.0) r.ph[k] -= 1.0;
    }
    r.w = (r.w + 1) & (RVS_SIZE - 1);
    r.dry[r.dw] = x;
    float v = delayS > 0 ? r.dry[(r.dw - delayS) & (RVS_SIZE - 1)] : x;
    r.dw = (r.dw + 1) & (RVS_SIZE - 1);
    return v + ghost * mix;
}

// ---------------- Distortion / bitcrusher ----------------
struct DistStyle { const wchar_t* name; int drive, crush, mix; };
static const DistStyle DIST_STYLES[] = {
    { L"Overdrive",  50,  0, 100 },
    { L"Fuzz",       70,  0, 100 },
    { L"Bitcrush",   25, 70, 100 },
    { L"Broken mic", 60, 30, 100 },
};
#define DIST_N ((int)(sizeof(DIST_STYLES) / sizeof(DIST_STYLES[0])))
static struct DistState {
    int style;                                  // style the filters are set up for
    Biquad pre, post[2], dc;
    float hold; int holdCount;
    AutoGain ag;
    int dropLeft; float dropEnv;
} gDist;

static float Distort(float x, int style, float drive, float crush, float mix)
{
    DistState& s = gDist;
    if (s.style != style) {
        s.style = style;
        BqSet(s.dc, 2, 30.0, 0.707);
        if (style == 3) { BqSet(s.pre, 2, 450.0, 0.707); BqSet(s.post[0], 0, 3200.0, 0.707); BqSet(s.post[1], 0, 3200.0, 0.707); }
        else {
            BqSet(s.pre, 2, 90.0, 0.707);
            double lp = style == 1 ? 4500.0 : style == 2 ? 12000.0 : 6500.0;
            BqSet(s.post[0], 0, lp, 0.5412); BqSet(s.post[1], 0, lp, 1.3066);
        }
        if (s.ag.g <= 0) s.ag.g = 1;
    }
    const float g = powf(10.0f, drive * 36.0f / 20.0f);    // drive 0..1 -> 0..36 dB
    float v = BqRun(s.pre, x), y;
    switch (style) {
    case 1: {                                   // fuzz: hard, lopsided, with a ghost octave up
        float u = v * g * 2.0f;
        y = u > 0.45f ? 0.45f : u < -0.9f ? -0.9f : u;
        y += 0.35f * fabsf(tanhf(v * g));
        y = BqRun(s.dc, y);
        break;
    }
    case 2: y = tanhf(v * (1.0f + g * 0.25f)); break;      // bitcrush: mostly clean, the crusher does the work
    case 3: {                                   // broken mic: thin, clipped, and it cuts out now and then
        float u = v * g * 1.5f;
        y = u > 0.6f ? 0.6f : u < -0.6f ? -0.6f : u;
        if (s.dropLeft <= 0 && FxRand() < 0.6f / RATE) s.dropLeft = (int)(RATE * (0.02f + 0.06f * FxRand()));
        float want = s.dropLeft > 0 ? 0.0f : 1.0f;
        if (s.dropLeft > 0) s.dropLeft--;
        s.dropEnv += (want - s.dropEnv) * 0.02f;
        y *= s.dropEnv;
        if (FxRand() < 3.0f / RATE) y += (FxRand() - 0.5f) * 0.4f;   // crackle
        break;
    }
    default: y = tanhf(v * g); break;           // overdrive: warm, rounded
    }
    if (crush > 0) {                            // fewer bits + a lower sample rate
        int holdN = 1 + (int)(crush * 10.0f);
        if (++s.holdCount >= holdN) { s.holdCount = 0; s.hold = y; }
        float bits = 16.0f - crush * 13.0f, step = powf(2.0f, 1.0f - bits);
        y = floorf(s.hold / step + 0.5f) * step;
    }
    y = BqRun(s.post[1], BqRun(s.post[0], y));
    y = AutoGainRun(s.ag, x, y);
    return x + (y - x) * mix;
}

// ---------------- Chorus / flanger ----------------
#define CHO_SIZE 8192
struct ChoStyle { const wchar_t* name; int speed, depth, mix; float baseMs, depthMs, fb; int voices; };
static const ChoStyle CHO_STYLES[] = {
    { L"Chorus",      35, 50, 50, 16.0f, 6.0f, 0.0f,  2 },
    { L"Flanger",     30, 70, 50,  1.0f, 3.0f, 0.65f, 1 },
    { L"Jet flanger", 15, 90, 60,  0.6f, 4.0f, 0.85f, 1 },
    { L"Doubler",     20, 30, 45, 28.0f, 3.0f, 0.0f,  1 },
};
#define CHO_N ((int)(sizeof(CHO_STYLES) / sizeof(CHO_STYLES[0])))
static struct ChoState { float buf[CHO_SIZE]; int w; double ph; float last; } gCho;

static float Chorus(float x, const ChoStyle& st, float hz, float depth, float mix)
{
    ChoState& c = gCho;
    c.buf[c.w] = x + c.last * st.fb;
    c.ph += 2 * 3.141592653589793 * hz / RATE;
    if (c.ph > 6.283185307179586) c.ph -= 6.283185307179586;
    float wet = 0;
    for (int v = 0; v < st.voices; v++) {
        double lfo = 0.5 + 0.5 * sin(c.ph + v * 1.5707963);
        double d = (st.baseMs + st.depthMs * depth * lfo) * RATE / 1000.0;
        wet += DlRead(c.buf, CHO_SIZE, c.w, d);
    }
    wet /= st.voices;
    c.last = wet;
    c.w = (c.w + 1) & (CHO_SIZE - 1);
    // the delayed copies don't line up with your voice, so a 50/50 blend sounds quieter: make up for it
    return (x * (1.0f - mix) + wet * mix) / sqrtf((1.0f - mix) * (1.0f - mix) + mix * mix);
}

// ---------------- Wobble: tremolo (volume) + vibrato (pitch) ----------------
#define WOB_SIZE 2048
static struct WobState { float buf[WOB_SIZE]; int w; double ph; } gWob;

static float Wobble(float x, float hz, float trem, float vib)
{
    WobState& s = gWob;
    s.ph += 2 * 3.141592653589793 * hz / RATE;
    if (s.ph > 6.283185307179586) s.ph -= 6.283185307179586;
    float sn = (float)sin(s.ph);
    s.buf[s.w] = x;
    double d = (3.0 + vib * 2.5 * sn) * RATE / 1000.0;     // up to +-2.5 ms around 3 ms
    float y = DlRead(s.buf, WOB_SIZE, s.w, d);
    s.w = (s.w + 1) & (WOB_SIZE - 1);
    return y * (1.0f - trem * (0.5f - 0.5f * sn));
}

// ---------------- Muffle: underwater / through a wall ----------------
struct MufStyle { const wchar_t* name; int amount, warble, bubbles; float q, lowHz, lowDb, level; };
static const MufStyle MUF_STYLES[] = {
    { L"Underwater",      70, 45, 40, 1.6f, 250.0f, 3.0f, 0.85f },
    { L"Through a wall",  85,  0,  0, 0.7f, 150.0f, 6.0f, 0.5f  },
    { L"Under a blanket", 55,  0,  0, 0.6f, 200.0f, 2.0f, 0.8f  },
};
#define MUF_N ((int)(sizeof(MUF_STYLES) / sizeof(MUF_STYLES[0])))
#define MUF_SIZE 2048
#define MUF_BUBBLES 3
static struct MufState {
    int style, amount;                          // what the filters are set up for
    Biquad lp[2], low;
    float buf[MUF_SIZE]; int w; double ph1, ph2;
    AutoGain ag;
    struct { float f, amp, decay; double ph; } bub[MUF_BUBBLES];
} gMuf;

static float Muffle(float x, int style, int amount, float warble, float bubbles)
{
    MufState& m = gMuf;
    const MufStyle& st = MUF_STYLES[style];
    if (m.style != style || m.amount != amount) {
        bool fresh = m.style < 0;
        m.style = style; m.amount = amount;
        double fc = 4000.0 * pow(250.0 / 4000.0, amount / 100.0);
        Biquad a = m.lp[0], b = m.lp[1];
        BqSet(m.lp[0], 0, fc, 0.5412); BqSet(m.lp[1], 0, fc, st.q);
        if (!fresh) { m.lp[0].z1 = a.z1; m.lp[0].z2 = a.z2; m.lp[1].z1 = b.z1; m.lp[1].z2 = b.z2; }   // no click while turning
        BqPeak(m.low, st.lowHz, st.lowDb, 0.8);
    }
    float y = x;
    if (warble > 0) {                           // slow, uneven pitch drift
        m.ph1 += 2 * 3.141592653589793 * 0.7 / RATE; m.ph2 += 2 * 3.141592653589793 * 1.9 / RATE;
        m.buf[m.w] = x;
        double d = (4.0 + warble * 3.0 * (0.6 * sin(m.ph1) + 0.4 * sin(m.ph2))) * RATE / 1000.0;
        y = DlRead(m.buf, MUF_SIZE, m.w, d);
        m.w = (m.w + 1) & (MUF_SIZE - 1);
    }
    // muffled = quieter, but only somewhat: bring it back up to the style's level (cutting highs loses a lot)
    y = AutoGainRun(m.ag, x, BqRun(m.low, BqRun(m.lp[1], BqRun(m.lp[0], y))), 12.0f) * st.level;
    if (bubbles > 0) {                          // little rising blips
        if (FxRand() < bubbles * 6.0f / RATE)
            for (auto& b : m.bub) if (b.amp < 0.001f) {
                b.f = 350.0f + 1300.0f * FxRand(); b.amp = 0.05f * bubbles * (0.4f + 0.6f * FxRand());
                b.decay = expf(-1.0f / (RATE * (0.012f + 0.03f * FxRand()))); b.ph = 0; break;
            }
        for (auto& b : m.bub) if (b.amp >= 0.001f) {
            b.ph += 2 * 3.141592653589793 * b.f / RATE;
            b.f *= 1.00003f;
            y += (float)sin(b.ph) * b.amp;
            b.amp *= b.decay;
        }
    }
    return y;
}

// ---------------- Glitch: a bad connection ----------------
#define GL_SIZE 32768
enum { GL_NONE = 0, GL_DROP, GL_STUTTER, GL_ROBOT };
static struct GlState {
    float buf[GL_SIZE]; int w;
    int mode, left, start, len, pos;
    bool choppy;
    float mix, env;
} gGl;

static float Glitch(float x, float rate, float wDrop, float wStut, float wRobot)
{
    GlState& g = gGl;
    g.buf[g.w] = x;
    if (g.mode == GL_NONE && g.mix < 0.001f) {
        float total = wDrop + wStut + wRobot;
        if (total > 0 && FxRand() < rate / RATE) {
            float pick = FxRand() * total;
            g.mode = pick < wDrop ? GL_DROP : pick < wDrop + wStut ? GL_STUTTER : GL_ROBOT;
            g.pos = 0;
            if (g.mode == GL_DROP)    { g.left = (int)(RATE * (0.04f + 0.2f * FxRand())); g.choppy = FxRand() < 0.5f; }
            if (g.mode == GL_STUTTER) { g.len = (int)(RATE * (0.03f + 0.06f * FxRand())); g.left = g.len * (2 + (int)(FxRand() * 4)); }
            if (g.mode == GL_ROBOT)   { g.len = (int)(RATE * (0.006f + 0.008f * FxRand())); g.left = (int)(RATE * (0.12f + 0.23f * FxRand())); }
            g.start = (g.w - g.len + GL_SIZE) & (GL_SIZE - 1);
        }
    }
    float ev = 0;
    if (g.mode != GL_NONE) {
        if (g.mode == GL_DROP) {
            ev = g.choppy && ((g.pos / (RATE / 50)) & 1) ? x : 0.0f;       // packet loss: 20 ms on, 20 ms off
            g.pos++;
        } else {
            int p = g.pos;
            ev = g.buf[(g.start + p) & (GL_SIZE - 1)];
            int edge = Imin(48, g.len / 4);     // soften each repeat's seam
            if (p < edge) ev *= (float)p / edge; else if (g.len - p < edge) ev *= (float)(g.len - p) / edge;
            if (g.mode == GL_ROBOT) ev = floorf(ev * 64.0f + 0.5f) / 64.0f;   // a little crunchy
            if (++g.pos >= g.len) g.pos = 0;
        }
        if (--g.left <= 0) g.mode = GL_NONE;
    }
    g.mix += ((g.mode != GL_NONE ? 1.0f : 0.0f) - g.mix) * 0.02f;     // ~1 ms fades in and out
    g.w = (g.w + 1) & (GL_SIZE - 1);
    return x + (ev - x) * g.mix;
}

static void FxMoreReset()
{
    FftSetup();
    memset(&gFm, 0, sizeof(gFm));
    memset(&gEcho, 0, sizeof(gEcho));
    memset(&gRvs, 0, sizeof(gRvs)); gRvs.ph[1] = 0.5;
    memset(&gDist, 0, sizeof(gDist)); gDist.style = -1; gDist.ag.g = 1;
    memset(&gCho, 0, sizeof(gCho));
    memset(&gWob, 0, sizeof(gWob));
    memset(&gMuf, 0, sizeof(gMuf)); gMuf.style = -1; gMuf.ag.g = 1;
    memset(&gGl, 0, sizeof(gGl));
}

// ======================= effect pack 2 =======================
// Ring mod, Wah, Whisper, Growl, Harmonizer, Shimmer, Gender (Voice FX) and EQ, De-esser, Broadcast (Mic tab).
static volatile bool gFxRingOn = false, gFxWahOn = false, gFxWhisperOn = false, gFxGrowlOn = false,
                     gFxHarmOn = false, gFxShimOn = false, gFxGenderOn = false, gBroadcast = false,
                     gHarmMute = false;   // Harmonizer: extra voices silenced (your own voice still passes)
static volatile int  gRingHz = 40, gRingMix = 100;
static volatile int  gWahSens = 60, gWahRange = 70, gWahRes = 60, gWahMix = 100;
static volatile int  gWhisperAmt = 100, gWhisperAir = 40;
static volatile int  gGrowlSub = 50, gGrowlRasp = 40, gGrowlGrit = 30;
static volatile int  gHarmStyle = 0, gHarmLevel = 70, gHarmDetune = 8, gHarmDry = 100;
static volatile int  gShimMix = 40, gShimDecay = 70, gShimAmt = 50;
static volatile int  gGenderAmt = 0, gGenderMix = 100;
static volatile int  gEqBass = 0, gEqLowMid = 0, gEqMid = 0, gEqPres = 0, gEqTreble = 0, gDeEss = 0;

// ---- Ring modulator ----
static double gRingPh = 0;
static float RingMod(float x, float hz, float mix)
{
    gRingPh += 2 * 3.141592653589793 * hz / RATE;
    if (gRingPh > 6.283185307179586) gRingPh -= 6.283185307179586;
    float y = x * (float)sin(gRingPh) * 1.4f;   // ring mod halves the level: make some back
    return x + (y - x) * mix;
}

// ---- Auto-wah: a resonant filter that opens as you get louder ----
static struct WahState { float low, band, env; AutoGain ag; } gWah;
static float Wah(float x, float sens, float range, float res, float mix)
{
    WahState& w = gWah;
    float a = fabsf(x);
    w.env += (a - w.env) * (a > w.env ? 0.007f : 0.0004f);   // ~3 ms up, ~50 ms down
    float amt = w.env * sens * 25.0f; if (amt > 1) amt = 1;
    float fc = 350.0f * (1.0f + range * 8.0f * amt);
    float f = 2.0f * sinf(3.1415927f * fc / RATE);
    float q = 1.0f / (1.0f + res * 7.0f);       // resonance 0..100% -> Q 1..8
    float high = x - w.low - q * w.band;
    w.band += f * high;
    w.low  += f * w.band;
    float y = AutoGainRun(w.ag, x, w.band * q * 2.2f, 3.0f);   // a narrow filter loses level: bring it back
    return x + (y - x) * mix;
}

// ---- STFT voices (Formant, Gender, Whisper share the frame code) ----
static void FormantFrameOf(FormantState& f, float factor, int mode, float air);   // mode 0 = formant, 1 = whisper

// ---- Whisper: your formants, but breath instead of a voiced tone ----
static FormantState gFmWhisper;
static AutoGain gWhisperAg;
static float Whisper(float x, float amt, float air)
{
    FormantState& f = gFmWhisper;
    float dry = f.in[f.w];
    f.in[f.w] = x; f.w = (f.w + 1) & (FM_N - 1);
    float y = f.acc[f.pos]; f.acc[f.pos] = 0; f.pos = (f.pos + 1) & (FM_N - 1);
    if (++f.hop >= FM_HOP) { f.hop = 0; FormantFrameOf(f, 1.0f, 1, air); }
    y = AutoGainRun(gWhisperAg, dry, y, 8.0f);
    return dry + (y - dry) * amt;
}

// ---- Growl: a rumble an octave below you, vocal-fry rasp, and grit ----
static struct GrowlState { Biquad lp[2], subLp[2]; float env, prev; bool flip; double fryPh; float fryRate; AutoGain ag; bool ready; } gGrowl;
static float Growl(float x, float sub, float rasp, float grit)
{
    GrowlState& g = gGrowl;
    if (!g.ready) { BqSet(g.lp[0], 0, 600, 0.5412); BqSet(g.lp[1], 0, 600, 1.3066); BqSet(g.subLp[0], 0, 380, 0.5412); BqSet(g.subLp[1], 0, 380, 1.3066); g.fryRate = 55; g.ag.g = 1; g.ready = true; }
    float l = BqRun(g.lp[1], BqRun(g.lp[0], x));
    if (g.prev <= 0 && l > 0.002f) g.flip = !g.flip;          // each rising zero crossing: flip -> half the pitch
    if (l < -0.002f || l > 0.002f) g.prev = l;
    float a = fabsf(x); g.env += (a - g.env) * 0.002f;
    float sq = (g.flip ? 1.0f : -1.0f) * g.env * 2.2f;
    float s = BqRun(g.subLp[1], BqRun(g.subLp[0], sq));
    float y = x + s * sub * 1.6f;
    if (rasp > 0) {                             // vocal fry: irregular little pulses
        g.fryPh += g.fryRate / RATE;
        if (g.fryPh >= 1) { g.fryPh -= 1; g.fryRate = 40.0f + 30.0f * FxRand(); }
        float pulse = g.fryPh < 0.35 ? 1.0f : 0.25f;
        y *= 1.0f - rasp * 0.75f * (1.0f - pulse);
    }
    if (grit > 0) y = y + (AutoGainRun(g.ag, y, tanhf(y * (1.0f + grit * 30.0f)), 4.0f) - y) * grit;
    return y;
}

// ---- Harmonizer: fixed extra voices ----
struct HarmStyle { const wchar_t* name; int a, b; };   // semitones (0 = no voice)
static const HarmStyle HARM_STYLES[] = {
    { L"Octave up", 12, 0 }, { L"Octave down", -12, 0 }, { L"Octaves", 12, -12 }, { L"Major chord", 4, 7 },
    { L"Minor chord", 3, 7 }, { L"Fifth", 7, 0 }, { L"Power chord", 7, -12 }, { L"Angel (up + 5th)", 12, 19 },
};
#define HARM_N ((int)(sizeof(HARM_STYLES) / sizeof(HARM_STYLES[0])))
static PShift gPsHarm[2];
static const wchar_t* HarmMuteText() { return gHarmMute ? L"Voices off (click: on)" : L"Turn the voices off"; }
static float gHarmVoiceG = 1.0f;                // extra voices' level, eased toward 0 / 1 when they're muted / unmuted
static float Harmonize(float x, const HarmStyle& st, float level, float detuneCt, float dry, bool mute)
{
    gHarmVoiceG += ((mute ? 0.0f : 1.0f) - gHarmVoiceG) * 0.002f;   // ~10 ms fade: no click
    const float g = gHarmVoiceG;
    float wet = 0;
    const int span = 2400;                      // 50 ms grains
    int semis[2] = { st.a, st.b };
    for (int k = 0; k < 2; k++) {
        if (!semis[k]) continue;
        double r = pow(2.0, (semis[k] + (k ? -detuneCt : detuneCt) / 100.0) / 12.0);
        wet += PitchShift(gPsHarm[k], x, r, span, 1.0f);
    }
    return x * (dry + (1.0f - dry) * (1.0f - g)) + wet * level * 0.8f * g;   // muted: your voice back at full level
}

// ---- Shimmer: reverb whose tail keeps rising an octave ----
static const int SH_COMB[6] = { 1687, 1601, 2053, 2251, 1931, 1777 }, SH_AP[3] = { 347, 113, 37 };
static struct ShimState { float comb[6][2600], st[6], ap[3][400]; int ci[6], ai[3]; float last; Biquad lp[2], hp; bool ready; } gShim;
static PShift gPsShim;
static float Shimmer(float x, float mix, float decay, float amt)
{
    ShimState& s = gShim;
    const float fb = 0.78f + 0.2f * decay;
    // The tail, an octave up, fed back in. Six combs can add up to 6 / (1 - fb) times what goes in, so the
    // feedback is scaled by (1 - fb) / 6: the loop always loses energy and can never run away.
    if (!s.ready) { BqSet(s.lp[0], 0, 5000, 0.5412); BqSet(s.lp[1], 0, 5000, 1.3066); BqSet(s.hp, 2, 150, 0.707); s.ready = true; }
    float up = PitchShift(gPsShim, s.last, 2.0, 2400, 1.0f);
    // Octave-up of very high sounds folds back down and would circulate forever: keep the loop to 150 Hz - 5 kHz,
    // and soft-limit it so it can never grow.
    up = BqRun(s.hp, BqRun(s.lp[1], BqRun(s.lp[0], up)));
    up = tanhf(up * 4.0f) * 0.25f;
    float in = x * 0.012f + up * amt * 0.5f * (1.0f - fb) / 6.0f, acc = 0;
    for (int i = 0; i < 6; i++) {
        int L = SH_COMB[i] * RATE / 44100;
        float y = s.comb[i][s.ci[i]];
        s.st[i] = y * 0.75f + s.st[i] * 0.25f;
        s.comb[i][s.ci[i]] = in + s.st[i] * fb;
        if (++s.ci[i] >= L) s.ci[i] = 0;
        acc += y;
    }
    for (int i = 0; i < 3; i++) {
        int L = SH_AP[i] * RATE / 44100;
        float b = s.ap[i][s.ai[i]];
        s.ap[i][s.ai[i]] = acc + b * 0.6f;
        acc = b - acc * 0.6f;
        if (++s.ai[i] >= L) s.ai[i] = 0;
    }
    s.last = acc > 4.0f ? 4.0f : acc < -4.0f ? -4.0f : acc;   // belt and braces
    return x + acc * 2.2f * mix;
}

// ---- Gender: pitch and throat size moved together, the right amount ----
static PShift gPsGender;
static FormantState gFmGender;
static float Gender(float x, float g, float mix)     // g: -1 (deeper, masculine) .. +1 (higher, feminine)
{
    if (g == 0) return x;
    double semis = g * 5.0;                     // pitch +-5 semitones
    float y = PitchShift(gPsGender, x, pow(2.0, semis / 12.0), 2400, 1.0f);
    float formantNet = g * 3.0f;                // throat size changes +-3 semitones' worth...
    float factor = powf(2.0f, (float)(formantNet - semis) / 12.0f);   // ...the pitch shift already moved it by `semis`
    FormantState& f = gFmGender;
    float dry = f.in[f.w];
    f.in[f.w] = y; f.w = (f.w + 1) & (FM_N - 1);
    float o = f.acc[f.pos]; f.acc[f.pos] = 0; f.pos = (f.pos + 1) & (FM_N - 1);
    if (++f.hop >= FM_HOP) { f.hop = 0; FormantFrameOf(f, factor, 0, 0); }
    (void)dry;
    return x + (o - x) * mix;                   // (the dry blend is a little early; at 100% it's pure)
}

// ---- Mic tab: 5-band EQ, de-esser, broadcast voice ----
static void BqShelf(Biquad& q, bool high, double fc, double db)   // keeps the filter's state (no clicks)
{
    double A = pow(10.0, db / 40.0), w = 2 * 3.141592653589793 * fc / RATE, c = cos(w), al = sin(w) / 2 * sqrt(2.0), sA = 2 * sqrt(A) * al;
    double b0, b1, b2, a0, a1, a2;
    if (!high) { b0 = A * ((A + 1) - (A - 1) * c + sA); b1 = 2 * A * ((A - 1) - (A + 1) * c); b2 = A * ((A + 1) - (A - 1) * c - sA);
                 a0 = (A + 1) + (A - 1) * c + sA; a1 = -2 * ((A - 1) + (A + 1) * c); a2 = (A + 1) + (A - 1) * c - sA; }
    else       { b0 = A * ((A + 1) + (A - 1) * c + sA); b1 = -2 * A * ((A - 1) + (A + 1) * c); b2 = A * ((A + 1) + (A - 1) * c - sA);
                 a0 = (A + 1) - (A - 1) * c + sA; a1 = 2 * ((A - 1) - (A + 1) * c); a2 = (A + 1) - (A - 1) * c - sA; }
    q.b0 = (float)(b0 / a0); q.b1 = (float)(b1 / a0); q.b2 = (float)(b2 / a0); q.a1 = (float)(a1 / a0); q.a2 = (float)(a2 / a0);
}
static void BqPeakKeep(Biquad& q, double fc, double db, double Q)
{
    float z1 = q.z1, z2 = q.z2; BqPeak(q, fc, db, Q); q.z1 = z1; q.z2 = z2;
}
static struct ToneState {
    int eq[5]; bool eqOn; Biquad band[5];
    Biquad deHp[2], deLp[2]; float deEnvHi, deEnvAll, deGain; bool deReady;
    Biquad bcPres, bcLow; float bcEnv, bcGain; bool bcReady;
} gTone;

static void ToneBlock()                         // per block: refilter only when a knob moved
{
    int v[5] = { gEqBass, gEqLowMid, gEqMid, gEqPres, gEqTreble };
    ToneState& t = gTone;
    static bool first = true;
    if (first) { for (int i = 0; i < 5; i++) t.eq[i] = 999; first = false; }
    bool on = false;
    for (int i = 0; i < 5; i++) {
        if (v[i] != 0) on = true;
        if (v[i] == t.eq[i]) continue;
        t.eq[i] = v[i];
        if (i == 0) BqShelf(t.band[0], false, 100, v[0]);
        else if (i == 4) BqShelf(t.band[4], true, 8000, v[4]);
        else BqPeakKeep(t.band[i], i == 1 ? 400 : i == 2 ? 1200 : 3500, v[i], 0.9);
    }
    t.eqOn = on;
}

static float ToneRun(float x, float deEss, bool broadcast)
{
    ToneState& t = gTone;
    if (t.eqOn) for (int i = 0; i < 5; i++) if (t.eq[i]) x = BqRun(t.band[i], x);
    if (broadcast) {                            // radio-host voice: tight compression, presence, a little less mud
        if (!t.bcReady) { BqPeak(t.bcPres, 4500, 3.0, 0.8); BqShelf(t.bcLow, false, 150, -2.0); t.bcGain = 1; t.bcReady = true; }
        x = BqRun(t.bcPres, BqRun(t.bcLow, x));
        t.bcEnv += (x * x - t.bcEnv) * 0.002f;  // ~10 ms RMS
        float lvl = 10.0f * log10f(t.bcEnv + 1e-12f);
        float gr = lvl > -26.0f ? (-26.0f - lvl) * 0.75f : 0.0f;   // 4:1 above -26 dBFS
        float want = powf(10.0f, (gr + 8.0f) / 20.0f);              // +8 dB makeup
        t.bcGain += (want - t.bcGain) * (want < t.bcGain ? 0.02f : 0.0003f);
        x *= t.bcGain;
        if (deEss < 0.4f) deEss = 0.4f;         // broadcast always tames esses a bit
    }
    if (deEss > 0) {                            // de-esser: turn down the "s" band when it sticks out
        if (!t.deReady) {                       // Linkwitz-Riley split at 5.5 kHz: low + high add back up flat
            for (int i = 0; i < 2; i++) { BqSet(t.deHp[i], 2, 5500, 0.7071); BqSet(t.deLp[i], 0, 5500, 0.7071); }
            t.deGain = 1; t.deReady = true;
        }
        float hi = BqRun(t.deHp[1], BqRun(t.deHp[0], x)), lo = BqRun(t.deLp[1], BqRun(t.deLp[0], x));
        t.deEnvHi  += (hi * hi - t.deEnvHi) * 0.004f;
        t.deEnvAll += (x * x - t.deEnvAll) * 0.004f;
        float ratio = sqrtf(t.deEnvHi / (t.deEnvAll + 1e-9f));      // share of energy above 5 kHz
        float want = 1.0f;
        if (ratio > 0.3f && t.deEnvHi > 1e-6f) want = 0.3f / ratio;
        want = 1.0f - (1.0f - want) * deEss;
        if (want < 0.1f) want = 0.1f;
        t.deGain += (want - t.deGain) * (want < t.deGain ? 0.02f : 0.002f);
        x = lo + hi * t.deGain;
    }
    if (broadcast) {                            // catch the first few ms of a sudden shout
        float ax = fabsf(x);
        if (ax > 0.9f) x = (x > 0 ? 1.0f : -1.0f) * (0.9f + 0.1f * tanhf((ax - 0.9f) / 0.1f));
    }
    return x;
}

static float PadPitch(int i, float x, double ratio)
{
    if (!gPadPs[i]) { gPadPs[i] = (PShift*)calloc(1, sizeof(PShift)); if (!gPadPs[i]) return x; }   // first use only
    return PitchShift(*gPadPs[i], x, ratio, 2400, 1.0f, false, PS_SEARCH, PS_CORR);
}

static void FxPack2Reset()
{
    gRingPh = 0;
    memset(&gWah, 0, sizeof(gWah)); gWah.ag.g = 1;
    memset(&gFmWhisper, 0, sizeof(gFmWhisper)); gWhisperAg = { 0, 0, 1 };
    memset(&gGrowl, 0, sizeof(gGrowl));
    PsReset(gPsHarm[0]); PsReset(gPsHarm[1]);
    memset(&gShim, 0, sizeof(gShim)); PsReset(gPsShim);
    PsReset(gPsGender); memset(&gFmGender, 0, sizeof(gFmGender));
}


// ---- Rewind (your last ~2 s backwards, speeding up like a tape) and Repeat word ("word-word-word") ----
enum { SP_NONE = 0, SP_REWIND, SP_REPEAT, SP_TAPE };
static int    spMode = SP_NONE, spT = 0, spIdx = 0, spRep = 0, spReps = 0, spLen = 0;
static double spPos = 0, spTravel = 0, spTotal = 0;
static size_t spStart = 0;

static PShift gPsRewind;                        // Rewind's pitch
static double spRwRatio = 1.0;                  // (worked out once per rewind, not every sample)
static void SpStartRewind()
{
    spMode = SP_REWIND; spT = 0; spTravel = 0;
    spTotal = Iclamp(gRewindMs, 300, 3500) * (double)RATE / 1000.0;   // how far back it goes
    spRwRatio = pow(2.0, Iclamp(gRewindPitch, -12, 12) / 12.0);
    spPos = (double)((wpos + HIST - 1) % HIST);
}


static void SpStartRepeat()                     // find the last word: the most recent burst of sound
{
    const int FR = RATE / 100, NF = 150;        // 10 ms frames, last 1.5 s
    float rms[NF], peak = 0;
    for (int k = 0; k < NF; k++) {              // frame k ends k frames before now
        double e = 0;
        for (int j = 0; j < FR; j++) { float v = hist[(wpos + HIST - (size_t)(k * FR + j + 1)) % HIST]; e += v * v; }
        rms[k] = sqrtf((float)(e / FR));
        if (rms[k] > peak) peak = rms[k];
    }
    const float thr = peak * 0.12f > 0.004f ? peak * 0.12f : 0.004f;
    int newest = -1;
    for (int k = 0; k < NF && newest < 0; k++) if (rms[k] > thr) newest = k;
    if (newest < 0) return;                     // nothing said lately
    int oldest = newest, quiet = 0;
    for (int k = newest + 1; k < NF && k - newest < 70; k++) {   // back to the gap before it (or 0.7 s)
        if (rms[k] > thr * 0.7f) { oldest = k; quiet = 0; } else if (++quiet >= 6) break;
    }
    int startBack = (oldest + 2) * FR, endBack = newest > 0 ? (newest - 1) * FR : 0;   // 10 ms either side
    spLen = startBack - endBack;
    if (spLen < RATE / 12) return;
    spStart = (wpos + HIST - (size_t)startBack) % HIST;
    spReps = Iclamp(gRepeatN, 1, 6);
    while (spReps > 1 && startBack + spLen * spReps > HIST - RATE / 4) spReps--;   // stay inside the history
    spMode = SP_REPEAT; spIdx = 0; spRep = 0;
}

static void SpStartTape()                       // tape stop: your voice slows down to nothing
{
    spMode = SP_TAPE; spT = 0; spTravel = 0;
    spTotal = RATE * 0.9;                       // 0.9 s from full speed to stopped
    spPos = (double)((wpos + HIST - 1) % HIST);
}

static float SpSample()
{
    float v = 0;
    if (spMode == SP_TAPE) {
        double prog = spT / spTotal, speed = 1.0 - prog;           // slows evenly to a stop
        speed *= speed > 0 ? 1.0 : 0.0;
        size_t i0 = (size_t)spPos; float t = (float)(spPos - (double)i0);
        v = hist[i0 % HIST] * (1.0f - t) + hist[(i0 + 1) % HIST] * t;
        spPos += speed; if (spPos >= HIST) spPos -= HIST;
        float env = prog > 0.8 ? (float)((1.0 - prog) / 0.2) : 1.0f;
        v *= env;
        if (++spT >= (int)spTotal) spMode = SP_NONE;
        return v;
    }
    if (spMode == SP_REWIND) {
        double prog = spTravel / spTotal;
        const double top = Iclamp(gRewindTop, 100, 800) / 100.0, ramp = Iclamp(gRewindRamp, 0, 100) / 100.0;
        double speed = 1.0 + (top - 1.0) * (ramp <= 0.0 || prog >= ramp ? 1.0 : prog / ramp);   // speeds up, like a tape spinning faster
        size_t i0 = (size_t)spPos; float t = (float)(spPos - (double)i0);
        v = hist[i0 % HIST] * (1.0f - t) + hist[(i0 + HIST - 1) % HIST] * t;
        spPos -= speed; if (spPos < 0) spPos += HIST;
        spTravel += speed;
        float env = spT < 240 ? spT / 240.0f : 1.0f;
        double left = spTotal - spTravel;
        if (left < 1440) env *= (float)(left > 0 ? left / 1440.0 : 0.0);
        v *= env * 0.9f;
        if (spRwRatio != 1.0) v = PitchShift(gPsRewind, v, spRwRatio, 1200, 1.0f);
        spT++;
        if (spTravel >= spTotal) spMode = SP_NONE;
    } else if (spMode == SP_REPEAT) {
        v = hist[(spStart + (size_t)spIdx) % HIST];
        int edge = 144;                         // 3 ms fades at each repeat
        if (spIdx < edge) v *= spIdx / (float)edge; else if (spLen - spIdx < edge) v *= (spLen - spIdx) / (float)edge;
        if (++spIdx >= spLen) { spIdx = 0; if (++spRep >= spReps) spMode = SP_NONE; }
    }
    return v;
}

static int randLeft = 0, randWait = 0, randLoopMs = 100;   // random lag state (audio thread)
static float duckGain = 1.0f;
static PShift gPsDive;                          // Pitch dive hotkey
static float  diveBend = 0;

static void FxReset()                          // audio thread only
{
    FxMoreReset();
    FxPack2Reset();
    PsReset(gPsFx); PsReset(gPsTune); VocReset(); RadioReset();
    memset(combBuf, 0, sizeof(combBuf)); memset(combStore, 0, sizeof(combStore));
    memset(apBuf, 0, sizeof(apBuf)); memset(preBuf, 0, sizeof(preBuf)); preW = 0;
    for (int i = 0; i < 8; i++) { combLen[i] = Imin(COMB_TUNE[i] * RATE / 44100, COMB_MAX); combIdx[i] = 0; }
    for (int i = 0; i < 4; i++) { apLen[i] = Imin(AP_TUNE[i] * RATE / 44100, AP_MAX); apIdx[i] = 0; }
}

static void AudioCallback(ma_device*, void* output, const void* input, ma_uint32 frames)
{
    gMainFrames = frames;
#ifdef HAVE_SSE_FLAGS
    _mm_setcsr(_mm_getcsr() | 0x8040);         // flush denormals to zero: reverb tails stay cheap
#endif
    float* out = (float*)output;                // stereo
    const float* in = (const float*)input;      // mono

    bool down = gFeatLag && !gCapturingKey && ComboDown();
    bool active;
    if (gToggleMode) { if (down && !prevDown) toggled = !toggled; active = toggled; }
    else             { toggled = false; active = down; }
    prevDown = down;
    if (gFeatLag && (int)(GetTickCount() - gWsLagUntil) < 0) active = true;   // remote control: {"do":"lag","ms":...}

    // Random lag: now and then the stutter fires by itself (a short random loop for a random time).
    const bool keyActive = active;
    bool randActive = false;
    if (gRandLagOn && gFeatLag) {
        if (randLeft > 0) { randLeft -= (int)frames; randActive = true; }
        else {
            if (randWait <= 0) {                // next one in a random time, Every on average
                float u = FxRand(), mean = (float)Iclamp(gRandLagSec, 2, 120);
                float sec = -logf(1.0f - u * 0.98f) * mean;
                if (sec < 1.0f) sec = 1.0f; if (sec > mean * 4) sec = mean * 4;
                randWait = (int)(sec * RATE);
            }
            randWait -= (int)frames;
            if (randWait <= 0) { randLeft = (int)(RATE * (0.25f + 0.9f * FxRand())); randLoopMs = 50 + (int)(200 * FxRand()); randActive = true; }
        }
    } else { randLeft = 0; randWait = 0; }
    active = keyActive || randActive;

    if (active && !looping) {                  // freeze the most recent audio
        int beatMs = 240000 / Iclamp(gBpm, 40, 300) / (4 << Iclamp(gBeatDiv, 0, 3));   // 1/4 note = 60000 / BPM
        size_t len = (size_t)(keyActive ? (gBeatSync ? Imin(beatMs, 2000) : (int)gLoopMs) : randLoopMs) * RATE / 1000;
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
    if (gRewindReq) { gRewindReq = false; if (!looping) SpStartRewind(); }
    if (gRepeatReq) { gRepeatReq = false; if (!looping) SpStartRepeat(); }
    if (gTapeReq)   { gTapeReq = false;   if (!looping) SpStartTape(); }
    if (looping) spMode = SP_NONE;

    // Mixer channels: how much each has buffered, its gain and where it goes (read once per block).
    float    chG[CH_MAX]; unsigned chRd[CH_MAX], chAv[CH_MAX], chRt[CH_MAX]; int chAdj[CH_MAX], act[CH_MAX], nAct = 0; bool anyCh = false;
    bool     chDk[CH_MAX];
    // Solo: while any channel is soloed, your listening output (the "Always hear sounds on" one, else output 1)
    // plays only the soloed channels; every other output carries on as normal.
    unsigned soloMask = 0;
    for (int c = 0; c < CH_MAX; c++) if (gCh[c].solo && gCh[c].type != CH_NONE) soloMask |= 1u << c;
    const int soloOut = gHearOut >= 1 && gHearOut <= MAX_OUT ? gHearOut - 1 : 0;
    for (int c = 0; c < CH_MAX; c++) {
        ChanAudio& a = gChA[c];
        chG[c] = 0; chRt[c] = 0; chAv[c] = 0; chRd[c] = a.r;
        if (!a.live) { a.primed = false; continue; }
        const unsigned wr = a.w; MemoryBarrier();
        unsigned rd = a.r, av = wr - rd;
        const unsigned target = frames + 1024;  // ~20 ms + a block of cushion against the capture's bursts
        if (av > target + 4096) { rd = wr - target; av = target; }   // fallen behind (clock drift / a hiccup): catch up
        if (!a.primed) { if (av < target) { chRd[c] = rd; continue; } a.primed = true; }
        if (av < frames) a.primed = false;      // about to run dry: wait for a cushion again after this block
        unsigned rt = gCh[c].routes;
        if (soloMask) { rt &= ~(1u << soloOut); if (soloMask & (1u << c)) rt |= 1u << soloOut; }
        if (gCh[c].mute || gCh[c].held || !rt) { chRd[c] = wr; continue; }   // can't be heard: just keep its buffer empty
        chRd[c] = rd; chAv[c] = av;
        // Its clock and ours never match exactly: drop / repeat one sample now and then to keep the cushion steady.
        chAdj[c] = av > target + 480 ? 1 : (av < target - 480 && av > frames + 64) ? -1 : 0;
        chG[c] = DbGain10(gCh[c].db10);
        chDk[c] = gCh[c].duck;
        chRt[c] = rt;
        act[nAct++] = c;                        // (the per-sample loop only visits these)
        anyCh = true;
    }

    int      mode[MAX_OUT];
    const int hearOut = gHearOut;
    const float duckTo = powf(10.0f, -Iclamp(gDuckDb, 0, 40) / 20.0f);
    float    vol[MAX_OUT];
    bool     on[MAX_OUT];
    unsigned w[MAX_OUT], r[MAX_OUT];
    for (int k = 0; k < MAX_OUT; k++) {
        mode[k] = gRowMode[k];
        vol[k]  = gOutMute[k] ? 0.0f : gRowVol[k] / 100.0f;
        on[k]   = k > 0 && ringOn[k];
        w[k]    = ringW[k];
        r[k]    = ringR[k];
    }

    const bool   talk    = gTalkOver;
    const float  talkVol = gTalkVolPct / 100.0f;
    const double speed   = gSpeedPct / 100.0;
    const double pitch   = gPitchPct / 100.0;
    const double len     = (double)frozenLen;
    double fade = (double)gFadeMs * RATE / 1000.0;
    if (fade * 2 > len) fade = len / 2.0;

    if (gFxResetReq) { FxReset(); gFxResetReq = false; }
    const bool fxNow = gFxOn && gFeatFx && !gFxBypass;   // A/B button held: you hear yourself without effects (and off with the feature)
    const bool   fxPitch = fxNow && gFxPitchOn;
    const bool   fxRev   = fxNow && gFxRevOn;
    const bool   fxVoc   = fxNow && gFxVocOn;
    if (fxVoc) VocBlock();
    const bool   fxRadio = fxNow && gFxRadioOn;
    if (fxRadio) RadioBlock();
    // the newer effects (Voice FX sub-tabs)
    const bool   fxForm = fxNow && gFxFormantOn, fxEcho = fxNow && gFxEchoOn, fxRvs = fxNow && gFxRvsOn,
                 fxDist = fxNow && gFxDistOn, fxCho = fxNow && gFxChorusOn, fxWob = fxNow && gFxWobbleOn,
                 fxMuf  = fxNow && gFxMuffleOn, fxGl = fxNow && gFxGlitchOn;
    const float  fmFactor = powf(2.0f, gFormantShift / 12.0f), fmMix = gFormantMix / 100.0f;
    const EchoStyle& ecSt = ECHO_STYLES[Iclamp(gEchoStyle, 0, ECHO_N - 1)];
    const double ecD = (double)gEchoMs * RATE / 1000.0;
    const float  ecFb = gEchoFb / 100.0f, ecMix = gEchoMix / 100.0f, ecLpA = FxOnePole(ecSt.lpHz);
    const int    rvLen = Imax(RATE / 20, gRvsLenMs * RATE / 1000), rvDelay = Iclamp(gRvsDelayMs * RATE / 1000, 0, RVS_SIZE - 1);
    const float  rvGhostMix = gRvsMix / 100.0f;
    const int    dsStyle = Iclamp(gDistStyle, 0, DIST_N - 1);
    const float  dsDrive = gDistDrive / 100.0f, dsCrush = gDistCrush / 100.0f, dsMix = gDistMix / 100.0f;
    const ChoStyle& chSt = CHO_STYLES[Iclamp(gChoStyle, 0, CHO_N - 1)];
    const float  chHz = 0.05f * powf(100.0f, gChoSpeed / 100.0f), chDepth = gChoDepth / 100.0f, chMix = gChoMix / 100.0f;
    const float  wbHz = (float)Iclamp(gWobSpeed, 1, 20), wbTrem = gWobTrem / 100.0f, wbVib = gWobVib / 100.0f;
    const int    mfStyle = Iclamp(gMufStyle, 0, MUF_N - 1), mfAmount = Iclamp(gMufAmount, 0, 100);
    const float  mfWarble = gMufWarble / 100.0f, mfBubbles = gMufBubbles / 100.0f;
    const float  glRate = gGlAmount / 100.0f * 3.0f, glDrop = gGlDrop / 100.0f, glStut = gGlStutter / 100.0f, glRobot = gGlRobot / 100.0f;
    // effect pack 2
    const bool   fxRing = fxNow && gFxRingOn, fxWah = fxNow && gFxWahOn, fxWhisper = fxNow && gFxWhisperOn,
                 fxGrowl = fxNow && gFxGrowlOn, fxHarm = fxNow && gFxHarmOn, fxShim = fxNow && gFxShimOn,
                 fxGender = fxNow && gFxGenderOn;
    const float  rmHz = (float)Iclamp(gRingHz, 10, 1000), rmMix = gRingMix / 100.0f;
    const float  whSens = gWahSens / 100.0f, whRange = gWahRange / 100.0f, whRes = gWahRes / 100.0f, whMix = gWahMix / 100.0f;
    const float  wsAmt = gWhisperAmt / 100.0f, wsAir = gWhisperAir / 100.0f;
    const float  grSub = gGrowlSub / 100.0f, grRasp = gGrowlRasp / 100.0f, grGrit = gGrowlGrit / 100.0f;
    const HarmStyle& hmSt = HARM_STYLES[Iclamp(gHarmStyle, 0, HARM_N - 1)];
    const float  hmLevel = gHarmLevel / 100.0f, hmDetune = (float)gHarmDetune, hmDry = gHarmDry / 100.0f;
    const bool   hmMute = gHarmMute;
    const float  shMix = gShimMix / 100.0f, shDecay = gShimDecay / 100.0f, shAmt = gShimAmt / 100.0f;
    const float  gdAmt = gGenderAmt / 100.0f, gdMix = gGenderMix / 100.0f;
    ToneBlock();
    const float  deEss = gDeEss / 100.0f;
    const bool   broadcast = gBroadcast;
    const double psRatio = pow(2.0, (gFxSemi + gFxCents / 100.0) / 12.0);
    const int    psGrain = Iclamp(gFxGrainMs * RATE / 1000, 64, PS_SIZE - PS_SEARCH - PS_CORR - 8);
    const float  psMix   = gFxPitchMix / 100.0f;
    const float  rvMix = gFxRevMix / 100.0f, rvSize = gFxRevSize / 100.0f, rvDamp = gFxRevDamp / 100.0f;
    const int    rvPre = Iclamp(gFxPreMs * RATE / 1000, 0, PRE_SIZE - 1);

    // Mic cleanup settings for this block
    const float boost    = powf(10.0f, gMicBoostDb / 20.0f);
    if (gLowCutHz != hpFc) LowCutSetup(gLowCutHz);
    const bool  lowCut   = hpFc > 0;
    const int   gateMode = gGateMode;
    const bool  nsOn     = gNsOn;
    const bool  nsStage  = nsOn || gateMode == GATE_VOICE || gateMode == GATE_BOTH;   // voice detection needs RNNoise too
    const float nsMix    = gNsStrength / 100.0f;
    const float thrOpen  = powf(10.0f, gGateThrDb / 20.0f), thrClose = thrOpen * 0.63f;   // 4 dB hysteresis
    const float voiceMin = gGateVoicePct / 100.0f;
    const int   holdN    = gGateHoldMs * RATE / 1000;
    const float relCoef  = 1.0f - expf(-1.0f / (gGateReleaseMs * 0.001f * RATE));
    const float atkCoef  = 1.0f - expf(-1.0f / (0.001f * RATE));                      // opens in ~1 ms
    const float floorLin = powf(10.0f, -gGateRangeDb / 20.0f);
    const float lvAmt    = gLevelerPct / 100.0f;
    const float lvRatio  = 1.0f + 3.0f * lvAmt, lvMakeupDb = 6.0f * lvAmt;
    float blockPeak = 0;
    float outPk[MAX_OUT] = {};

    bool padsIdle = true;                       // nothing playing / starting / stopping: skip the soundboard mixer this block
    for (int i = 0; i < SB_N && padsIdle; i++) { const Pad& p = gPads[i]; if (p.playing || p.trigger || p.stop || p.fade > 0) padsIdle = false; }
    for (ma_uint32 f = 0; f < frames; f++) {
        float sbFx = 0; int padsOn = 0;
        const float sb = padsIdle ? 0.0f : PadsMix(sbFx, padsOn);   // soundboard: every output that isn't Off (sbFx: through the effects)
        duckGain += ((gPadDuck && padsOn ? 0.32f : 1.0f) - duckGain) * 0.002f;   // "lower my voice while a pad plays"
        float s = in ? in[f] * boost : 0.0f;
        muteGain += ((gMicMuted ? 0.0f : 1.0f) - muteGain) * 0.004f;   // ~5 ms fade
        s *= muteGain;
        {                                       // push-to-talk / push-to-mute (5 ms fades, no clicks)
            float want = gPttMode == 1 ? (gPttHeld ? 1.0f : 0.0f) : gPttMode == 2 ? (gPttHeld ? 0.0f : 1.0f) : 1.0f;
            pttGain += (want - pttGain) * 0.004f;
            s *= pttGain;
        }
        if (lowCut) s = LowCut(s);

        if (nsStage) {
            float dry, den = NoiseStage(s, &dry);
            s = nsOn ? dry + (den - dry) * nsMix : dry;
        }
        { float a = s < 0 ? -s : s; if (a > blockPeak) blockPeak = a; }

        if (gateMode != GATE_OFF) {             // noise gate: opens in 1 ms, then hold, then release
            float a = s < 0 ? -s : s;
            gateEnv = a > gateEnv ? a : gateEnv * 0.99792f;          // 10 ms peak follower
            bool loud  = gateEnv > (gateHold > 0 ? thrClose : thrOpen);
            bool voice = nsVad >= voiceMin;
            bool open  = gateMode == GATE_VOLUME ? loud : gateMode == GATE_VOICE ? voice : (loud && voice);
            if (open) gateHold = holdN + 1;
            else if (gateHold > 0) gateHold--;
            float target = gateHold > 0 ? 1.0f : floorLin;
            gateGain += (target - gateGain) * (target > gateGain ? atkCoef : relCoef);
            s *= gateGain;
        } else {
            gateGain = 1.0f; gateHold = 1;
        }
        {                                       // Mixer ducking: are you talking? (gate open, or over -34 dB)
            float a = s < 0 ? -s : s;
            talkEnv = a > talkEnv ? a : talkEnv * 0.9995f;
            const bool talking = (gateMode != GATE_OFF ? gateHold > 0 && gateGain > 0.5f : talkEnv > 0.02f) && muteGain * pttGain > 0.5f;
            if (talking) talkHold = RATE * 3 / 10; else if (talkHold > 0) talkHold--;   // stays down 0.3 s after you stop
            const float want = talkHold > 0 ? duckTo : 1.0f;
            chDuck += (want - chDuck) * (want < chDuck ? 0.0015f : 0.00005f);           // down in ~15 ms, back up over ~0.5 s
        }

        if (lvAmt > 0) {                        // leveler: gentle compressor above -30 dBFS + make-up gain
            float pw = s * s;
            lvEnv += (pw - lvEnv) * (pw > lvEnv ? 0.0042f : 0.0001f);   // ~5 ms attack, ~200 ms release
            float lvl = 10.0f * log10f(lvEnv + 1e-12f);
            float gdb = (lvl > -30.0f ? (-30.0f - lvl) * (1.0f - 1.0f / lvRatio) : 0.0f) + lvMakeupDb;
            s *= powf(10.0f, gdb / 20.0f);
        }

        s = ToneRun(s, deEss, broadcast);      // Mic tab: EQ, broadcast voice, de-esser
        float clean = s;                        // for outputs set to "Clean voice"
        s += sbFx;                              // pads / clips set to play through the voice effects
        if (fxPitch)  s = PitchShift(gPsFx, s, psRatio, psGrain, psMix);
        if (fxGender) s = Gender(s, gdAmt, gdMix);
        if (fxForm)   s = Formant(s, fmFactor, fmMix);
        if (fxHarm)   s = Harmonize(s, hmSt, hmLevel, hmDetune, hmDry, hmMute);
        else          gHarmVoiceG = hmMute ? 0.0f : 1.0f;
        if (fxVoc)    s = Vocoder(s);
        if (fxWhisper) s = Whisper(s, wsAmt, wsAir);
        if (fxGrowl)  s = Growl(s, grSub, grRasp, grGrit);
        if (fxRing)   s = RingMod(s, rmHz, rmMix);
        if (fxDist)   s = Distort(s, dsStyle, dsDrive, dsCrush, dsMix);
        if (fxWah)    s = Wah(s, whSens, whRange, whRes, whMix);
        if (fxCho)    s = Chorus(s, chSt, chHz, chDepth, chMix);
        if (fxWob)    s = Wobble(s, wbHz, wbTrem, wbVib);
        if (fxMuf)    s = Muffle(s, mfStyle, mfAmount, mfWarble, mfBubbles);
        if (fxEcho)   s = Echo(s, ecD, ecFb, ecMix, ecLpA, ecSt.wow, ecSt.sat);
        if (fxRvs)    s = Reverse(s, rvLen, rvGhostMix, rvDelay);
        if (fxShim)   s = Shimmer(s, shMix, shDecay, shAmt);
        if (fxRev)    s = Reverb(s, rvSize, rvDamp, rvMix, rvPre);
        if (fxRadio) s = Radio(s);                  // you're heard *through* the device...
        if (fxGl)    s = Glitch(s, glRate, glDrop, glStut, glRobot);   // ...over a bad connection
        if (!(fabsf(s) < 16.0f)) { s = 0.0f; gFxResetReq = true; }    // an effect ran away (or NaN): silence it, reset all effects
        {                                       // Pitch dive hotkey: bend down (or up) while held, spring back
            float target = gDiveHeld ? (float)gDiveSemis : 0.0f;
            float step = (gDiveHeld ? 12.0f / (0.35f * RATE) : 12.0f / (0.15f * RATE));
            if (diveBend < target) diveBend = diveBend + step > target ? target : diveBend + step;
            else if (diveBend > target) diveBend = diveBend - step < target ? target : diveBend - step;
            if (diveBend != 0.0f || gPsDive.primed) s = PitchShift(gPsDive, s, pow(2.0, diveBend / 12.0), 2400, 1.0f);
        }

        float effect = 0.0f, everything;
        if (looping) {
            float v = 0.0f;
            for (int k = 0; k < 2; k++) {
                double rp = WrapPos(grainStart[k] + grainAge[k] * pitch, len);
                size_t i0 = (size_t)rp;
                float t = (float)(rp - (double)i0);
                size_t im = (i0 + frozenLen - 1) % frozenLen, i1 = (i0 + 1) % frozenLen, i2 = (i0 + 2) % frozenLen;
                float smp = Hermite(frozen[im], frozen[i0], frozen[i1], frozen[i2], t);
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
            if (spMode != SP_NONE) {            // Rewind / Repeat word play instead of your live voice
                float v = SpSample();
                effect = v;
                everything = talk ? v + s * talkVol : v;
            }
        }

        if (duckGain < 0.999f) { everything *= duckGain; effect *= duckGain; clean *= duckGain; }
        if (gRecVoiceOn) RecPut(gRecVoice, everything + sb);   // instant replay: what Discord hears
        if (gPadRec) {                          // recording a pad from the mic (what Discord hears from you)
            float t = everything; t = t > 1 ? 1 : t < -1 ? -1 : t;
            unsigned rp = gPadRecPos;
            gPadRecBuf[rp] = (short)(t * 32767.0f);
            if (++rp >= PADREC_LEN) gPadRec = false;
            gPadRecPos = rp;
        }
        if (gTestRec) {                         // mic test
            float t = everything + sb; t = t > 1 ? 1 : t < -1 ? -1 : t;
            unsigned tp = gTestPos;
            gTestBuf[tp] = (short)(t * 32767.0f);
            if (++tp >= TEST_LEN) { gTestRec = false; gTestLen = TEST_LEN; }
            gTestPos = tp;
        }
        // "Always hear sounds on": that output gets the sounds even when it's Off / Effect only, and the ones
        // going through the voice effects even when its signal doesn't carry your (effected) voice
        auto sounds = [&](int k) {
            const bool always = hearOut == MAX_OUT + 1 || hearOut == k + 1;
            return (mode[k] != MODE_OFF && mode[k] != MODE_APPS) || always ? sb + (always && mode[k] != MODE_ALL ? sbFx : 0.0f) : 0.0f;
        };
        // mixer channels: this frame of each, summed per output (stereo)
        float cL[MAX_OUT] = {}, cR[MAX_OUT] = {};
        if (anyCh)
            for (int ci = 0; ci < nAct; ci++) {
                const int c = act[ci];
                if (!chAv[c]) continue;
                const unsigned i = (chRd[c] & (CH_RING - 1)) * 2;
                const float g = chDk[c] ? chG[c] * chDuck : chG[c];
                const float L = gChA[c].buf[i] * g, R = gChA[c].buf[i + 1] * g;
                if (f == frames / 2 && chAdj[c] < 0) { /* hold this sample one frame longer */ }
                else { chRd[c]++; chAv[c]--; }
                if (f == frames / 2 && chAdj[c] > 0 && chAv[c] > 1) { chRd[c]++; chAv[c]--; }   // skip one
                for (int k = 0; k < MAX_OUT; k++) if (chRt[c] & (1u << k)) { cL[k] += L; cR[k] += R; }
            }
        float m0 = soloMask && soloOut == 0 ? 0.0f : RowSignal(mode[0], effect, everything, clean) + sounds(0);
        float oL = (m0 + cL[0]) * vol[0], oR = (m0 + cR[0]) * vol[0];
        LimitStereo(0, oL, oR);
        { float a = Max(fabsf(oL), fabsf(oR)); if (a > outPk[0]) outPk[0] = a; }
        out[f * 2] = oL;
        out[f * 2 + 1] = oR;

        for (int k = 1; k < MAX_OUT; k++) {
            if (!on[k] || (w[k] - r[k]) >= RING_FRAMES) continue;
            const float mk = soloMask && soloOut == k ? 0.0f : RowSignal(mode[k], effect, everything, clean) + sounds(k);
            float kL = (mk + cL[k]) * vol[k], kR = (mk + cR[k]) * vol[k];
            LimitStereo(k, kL, kR);
            const unsigned i = (w[k] & (RING_FRAMES - 1)) * 2;
            ring[k][i] = kL; ring[k][i + 1] = kR;
            { float a = Max(fabsf(kL), fabsf(kR)); if (a > outPk[k]) outPk[k] = a; }
            w[k]++;
        }
    }
    for (int c = 0; c < CH_MAX; c++) if (gChA[c].live) gChA[c].r = chRd[c];
    MemoryBarrier();
    for (int k = 1; k < MAX_OUT; k++) if (on[k]) ringW[k] = w[k];
    if (blockPeak > gMeterPeak) gMeterPeak = blockPeak;
    for (int k = 0; k < MAX_OUT && k < 8; k++) if (outPk[k] > gOutPeak[k]) gOutPeak[k] = outPk[k];
    gMeterVad = nsStage ? nsVad : -1.0f;
    gMeterGateOpen = gateHold > 0;
}

// Each extra output (a cable, headphones...) runs on its own clock, a tiny bit faster or slower than
// ours. Instead of letting the gap grow and then jumping (a tick), it keeps a steady cushion and
// nudges by one sample at a time: blending two samples into one, or holding one, which can't be heard.
static float    gExtFill[MAX_OUT];              // how full its buffer usually is (smoothed)
static float    gExtAcc[MAX_OUT];               // corrections owed (part samples carry over)
static bool     gExtPrimed[MAX_OUT];
static float    gExtL[MAX_OUT], gExtR[MAX_OUT]; // the last sample it played
static void ExtraOutputCallback(ma_device* dev, void* output, const void*, ma_uint32 frames)
{
    int k = (int)(INT_PTR)dev->pUserData;
    float* out = (float*)output;                // stereo
    unsigned w = ringW[k];
    MemoryBarrier();
    unsigned r = ringR[k];
    unsigned avail = w - r;
    unsigned period = dev->playback.internalPeriodSizeInFrames; if (period < frames) period = frames;
    const unsigned target = period + gMainFrames + 384;   // (enough that neither side's block size empties it)
    float L = gExtL[k], R = gExtR[k];

    if (!gExtPrimed[k]) {                       // starting (or it ran dry): wait for a full cushion,
        if (avail < target) {                   // one short gap instead of many little ones
            for (ma_uint32 f = 0; f < frames; f++) { L *= 0.97f; R *= 0.97f; out[f * 2] = L; out[f * 2 + 1] = R; }
            gExtL[k] = L; gExtR[k] = R;
            return;
        }
        r = w - target; avail = target; gExtFill[k] = (float)target; gExtAcc[k] = 0; gExtPrimed[k] = true;
    }
    if (avail > target + 4096) { r = w - target; avail = target; gExtFill[k] = (float)target; }   // a big hiccup: catch up
    gExtFill[k] += ((float)avail - gExtFill[k]) * 0.05f;
    const float off = gExtFill[k] - (float)target;
    // Too full: use a sample fewer; too empty: one more. Further off = a few per block, spread out.
    // (A little of the gap each block, carried over: steady clock drift is matched exactly.)
    if (fabsf(off) > 48.0f) gExtAcc[k] += off * 0.01f; else gExtAcc[k] *= 0.9f;
    int n = (int)fabsf(gExtAcc[k]); const int nMax = frames >= 96 ? (int)frames / 96 : 1; if (n > nMax) n = nMax;
    const int adj = n == 0 ? 0 : gExtAcc[k] > 0 ? 1 : -1;
    gExtAcc[k] -= (float)(adj * n);
    if (gExtAcc[k] > 4) gExtAcc[k] = 4; else if (gExtAcc[k] < -4) gExtAcc[k] = -4;
    const ma_uint32 step = n ? frames / (ma_uint32)(n + 1) : frames + 1;
    ma_uint32 next = step;

    for (ma_uint32 f = 0; f < frames; f++) {
        const bool fix = adj && f == next; if (fix) next += step;
        if (fix && adj < 0) {
            // hold: play the last sample again without using one
        } else if (avail) {
            unsigned i = (r & (RING_FRAMES - 1)) * 2; L = ring[k][i]; R = ring[k][i + 1]; r++; avail--;
            if (fix && adj > 0 && avail) {      // blend this one with the next: one sample fewer
                i = (r & (RING_FRAMES - 1)) * 2; L = (L + ring[k][i]) * 0.5f; R = (R + ring[k][i + 1]) * 0.5f; r++; avail--;
            }
        } else {                                // ran dry: fade out (no click) and re-prime
            L *= 0.97f; R *= 0.97f; gExtPrimed[k] = false;
        }
        out[f * 2] = L;
        out[f * 2 + 1] = R;
    }
    gExtL[k] = L; gExtR[k] = R;
    ringR[k] = r;
}

// ======================= app state =======================
enum {
    IDC_MIC = 101, IDC_ADDOUT, IDC_VBCABLE,
    IDC_LOOP, IDC_SPEED, IDC_PITCH, IDC_FADE, IDC_GATE, IDC_TALKVOL,
    IDC_GATEON, IDC_TALKON, IDC_HOTKEY, IDC_HOLD, IDC_TOGGLE, IDC_BUFFER, IDC_EXCL,
    IDC_STATUS, IDC_START, IDC_TRAY, IDC_HELPBTN, IDC_AUTO,
    IDC_THEME, IDC_REPO, IDC_CHECKUPD, IDC_UPDSTART, IDC_HDR, IDC_TAB0, IDC_TAB1, IDC_TAB2, IDC_TAB3, IDC_TAB4, IDC_TAB5, IDC_TAB6,   // tabs must stay consecutive
    IDC_FXON, IDC_FXKEY_MASTER, IDC_METER, IDC_GATEMODE, IDC_NSON, IDC_OPENSET, IDC_VOCSTYLE, IDC_VOCKEY, IDC_VOCSCALE, IDC_VOCRANGE, IDC_HIDESHARE, IDC_COLORTHEME, IDC_SONGBTN, IDC_SONGSRC, IDC_SONGSTATUS,
    IDC_MUTEBTN, IDC_MUTEKEY, IDC_OSD, IDC_TOPMOST, IDC_STARTWIN,
    IDC_PADMASTER, IDC_PADSTOP, IDC_PADHINT,
    IDC_CLIPNOW, IDC_CLIPNOWKEY, IDC_RECSECS, IDC_RECSRC, IDC_CLIPMASTER, IDC_CLIPFOLDER, IDC_CLIPSTOP, IDC_RECSTATUS, IDC_RADIOPRESET, IDC_RADIODESC,
    IDC_FXSUB0, IDC_FXSUB1, IDC_FXSUB2, IDC_FXSUB3, IDC_FXSUB4, IDC_FXSUB5, IDC_FXSUB6,   // Voice FX sub-tabs: consecutive
    IDC_MICSUB0, IDC_MICSUB1,                   // Mic tab sub-tabs: consecutive
    IDC_HARMSTYLE, IDC_BROADCAST, IDC_EQRESET,
    IDC_SETSUB0, IDC_SETSUB1, IDC_SETSUB2, IDC_SETSUB3,   // Settings sub-tabs: consecutive
    IDC_FEATLAG, IDC_FEATFX, IDC_FEATSOUND, IDC_FEATCLIPS,
    IDC_WSON, IDC_WSPORT, IDC_WSPASS, IDC_WSSTATUS, IDC_WSHELP, IDC_WSGUIDE,
    IDC_COLRESET, IDC_FONT, IDC_OPACITY, IDC_PICCHOOSE, IDC_PICREMOVE, IDC_PICFIT, IDC_PICDIM, IDC_PICINFO, IDC_CORNERS,
    IDC_PTTMODE, IDC_PTTKEY, IDC_OVERLAY, IDC_BEEPS, IDC_UISCALE, IDC_EXPORT, IDC_IMPORT, IDC_COMPACT, IDC_COMPACTFX,
    IDC_COMPACTFULL, IDC_PROFAUTO, IDC_PROFAUTOINFO, IDC_VERSION,
    IDC_PADCHOKE, IDC_PADDUCK, IDC_PADFOLDER, IDC_CLIPSEP, IDC_CLIPREPLACE, IDC_CLIPHIST,
    IDC_CLIPBANK0, IDC_CLIPBANK1, IDC_CLIPBANK2, IDC_CLIPBANK3,   // clip pages: consecutive
    IDC_LAGPRESET, IDC_BEATSYNC, IDC_BPM, IDC_BEATDIV, IDC_TAPEKEY, IDC_DIVEKEY, IDC_DIVESEMIS, IDC_SURPRISE, IDC_ABTEST,
    IDC_FXCHAR, IDC_ECHOSTYLE, IDC_DISTSTYLE, IDC_CHOSTYLE, IDC_MUFSTYLE, IDC_FXORDER,
    IDC_RANDLAG, IDC_RANDSEC, IDC_REWINDKEY, IDC_REPEATKEY, IDC_RWLEN, IDC_RWTOP, IDC_RWRAMP, IDC_RWPITCH,
    IDC_PADBANK0, IDC_PADBANK1, IDC_PADBANK2, IDC_PADBANK3, IDC_PADBANKKEY, IDC_PADFX,   // bank buttons: consecutive
    IDC_TTSTEXT, IDC_TTSVOICE, IDC_TTSSPEAK, IDC_CLIPFX, IDC_CLIPAUTOTRIM,
    IDC_PROFILE, IDC_PROFSAVE, IDC_PROFDEL, IDC_PROFKEY, IDC_PROFNEXTKEY, IDC_FXHOLD, IDC_MICTEST, IDC_MICPLAY, IDC_MICTESTINFO,
    IDC_HARMMUTE, IDC_HEARLBL, IDC_HEARON, IDC_FONTSIZE, IDC_LAYEDIT, IDC_LAYRESET, IDC_STKLIST, IDC_STKADD, IDC_STKDEL,
    IDC_STKSIZE, IDC_STKOPAC, IDC_STKMOVE, IDC_GIFFPS, IDC_GIFPAUSE, IDC_TTSACCENT, IDC_PICPLACE, IDC_VOICEPROG, IDC_TTSVOL, IDC_TTSMORE,
    IDC_COLSW0 = 1400,                          // + colour slot (USERCOL_N): its own range
    IDC_ROWLBL = 400, IDC_ROWDEV = 410, IDC_ROWMODE = 420, IDC_ROWVOL = 430, IDC_ROWDEL = 440,
    // Mixer page: + channel (CH_MAX), routing buttons + channel * MAX_OUT + output, output strips + output
    IDC_CHSRC0 = 1500, IDC_CHMUTE0 = 1510, IDC_CHVOL0 = 1520, IDC_CHMETER0 = 1530, IDC_CHRT0 = 1540,
    IDC_OMUTE0 = 1590, IDC_OVOL0 = 1600, IDC_OLBL0 = 1610, IDC_OMETER0 = 1620,
    IDC_CHSOLO0 = 1640, IDC_CHDUCK0 = 1650, IDC_CHDB0 = 1660, IDC_CHADD0 = 1670,
    IDC_ODEV0 = 1680, IDC_ODB0 = 1690, IDC_OLIM0 = 1700, IDC_DUCKDB = 1710, IDC_RESTARTAUD = 1711, IDC_CHNAMEED = 1712,
    IDC_CHADDBTN = 1713, IDC_MIXHINT = 1714, IDC_MIXKEYSBTN = 1715, IDC_MIXSTEP = 1716, IDC_MIXKEYHDR = 1717, IDC_MIXSTEPDB = 1718,
    IDC_MIXKEY0 = 1720,                         // .. +63: one button per mixer hotkey (SLOT_MIX0 order)
    IDC_MIXKROW0 = 1790,                        // .. +13: each row's name (channels, then outputs)
    IDC_MIXHOLDMODE0 = 1810,                    // .. +8: a channel's hold key: mutes it / push-to-talk
    IDC_MIXKCOL0 = 1820,                        // .. +7: the column headings
    IDC_PADMORE = 1100, IDC_CLIPMORE = 1110,    // + row: the "..." options button
    IDC_FXGRP_ON = 1000, IDC_FXGRP_RESET = 1020, IDC_FXGRP_KEY = 1040, IDC_FXGRP_HOLD = 1060,   // + group index (room for 20 effects)
    IDC_KNOB = 600,                             // + knob index (needs room for ~40 knobs: keep clear of other ranges)
    IDC_PADPLAY = 700, IDC_PADVOL = 710, IDC_PADKEY = 720, IDC_PADLOAD = 730, IDC_PADCLR = 740,   // + pad index
    IDC_CLIPPLAY = 750, IDC_CLIPVOL = 760, IDC_CLIPKEY = 770, IDC_CLIPTRIM = 780, IDC_CLIPCLR = 790, // + clip index
    ID_TRAY_OPEN = 900, ID_TRAY_RUN, ID_TRAY_EXIT, ID_TRAY_FX, ID_TRAY_SONG, ID_TRAY_NS, ID_TRAY_GATE, ID_TRAY_MUTE
};
#define SPIN_UD(id)        ((id) + 2000)     // up-down control paired with a number box (its own range: +100 used to collide with real controls)
#define WM_TRAY            (WM_APP + 1)
#define WM_DEVICE_LOST     (WM_APP + 2)
#define WM_UPDATE_CHECKED  (WM_APP + 3)
#define WM_UPDATE_DOWNLOAD (WM_APP + 4)
#define WM_SONGFILE_LOADED (WM_APP + 5)
#define WM_SHOW_ME         (WM_APP + 6)          // another copy was started: come to the front
#define WM_TTS_DONE        (WM_APP + 7)          // text-to-speech finished rendering
#define WM_PIC_DECODED     (WM_APP + 8)          // a picture / GIF finished decoding in the background
#define WM_VOICE_INSTALLED (WM_APP + 9)          // Windows finished installing a text-to-speech voice
#define WM_VOICES_LISTED   (WM_APP + 10)         // the voice list (read in the background) is ready
#define WM_NVSA_READY      (WM_APP + 11)         // NaturalVoiceSAPIAdapter downloaded + unpacked (or failed)
#define WM_NVSA_DONE       (WM_APP + 12)         // its installer was closed
#define WM_APPS_SCANNED    (WM_APP + 13)         // the list of apps with sound (for the Mixer) is ready
#define WM_OUTPUT_LOST     (WM_APP + 14)         // an extra output's device stopped (unplugged...): reopen just that one
#define WM_RENAME_DONE     (WM_APP + 15)         // a Mixer channel's name box closed (wParam 1 = keep the text)
#define WM_WS_MSG          (WM_APP + 17)         // remote control: a command arrived (wParam: connection, lParam: the text)
#define WM_WS_CONN         (WM_APP + 18)         // remote control: something connected (lParam 1) / left (0)
#define WM_WS_STATE        (WM_APP + 19)         // remote control: listening (1) / the port is in use (2)
#define TIMER_STATUS    1
#define TIMER_KEY       2
#define TIMER_RECONNECT 3
#define TIMER_CLEANUP   4
#define TIMER_FXKEYS    5
#define TIMER_OSD       6

static HINSTANCE gInst; static HWND gWnd, gStatus; static HFONT gFont, gFontBold; static HICON gIcon;
static ma_context gCtx; static ma_device gDev, gExtraDev[MAX_OUT];
static ma_device gRecDev;                         // loopback capture of PC sound (instant replay)
static bool      gRecRunning = false;
static volatile bool gRecLost = false;
static int       gRecPcState = 0;                 // 0 off, 1 recording, 2 whole output (fallback), 3 failed, 4 waiting for Discord
static ma_device gSongDev;                        // loopback capture of the music (Vocode to song)

// ---- Recording one app's sound, or everything except one app ("process loopback", Windows 10 20348+ / 11) ----
// miniaudio's desktop build can't open this (it asks for a device that doesn't exist and silently fails), so it's
// done directly: ActivateAudioInterfaceAsync on the virtual process-loopback device, then a small capture thread
// that hands stereo float audio to the same callbacks the miniaudio devices use.
static const GUID kIID_IAudioClient        = { 0x1CB9AD4C, 0xDBFA, 0x4C32, { 0xB1, 0x78, 0xC2, 0xF5, 0x68, 0xA7, 0x03, 0xB2 } };
static const GUID kIID_IAudioCaptureClient = { 0xC8ADBD64, 0xE71E, 0x48A0, { 0xA4, 0xDE, 0x18, 0x5C, 0x39, 0x5C, 0xD3, 0x17 } };
static const GUID kIID_ActivateHandler     = { 0x41D949AB, 0x9862, 0x444A, { 0x80, 0xF6, 0xC2, 0x61, 0x33, 0x4D, 0xA5, 0xEB } };
static const GUID kIID_IAgileObject        = { 0x94EA2B94, 0xE9CC, 0x49E0, { 0xC0, 0xFF, 0xEE, 0x64, 0xCA, 0x8F, 0x5B, 0x90 } };
struct PLActivationParams { int type; DWORD pid; int mode; };   // AUDIOCLIENT_ACTIVATION_PARAMS (type 1 = process loopback)
typedef HRESULT (WINAPI* PFN_ActivateAudioInterfaceAsync)(LPCWSTR, REFIID, PROPVARIANT*, IActivateAudioInterfaceCompletionHandler*,
                                                          IActivateAudioInterfaceAsyncOperation**);

struct PLHandler : public IActivateAudioInterfaceCompletionHandler {   // signals when Windows has activated the client
    LONG   ref = 1;
    HANDLE done = CreateEventW(nullptr, TRUE, FALSE, nullptr);
    virtual ~PLHandler() { if (done) CloseHandle(done); }
    HRESULT STDMETHODCALLTYPE QueryInterface(REFIID riid, void** ppv) override {
        if (IsEqualGUID(riid, IID_IUnknown) || IsEqualGUID(riid, kIID_ActivateHandler) || IsEqualGUID(riid, kIID_IAgileObject)) {
            *ppv = this; AddRef(); return S_OK;
        }
        *ppv = nullptr; return E_NOINTERFACE;
    }
    ULONG STDMETHODCALLTYPE AddRef() override  { return (ULONG)InterlockedIncrement(&ref); }
    ULONG STDMETHODCALLTYPE Release() override { LONG r = InterlockedDecrement(&ref); if (!r) delete this; return (ULONG)r; }
    HRESULT STDMETHODCALLTYPE ActivateCompleted(IActivateAudioInterfaceAsyncOperation*) override { SetEvent(done); return S_OK; }
};

struct ProcLoop {
    IAudioClient*        client = nullptr;
    IAudioCaptureClient* cap = nullptr;
    HANDLE               ev = nullptr, thread = nullptr;
    volatile bool        stop = false;
    bool                 pcm16 = false;
    ma_device_data_proc  cb = nullptr;
    volatile bool*       lost = nullptr;
    int                  priority = THREAD_PRIORITY_HIGHEST;
};
static ProcLoop gSongPL, gRecPL;

static DWORD WINAPI ProcLoopThread(LPVOID arg)
{
    ProcLoop* pl = (ProcLoop*)arg;
    CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    SetThreadPriority(GetCurrentThread(), pl->priority);
    static thread_local float buf[2048 * 2];
    LARGE_INTEGER freq, last, now;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&last);
    while (!pl->stop) {
        WaitForSingleObject(pl->ev, 20);
        UINT32 packet = 0;
        bool got = false;
        for (;;) {
            HRESULT hr = pl->cap->GetNextPacketSize(&packet);
            if (FAILED(hr)) { if (pl->lost) *pl->lost = true; pl->stop = true; break; }
            if (!packet) break;
            BYTE* data; UINT32 frames; DWORD flags;
            if (FAILED(pl->cap->GetBuffer(&data, &frames, &flags, nullptr, nullptr))) break;
            for (UINT32 done = 0; done < frames;) {
                UINT32 n = frames - done; if (n > 2048) n = 2048;
                if (flags & AUDCLNT_BUFFERFLAGS_SILENT) memset(buf, 0, n * 2 * sizeof(float));
                else if (pl->pcm16) { const short* s16 = (const short*)data + done * 2; for (UINT32 k = 0; k < n * 2; k++) buf[k] = s16[k] * (1.0f / 32768.0f); }
                else memcpy(buf, (const float*)data + done * 2, n * 2 * sizeof(float));
                pl->cb(nullptr, nullptr, buf, n);
                done += n;
            }
            pl->cap->ReleaseBuffer(frames);
            got = true;
        }
        // Windows sends nothing while the PC is silent: fill that time with silence so clips stay in sync.
        QueryPerformanceCounter(&now);
        if (got) last = now;
        else if (now.QuadPart - last.QuadPart > freq.QuadPart * 3 / 100) {   // 30 ms with no audio
            long long n = (now.QuadPart - last.QuadPart) * RATE / freq.QuadPart;
            last = now;
            memset(buf, 0, sizeof(buf));
            while (n > 0 && !pl->stop) { UINT32 k = n > 2048 ? 2048 : (UINT32)n; pl->cb(nullptr, nullptr, buf, k); n -= k; }
        }
    }
    CoUninitialize();
    return 0;
}

static void ProcLoopStop(ProcLoop* pl)
{
    if (pl->thread) { pl->stop = true; SetEvent(pl->ev); WaitForSingleObject(pl->thread, 3000); CloseHandle(pl->thread); pl->thread = nullptr; }
    if (pl->client) pl->client->Stop();
    if (pl->cap)    { pl->cap->Release(); pl->cap = nullptr; }
    if (pl->client) { pl->client->Release(); pl->client = nullptr; }
    if (pl->ev)     { CloseHandle(pl->ev); pl->ev = nullptr; }
}

static bool ProcLoopTry(ProcLoop* pl, DWORD pid, bool exclude, ma_device_data_proc cb, volatile bool* lost, bool pcm16)
{
    static PFN_ActivateAudioInterfaceAsync activate =
        (PFN_ActivateAudioInterfaceAsync)(void*)GetProcAddress(LoadLibraryW(L"mmdevapi.dll"), "ActivateAudioInterfaceAsync");
    if (!activate || !pid) return false;
    ProcLoopStop(pl);
    PLActivationParams ap = { 1, pid, exclude ? 1 : 0 };   // mode 0 = include the process tree, 1 = exclude it
    PROPVARIANT pv = {};
    pv.vt = VT_BLOB;
    pv.blob.cbSize = sizeof(ap);
    pv.blob.pBlobData = (BYTE*)&ap;
    PLHandler* h = new PLHandler();
    IActivateAudioInterfaceAsyncOperation* op = nullptr;
    HRESULT hr = activate(L"VAD\\Process_Loopback", kIID_IAudioClient, &pv, h, &op);
    bool ok = false;
    if (SUCCEEDED(hr) && WaitForSingleObject(h->done, 3000) == WAIT_OBJECT_0) {
        HRESULT act = E_FAIL; IUnknown* unk = nullptr;
        if (SUCCEEDED(op->GetActivateResult(&act, &unk)) && SUCCEEDED(act) && unk) {
            ok = SUCCEEDED(unk->QueryInterface(kIID_IAudioClient, (void**)&pl->client));
            unk->Release();
        }
    }
    if (op) op->Release();
    h->Release();
    if (!ok) { ProcLoopStop(pl); return false; }

    const DWORD flags = AUDCLNT_STREAMFLAGS_LOOPBACK | AUDCLNT_STREAMFLAGS_EVENTCALLBACK | AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM;
    WAVEFORMATEX wf = pcm16 ? WAVEFORMATEX{ WAVE_FORMAT_PCM, 2, RATE, RATE * 4, 4, 16, 0 }
                            : WAVEFORMATEX{ WAVE_FORMAT_IEEE_FLOAT, 2, RATE, RATE * 8, 8, 32, 0 };
    pl->pcm16 = pcm16;
    hr = pl->client->Initialize(AUDCLNT_SHAREMODE_SHARED, flags, 200000, 0, &wf, nullptr);   // 20 ms buffer
    if (FAILED(hr)) { ProcLoopStop(pl); return false; }
    pl->ev = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    if (FAILED(pl->client->SetEventHandle(pl->ev)) ||
        FAILED(pl->client->GetService(kIID_IAudioCaptureClient, (void**)&pl->cap)) ||
        FAILED(pl->client->Start())) { ProcLoopStop(pl); return false; }
    pl->cb = cb; pl->lost = lost; pl->stop = false;
    pl->thread = CreateThread(nullptr, 0, ProcLoopThread, pl, 0, nullptr);
    if (!pl->thread) { ProcLoopStop(pl); return false; }
    return true;
}

static bool ProcLoopStart(ProcLoop* pl, DWORD pid, bool exclude, ma_device_data_proc cb, volatile bool* lost)
{
    return ProcLoopTry(pl, pid, exclude, cb, lost, false)     // 32-bit float
        || ProcLoopTry(pl, pid, exclude, cb, lost, true);     // some systems only take 16-bit here
}

static void RecPcCallback(ma_device*, void*, const void* input, ma_uint32 frames);
static bool gSongPLOn = false, gRecPLOn = false;
static DWORD gSongPid = 0;                        // the app being recorded (Vocode to song, one app)  // true: running on ProcLoop, false: on a miniaudio device

static void SongDevStop() { if (gSongPLOn) ProcLoopStop(&gSongPL); else ma_device_uninit(&gSongDev); gSongPLOn = false; }
static void RecDevStop()  { if (gRecPLOn)  ProcLoopStop(&gRecPL);  else ma_device_uninit(&gRecDev);  gRecPLOn = false; }
static bool      gSongRunning = false;
static volatile bool gSongLost = false, gSongRetryNow = false;
static bool gCtxOk = false, gRunning = false, gWantRunning = false, gStopping = false;
static bool gExtraRunning[MAX_OUT];
static ma_device_info *gPlayDevs = nullptr, *gCapDevs = nullptr; static ma_uint32 gPlayCount = 0, gCapCount = 0;
static int  gRows = 1, gBufIdx = 2;
static bool gExclusive = false, gAutoStart = false, gInTray = false, gUiReady = false;
static bool gHideShare = false;                 // lock virtual-cable outputs so screen shares can't record them
static bool gShowOsd = true, gTopMost = false;   // pop-up when hotkeys toggle things; window always on top
static int  gWinX = INT_MIN, gWinY = INT_MIN;    // last window position
static wchar_t gMicName[512], gRowName[MAX_OUT][512], gIni[MAX_PATH];
static bool gKeyWasDown[256];
static int  gCapKeys[MAX_KEYS], gCapKeyCount = 0;

struct Range { int id, lo, hi; volatile int* var; const wchar_t* key; };
static Range gRanges[] = {
    { IDC_LOOP,    10, 2000, &gLoopMs,     L"loop_ms"         },
    { IDC_SPEED,   10, 400,  &gSpeedPct,   L"speed"           },
    { IDC_PITCH,   25, 400,  &gPitchPct,   L"pitch"           },
    { IDC_FADE,    0,  50,   &gFadeMs,     L"smoothing_ms"    },
    { IDC_TALKVOL, 0,  200,  &gTalkVolPct, L"talkover_volume" },
    { IDC_RWLEN,   300, 3500, &gRewindMs,  L"rewind_ms"       },
    { IDC_RWTOP,   100, 800, &gRewindTop,  L"rewind_top_speed" },
    { IDC_RWRAMP,  0,   100, &gRewindRamp, L"rewind_speed_up" },
    { IDC_RWPITCH, -12, 12,  &gRewindPitch, L"rewind_pitch"   },
};

static const wchar_t* CHARACTERS[] = { L"Pick a voice...", L"Demon", L"Giant", L"Deeper voice", L"Higher voice", L"Child",
                                       L"Chipmunk", L"Alien", L"Ghost", L"Underwater", L"Bad connection",
                                       L"Robot announcer", L"Old man", L"Stadium announcer", L"Cave troll", L"Space helmet",
                                       L"Dark lord", L"Radio DJ", L"Angel", L"Monster", L"Whisperer" };
#define CHAR_N ((int)(sizeof(CHARACTERS) / sizeof(CHARACTERS[0])))   // built-ins (0 = the prompt)
#define MAX_MYCHARS 16
static wchar_t gMyChars[MAX_MYCHARS][64];       // your saved characters
static int     gMyCharN = 0;

// A/B button: effects bypassed only while the mouse button is held on it.
static LRESULT CALLBACK AbButtonProc(HWND h, UINT m, WPARAM w, LPARAM l, UINT_PTR, DWORD_PTR)
{
    if (m == WM_LBUTTONDOWN || m == WM_LBUTTONDBLCLK) gFxBypass = true;
    else if (m == WM_LBUTTONUP || m == WM_CAPTURECHANGED || m == WM_KILLFOCUS) gFxBypass = false;
    else if (m == WM_KEYDOWN && w == VK_SPACE) gFxBypass = true;
    else if (m == WM_KEYUP && w == VK_SPACE) gFxBypass = false;
    return DefSubclassProc(h, m, w, l);
}

struct LagPreset { const wchar_t* name; int loopMs, speed, pitch, fade, randSec; };   // randSec 0 = leave random lag alone
static const LagPreset LAG_PRESETS[] = {
    { L"Lag preset...", 0, 0, 0, 0, 0 },
    { L"Bad Wi-Fi",     120, 100, 100, 5,  6 },
    { L"Frozen call",    60, 100, 100, 2,  0 },
    { L"Robot glitch",   25, 100, 100, 0,  0 },
    { L"Buffering",     400, 100, 100, 10, 0 },
    { L"Slow-mo",       600,  50,  70, 10, 0 },
    { L"Chipmunk loop", 300, 150, 160, 8,  0 },
    { L"Default",       300, 100, 100, 5,  0 },
};
#define LAG_PRESET_N ((int)(sizeof(LAG_PRESETS) / sizeof(LAG_PRESETS[0])))

// Voice FX page: one group (section) per effect, each with an on/off box and a row of knobs.
// The page has four sub-tabs (sub) of three effects each (slot = row on the sub-tab).
// New effects start off (def = false), so updating never changes how you sound.
struct FxGroup { const wchar_t* title; volatile bool* on; const wchar_t* key; bool def; const wchar_t* hotkeyKey; int sub, slot; };
#define FX_SUBS 7
static int gFxSub = 0;                          // which Voice FX sub-tab is showing
static const wchar_t* FX_SUB_NAMES[FX_SUBS] = { L"Voice", L"Tune", L"Monster", L"Space", L"Motion", L"Filter", L"Fun" };
static int gMicSub = 0;                         // Mic tab: 0 = Cleanup, 1 = Tone
static int gSetSub = 0;                         // Settings tab: 0 = General, 1 = Look, 2 = Pictures, 3 = Features
static FxGroup gFxGroups[] = {
    { L"Pitch",      &gFxPitchOn,   L"fx_pitch_on",    true,  L"fx_pitch_hotkey",   0, 0 },
    { L"Reverb",     &gFxRevOn,     L"fx_reverb_on",   true,  L"fx_reverb_hotkey",  3, 0 },
    { L"Vocoder",    &gFxVocOn,     L"fx_vocoder_on",  true,  L"fx_vocoder_hotkey", 1, 0 },
    { L"Radio",      &gFxRadioOn,   L"fx_radio_on",    true,  L"fx_radio_hotkey",   5, 2 },
    { L"Formant",    &gFxFormantOn, L"fx_formant_on",  false, L"fx_formant_hotkey", 0, 1 },
    { L"Echo",       &gFxEchoOn,    L"fx_echo_on",     false, L"fx_echo_hotkey",    3, 2 },
    { L"Ghost",      &gFxRvsOn,     L"fx_ghost_on",    false, L"fx_ghost_hotkey",   4, 0 },
    { L"Distortion", &gFxDistOn,    L"fx_dist_on",     false, L"fx_dist_hotkey",    2, 2 },
    { L"Chorus",     &gFxChorusOn,  L"fx_chorus_on",   false, L"fx_chorus_hotkey",  4, 1 },
    { L"Wobble",     &gFxWobbleOn,  L"fx_wobble_on",   false, L"fx_wobble_hotkey",  4, 2 },
    { L"Muffle",     &gFxMuffleOn,  L"fx_muffle_on",   false, L"fx_muffle_hotkey",  5, 1 },
    { L"Glitch",     &gFxGlitchOn,  L"fx_glitch_on",   false, L"fx_glitch_hotkey",  6, 0 },
    { L"Ring mod",   &gFxRingOn,    L"fx_ring_on",     false, L"fx_ring_hotkey",    2, 1 },
    { L"Wah",        &gFxWahOn,     L"fx_wah_on",      false, L"fx_wah_hotkey",     5, 0 },
    { L"Whisper",    &gFxWhisperOn, L"fx_whisper_on",  false, L"fx_whisper_hotkey", 1, 2 },
    { L"Growl",      &gFxGrowlOn,   L"fx_growl_on",    false, L"fx_growl_hotkey",   2, 0 },
    { L"Harmonizer", &gFxHarmOn,    L"fx_harm_on",     false, L"fx_harm_hotkey",    1, 1 },
    { L"Shimmer",    &gFxShimOn,    L"fx_shimmer_on",  false, L"fx_shimmer_hotkey", 3, 1 },
    { L"Gender",     &gFxGenderOn,  L"fx_gender_on",   false, L"fx_gender_hotkey",  0, 2 },
};
#define FX_GROUPS ((int)(sizeof(gFxGroups) / sizeof(gFxGroups[0])))
static_assert(FX_GROUPS <= 20, "room for 20 effects in the IDC_FXGRP_* ranges");

// Optional hotkeys that switch Voice FX on/off: slot 0 = the whole page, slot 1+g = effect group g.
// Each is a combination of up to MAX_KEYS keys (0 = unused). Polled by the window (TIMER_FXKEYS).
#define FX_KEY_SLOTS (1 + FX_GROUPS)
#define SLOT_MUTE    FX_KEY_SLOTS                // one more hotkey after the Voice FX ones: Mute mic
#define SLOT_PAD0    (SLOT_MUTE + 1)             // then one per soundboard pad
#define SLOT_CLIPNOW (SLOT_PAD0 + PADS)            // "Clip it"
#define SLOT_CLIP0   (SLOT_CLIPNOW + 1)          // then one per clip
#define SLOT_REWIND  (SLOT_CLIP0 + CLIPS)        // Main tab extras
#define SLOT_REPEAT  (SLOT_REWIND + 1)
#define SLOT_PADBANK (SLOT_REPEAT + 1)           // soundboard: next page
#define SLOT_PROFNEXT (SLOT_PADBANK + 1)         // Settings: next profile
#define PROF_MAX     8                           // profiles (each can have a hotkey)
#define SLOT_TAPESTOP (SLOT_PROFNEXT + 1)        // Voice FX > Fun: hotkey tricks
#define SLOT_DIVE    (SLOT_TAPESTOP + 1)
#define SLOT_PTT     (SLOT_DIVE + 1)             // Mic tab: push-to-talk / push-to-mute key
#define SLOT_PROF0   (SLOT_PTT + 1)
// Mixer: per channel MIXA_N hotkeys, then per output MIXO_N (after everything older, so saved keys keep their place)
enum { MIXA_UP, MIXA_DOWN, MIXA_MUTE, MIXA_SOLO, MIXA_DUCK, MIXA_HOLD, MIXA_N };
enum { MIXO_UP, MIXO_DOWN, MIXO_MUTE, MIXO_N };
#define SLOT_MIX0    (SLOT_PROF0 + PROF_MAX)
#define SLOT_MIXOUT0 (SLOT_MIX0 + CH_MAX * MIXA_N)
#define KEY_SLOTS    (SLOT_MIXOUT0 + MAX_OUT * MIXO_N)
static int  gFxKeys[KEY_SLOTS][MAX_KEYS];
static bool gFxKeyWasDown[KEY_SLOTS];
static bool gFxHold[1 + FX_GROUPS];             // hold-to-activate: [0] = the Voice effects switch, [1+g] = effect g
static int  gProfSel = -1;                      // profile selected on the Settings tab (-1 = none)
static wchar_t gProfNames[PROF_MAX][64];
static int  gProfCount = 0, gProfCur = -1;      // gProfCur: the profile last loaded
static void ProfileKeysSave();

// Knob groups: 0..FX_GROUPS-1 are the Voice FX effects; the rest live on the Mic tab.
enum { KG_PITCH = 0, KG_REVERB, KG_VOCODER, KG_RADIO, KG_FORMANT, KG_ECHO, KG_GHOST, KG_DIST, KG_CHORUS, KG_WOBBLE,
       KG_MUFFLE, KG_GLITCH, KG_RING, KG_WAH, KG_WHISPER, KG_GROWL, KG_HARM, KG_SHIMMER, KG_GENDER,
       KG_NS, KG_GATE, KG_TONE, KG_EQ };
struct Knob { const wchar_t* label; const wchar_t* unit; int lo, hi, def; volatile int* var; const wchar_t* key; int group; bool bipolar;
              const wchar_t* offText; };          // shown (and the knob dimmed) when the value is at its minimum
static Knob gKnobs[] = {
    { L"Pitch",     L" st", -12, 12,  0,   &gFxSemi,     L"fx_pitch_semitones", 0, true, nullptr  },
    { L"Fine",      L" ct", -100, 100, 0,  &gFxCents,    L"fx_pitch_cents",     0, true, nullptr  },
    { L"Grain",     L" ms", 20,  100, 50,  &gFxGrainMs,  L"fx_pitch_grain_ms",  0, false, nullptr },
    { L"Mix",       L"%",   0,   100, 100, &gFxPitchMix, L"fx_pitch_mix",       0, false, nullptr },
    { L"Mix",       L"%",   0,   100, 30,  &gFxRevMix,   L"fx_reverb_mix",      1, false, nullptr },
    { L"Size",      L"%",   0,   100, 60,  &gFxRevSize,  L"fx_reverb_size",     1, false, nullptr },
    { L"Damping",   L"%",   0,   100, 50,  &gFxRevDamp,  L"fx_reverb_damping",  1, false, nullptr },
    { L"Pre-delay", L" ms", 0,   200, 20,  &gFxPreMs,    L"fx_reverb_predelay", 1, false, nullptr },
    { L"Retune",    L" ms", 0,   200, 15,  &gVocRetuneMs,   L"voc_retune_ms",     KG_VOCODER, false, nullptr },
    { L"Synth",     L"%",   0,   100, 60,  &gVocSynth,      L"voc_synth",         KG_VOCODER, false, nullptr },
    { L"Mix",       L"%",   0,   100, 100, &gVocMix,        L"voc_mix",           KG_VOCODER, false, nullptr },
    { L"Drive",     L"%",   0,   100, 50,  &gRadioDrive,    L"radio_drive",       KG_RADIO, false, nullptr },
    { L"Static",    L"%",   0,   100, 50,  &gRadioStatic,   L"radio_static",      KG_RADIO, false, L"Off" },
    { L"Squelch",   L"%",   0,   100, 70,  &gRadioSquelch,  L"radio_squelch",     KG_RADIO, false, L"Off" },
    { L"Formant",   L"",    -12, 12,  0,   &gFormantShift,  L"fx_formant_shift",  KG_FORMANT, true, nullptr },
    { L"Mix",       L"%",   0,   100, 100, &gFormantMix,    L"fx_formant_mix",    KG_FORMANT, false, nullptr },
    { L"Time",      L" ms", 20,  1500, 350, &gEchoMs,       L"fx_echo_ms",        KG_ECHO, false, nullptr },
    { L"Feedback",  L"%",   0,   90,  35,  &gEchoFb,        L"fx_echo_feedback",  KG_ECHO, false, L"Off" },
    { L"Mix",       L"%",   0,   100, 35,  &gEchoMix,       L"fx_echo_mix",       KG_ECHO, false, nullptr },
    { L"Length",    L" ms", 100, 1000, 400, &gRvsLenMs,     L"fx_ghost_length",   KG_GHOST, false, nullptr },
    { L"Mix",       L"%",   0,   100, 60,  &gRvsMix,        L"fx_ghost_mix",      KG_GHOST, false, nullptr },
    { L"Voice delay", L" ms", 0, 600, 0,   &gRvsDelayMs,    L"fx_ghost_delay",    KG_GHOST, false, L"Off" },
    { L"Drive",     L"%",   0,   100, 50,  &gDistDrive,     L"fx_dist_drive",     KG_DIST, false, nullptr },
    { L"Crush",     L"%",   0,   100, 0,   &gDistCrush,     L"fx_dist_crush",     KG_DIST, false, L"Off" },
    { L"Mix",       L"%",   0,   100, 100, &gDistMix,       L"fx_dist_mix",       KG_DIST, false, nullptr },
    { L"Speed",     L"%",   0,   100, 35,  &gChoSpeed,      L"fx_chorus_speed",   KG_CHORUS, false, nullptr },
    { L"Depth",     L"%",   0,   100, 50,  &gChoDepth,      L"fx_chorus_depth",   KG_CHORUS, false, nullptr },
    { L"Mix",       L"%",   0,   100, 50,  &gChoMix,        L"fx_chorus_mix",     KG_CHORUS, false, nullptr },
    { L"Speed",     L" Hz", 1,   20,  6,   &gWobSpeed,      L"fx_wobble_speed",   KG_WOBBLE, false, nullptr },
    { L"Tremolo",   L"%",   0,   100, 50,  &gWobTrem,       L"fx_wobble_tremolo", KG_WOBBLE, false, L"Off" },
    { L"Vibrato",   L"%",   0,   100, 0,   &gWobVib,        L"fx_wobble_vibrato", KG_WOBBLE, false, L"Off" },
    { L"Muffle",    L"%",   0,   100, 70,  &gMufAmount,     L"fx_muffle_amount",  KG_MUFFLE, false, nullptr },
    { L"Warble",    L"%",   0,   100, 45,  &gMufWarble,     L"fx_muffle_warble",  KG_MUFFLE, false, L"Off" },
    { L"Bubbles",   L"%",   0,   100, 40,  &gMufBubbles,    L"fx_muffle_bubbles", KG_MUFFLE, false, L"Off" },
    { L"Amount",    L"%",   0,   100, 30,  &gGlAmount,      L"fx_glitch_amount",  KG_GLITCH, false, L"Off" },
    { L"Dropouts",  L"%",   0,   100, 50,  &gGlDrop,        L"fx_glitch_drop",    KG_GLITCH, false, L"Off" },
    { L"Stutter",   L"%",   0,   100, 50,  &gGlStutter,     L"fx_glitch_stutter", KG_GLITCH, false, L"Off" },
    { L"Robot",     L"%",   0,   100, 50,  &gGlRobot,       L"fx_glitch_robot",   KG_GLITCH, false, L"Off" },
    { L"Freq",      L" Hz", 10,  1000, 40, &gRingHz,        L"fx_ring_hz",        KG_RING, false, nullptr },
    { L"Mix",       L"%",   0,   100, 100, &gRingMix,       L"fx_ring_mix",       KG_RING, false, nullptr },
    { L"Sensitivity", L"%", 0,   100, 60,  &gWahSens,       L"fx_wah_sens",       KG_WAH, false, nullptr },
    { L"Range",     L"%",   0,   100, 70,  &gWahRange,      L"fx_wah_range",      KG_WAH, false, nullptr },
    { L"Resonance", L"%",   0,   100, 60,  &gWahRes,        L"fx_wah_res",        KG_WAH, false, nullptr },
    { L"Mix",       L"%",   0,   100, 100, &gWahMix,        L"fx_wah_mix",        KG_WAH, false, nullptr },
    { L"Whisper",   L"%",   0,   100, 100, &gWhisperAmt,    L"fx_whisper_amount", KG_WHISPER, false, nullptr },
    { L"Air",       L"%",   0,   100, 40,  &gWhisperAir,    L"fx_whisper_air",    KG_WHISPER, false, L"Off" },
    { L"Sub",       L"%",   0,   100, 50,  &gGrowlSub,      L"fx_growl_sub",      KG_GROWL, false, L"Off" },
    { L"Rasp",      L"%",   0,   100, 40,  &gGrowlRasp,     L"fx_growl_rasp",     KG_GROWL, false, L"Off" },
    { L"Grit",      L"%",   0,   100, 30,  &gGrowlGrit,     L"fx_growl_grit",     KG_GROWL, false, L"Off" },
    { L"Harmony",   L"%",   0,   100, 70,  &gHarmLevel,     L"fx_harm_level",     KG_HARM, false, nullptr },
    { L"Detune",    L" ct", 0,   30,  8,   &gHarmDetune,    L"fx_harm_detune",    KG_HARM, false, L"Off" },
    { L"Your voice", L"%",  0,   100, 100, &gHarmDry,       L"fx_harm_dry",       KG_HARM, false, nullptr },
    { L"Mix",       L"%",   0,   100, 40,  &gShimMix,       L"fx_shimmer_mix",    KG_SHIMMER, false, nullptr },
    { L"Decay",     L"%",   0,   100, 70,  &gShimDecay,     L"fx_shimmer_decay",  KG_SHIMMER, false, nullptr },
    { L"Shimmer",   L"%",   0,   100, 50,  &gShimAmt,       L"fx_shimmer_amount", KG_SHIMMER, false, L"Off" },
    { L"Gender",    L"",    -100, 100, 0,  &gGenderAmt,     L"fx_gender",         KG_GENDER, true, nullptr },
    { L"Mix",       L"%",   0,   100, 100, &gGenderMix,     L"fx_gender_mix",     KG_GENDER, false, nullptr },
    { L"Strength",  L"%",   0,   100, 100, &gNsStrength,    L"ns_strength",       KG_NS,   false, nullptr },
    { L"Threshold", L" dB", -90, -10, -50, &gGateThrDb,     L"gate_threshold_db", KG_GATE, false, nullptr },
    { L"Voice",     L"%",   10,  99,  60,  &gGateVoicePct,  L"gate_voice_pct",    KG_GATE, false, nullptr },
    { L"Hold",      L" ms", 0,   1000, 150, &gGateHoldMs,   L"gate_hold_ms",      KG_GATE, false, nullptr },
    { L"Release",   L" ms", 10,  1000, 80, &gGateReleaseMs, L"gate_release_ms",   KG_GATE, false, nullptr },
    { L"Range",     L" dB", 0,   80,  80,  &gGateRangeDb,   L"gate_range_db",     KG_GATE, false, nullptr },
    { L"Mic boost", L" dB", -12, 24,  0,   &gMicBoostDb,    L"mic_boost_db",      KG_TONE, true, nullptr  },
    { L"Low cut",   L" Hz", 0,   300, 80,  &gLowCutHz,      L"low_cut_hz",        KG_TONE, false, L"Off" },
    { L"Leveler",   L"%",   0,   100, 0,   &gLevelerPct,    L"leveler",           KG_TONE, false, L"Off" },
    { L"De-ess",    L"%",   0,   100, 0,   &gDeEss,         L"de_ess",            KG_TONE, false, L"Off" },
    { L"Bass",      L" dB", -12, 12,  0,   &gEqBass,        L"eq_bass",           KG_EQ, true, nullptr },
    { L"Low mid",   L" dB", -12, 12,  0,   &gEqLowMid,      L"eq_low_mid",        KG_EQ, true, nullptr },
    { L"Mid",       L" dB", -12, 12,  0,   &gEqMid,         L"eq_mid",            KG_EQ, true, nullptr },
    { L"Presence",  L" dB", -12, 12,  0,   &gEqPres,        L"eq_presence",       KG_EQ, true, nullptr },
    { L"Treble",    L" dB", -12, 12,  0,   &gEqTreble,      L"eq_treble",         KG_EQ, true, nullptr },
};
#define KNOB_N ((int)(sizeof(gKnobs) / sizeof(gKnobs[0])))
static_assert(IDC_KNOB + KNOB_N <= IDC_PADPLAY, "knob IDs would run into the soundboard IDs");

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
static HBRUSH gBrDarkBg, gBrDarkCtl, gBrLightBg;
static HWND   gTip;                             // hover-help tooltip window (see AddTips)

// ---- color themes ----
// Each theme has an accent (knobs, switches, tabs, checkboxes) in a bright version for dark mode and a
// deeper one for light mode, plus how strongly it tints the backgrounds. Add a row to add a theme.
struct ColorTheme { const wchar_t* name; COLORREF dark, light; float tint; };
static ColorTheme COLOR_THEMES[] = {             // (not const: the last one, Custom, takes your colour)
    { L"Classic",  RGB(76, 160, 255),  RGB(0, 103, 192),   0.0f  },   // the original look: blue on neutral grey
    { L"Blue",     RGB(76, 160, 255),  RGB(0, 103, 192),   1.0f  },
    { L"Purple",   RGB(170, 128, 255), RGB(118, 70, 220),  1.0f  },
    { L"Pink",     RGB(255, 110, 190), RGB(214, 51, 140),  1.0f  },
    { L"Red",      RGB(255, 92, 92),   RGB(205, 38, 38),   1.0f  },
    { L"Orange",   RGB(255, 152, 64),  RGB(190, 88, 0),    1.0f  },
    { L"Yellow",   RGB(245, 205, 70),  RGB(146, 110, 0),   0.8f  },
    { L"Green",    RGB(80, 205, 120),  RGB(24, 140, 64),   1.0f  },
    { L"Teal",     RGB(56, 204, 204),  RGB(0, 132, 140),   1.0f  },
    { L"Graphite", RGB(200, 200, 200), RGB(80, 80, 80),    0.0f  },
    { L"Crimson",  RGB(235, 70, 110),  RGB(170, 20, 60),   1.2f  },
    { L"Coral",    RGB(255, 127, 110), RGB(210, 80, 60),   1.0f  },
    { L"Gold",     RGB(230, 185, 80),  RGB(150, 110, 20),  0.9f  },
    { L"Lime",     RGB(170, 230, 70),  RGB(90, 150, 0),    0.9f  },
    { L"Mint",     RGB(110, 230, 180), RGB(20, 150, 110),  1.0f  },
    { L"Ocean",    RGB(60, 140, 230),  RGB(10, 80, 170),   1.6f  },
    { L"Lavender", RGB(190, 165, 255), RGB(120, 95, 200),  1.3f  },
    { L"Magenta",  RGB(240, 90, 240),  RGB(170, 30, 170),  1.2f  },
    { L"Forest",   RGB(90, 180, 100),  RGB(30, 110, 50),   1.8f  },
    { L"Sunset",   RGB(255, 120, 70),  RGB(200, 70, 30),   1.8f  },
    { L"Midnight", RGB(120, 140, 255), RGB(50, 60, 190),   2.4f  },
    { L"Mono",     RGB(235, 235, 235), RGB(30, 30, 30),    0.0f  },
    { L"Midnight purple", RGB(165, 120, 255), RGB(78, 40, 168), 3.0f },
    { L"Custom (hex)...", RGB(76, 160, 255), RGB(0, 103, 192), 1.0f },   // set from gCustomAccent
};
#define COLOR_THEME_N ((int)(sizeof(COLOR_THEMES) / sizeof(COLOR_THEMES[0])))
static int gColorTheme = 0;
static COLORREF gCustomAccent = RGB(255, 110, 190);   // the Custom theme's colour (typed as hex)
static void CustomThemeSync()                   // the Custom theme's swatch / colours follow gCustomAccent
{
    ColorTheme& c = COLOR_THEMES[COLOR_THEME_N - 1];
    c.dark = gCustomAccent;
    c.light = RGB(GetRValue(gCustomAccent) * 3 / 4, GetGValue(gCustomAccent) * 3 / 4, GetBValue(gCustomAccent) * 3 / 4);   // deeper for light mode
}

// The palette in use (set by ApplyPalette). The old constant names now point at these.
static COLORREF gDkBg, gDkCtl, gDkBorder, gDkSection, gDkText = RGB(235, 235, 235), gDkDim = RGB(160, 160, 160);
// Look tab: your own colours (CLR_NONE = the theme's), a background picture, font, opacity.
#define USERCOL_N 12
// accent, background, panels, borders, text, dim text, box titles, knobs, knob track, meters, tabs, status bar
static COLORREF gUserCol[USERCOL_N] = { CLR_NONE, CLR_NONE, CLR_NONE, CLR_NONE, CLR_NONE, CLR_NONE,
                                        CLR_NONE, CLR_NONE, CLR_NONE, CLR_NONE, CLR_NONE, CLR_NONE };
static int      gFontPx = 13;                    // text size (px at 100%)
static COLORREF gLtText = RGB(30, 30, 30), gLtDim = RGB(110, 110, 110);
static wchar_t  gPicPath[MAX_PATH];
static int      gPicFit = 0, gPicDim = 60;       // fit: 0 cover, 1 stretch, 2 centre, 3 tile, 4 placed by you; dim: % of the theme colour on top
static int      gPicX = 40, gPicY = 80, gPicSize = 100;   // background in "place it yourself" mode (design px, %)
static int      gGifFps = 30;                    // GIF frame-rate limit (0 = as fast as the GIF says)
static bool     gGifPauseBg = false;             // pause GIFs while another window is in front
static HBRUSH   gBrPicture = nullptr;            // the picture, sized to the window and dimmed (a pattern brush)
static wchar_t  gFontName[40] = L"Segoe UI";
static int      gOpacity = 100;
static COLORREF gDkTrack, gDkKnob, gLtBg, gLtCard, gLtBorder, gLtTrack, gLtStatus, gAccentNow;
#define DK_BG      gDkBg
#define DK_CTL     gDkCtl
#define DK_BORDER  gDkBorder
#define DK_SECTION gDkSection
#define DK_TEXT    gDkText
#define DK_DIM     gDkDim
#define DK_TRACK   gDkTrack
#define DK_KNOB    gDkKnob
#define LT_CARD    gLtCard
#define LT_BORDER  gLtBorder
#define LT_TRACK   gLtTrack
#define LT_STATUS  gLtStatus
#define ACCENT     gAccentNow

static COLORREF Mix(COLORREF a, COLORREF b, float t)   // a blended toward b by t (0..1)
{
    return RGB((int)(GetRValue(a) + (GetRValue(b) - GetRValue(a)) * t + 0.5f),
               (int)(GetGValue(a) + (GetGValue(b) - GetGValue(a)) * t + 0.5f),
               (int)(GetBValue(a) + (GetBValue(b) - GetBValue(a)) * t + 0.5f));
}

static void ApplyPalette()
{
    CustomThemeSync();
    const ColorTheme& t = COLOR_THEMES[Iclamp(gColorTheme, 0, COLOR_THEME_N - 1)];
    const float k = t.tint;
    gDkBg      = Mix(RGB(32, 32, 32), t.dark, 0.06f * k);
    gDkCtl     = Mix(RGB(45, 45, 45), t.dark, 0.08f * k);
    gDkBorder  = Mix(RGB(78, 78, 78), t.dark, 0.14f * k);
    gDkSection = Mix(RGB(64, 64, 64), t.dark, 0.18f * k);
    gDkTrack   = Mix(RGB(64, 64, 64), t.dark, 0.12f * k);
    gDkKnob    = Mix(RGB(54, 54, 54), t.dark, 0.07f * k);
    gLtBg      = Mix(GetSysColor(COLOR_BTNFACE), t.light, 0.07f * k);
    gLtCard    = Mix(RGB(252, 252, 252), t.light, 0.025f * k);
    gLtBorder  = Mix(RGB(206, 206, 206), t.light, 0.22f * k);
    gLtTrack   = Mix(RGB(218, 218, 218), t.light, 0.15f * k);
    gLtStatus  = Mix(RGB(228, 228, 228), t.light, 0.10f * k);
    gAccentNow = gDark ? t.dark : t.light;
    gDkText = RGB(235, 235, 235); gDkDim = RGB(160, 160, 160); gLtText = RGB(30, 30, 30); gLtDim = RGB(110, 110, 110);
    if (gUserCol[0] != CLR_NONE) gAccentNow = gUserCol[0];
    if (gUserCol[1] != CLR_NONE) { gDkBg = gLtBg = gUserCol[1]; }
    if (gUserCol[2] != CLR_NONE) { gDkCtl = gLtCard = gUserCol[2]; gDkKnob = Mix(gUserCol[2], RGB(0, 0, 0), 0.1f); }
    if (gUserCol[3] != CLR_NONE) { gDkSection = gLtBorder = gDkBorder = gUserCol[3]; }
    if (gUserCol[4] != CLR_NONE) { gDkText = gLtText = gUserCol[4]; }
    if (gUserCol[5] != CLR_NONE) { gDkDim = gLtDim = gUserCol[5]; }
    if (gUserCol[8] != CLR_NONE) { gDkTrack = gLtTrack = gUserCol[8]; }
    if (gBrDarkBg)  DeleteObject(gBrDarkBg);
    if (gBrDarkCtl) DeleteObject(gBrDarkCtl);
    if (gBrLightBg) DeleteObject(gBrLightBg);
    gBrDarkBg  = CreateSolidBrush(gDkBg);
    gBrDarkCtl = CreateSolidBrush(gDkCtl);
    gBrLightBg = CreateSolidBrush(gLtBg);
}

static COLORREF BgColor()  { return gDark ? DK_BG : gLtBg; }
static HBRUSH   BgBrush()  { return gBrPicture ? gBrPicture : gDark ? gBrDarkBg : gBrLightBg; }
static HBRUSH   BgSolid()  { return gDark ? gBrDarkBg : gBrLightBg; }   // pop-up windows (not lined up with the picture)
#define TXT_C (gDark ? DK_TEXT : gLtText)
static COLORREF UC(int i, COLORREF def) { return gUserCol[i] != CLR_NONE ? gUserCol[i] : def; }   // your colour, or the theme's
#define TITLE_C  UC(6, TXT_C)
#define KNOB_C   UC(7, gDark ? DK_KNOB : LT_CARD)
#define METER_C  UC(9, RGB(40, 190, 90))
#define TAB_C    UC(10, ACCENT)
#define STATUS_C UC(11, gDark ? DK_CTL : LT_STATUS)

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
    ApplyPalette();
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

static bool PictureLoad(const wchar_t* path);   // background picture + pictures on top: see "background picture"
static void PictureRebuild();
static bool PicActive();

static void ApplyOpacity()
{
    LONG ex = GetWindowLongW(gWnd, GWL_EXSTYLE);
    if (gOpacity >= 100) { if (ex & WS_EX_LAYERED) SetWindowLongW(gWnd, GWL_EXSTYLE, ex & ~WS_EX_LAYERED); return; }
    if (!(ex & WS_EX_LAYERED)) SetWindowLongW(gWnd, GWL_EXSTYLE, ex | WS_EX_LAYERED);
    SetLayeredWindowAttributes(gWnd, 0, (BYTE)(Iclamp(gOpacity, 40, 100) * 255 / 100), LWA_ALPHA);
}

static void FitText();
static void FitOne(HWND h);
static int CALLBACK FontEnumProc(const LOGFONTW* lf, const TEXTMETRICW*, DWORD, LPARAM l)
{
    HWND c = (HWND)l;
    if (lf->lfFaceName[0] == L'@') return 1;    // sideways (vertical) copies of East Asian fonts
    if (SendMessageW(c, CB_FINDSTRINGEXACT, (WPARAM)-1, (LPARAM)lf->lfFaceName) == CB_ERR)
        SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)lf->lfFaceName);
    return 1;
}
static void FontsFill(HWND c)                   // every font installed on this PC
{
    LOGFONTW lf = {}; lf.lfCharSet = DEFAULT_CHARSET;
    HDC dc = GetDC(nullptr);
    EnumFontFamiliesExW(dc, &lf, (FONTENUMPROCW)FontEnumProc, (LPARAM)c, 0);
    ReleaseDC(nullptr, dc);
    LRESULT i = SendMessageW(c, CB_FINDSTRINGEXACT, (WPARAM)-1, (LPARAM)gFontName);
    if (i == CB_ERR) i = SendMessageW(c, CB_FINDSTRINGEXACT, (WPARAM)-1, (LPARAM)L"Segoe UI");
    SendMessageW(c, CB_SETCURSEL, i == CB_ERR ? 0 : i, 0);
    SendMessageW(c, CB_SETDROPPEDWIDTH, SC(240), 0);
}
static HFONT gFontFit[3];                       // smaller copies of the font for text that would not fit otherwise
static BOOL CALLBACK SetFontProc(HWND c, LPARAM) { SendMessageW(c, WM_SETFONT, (WPARAM)gFont, TRUE); return TRUE; }
static void ApplyFont()                         // re-create the fonts and hand them to every control
{
    HFONT f = CreateFontW(-SC(gFontPx), 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, gFontName);
    HFONT b = CreateFontW(-SC(gFontPx), 0, 0, 0, FW_SEMIBOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, gFontName);
    if (!f || !b) { if (f) DeleteObject(f); if (b) DeleteObject(b); return; }
    HFONT of = gFont, ob = gFontBold;
    gFont = f; gFontBold = b;
    if (gWnd) EnumChildWindows(gWnd, SetFontProc, 0);
    if (of) DeleteObject(of); if (ob) DeleteObject(ob);
    for (HFONT& ff : gFontFit) if (ff) { DeleteObject(ff); ff = nullptr; }
    if (gWnd) FitText();                        // a wider font needs more room: re-measure every label
}

static void ThemeTitleBar(HWND w)
{
    if (!pDwmSetWindowAttribute || !w) return;
    BOOL d = gDark;
    if (FAILED(pDwmSetWindowAttribute(w, 20, &d, sizeof(d))))    // DWMWA_USE_IMMERSIVE_DARK_MODE
        pDwmSetWindowAttribute(w, 19, &d, sizeof(d));            // older Windows 10 builds
    // Windows 11: title bar matches the window, thin border in the accent (Classic keeps Windows' own)
    bool tinted = COLOR_THEMES[Iclamp(gColorTheme, 0, COLOR_THEME_N - 1)].tint > 0;
    COLORREF cap = tinted ? BgColor() : 0xFFFFFFFF, brd = tinted ? ACCENT : 0xFFFFFFFF;   // 0xFFFFFFFF = default
    pDwmSetWindowAttribute(w, 35, &cap, sizeof(cap));          // DWMWA_CAPTION_COLOR
    pDwmSetWindowAttribute(w, 34, &brd, sizeof(brd));          // DWMWA_BORDER_COLOR
}

static void ApplyTheme()
{
    gDark = gThemeMode == THEME_DARK || (gThemeMode == THEME_SYSTEM && SystemUsesDark());
    ApplyPalette();
    PictureRebuild();                           // the dim colour follows the theme
    ThemeTitleBar(gWnd);
    if (pSetPreferredAppMode) {                 // dark tray menu
        pSetPreferredAppMode(gDark ? 2 : 3);
        if (pFlushMenuThemes) pFlushMenuThemes();
    }
    EnumChildWindows(gWnd, ThemeChild, 0);
    if (gTrimWnd) { ThemeTitleBar(gTrimWnd); EnumChildWindows(gTrimWnd, ThemeChild, 0); InvalidateRect(gTrimWnd, nullptr, TRUE); }
    if (gTip) SetTheme(gTip, gDark ? L"DarkMode_Explorer" : nullptr, nullptr);
    RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_ALLCHILDREN | RDW_FRAME);
}

// Dark-mode checkbox / radio button, drawn from scratch (Windows has no dark version of these).
// ---- one shared off-screen buffer ----
// Labels, checkboxes and custom-drawn controls draw off-screen and copy in one go (no flicker). Making a fresh
// buffer for every one of those paints is slow with a GIF behind them, so they share one that only grows.
// (If it's in use, a control gets its own for that paint.)
static struct { HDC dc; HBITMAP bmp; HGDIOBJ old; int w, h; bool busy; } gBuf;
struct OffScreen {
    HDC dc = nullptr; HBITMAP own = nullptr; HGDIOBJ ownOld = nullptr; bool shared = false;
    OffScreen(HDC like, int w, int h)
    {
        w = Imax(1, w); h = Imax(1, h);
        if (!gBuf.busy) {
            if (!gBuf.dc) gBuf.dc = CreateCompatibleDC(like);
            if (gBuf.dc && (w > gBuf.w || h > gBuf.h)) {
                const int nw = Imax(w, gBuf.w), nh = Imax(h, gBuf.h);
                if (HBITMAP b = CreateCompatibleBitmap(like, nw, nh)) {
                    HGDIOBJ prev = SelectObject(gBuf.dc, b);
                    if (gBuf.bmp) DeleteObject(gBuf.bmp); else gBuf.old = prev;
                    gBuf.bmp = b; gBuf.w = nw; gBuf.h = nh;
                }
            }
            if (gBuf.bmp && gBuf.w >= w && gBuf.h >= h) {
                gBuf.busy = true; shared = true; dc = gBuf.dc;
                SetViewportOrgEx(dc, 0, 0, nullptr); SetBrushOrgEx(dc, 0, 0, nullptr); SelectClipRgn(dc, nullptr);
                SetBkMode(dc, OPAQUE); SetTextColor(dc, RGB(0, 0, 0)); SetBkColor(dc, RGB(255, 255, 255));
                return;
            }
        }
        dc = CreateCompatibleDC(like); own = CreateCompatibleBitmap(like, w, h); ownOld = SelectObject(dc, own);
    }
    ~OffScreen() { if (shared) gBuf.busy = false; else if (dc) { SelectObject(dc, ownOld); DeleteObject(own); DeleteDC(dc); } }
};

static LRESULT DrawDarkCheck(NMCUSTOMDRAW* cd)
{
    if (cd->dwDrawStage != CDDS_PREPAINT) return CDRF_DODEFAULT;
    HWND h = cd->hdr.hwndFrom;
    LONG type = GetWindowLongW(h, GWL_STYLE) & BS_TYPEMASK;
    bool radio = type == BS_AUTORADIOBUTTON || type == BS_RADIOBUTTON;
    if (!radio && type != BS_AUTOCHECKBOX && type != BS_CHECKBOX) return CDRF_DODEFAULT;

    HDC real = cd->hdc;                         // drawn off-screen, then copied in one go (no flicker over a GIF)
    RECT rc = cd->rc;
    OffScreen os(real, (int)rc.right, (int)rc.bottom);
    HDC dc = os.dc;
    if (gBrPicture && GetParent(h) == gWnd) {   // over a picture: show the picture behind it, not a box
        POINT pt = { 0, 0 }; MapWindowPoints(h, gWnd, &pt, 1);
        SetBrushOrgEx(dc, -pt.x, -pt.y, nullptr);
        FillRect(dc, &rc, gBrPicture);
    } else FillRect(dc, &rc, gBrDarkBg);
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
    BitBlt(real, rc.left, rc.top, rc.right - rc.left, rc.bottom - rc.top, dc, rc.left, rc.top, SRCCOPY);
    return CDRF_SKIPDEFAULT;
}

// ---- text labels, painted off-screen ----
// Windows' own label paints its background, then its text: over a moving picture that flickers. This draws
// both into a buffer first, using the same colours / brush the window hands every label (WM_CTLCOLORSTATIC).
static void HitchLog(UINT m, WPARAM w, int ms);
struct HitchTimer {                             // (a child control's paint, timed for the hitch log)
    LARGE_INTEGER a; UINT m; int id;
    HitchTimer(UINT msg, int ctl) : m(msg), id(ctl) { QueryPerformanceCounter(&a); }
    ~HitchTimer() { LARGE_INTEGER b, f; QueryPerformanceCounter(&b); QueryPerformanceFrequency(&f);
                    int ms = (int)((b.QuadPart - a.QuadPart) * 1000 / f.QuadPart); if (ms > 25) HitchLog(0x10000 | m, (WPARAM)id, ms); }
};
static LRESULT CALLBACK BufLabelProc(HWND h, UINT m, WPARAM w, LPARAM l, UINT_PTR, DWORD_PTR)
{
    HitchTimer ht(m, GetDlgCtrlID(h));
    if (m == WM_ERASEBKGND) return 1;
    if (m == WM_PAINT || m == WM_PRINTCLIENT) {
        PAINTSTRUCT ps = {};
        HDC dc = m == WM_PAINT ? BeginPaint(h, &ps) : (HDC)w;
        RECT rc; GetClientRect(h, &rc);
        if (rc.right > 0 && rc.bottom > 0) {
            OffScreen os(dc, rc.right, rc.bottom);
            HDC mem = os.dc;
            HBRUSH br = (HBRUSH)SendMessageW(GetParent(h), WM_CTLCOLORSTATIC, (WPARAM)mem, (LPARAM)h);   // colours + lined-up brush
            FillRect(mem, &rc, br ? br : GetSysColorBrush(COLOR_BTNFACE));
            wchar_t text[1024]; GetWindowTextW(h, text, 1024);
            HGDIOBJ of = SelectObject(mem, (HFONT)SendMessageW(h, WM_GETFONT, 0, 0));
            const LONG st = GetWindowLongW(h, GWL_STYLE), type = st & SS_TYPEMASK;
            UINT fl = DT_EXPANDTABS;
            if (type == SS_CENTER) fl |= DT_CENTER; else if (type == SS_RIGHT) fl |= DT_RIGHT;
            if (st & SS_NOPREFIX) fl |= DT_NOPREFIX;
            if (st & SS_CENTERIMAGE) fl |= DT_SINGLELINE | DT_VCENTER;
            if (st & SS_ENDELLIPSIS) fl |= DT_END_ELLIPSIS | DT_SINGLELINE;
            else if (type != SS_LEFTNOWORDWRAP && type != SS_SIMPLE && !(fl & DT_SINGLELINE)) fl |= DT_WORDBREAK;
            if (!IsWindowEnabled(h)) SetTextColor(mem, gDark ? RGB(110, 110, 110) : GetSysColor(COLOR_GRAYTEXT));
            DrawTextW(mem, text, -1, &rc, fl);
            SelectObject(mem, of);
            BitBlt(dc, 0, 0, rc.right, rc.bottom, mem, 0, 0, SRCCOPY);
        }
        if (m == WM_PAINT) EndPaint(h, &ps);
        return 0;
    }
    if (m == WM_SETTEXT || m == WM_ENABLE || m == WM_SETFONT) {
        LRESULT r = DefSubclassProc(h, m, w, l);
        InvalidateRect(h, nullptr, FALSE);
        return r;
    }
    return DefSubclassProc(h, m, w, l);
}
static BOOL CALLBACK BufLabelAttach(HWND c, LPARAM)
{
    if (GetParent(c) != gWnd) return TRUE;
    wchar_t cls[16]; GetClassNameW(c, cls, 16);
    if (lstrcmpiW(cls, L"Static")) return TRUE;
    LONG type = GetWindowLongW(c, GWL_STYLE) & SS_TYPEMASK;
    if (type == SS_LEFT || type == SS_CENTER || type == SS_RIGHT || type == SS_LEFTNOWORDWRAP || type == SS_SIMPLE)
        SetWindowSubclass(c, BufLabelProc, 7, 0);
    return TRUE;
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
static const wchar_t* FxKeyIniName(int slot)
{
    if (slot >= SLOT_MIX0) {                    // mixer: "mix_ch3_up", "mix_out2_mute"...
        static wchar_t names[KEY_SLOTS - SLOT_MIX0][24];
        static const wchar_t* ca[MIXA_N] = { L"up", L"down", L"mute", L"solo", L"duck", L"hold" };
        static const wchar_t* oa[MIXO_N] = { L"up", L"down", L"mute" };
        wchar_t* n = names[slot - SLOT_MIX0];
        if (!n[0]) {
            if (slot < SLOT_MIXOUT0) wsprintfW(n, L"mix_ch%d_%s", (slot - SLOT_MIX0) / MIXA_N + 1, ca[(slot - SLOT_MIX0) % MIXA_N]);
            else wsprintfW(n, L"mix_out%d_%s", (slot - SLOT_MIXOUT0) / MIXO_N + 1, oa[(slot - SLOT_MIXOUT0) % MIXO_N]);
        }
        return n;
    }
    static const wchar_t* padKeys[PADS] = { L"pad1_hotkey", L"pad2_hotkey", L"pad3_hotkey", L"pad4_hotkey",
                                            L"pad5_hotkey", L"pad6_hotkey", L"pad7_hotkey", L"pad8_hotkey" };
    static const wchar_t* clipKeys[CLIPS] = { L"clip1_hotkey", L"clip2_hotkey", L"clip3_hotkey", L"clip4_hotkey",
                                              L"clip5_hotkey", L"clip6_hotkey", L"clip7_hotkey", L"clip8_hotkey" };
    if (slot >= SLOT_PROF0)    return nullptr;           // saved by profile name (ProfileKeysSave)
    if (slot == SLOT_TAPESTOP) return L"tape_stop_hotkey";
    if (slot == SLOT_PTT)      return L"push_to_talk_hotkey";
    if (slot == SLOT_DIVE)     return L"pitch_dive_hotkey";
    if (slot == SLOT_PROFNEXT) return L"profile_next_hotkey";
    if (slot == SLOT_REWIND)  return L"rewind_hotkey";
    if (slot == SLOT_REPEAT)  return L"repeat_word_hotkey";
    if (slot == SLOT_PADBANK) return L"pad_page_hotkey";
    if (slot >= SLOT_CLIP0)  return clipKeys[slot - SLOT_CLIP0];
    if (slot == SLOT_CLIPNOW) return L"clip_now_hotkey";
    if (slot >= SLOT_PAD0) return padKeys[slot - SLOT_PAD0];
    return slot == SLOT_MUTE ? L"mute_hotkey" : slot == 0 ? L"fx_hotkey" : gFxGroups[slot - 1].hotkeyKey;
}

static wchar_t gUpdateRepo[200];
static wchar_t gSongApp[64] = L"";               // Vocode to song: app to take music from ("" = all PC sound)
static wchar_t gSongFile[MAX_PATH] = L"";        // ...or an audio file (used when gUseFile)
static bool    gSongUseFile = false;
static int     gVocSynthSaved = 100;             // Synth value of the other side: Song style keeps its own
static wchar_t gPadFile[SB_N][MAX_PATH];         // soundboard sounds (4 pages), then clips
static bool    gClipAutoTrim = true;             // cut silence off the ends of new clips
static wchar_t gTtsVoice[128];                   // text-to-speech voice (its name; empty = Windows' default)
static int     gTtsAccent = 0;                    // text-to-speech accent (TTS_ACCENTS index; 0 = none)
static int     gTtsVol = 100;                     // text-to-speech volume (%)
static int     gTtsRate = 0, gTtsPitch = 0;       // speed (-10..10, on top of the accent's), pitch (semitones)
static int     gTtsRoom = 35, gTtsPause = 100;    // room sound (%), pauses between sentences (%)
static bool    gTtsNatural = true;                // per-sentence pace / pitch, warmth, room, even level
static bool    gVoiceInstalling = false;          // Windows is installing a voice for an accent
static int     gVoicePct = -1;                    // how far (from DISM's own progress; -1 = not known yet)
static DWORD   gVoiceStart = 0;                   // when it started (for the time shown until DISM reports)
static wchar_t gVoiceLog[MAX_PATH];               // DISM's output, read for its progress
static void    VoiceProgressTick();
static int     gRecSeconds = 15;                 // instant replay length
// What clips keep. The numbers are saved in the settings file, so new ones go at the end.
enum { REC_BOTH = 0, REC_VOICE = 1, REC_PC = 2, REC_OFF = 3, REC_DISCORD = 4, REC_VOICE_DISCORD = 5, REC_N };
static int     gRecSource = REC_BOTH;
static const int      kRecOrder[REC_N] = { REC_BOTH, REC_VOICE_DISCORD, REC_VOICE, REC_PC, REC_DISCORD, REC_OFF };   // list order
static const wchar_t* kRecNames[REC_N] = { L"Your voice + PC sound", L"Your voice + Discord", L"Only your voice",
                                           L"Only PC sound", L"Only Discord", L"Off" };
static bool RecHasVoice(int s)   { return s == REC_BOTH || s == REC_VOICE || s == REC_VOICE_DISCORD; }
static bool RecHasOther(int s)   { return s == REC_BOTH || s == REC_PC || s == REC_DISCORD || s == REC_VOICE_DISCORD; }
static bool RecIsDiscord(int s)  { return s == REC_DISCORD || s == REC_VOICE_DISCORD; }
struct TrimState { unsigned s, e; };
#define TRIM_HIST 64
struct Clip {
    short*    base;  unsigned baseLen;           // the whole recording (never changed by trimming)
    unsigned  ts, te;                            // the part that plays
    unsigned  pendTs, pendTe;                    // saved trim, applied when the file finishes loading
    TrimState undo[TRIM_HIST]; int nUndo;
    TrimState redo[TRIM_HIST]; int nRedo;
};
static Clip    gClips[CLIP_N];
static int     gClipBank = 0;                    // clip page on screen
static inline int ClipSlot(int row) { return gClipBank * CLIPS + row; }
static bool    gClipPinned[CLIP_N];              // never replaced when the board is full
static unsigned gClipStamp[CLIP_N], gClipStampNext = 1;   // capture order (oldest gets replaced)
static bool    gClipSeparate = false, gClipReplace = true;
// pads: names and colours (CLR_NONE = the theme's card colour)
static wchar_t gPadName[PAD_N][48];
static COLORREF gPadColor[PAD_N];
static bool    gUpdateOnStart = true;

static void LoadSettings()
{
    // Settings live in %APPDATA%\LagEffect\LagEffect.ini, so every copy of the app (any folder,
    // any version, after updates) shares them. The first time, settings saved next to the exe by
    // older versions are copied over.
    wchar_t local[MAX_PATH];
    GetModuleFileNameW(nullptr, local, MAX_PATH);
    wchar_t* slash = wcsrchr(local, L'\\');
    if (slash) slash[1] = 0; else local[0] = 0;
    lstrcatW(local, L"LagEffect.ini");

    wchar_t dir[MAX_PATH];
    DWORD n = GetEnvironmentVariableW(L"APPDATA", dir, MAX_PATH);
    if (n > 0 && n < MAX_PATH - 32) {
        lstrcatW(dir, L"\\LagEffect");
        CreateDirectoryW(dir, nullptr);         // fine if it already exists
        lstrcpynW(gIni, dir, MAX_PATH);
        lstrcatW(gIni, L"\\LagEffect.ini");
        if (GetFileAttributesW(gIni) == INVALID_FILE_ATTRIBUTES && GetFileAttributesW(local) != INVALID_FILE_ATTRIBUTES)
            CopyFileW(local, gIni, TRUE);
        if (GetFileAttributesW(dir) == INVALID_FILE_ATTRIBUTES) lstrcpynW(gIni, local, MAX_PATH);   // no AppData: old place
    } else {
        lstrcpynW(gIni, local, MAX_PATH);
    }

    #define INI_INT(k, d) (int)GetPrivateProfileIntW(L"settings", k, d, gIni)
    for (Range& r : gRanges) *r.var = Iclamp(INI_INT(r.key, *r.var), r.lo, r.hi);
    gHotkeys[0]    = Iclamp(INI_INT(L"hotkey",  VK_F8), 0, 255);
    gHotkeys[1]    = Iclamp(INI_INT(L"hotkey2", 0), 0, 255);
    gHotkeys[2]    = Iclamp(INI_INT(L"hotkey3", 0), 0, 255);
    if (!gHotkeys[0]) gHotkeys[0] = VK_F8;
    gToggleMode    = INI_INT(L"toggle", 0) != 0;
    gTalkOver      = INI_INT(L"talkover", 0) != 0;
    gBufIdx        = Iclamp(INI_INT(L"buffer", 2), 0, 4);
    gExclusive     = INI_INT(L"exclusive", 0) != 0;
    gHideShare     = INI_INT(L"hide_from_share", 0) != 0;
    gShowOsd       = INI_INT(L"hotkey_popup", 1) != 0;
    gTopMost       = INI_INT(L"always_on_top", 0) != 0;
    {
        wchar_t b[32];
        GetPrivateProfileStringW(L"settings", L"win_x", L"", b, 32, gIni); if (b[0]) gWinX = _wtoi(b);
        GetPrivateProfileStringW(L"settings", L"win_y", L"", b, 32, gIni); if (b[0]) gWinY = _wtoi(b);
    }
    gAutoStart     = INI_INT(L"autostart", 0) != 0;
    gThemeMode     = Iclamp(INI_INT(L"theme", THEME_SYSTEM), 0, 2);
    gColorTheme    = Iclamp(INI_INT(L"color_theme", 0), 0, COLOR_THEME_N - 1);
    gCustomAccent  = (COLORREF)INI_INT(L"color_theme_custom", (int)RGB(255, 110, 190)) & 0xFFFFFF;
    gUpdateOnStart = INI_INT(L"update_on_start", 1) != 0;

    gFxOn = INI_INT(L"fx_on", 0) != 0;
    for (int slot = 0; slot < KEY_SLOTS; slot++) {
        wchar_t b[64];
        if (!FxKeyIniName(slot)) continue;
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
    // Mic tab. Settings from 1.5 and older: gate=1/0 and gate_db=50 (meaning -50 dB).
    gNsOn         = INI_INT(L"ns_on", 0) != 0;
    gVocStyle     = Iclamp(INI_INT(L"voc_style", VOC_HARMONY), 0, VOC_STYLES - 1);
    gVocKey       = Iclamp(INI_INT(L"voc_key", 0), 0, 11);
    gVocScale     = Iclamp(INI_INT(L"voc_scale", 1), 0, VOC_SCALES - 1);
    gVocRange     = Iclamp(INI_INT(L"voc_range", VR_AUTO), 0, 2);
    GetPrivateProfileStringW(L"settings", L"voc_song_app", L"", gSongApp, 64, gIni);
    GetPrivateProfileStringW(L"settings", L"voc_song_file", L"", gSongFile, MAX_PATH, gIni);
    gSongUseFile = INI_INT(L"voc_song_use_file", 0) != 0 && gSongFile[0];
    gPadMaster = Iclamp(INI_INT(L"pad_master", 100), 0, 200);
    for (int i = 0; i < PAD_N; i++) {            // pad1-8 = page A, 9-16 = B, ...
        wchar_t key[32];
        wsprintfW(key, L"pad%d_file", i + 1);   GetPrivateProfileStringW(L"settings", key, L"", gPadFile[i], MAX_PATH, gIni);
        wsprintfW(key, L"pad%d_volume", i + 1); gPads[i].vol = Iclamp(INI_INT(key, 100), 0, 200);
    }
    gRecSeconds = Iclamp(INI_INT(L"rec_seconds", 15), 3, REC_MAX_S);
    gPadBank      = Iclamp(INI_INT(L"pad_page", 0), 0, PAD_BANKS - 1);
    gPttMode      = Iclamp(INI_INT(L"push_to_talk_mode", 0), 0, 2);
    gOverlayOn    = INI_INT(L"overlay", 0) != 0;
    gOverlayX     = INI_INT(L"overlay_x", INT_MIN); gOverlayY = INI_INT(L"overlay_y", INT_MIN);
    gBeeps        = INI_INT(L"hotkey_beeps", 0) != 0;
    gUiScale      = Iclamp(INI_INT(L"ui_scale", 100), 80, 250);
    gCompact      = INI_INT(L"compact", 0) != 0;
    gCmdLine      = INI_INT(L"command_line_control", 0) != 0;
    gSetSub       = Iclamp(INI_INT(L"settings_subtab", 0), 0, 3);
    for (int i = 0; i < USERCOL_N; i++) { wchar_t k[32]; wsprintfW(k, L"color_custom_%d", i); gUserCol[i] = (COLORREF)INI_INT(k, (int)CLR_NONE); }
    GetPrivateProfileStringW(L"settings", L"background_picture", L"", gPicPath, MAX_PATH, gIni);
    gPicFit       = Iclamp(INI_INT(L"background_fit", 0), 0, 4);
    gPicX         = Iclamp(INI_INT(L"background_x", 40), -2000, 4000);
    gPicY         = Iclamp(INI_INT(L"background_y", 80), -2000, 4000);
    gPicSize      = Iclamp(INI_INT(L"background_size", 100), 5, 400);
    gGifFps       = Iclamp(INI_INT(L"gif_fps_limit", 30), 0, 120);
    gGifPauseBg   = INI_INT(L"gif_pause_in_background", 0) != 0;
    gPicDim       = Iclamp(INI_INT(L"background_dim", 60), 0, 95);
    GetPrivateProfileStringW(L"settings", L"font", L"Segoe UI", gFontName, 40, gIni);
    gFontPx = Iclamp(INI_INT(L"font_px", 13), 10, 20);
    gOpacity      = Iclamp(INI_INT(L"window_opacity", 100), 40, 100);
    gFxHold[0]    = INI_INT(L"fx_hotkey_hold", 0) != 0;
    for (int g = 0; g < FX_GROUPS; g++) { wchar_t k[64]; wsprintfW(k, L"%s_hold", gFxGroups[g].hotkeyKey); gFxHold[1 + g] = INI_INT(k, 0) != 0; }
    gPadsFx       = INI_INT(L"pads_through_fx", 0) != 0;
    gClipsFx      = INI_INT(L"clips_through_fx", 0) != 0;
    gClipAutoTrim = INI_INT(L"clip_auto_trim", 1) != 0;
    gRandLagOn    = INI_INT(L"random_lag", 0) != 0;
    {                                           // features: off for a new install; someone upgrading keeps everything they had
        const int had = GetFileAttributesW(gIni) != INVALID_FILE_ATTRIBUTES && INI_INT(L"feat_lag", -1) == -1 &&
                        GetPrivateProfileIntW(L"settings", L"loop_ms", -1, gIni) != -1 ? 1 : 0;
        gFeatLag   = INI_INT(L"feat_lag", had) != 0;
        gFeatFx    = INI_INT(L"feat_voicefx", had) != 0;
        gFeatSound = INI_INT(L"feat_soundboard", had) != 0;
        gFeatClips = INI_INT(L"feat_clips", had) != 0;
    }
    gWsOn   = INI_INT(L"remote_on", 0) != 0;     // (off unless you switch it on)
    gWsPort = Iclamp(INI_INT(L"remote_port", 7600), 1024, 65535);
    GetPrivateProfileStringW(L"settings", L"remote_password", L"", gWsPass, 64, gIni);
    gRandLagSec   = Iclamp(INI_INT(L"random_lag_every_s", 8), 2, 120);
    gRepeatN      = Iclamp(INI_INT(L"repeat_word_times", 3), 1, 6);
    GetPrivateProfileStringW(L"settings", L"tts_voice", L"", gTtsVoice, 128, gIni);
    gTtsAccent = INI_INT(L"tts_accent", 0);
    for (int c = 0; c < CH_MAX; c++) {           // mixer channels
        wchar_t k[32];
        wsprintfW(k, L"ch_%d_type", c);   gCh[c].type = Iclamp(INI_INT(k, CH_NONE), CH_NONE, CH_OUT);
        wsprintfW(k, L"ch_%d_src", c);    GetPrivateProfileStringW(L"settings", k, L"", gCh[c].src, 128, gIni);
        {                                       // volume in dB (older settings kept it in %)
            wsprintfW(k, L"ch_%d_db", c);
            int db = INI_INT(k, 9999);
            if (db == 9999) { wsprintfW(k, L"ch_%d_vol", c); int v = Iclamp(INI_INT(k, 100), 0, 200); db = v <= 0 ? -600 : (int)lroundf(200.0f * log10f(v / 100.0f)); }
            gCh[c].db10 = Iclamp(db, -600, 60);
        }
        wsprintfW(k, L"ch_%d_duck", c);   gCh[c].duck = INI_INT(k, 0) != 0;
        wsprintfW(k, L"ch_%d_color", c);  gCh[c].color = Iclamp(INI_INT(k, c), 0, 7);
        wsprintfW(k, L"ch_%d_name", c);   GetPrivateProfileStringW(L"settings", k, L"", gCh[c].name, 32, gIni);
        wsprintfW(k, L"ch_%d_holdtalk", c); gCh[c].holdTalk = INI_INT(k, 0) != 0;
        gCh[c].solo = false;
        wsprintfW(k, L"ch_%d_mute", c);   gCh[c].mute = INI_INT(k, 0) != 0;
        wsprintfW(k, L"ch_%d_routes", c); gCh[c].routes = (unsigned)INI_INT(k, 1) & ((1u << MAX_OUT) - 1);
        if (!gCh[c].src[0]) gCh[c].type = CH_NONE;
    }
    gDuckDb = Iclamp(INI_INT(L"mixer_duck_db", 12), 3, 30);
    gMixStep = Iclamp(INI_INT(L"mixer_key_step", 2), 1, 10);
    for (int c = 0; c < CH_MAX; c++)  { wchar_t key[24]; wsprintfW(key, L"ch_%d_width", c);  int v = INI_INT(key, 0); gChW[c] = v ? Iclamp(v, 52, 240) : 0; }
    for (int k = 0; k < MAX_OUT; k++) { wchar_t key[24]; wsprintfW(key, L"out_%d_width", k); int v = INI_INT(key, 0); gOutW[k] = v ? Iclamp(v, 84, 320) : 0; }
    for (int k = 0; k < MAX_OUT; k++) { wchar_t key[24]; wsprintfW(key, L"out_%d_mute", k); gOutMute[k] = INI_INT(key, 0) != 0; }
    for (int k = 0; k < MAX_OUT; k++) { wchar_t key[24]; wsprintfW(key, L"out_%d_name", k); GetPrivateProfileStringW(L"settings", key, L"", gOutName[k], 32, gIni); }
    gTtsVol = Iclamp(INI_INT(L"tts_volume", 100), 0, 200);
    gTtsRate = Iclamp(INI_INT(L"tts_speed", 0), -10, 10); gTtsPitch = Iclamp(INI_INT(L"tts_pitch", 0), -12, 12);
    gTtsRoom = Iclamp(INI_INT(L"tts_room", 35), 0, 100); gTtsPause = Iclamp(INI_INT(L"tts_pauses", 100), 0, 300);
    gTtsNatural = INI_INT(L"tts_natural", 1) != 0;
    gEchoStyle = Iclamp(INI_INT(L"fx_echo_style", 0), 0, ECHO_N - 1);
    gHarmStyle = Iclamp(INI_INT(L"fx_harm_style", 0), 0, HARM_N - 1);
    gBeatSync  = INI_INT(L"beat_sync", 0) != 0;
    gBpm       = Iclamp(INI_INT(L"bpm", 120), 40, 300);
    gBeatDiv   = Iclamp(INI_INT(L"beat_division", 1), 0, 3);
    gDiveSemis = Iclamp(INI_INT(L"pitch_dive_semitones", -12), -12, 12);
    gBroadcast = INI_INT(L"broadcast_voice", 0) != 0;
    gHarmMute = INI_INT(L"fx_harm_mute", 0) != 0;
    gMicSub    = Iclamp(INI_INT(L"mic_subtab", 0), 0, 1);
    gDistStyle = Iclamp(INI_INT(L"fx_dist_style", 0), 0, DIST_N - 1);
    gChoStyle  = Iclamp(INI_INT(L"fx_chorus_style", 0), 0, CHO_N - 1);
    gMufStyle  = Iclamp(INI_INT(L"fx_muffle_style", 0), 0, MUF_N - 1);
    gFxSub     = Iclamp(INI_INT(L"fx_subtab", 0), 0, FX_SUBS - 1);
    gRecSource  = Iclamp(INI_INT(L"rec_source", REC_BOTH), 0, REC_N - 1);
    gClipMaster = Iclamp(INI_INT(L"clip_master", 100), 0, 200);
    gClipBank     = Iclamp(INI_INT(L"clip_page", 0), 0, CLIP_BANKS - 1);
    gClipSeparate = INI_INT(L"clip_separate_tracks", 0) != 0;
    gClipReplace  = INI_INT(L"clip_replace_oldest", 1) != 0;
    gPadChoke     = INI_INT(L"pads_one_at_a_time", 0) != 0;
    gPadDuck      = INI_INT(L"pads_duck_voice", 0) != 0;
    gHearOut      = Iclamp(INI_INT(L"always_hear_sounds_on", 0), 0, MAX_OUT + 1);
    gClipStampNext = (unsigned)Imax(1, INI_INT(L"clip_stamp_next", 1));
    for (int i = 0; i < PAD_N; i++) {
        wchar_t key[32]; Pad& p = gPads[i];
        wsprintfW(key, L"pad%d_mode", i + 1);     p.mode = Iclamp(INI_INT(key, 0), 0, 3);
        wsprintfW(key, L"pad%d_speed", i + 1);    p.speed = Iclamp(INI_INT(key, 100), 25, 400);
        wsprintfW(key, L"pad%d_pitch", i + 1);    p.pitch = Iclamp(INI_INT(key, 0), -12, 12);
        wsprintfW(key, L"pad%d_fade_in", i + 1);  p.fadeInMs = Iclamp(INI_INT(key, 0), 0, 5000);
        wsprintfW(key, L"pad%d_fade_out", i + 1); p.fadeOutMs = Iclamp(INI_INT(key, 0), 0, 5000);
        wsprintfW(key, L"pad%d_name", i + 1);     GetPrivateProfileStringW(L"settings", key, L"", gPadName[i], 48, gIni);
        wsprintfW(key, L"pad%d_color", i + 1);    gPadColor[i] = (COLORREF)INI_INT(key, (int)CLR_NONE);
    }
    for (int i = 0; i < CLIP_N; i++) {
        wchar_t key[32];
        wsprintfW(key, L"clip%d_pinned", i + 1); gClipPinned[i] = INI_INT(key, 0) != 0;
        wsprintfW(key, L"clip%d_stamp", i + 1);  gClipStamp[i] = (unsigned)Imax(0, INI_INT(key, 0));
        wsprintfW(key, L"clip%d_file", i + 1);   GetPrivateProfileStringW(L"settings", key, L"", gPadFile[CLIP0 + i], MAX_PATH, gIni);
        wsprintfW(key, L"clip%d_volume", i + 1); gPads[CLIP0 + i].vol = Iclamp(INI_INT(key, 100), 0, 200);
        wsprintfW(key, L"clip%d_start", i + 1);  gClips[i].pendTs = (unsigned)Iclamp(INI_INT(key, 0), 0, REC_LEN);
        wsprintfW(key, L"clip%d_end", i + 1);    gClips[i].pendTe = (unsigned)Iclamp(INI_INT(key, 0), 0, REC_LEN);
    }
    {   // Song style has its own Synth (default 100%: the song fully replaces your voice)
        wchar_t b[32];
        GetPrivateProfileStringW(L"settings", L"voc_synth_other", L"", b, 32, gIni);
        if (b[0]) gVocSynthSaved = Iclamp(_wtoi(b), 0, 100);
        else if (gVocStyle == VOC_SONG) { gVocSynthSaved = gVocSynth; gVocSynth = 100; }   // from 1.11
        else gVocSynthSaved = 100;
    }
    gRadioPreset  = Iclamp(INI_INT(L"radio_preset", 0), 0, RADIO_N - 1);
    gGateMode     = Iclamp(INI_INT(L"gate_mode", INI_INT(L"gate", 0) ? GATE_VOLUME : GATE_OFF), 0, 3);
    gGateLastMode = Iclamp(INI_INT(L"gate_last_mode", GATE_VOLUME), 1, 3);
    {
        wchar_t b[32];
        GetPrivateProfileStringW(L"settings", L"gate_threshold_db", L"", b, 32, gIni);
        if (!b[0]) gGateThrDb = Iclamp(-INI_INT(L"gate_db", 50), -90, -10);
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
            wsprintfW(key, L"out%d_mode", k + 1);   gRowMode[k] = Iclamp(INI_INT(key, k == 0 ? DEF_MODE0 : DEF_MODEK), 0, MODE_APPS);
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

// ---- writing the settings file in one go ----
// Each WritePrivateProfileString opens, reads and rewrites the whole file; saving hundreds of settings that way is
// slow. While a batch is open, changes collect here and the [settings] section is written once at the end.
#define IB_MAX 4000
static struct { bool on; int n; wchar_t* key[IB_MAX]; wchar_t* val[IB_MAX]; } gIB;
static wchar_t* IbDup(const wchar_t* t)
{
    if (!t) return nullptr;
    size_t l = (size_t)lstrlenW(t) + 1;
    wchar_t* d = (wchar_t*)HeapAlloc(GetProcessHeap(), 0, l * sizeof(wchar_t));
    if (d) memcpy(d, t, l * sizeof(wchar_t));
    return d;
}
static void IbClear() { for (int i = 0; i < gIB.n; i++) { HeapFree(GetProcessHeap(), 0, gIB.key[i]); if (gIB.val[i]) HeapFree(GetProcessHeap(), 0, gIB.val[i]); } gIB.n = 0; gIB.on = false; }
static void IniBatchBegin()
{
    const DWORD cap = 512 * 1024;
    wchar_t* buf = (wchar_t*)HeapAlloc(GetProcessHeap(), 0, cap * sizeof(wchar_t));
    if (!buf) return;
    DWORD got = GetPrivateProfileSectionW(L"settings", buf, cap, gIni);
    if (got < cap - 2) {                        // (too big to read whole: don't batch, so nothing can be lost)
        gIB.n = 0; gIB.on = true;
        for (wchar_t* q = buf; *q && gIB.n < IB_MAX; q += lstrlenW(q) + 1) {
            wchar_t* eq = wcschr(q, L'=');
            if (!eq) continue;
            *eq = 0;
            gIB.key[gIB.n] = IbDup(q); gIB.val[gIB.n] = IbDup(eq + 1);
            if (gIB.key[gIB.n]) gIB.n++;
            *eq = L'=';
        }
        if (gIB.n >= IB_MAX) IbClear();
    }
    HeapFree(GetProcessHeap(), 0, buf);
}
static void IniSet(const wchar_t* k, const wchar_t* v)   // a [settings] value (nullptr removes it)
{
    if (!gIB.on) { WritePrivateProfileStringW(L"settings", k, v, gIni); return; }
    for (int i = 0; i < gIB.n; i++)
        if (!lstrcmpiW(gIB.key[i], k)) { if (gIB.val[i]) HeapFree(GetProcessHeap(), 0, gIB.val[i]); gIB.val[i] = IbDup(v); return; }
    if (!v) return;
    if (gIB.n >= IB_MAX) { WritePrivateProfileStringW(L"settings", k, v, gIni); return; }
    gIB.key[gIB.n] = IbDup(k); gIB.val[gIB.n] = IbDup(v);
    if (gIB.key[gIB.n]) gIB.n++;
}
static void IniBatchEnd()
{
    if (!gIB.on) return;
    size_t len = 2;
    for (int i = 0; i < gIB.n; i++) if (gIB.val[i]) len += lstrlenW(gIB.key[i]) + lstrlenW(gIB.val[i]) + 2;
    wchar_t* buf = (wchar_t*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, len * sizeof(wchar_t));
    if (buf) {
        size_t o = 0;
        for (int i = 0; i < gIB.n; i++) {
            if (!gIB.val[i]) continue;
            int kl = lstrlenW(gIB.key[i]), vl = lstrlenW(gIB.val[i]);
            memcpy(buf + o, gIB.key[i], kl * sizeof(wchar_t)); o += kl; buf[o++] = L'=';
            memcpy(buf + o, gIB.val[i], vl * sizeof(wchar_t)); o += vl; buf[o++] = 0;
        }
        buf[o] = 0;
        WritePrivateProfileSectionW(L"settings", buf, gIni);
        HeapFree(GetProcessHeap(), 0, buf);
    } else {                                    // (out of memory: the slow way)
        for (int i = 0; i < gIB.n; i++) WritePrivateProfileStringW(L"settings", gIB.key[i], gIB.val[i], gIni);
    }
    IbClear();
}

static void LayoutSave(const wchar_t* path);    // (moving things around: defined with the editor)
static void SaveInt(const wchar_t* k, int v)
{
    wchar_t b[32]; wsprintfW(b, L"%d", v);
    IniSet(k, b);
}

// ======================= background picture + pictures on top =======================
#define PICINT(k, d) (int)GetPrivateProfileIntW(L"settings", k, d, gIni)
// One background picture (fitted, then faded toward the theme colour so text stays readable) and up to
// STK_MAX pictures on top that you place yourself (not faded). Any of them can be an animated GIF.
// Loaded with GDI+ (flat API, run-time linked). Frames are decoded once, already at the size they're shown,
// and GIFs never run faster than the frame-rate limit (frames in between are merged, which also saves memory).
// The window background is one pattern brush built from all of this; an animated picture on top only
// redraws its own rectangle, and nothing animates while the window is hidden or minimised.
typedef int (WINAPI* PGpLoad)(const WCHAR*, void**);
typedef int (WINAPI* PGpDispose)(void*);
typedef int (WINAPI* PGpUint)(void*, UINT*);
typedef int (WINAPI* PGpDimList)(void*, GUID*, UINT);
typedef int (WINAPI* PGpFrameCount)(void*, const GUID*, UINT*);
typedef int (WINAPI* PGpSelFrame)(void*, const GUID*, UINT);
typedef int (WINAPI* PGpPropSize)(void*, ULONG, UINT*);
typedef int (WINAPI* PGpProp)(void*, ULONG, UINT, void*);
typedef int (WINAPI* PGpScan0)(INT, INT, INT, INT, BYTE*, void**);
typedef int (WINAPI* PGpCtx)(void*, void**);
typedef int (WINAPI* PGpClear)(void*, DWORD);
typedef int (WINAPI* PGpSetInt)(void*, int);
typedef int (WINAPI* PGpDrawRectI)(void*, void*, INT, INT, INT, INT);
typedef int (WINAPI* PGpDelG)(void*);
static struct GpApi {
    bool ok, tried;
    PGpLoad load; PGpDispose dispose; PGpUint width, height, dimCount; PGpDimList dimList; PGpFrameCount frameCount;
    PGpSelFrame selFrame; PGpPropSize propSize; PGpProp prop; PGpScan0 fromScan0; PGpCtx ctx; PGpClear clear;
    PGpSetInt interp, pixOff; PGpDrawRectI draw; PGpDelG delG;
} gGp;
static bool GpReady()
{
    if (gGp.tried) return gGp.ok;
    gGp.tried = true;
    HMODULE gp = LoadLibraryW(L"gdiplus.dll");
    if (!gp) return false;
    struct StartupInput { UINT32 ver; void* cb; BOOL noThread, noCodecs; };
    typedef int (WINAPI* PStartup)(ULONG_PTR*, const StartupInput*, void*);
    auto startup = (PStartup)(void*)GetProcAddress(gp, "GdiplusStartup");
    #define GPF(field, T, name) gGp.field = (T)(void*)GetProcAddress(gp, name); if (!gGp.field) return false;
    GPF(load, PGpLoad, "GdipLoadImageFromFile") GPF(dispose, PGpDispose, "GdipDisposeImage")
    GPF(width, PGpUint, "GdipGetImageWidth") GPF(height, PGpUint, "GdipGetImageHeight")
    GPF(dimCount, PGpUint, "GdipImageGetFrameDimensionsCount") GPF(dimList, PGpDimList, "GdipImageGetFrameDimensionsList")
    GPF(frameCount, PGpFrameCount, "GdipImageGetFrameCount") GPF(selFrame, PGpSelFrame, "GdipImageSelectActiveFrame")
    GPF(propSize, PGpPropSize, "GdipGetPropertyItemSize") GPF(prop, PGpProp, "GdipGetPropertyItem")
    GPF(fromScan0, PGpScan0, "GdipCreateBitmapFromScan0") GPF(ctx, PGpCtx, "GdipGetImageGraphicsContext")
    GPF(clear, PGpClear, "GdipGraphicsClear") GPF(interp, PGpSetInt, "GdipSetInterpolationMode")
    GPF(pixOff, PGpSetInt, "GdipSetPixelOffsetMode") GPF(draw, PGpDrawRectI, "GdipDrawImageRectI")
    GPF(delG, PGpDelG, "GdipDeleteGraphics")
    #undef GPF
    static ULONG_PTR token = 0;
    StartupInput si = { 1, nullptr, FALSE, FALSE };
    if (!startup || startup(&token, &si, nullptr) != 0) return false;
    gGp.ok = true;
    return true;
}

// Frames are either all kept (cached), or, for GIFs too big for that, streamed: a worker decodes a little
// ahead into a small ring while the window shows them, so memory stays small however long the GIF is.
// The background's frames are faded into the theme colour as they're decoded ("baked"), so showing a frame
// is a plain copy instead of a fade over the whole window every frame.
#define PIC_CACHE_MAX  (160ll << 20)            // bytes of frames one picture may keep; more = stream it
#define PIC_RING_BYTES (64ll << 20)             // a streamed picture's ring of frames decoded ahead
struct PicStream {
    HANDLE th, wake; volatile LONG stop, head, tail; // head: frames decoded so far, tail: frames shown (ring = head - tail)
    void* gp; GUID dim; int nAll, nk, rn, w, h; unsigned bake; bool blocky;
    int* keep; int* kdel;                       // which source frames, and how long each shows
    DWORD* ring; int* rdel;                     // rn frames of w*h, and their times
};
struct PicImg {
    void*  gp;                                  // the file, kept open so it can be decoded again at another size
    int    w0, h0, nAll;                        // its own size and frame count
    GUID   dim;                                 // frame dimension (time, for GIFs)
    int*   delayAll;                            // each frame's delay (ms)
    int    w, h, n, fps;                        // shown frames: size, count, the frame-rate limit used
    int    rw, rh;                              // the size that was asked for (huge sizes are decoded smaller)
    unsigned bake;                              // background: the colour + fade its frames were baked with (0 = none)
    int    uid;                                 // finds it again when its background decode finishes
    struct PicJob* job;                         // decoding in the background (owns gp while it runs)
    bool   want; int wantW, wantH; unsigned wantBake;   // asked for something else while that was running
    DWORD* px;                                  // cached: n frames of w*h premultiplied BGRA
    int*   delay;                               // cached: how long each frame shows (ms)
    PicStream* st;                              // streamed instead
    int    cur; ULONGLONG due; bool shown;      // frame showing and when the next one is due
};
static void PicStreamStop(PicImg& m)            // (waits at most for the frame being decoded)
{
    PicStream* st = m.st;
    if (!st) return;
    m.st = nullptr;
    InterlockedExchange(&st->stop, 1); SetEvent(st->wake);
    WaitForSingleObject(st->th, INFINITE);
    CloseHandle(st->th); CloseHandle(st->wake);
    if (st->ring) HeapFree(GetProcessHeap(), 0, st->ring);
    if (st->rdel) HeapFree(GetProcessHeap(), 0, st->rdel);
    if (st->keep) HeapFree(GetProcessHeap(), 0, st->keep);
    if (st->kdel) HeapFree(GetProcessHeap(), 0, st->kdel);
    HeapFree(GetProcessHeap(), 0, st);
}
static void PicFreeFrames(PicImg& m)
{
    PicStreamStop(m);
    if (m.px) HeapFree(GetProcessHeap(), 0, m.px);
    if (m.delay) HeapFree(GetProcessHeap(), 0, m.delay);
    m.px = nullptr; m.delay = nullptr; m.w = m.h = m.n = 0; m.cur = 0; m.shown = false;
}
static const DWORD* PicCurFrame(const PicImg& m)   // the frame to show now (nullptr: none decoded yet)
{
    if (m.st) return m.st->head > m.st->tail ? m.st->ring + (size_t)m.st->w * m.st->h * (m.st->tail % m.st->rn) : nullptr;
    return m.px ? m.px + (size_t)m.w * m.h * m.cur : nullptr;
}
struct PicJob {                                 // one background decode: everything it needs is its own copy
    volatile LONG orphan;                       // the picture was closed meanwhile: throw the result (and gp) away
    void* gp; GUID dim; int nAll; int* delays; int tw, th, askW, askH, fps, uid; unsigned bake;
    DWORD* px; int* delay; int n;
};
static void PicJobFree(PicJob* j, bool withGp)
{
    if (j->px) HeapFree(GetProcessHeap(), 0, j->px);
    if (j->delay) HeapFree(GetProcessHeap(), 0, j->delay);
    if (j->delays) HeapFree(GetProcessHeap(), 0, j->delays);
    if (withGp && j->gp && gGp.ok) gGp.dispose(j->gp);
    HeapFree(GetProcessHeap(), 0, j);
}
static void PicClose(PicImg& m)
{
    PicFreeFrames(m);                           // (stops a stream first: it uses gp)
    if (m.delayAll) HeapFree(GetProcessHeap(), 0, m.delayAll);
    if (m.job) { InterlockedExchange(&m.job->orphan, 1); m.gp = nullptr; }   // the job disposes of it when done
    if (m.gp && gGp.ok) gGp.dispose(m.gp);
    m = {};
}
static bool PicOpen(PicImg& m, const wchar_t* path)
{
    PicClose(m);
    if (!path || !path[0] || !GpReady()) return false;
    if (gGp.load(path, &m.gp) != 0 || !m.gp) { m.gp = nullptr; return false; }
    static int uids = 0; m.uid = ++uids;
    UINT w = 0, h = 0, dims = 0, n = 1;
    gGp.width(m.gp, &w); gGp.height(m.gp, &h);
    if (!w || !h) { PicClose(m); return false; }
    m.w0 = (int)w; m.h0 = (int)h;
    if (gGp.dimCount(m.gp, &dims) == 0 && dims > 0) {
        GUID list[4]; gGp.dimList(m.gp, list, dims > 4 ? 4 : dims); m.dim = list[0];
        if (gGp.frameCount(m.gp, &m.dim, &n) != 0 || n < 1) n = 1;
    }
    m.nAll = (int)Imin((int)n, 2000);
    m.delayAll = (int*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, m.nAll * sizeof(int));
    if (!m.delayAll) { PicClose(m); return false; }
    for (int i = 0; i < m.nAll; i++) m.delayAll[i] = 100;
    UINT sz = 0;
    if (m.nAll > 1 && gGp.propSize(m.gp, 0x5100, &sz) == 0 && sz > 16) {   // PropertyTagFrameDelay: 1/100 s per frame
        struct PropItem { ULONG id; ULONG len; WORD type; void* value; };
        PropItem* pi = (PropItem*)HeapAlloc(GetProcessHeap(), 0, sz);
        if (pi && gGp.prop(m.gp, 0x5100, sz, pi) == 0) {
            int cnt = Imin((int)(pi->len / 4), m.nAll);
            for (int i = 0; i < cnt; i++) { int d = ((LONG*)pi->value)[i] * 10; m.delayAll[i] = d <= 10 ? 100 : d; }   // 0 / 10 ms: browsers use 100
        }
        if (pi) HeapFree(GetProcessHeap(), 0, pi);
    }
    return true;
}
static void PicCapSize(int* tw, int* th)        // never more than ~6 megapixels a frame (drawn bigger if needed)
{
    const double big = (double)*tw * *th;
    if (big > 6.0e6) { double k = sqrt(6.0e6 / big); *tw = Imax(1, (int)(*tw * k)); *th = Imax(1, (int)(*th * k)); }
}
static int PicKeepList(const int* delays, int nAll, int fps, int* keep, int* kdel)   // frames to show at <= fps
{
    int nk = 0, t = 0, nextAt = 0; const int minMs = fps > 0 ? 1000 / fps : 0;
    for (int i = 0; i < nAll; i++) {
        if (i == 0 || t >= nextAt) { keep[nk] = i; kdel[nk] = 0; nk++; nextAt = t + minMs; }
        kdel[nk - 1] += delays[i];
        t += delays[i];
    }
    for (int k = 0; k < nk; k++) kdel[k] = Imax(kdel[k], 15);
    return nk;
}
static void PicBake(DWORD* p, size_t n, unsigned key)   // over the theme colour, then faded toward it: opaque
{
    const COLORREF bg = key & 0xFFFFFF;
    const int a = (int)((key >> 24) & 0x7F) * 256 / 100;
    const int br = GetRValue(bg), bgc = GetGValue(bg), bb = GetBValue(bg);
    for (size_t i = 0; i < n; i++) {
        const DWORD v = p[i]; const int A = v >> 24;
        int r = (v >> 16) & 255, g = (v >> 8) & 255, b = v & 255;
        if (A < 255) { r += br * (255 - A) / 255; g += bgc * (255 - A) / 255; b += bb * (255 - A) / 255; }
        r = (r * (256 - a) + br * a) >> 8; g = (g * (256 - a) + bgc * a) >> 8; b = (b * (256 - a) + bb * a) >> 8;
        p[i] = 0xFF000000 | (Imin(r, 255) << 16) | (Imin(g, 255) << 8) | Imin(b, 255);
    }
}
static void PicDecodeFrame(void* gp, const GUID& dim, int nAll, int idx, DWORD* out, int tw, int th, bool blocky, unsigned bake)
{
    if (nAll > 1) gGp.selFrame(gp, &dim, (UINT)idx);
    void* bmp = nullptr; void* g = nullptr;
    if (gGp.fromScan0(tw, th, tw * 4, 0x000E200B /* 32bpp PARGB */, (BYTE*)out, &bmp) == 0 && bmp) {
        if (gGp.ctx(bmp, &g) == 0 && g) {
            gGp.clear(g, 0);
            gGp.interp(g, blocky ? 5 /* nearest */ : 7 /* high-quality bicubic */);
            gGp.pixOff(g, blocky ? 4 /* half */ : 2 /* high quality */);
            gGp.draw(g, gp, 0, 0, tw, th);
            gGp.delG(g);
        }
        gGp.dispose(bmp);
    }
    if (bake) PicBake(out, (size_t)tw * th, bake);
}
static void PicJobRun(PicJob* j)                // (worker thread) all kept frames at tw x th
{
    int tw = j->tw, th = j->th;
    PicCapSize(&tw, &th);
    int* keep = (int*)HeapAlloc(GetProcessHeap(), 0, j->nAll * sizeof(int) * 2);
    if (!keep) { j->n = 0; return; }
    int* kdel = keep + j->nAll;
    const int nk = PicKeepList(j->delays, j->nAll, j->fps, keep, kdel);
    j->px = (DWORD*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, (size_t)tw * th * 4 * nk);
    j->delay = (int*)HeapAlloc(GetProcessHeap(), 0, nk * sizeof(int));
    if (!j->px || !j->delay) { j->n = 0; HeapFree(GetProcessHeap(), 0, keep); return; }
    UINT a = 0, b = 0; gGp.width(j->gp, &a); gGp.height(j->gp, &b);
    const bool blocky = tw >= (int)a * 2 && th >= (int)b * 2;   // big enlargements of small (pixel-art) GIFs stay crisp
    for (int k = 0; k < nk && !j->orphan; k++) {
        PicDecodeFrame(j->gp, j->dim, j->nAll, keep[k], j->px + (size_t)tw * th * k, tw, th, blocky, j->bake);
        j->delay[k] = kdel[k];
    }
    HeapFree(GetProcessHeap(), 0, keep);
    j->tw = tw; j->th = th; j->n = nk;
}
static DWORD WINAPI PicJobThread(LPVOID arg)
{
    PicJob* j = (PicJob*)arg;
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_BELOW_NORMAL);   // never in the way of the audio or the window
    PicJobRun(j);
    if (!PostMessageW(gWnd, WM_PIC_DECODED, 0, (LPARAM)j)) PicJobFree(j, j->orphan != 0);
    return 0;
}
static DWORD WINAPI PicStreamThread(LPVOID arg)  // decodes ahead into the ring until told to stop
{
    PicStream* st = (PicStream*)arg;
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_BELOW_NORMAL);
    int next = 0;
    while (!st->stop) {
        if (st->head - st->tail >= st->rn - 1) { WaitForSingleObject(st->wake, 30); continue; }   // ring full: wait
        const int slot = st->head % st->rn;
        PicDecodeFrame(st->gp, st->dim, st->nAll, st->keep[next], st->ring + (size_t)st->w * st->h * slot, st->w, st->h, st->blocky, st->bake);
        st->rdel[slot] = st->kdel[next];
        next = (next + 1) % st->nk;
        InterlockedIncrement(&st->head);
    }
    return 0;
}
// Ask for a picture at tw x th (bake: background colour + fade, 0 for pictures on top): decoded in the background,
// shown when ready (meanwhile the old frames, stretched).
static void PicWant(PicImg& m, int tw, int th, unsigned bake = 0)
{
    if (!m.gp || tw < 1 || th < 1) return;
    if (m.job) { m.want = true; m.wantW = tw; m.wantH = th; m.wantBake = bake; return; }   // one at a time: this next
    if ((m.px || m.st) && m.rw == tw && m.rh == th && m.fps == gGifFps && m.bake == bake) return;
    int cw = tw, ch = th; PicCapSize(&cw, &ch);
    int* keep = (int*)HeapAlloc(GetProcessHeap(), 0, m.nAll * sizeof(int) * 2);
    if (!keep) return;
    int* kdel = keep + m.nAll;
    const int nk = PicKeepList(m.delayAll, m.nAll, gGifFps, keep, kdel);
    const long long frameBytes = (long long)cw * ch * 4;
    if (nk > 1 && frameBytes * nk > PIC_CACHE_MAX) {      // too big to keep: stream it
        PicFreeFrames(m);
        PicStream* st = (PicStream*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(PicStream));
        if (!st) { HeapFree(GetProcessHeap(), 0, keep); return; }
        st->gp = m.gp; st->dim = m.dim; st->nAll = m.nAll; st->nk = nk; st->w = cw; st->h = ch; st->bake = bake;
        st->blocky = cw >= m.w0 * 2 && ch >= m.h0 * 2;
        st->rn = (int)Iclamp((int)(PIC_RING_BYTES / frameBytes), 3, 30);
        st->keep = keep; st->kdel = (int*)HeapAlloc(GetProcessHeap(), 0, nk * sizeof(int));
        st->ring = (DWORD*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, (size_t)frameBytes * st->rn);
        st->rdel = (int*)HeapAlloc(GetProcessHeap(), 0, st->rn * sizeof(int));
        st->wake = CreateEventW(nullptr, FALSE, FALSE, nullptr);
        if (st->kdel) memcpy(st->kdel, kdel, nk * sizeof(int));
        if (!st->kdel || !st->ring || !st->rdel || !st->wake ||
            !(st->th = CreateThread(nullptr, 0, PicStreamThread, st, 0, nullptr))) {
            if (st->wake) CloseHandle(st->wake);
            if (st->ring) HeapFree(GetProcessHeap(), 0, st->ring);
            if (st->rdel) HeapFree(GetProcessHeap(), 0, st->rdel);
            if (st->kdel) HeapFree(GetProcessHeap(), 0, st->kdel);
            HeapFree(GetProcessHeap(), 0, keep); HeapFree(GetProcessHeap(), 0, st);
            return;
        }
        m.st = st; m.w = cw; m.h = ch; m.n = nk; m.rw = tw; m.rh = th; m.fps = gGifFps; m.bake = bake; m.shown = false;
        return;
    }
    HeapFree(GetProcessHeap(), 0, keep);
    PicStreamStop(m);                           // (it used gp; a cached decode needs it now)
    PicJob* j = (PicJob*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(PicJob));
    if (!j) return;
    j->gp = m.gp; j->dim = m.dim; j->nAll = m.nAll; j->tw = tw; j->th = th; j->askW = tw; j->askH = th;
    j->fps = gGifFps; j->uid = m.uid; j->bake = bake;
    j->delays = (int*)HeapAlloc(GetProcessHeap(), 0, m.nAll * sizeof(int));
    if (!j->delays) { HeapFree(GetProcessHeap(), 0, j); return; }
    memcpy(j->delays, m.delayAll, m.nAll * sizeof(int));
    m.job = j; m.want = false;
    HANDLE t = CreateThread(nullptr, 0, PicJobThread, j, 0, nullptr);
    if (t) CloseHandle(t);
    else { m.job = nullptr; PicJobRun(j); PostMessageW(gWnd, WM_PIC_DECODED, 0, (LPARAM)j); m.job = j; }
}
#define STK_MAX 8
struct Sticker { wchar_t path[MAX_PATH]; int x, y, size, opacity; PicImg img; bool stale; };
static Sticker  gStk[STK_MAX];  static int gStkN = 0, gStkSel = 0;
static PicImg   gBase;                          // the background picture
static int      gCW = 0, gCH = 0;               // composite size (the window's client area)
static DWORD*   gBaseBuf = nullptr;             // theme colour + background picture + fade
static HBITMAP  gCompBmp = nullptr; static DWORD* gCompBits = nullptr;   // ... + pictures on top
static bool PicActive() { return gBase.gp != nullptr || gStkN > 0; }
static unsigned BaseBake() { return 0x80000000u | ((unsigned)Iclamp(gPicDim, 0, 95) << 24) | (BgColor() & 0xFFFFFF); }

static void StkRect(const Sticker& s, RECT* r)  // where a picture on top is drawn (client px)
{
    int w = Imax(1, SC(s.img.w0) * s.size / 100), h = Imax(1, SC(s.img.h0) * s.size / 100);
    r->left = SC(s.x); r->top = SC(s.y); r->right = r->left + w; r->bottom = r->top + h;
}
static void BaseTarget(int W, int H, int* tw, int* th, int* dx, int* dy)   // background: decoded size and where it goes
{
    const int w0 = gBase.w0, h0 = gBase.h0;
    switch (gPicFit) {
    case 1:  *tw = W; *th = H; *dx = 0; *dy = 0; break;                                     // stretch
    case 2:  *tw = w0; *th = h0; *dx = (W - w0) / 2; *dy = (H - h0) / 2; break;              // centre
    case 3:  *tw = w0; *th = h0; *dx = 0; *dy = 0; break;                                   // tile
    case 4:  *tw = Imax(1, SC(w0) * gPicSize / 100); *th = Imax(1, SC(h0) * gPicSize / 100);  // placed by you
             *dx = SC(gPicX); *dy = SC(gPicY); break;
    default: {                                                                               // fill (crop)
        double sc = Max((double)W / w0, (double)H / h0);
        *tw = Imax(W, (int)(w0 * sc + 0.5)); *th = Imax(H, (int)(h0 * sc + 0.5));
        *dx = (W - *tw) / 2; *dy = (H - *th) / 2;
    }
    }
}
// src (premultiplied BGRA, sw x sh) over dst at dx,dy scaled to dw x dh, faded to op/256, only inside clip
static void BlitOver(DWORD* dst, int W, int H, const DWORD* src, int sw, int sh, int dx, int dy, int dw, int dh, int op, const RECT& clip)
{
    int x0 = Imax(Imax(dx, 0), (int)clip.left), y0 = Imax(Imax(dy, 0), (int)clip.top);
    int x1 = Imin(Imin(dx + dw, W), (int)clip.right), y1 = Imin(Imin(dy + dh, H), (int)clip.bottom);
    if (x0 >= x1 || y0 >= y1 || dw <= 0 || dh <= 0) return;
    const bool same = dw == sw && dh == sh;
    for (int y = y0; y < y1; y++) {
        const int sy = same ? y - dy : (int)((long long)(y - dy) * sh / dh);
        const DWORD* srow = src + (size_t)sy * sw;
        DWORD* drow = dst + (size_t)y * W;
        for (int x = x0; x < x1; x++) {
            DWORD s = srow[same ? x - dx : (int)((long long)(x - dx) * sw / dw)];
            if (op < 256) {
                s = ((((s & 0x00FF00FF) * op) >> 8) & 0x00FF00FF) | ((((s >> 8) & 0x00FF00FF) * op) & 0xFF00FF00);
            }
            const DWORD a = s >> 24;
            if (a == 0) continue;
            if (a == 255) { drow[x] = s | 0xFF000000; continue; }
            const DWORD d = drow[x], ia = 256 - a;   // channels are 16 bits apart: one multiply does red and blue
            const DWORD rb = (((d & 0x00FF00FF) * ia) >> 8) & 0x00FF00FF;
            const DWORD g  = (((d & 0x0000FF00) * ia) >> 8) & 0x0000FF00;
            drow[x] = 0xFF000000 | ((s & 0x00FFFFFF) + rb + g);
        }
    }
}
static void BlitCopy(DWORD* dst, int W, int H, const DWORD* src, int sw, int sh, int dx, int dy, int dw, int dh, const RECT& clip)
{
    int x0 = Imax(Imax(dx, 0), (int)clip.left), y0 = Imax(Imax(dy, 0), (int)clip.top);
    int x1 = Imin(Imin(dx + dw, W), (int)clip.right), y1 = Imin(Imin(dy + dh, H), (int)clip.bottom);
    if (x0 >= x1 || y0 >= y1 || dw <= 0 || dh <= 0) return;
    const bool same = dw == sw && dh == sh;
    for (int y = y0; y < y1; y++) {
        DWORD* drow = dst + (size_t)y * W;
        if (same) { memcpy(drow + x0, src + (size_t)(y - dy) * sw + (x0 - dx), (size_t)(x1 - x0) * 4); continue; }
        const DWORD* srow = src + (size_t)((long long)(y - dy) * sh / dh) * sw;
        for (int x = x0; x < x1; x++) drow[x] = srow[(long long)(x - dx) * sw / dw];
    }
}
static void StkEnsureDecoded(Sticker& s)
{
    RECT r; StkRect(s, &r);
    PicWant(s.img, r.right - r.left, r.bottom - r.top);
    s.stale = false;
}
static void PicComposeBase()                    // theme colour, background picture, fade
{
    const COLORREF bg = BgColor();
    const DWORD bgpx = 0xFF000000 | (GetRValue(bg) << 16) | (GetGValue(bg) << 8) | GetBValue(bg);
    for (int i = 0; i < gCW * gCH; i++) gBaseBuf[i] = bgpx;
    const DWORD* f = gBase.gp ? PicCurFrame(gBase) : nullptr;
    if (!f) return;
    int tw, th, dx, dy; BaseTarget(gCW, gCH, &tw, &th, &dx, &dy);
    RECT all = { 0, 0, gCW, gCH };
    if (gBase.bake) {                           // already faded in when decoded: just copy it in
        if (gPicFit == 3) { for (int y = 0; y < gCH; y += th) for (int x = 0; x < gCW; x += tw) BlitCopy(gBaseBuf, gCW, gCH, f, gBase.w, gBase.h, x, y, tw, th, all); }
        else BlitCopy(gBaseBuf, gCW, gCH, f, gBase.w, gBase.h, dx, dy, tw, th, all);
        return;
    }
    if (gPicFit == 3) { for (int y = 0; y < gCH; y += th) for (int x = 0; x < gCW; x += tw) BlitOver(gBaseBuf, gCW, gCH, f, gBase.w, gBase.h, x, y, tw, th, 256, all); }
    else BlitOver(gBaseBuf, gCW, gCH, f, gBase.w, gBase.h, dx, dy, tw, th, 256, all);
    const int a = Iclamp(gPicDim, 0, 95) * 256 / 100;   // fade toward the theme colour so text stays readable
    const DWORD br = GetRValue(bg) * a, bgc = GetGValue(bg) * a, bb = GetBValue(bg) * a;
    BYTE* p = (BYTE*)gBaseBuf;
    for (int i = 0; i < gCW * gCH; i++, p += 4) {
        p[0] = (BYTE)((p[0] * (256 - a) + bb) >> 8);
        p[1] = (BYTE)((p[1] * (256 - a) + bgc) >> 8);
        p[2] = (BYTE)((p[2] * (256 - a) + br) >> 8);
    }
}
static void PicComposeTop(const RECT& r)        // background + pictures on top, inside r
{
    RECT c = { Imax((int)r.left, 0), Imax((int)r.top, 0), Imin((int)r.right, gCW), Imin((int)r.bottom, gCH) };
    if (c.left >= c.right || c.top >= c.bottom) return;
    for (int y = c.top; y < c.bottom; y++)
        memcpy(gCompBits + (size_t)y * gCW + c.left, gBaseBuf + (size_t)y * gCW + c.left, (c.right - c.left) * 4);
    for (int i = 0; i < gStkN; i++) {
        Sticker& s = gStk[i];
        const DWORD* f = PicCurFrame(s.img);
        if (!f) continue;
        RECT sr; StkRect(s, &sr);
        BlitOver(gCompBits, gCW, gCH, f, s.img.w, s.img.h,
                 sr.left, sr.top, sr.right - sr.left, sr.bottom - sr.top, Iclamp(s.opacity, 5, 100) * 256 / 100, c);
    }
    GdiFlush();
}
static void PicMakeBrush()
{
    if (gBrPicture) { DeleteObject(gBrPicture); gBrPicture = nullptr; }
    if (gCompBmp) gBrPicture = CreatePatternBrush(gCompBmp);
}
static void PicFreeComposite()
{
    if (gBrPicture) { DeleteObject(gBrPicture); gBrPicture = nullptr; }
    if (gCompBmp) { DeleteObject(gCompBmp); gCompBmp = nullptr; gCompBits = nullptr; }
    if (gBaseBuf) { HeapFree(GetProcessHeap(), 0, gBaseBuf); gBaseBuf = nullptr; }
    gCW = gCH = 0;
}
static void PicAnimTimer();
static void PictureRebuild()                    // everything, at the window's size
{
    if (!gWnd) return;
    if (!PicActive()) { PicFreeComposite(); PicAnimTimer(); return; }
    RECT rc; GetClientRect(gWnd, &rc);
    const int W = rc.right, H = rc.bottom;
    if (W <= 0 || H <= 0) return;
    if (W != gCW || H != gCH || !gCompBmp) {
        PicFreeComposite();
        BITMAPINFO bi = {}; bi.bmiHeader.biSize = sizeof(bi.bmiHeader); bi.bmiHeader.biWidth = W; bi.bmiHeader.biHeight = -H;
        bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32;
        void* bits = nullptr;
        gCompBmp = CreateDIBSection(nullptr, &bi, DIB_RGB_COLORS, &bits, nullptr, 0);
        gBaseBuf = (DWORD*)HeapAlloc(GetProcessHeap(), 0, (size_t)W * H * 4);
        if (!gCompBmp || !gBaseBuf) { PicFreeComposite(); return; }
        gCompBits = (DWORD*)bits; gCW = W; gCH = H;
    }
    if (gBase.gp) { int tw, th, dx, dy; BaseTarget(W, H, &tw, &th, &dx, &dy); PicWant(gBase, tw, th, BaseBake()); }
    for (int i = 0; i < gStkN; i++) StkEnsureDecoded(gStk[i]);
    PicComposeBase();
    RECT all = { 0, 0, W, H };
    PicComposeTop(all);
    PicMakeBrush();
    PicAnimTimer();
}
static bool PictureLoad(const wchar_t* path)    // the background picture (empty path = none)
{
    PicClose(gBase);
    return path && path[0] && PicOpen(gBase, path);
}
static void PicRedraw(const RECT* r)            // repaint the window (or part of it) and its controls, now
{
    RedrawWindow(gWnd, r, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_ALLCHILDREN | RDW_UPDATENOW);
}
static void StkRefresh(const RECT* also)        // pictures on top changed: re-compose and repaint just there
{
    if (!gCompBmp) { PictureRebuild(); PicRedraw(nullptr); return; }
    RECT u = {}; if (also) u = *also;
    for (int i = 0; i < gStkN; i++) { RECT r; StkRect(gStk[i], &r); UnionRect(&u, &u, &r); }
    PicComposeTop(u);
    PicMakeBrush();
    PicRedraw(&u);
}
// ---- animation ----
#define TIMER_PICANIM  41
#define TIMER_STKSIZE  42
static void PicAnimTimer()                      // run the animation timer only while something animates
{
    bool any = gBase.n > 1;
    for (int i = 0; i < gStkN; i++) if (gStk[i].img.n > 1) any = true;
    // (Labels, checkboxes and owner-drawn controls paint off-screen themselves, so the whole window no longer
    //  needs WS_EX_COMPOSITED while a GIF plays, which made every frame repaint everything.)
    // Frames are shown when they're due, checked every 5 ms with Windows' timer made precise (1 ms) only while
    // something animates: the default ~16 ms steps make GIF timing uneven.
    static bool fine = false;
    typedef UINT (WINAPI* PTimePeriod)(UINT);
    static HMODULE wm = LoadLibraryW(L"winmm.dll");
    static PTimePeriod begin = wm ? (PTimePeriod)(void*)GetProcAddress(wm, "timeBeginPeriod") : nullptr;
    static PTimePeriod end   = wm ? (PTimePeriod)(void*)GetProcAddress(wm, "timeEndPeriod") : nullptr;
    if (any && !fine && begin) { begin(1); fine = true; }
    if (!any && fine && end)   { end(1); fine = false; }
    if (any) SetTimer(gWnd, TIMER_PICANIM, 5, nullptr);
    else KillTimer(gWnd, TIMER_PICANIM);
}
static ULONGLONG PicNow()                       // ms, precise (GetTickCount64 moves in ~16 ms steps)
{
    static LARGE_INTEGER f = {}; if (!f.QuadPart) QueryPerformanceFrequency(&f);
    LARGE_INTEGER c; QueryPerformanceCounter(&c);
    return (ULONGLONG)(c.QuadPart * 1000 / f.QuadPart);
}
static bool PicAdvance(PicImg& m, ULONGLONG now)
{
    if (PicStream* st = m.st) {                 // streamed: move on when the next frame is decoded and due
        if (st->head < 1) return false;
        if (!m.shown) { m.shown = true; m.due = now + st->rdel[st->tail % st->rn]; return true; }
        if (now < m.due) return false;
        if (st->head - st->tail < 2) return false;           // the decoder is behind: hold this frame a moment
        InterlockedIncrement(&st->tail); SetEvent(st->wake);
        m.due = now - m.due > 250 ? now + st->rdel[st->tail % st->rn] : m.due + st->rdel[st->tail % st->rn];
        return true;
    }
    if (m.n <= 1 || now < m.due) return false;
    if (now - m.due > 250) { m.cur = (m.cur + 1) % m.n; m.due = now + m.delay[m.cur]; return true; }   // was paused / hidden
    int steps = 0;
    while (now >= m.due && steps++ < m.n) { m.cur = (m.cur + 1) % m.n; m.due += m.delay[m.cur]; }   // keeps its speed
    return true;
}
static void PicAnimTick()
{
    if (!gWnd || !IsWindowVisible(gWnd) || IsIconic(gWnd) || !gCompBmp) return;   // nobody can see it
    if (gGifPauseBg && GetForegroundWindow() != gWnd) return;
    const ULONGLONG now = PicNow();
    if (PicAdvance(gBase, now)) {               // the background moved: everything changes
        for (int i = 0; i < gStkN; i++) PicAdvance(gStk[i].img, now);
        PicComposeBase();
        RECT all = { 0, 0, gCW, gCH };
        PicComposeTop(all); PicMakeBrush(); PicRedraw(nullptr);
        return;
    }
    RECT u = {}; bool any = false;
    for (int i = 0; i < gStkN; i++)
        if (PicAdvance(gStk[i].img, now)) { RECT r; StkRect(gStk[i], &r); UnionRect(&u, &u, &r); any = true; }
    if (!any) return;
    PicComposeTop(u); PicMakeBrush(); PicRedraw(&u);
}
static void OnPicDecoded(PicJob* j)
{
    if (j->orphan) { PicJobFree(j, true); return; }
    PicImg* m = gBase.uid == j->uid && gBase.job == j ? &gBase : nullptr;
    int stk = -1;
    for (int i = 0; i < gStkN && !m; i++) if (gStk[i].img.uid == j->uid && gStk[i].img.job == j) { m = &gStk[i].img; stk = i; }
    if (!m) { PicJobFree(j, true); return; }
    m->job = nullptr;
    if (j->n > 0 && j->px) {                    // swap in the new frames
        PicFreeFrames(*m);
        m->px = j->px; m->delay = j->delay; j->px = nullptr; j->delay = nullptr;
        m->w = j->tw; m->h = j->th; m->rw = j->askW; m->rh = j->askH; m->n = j->n; m->fps = j->fps; m->bake = j->bake;
        m->cur = 0; m->due = PicNow() + m->delay[0];
    }
    PicJobFree(j, false);
    if (m->want) { m->want = false; PicWant(*m, m->wantW, m->wantH, m->wantBake); }
    if (stk >= 0 && gCompBmp) { StkRefresh(nullptr); PicAnimTimer(); }
    else { PictureRebuild(); PicRedraw(nullptr); }
}

// ---- pictures on top: add / remove / save ----
static bool StkAdd(const wchar_t* path)
{
    if (gStkN >= STK_MAX) return false;
    Sticker& s = gStk[gStkN];
    s = {};
    if (!PicOpen(s.img, path)) return false;
    lstrcpynW(s.path, path, MAX_PATH);
    int big = Imax(s.img.w0, s.img.h0);
    s.size = Iclamp(big > 160 ? 16000 / big : 100, 5, 400);   // start about 160 px across
    s.opacity = 100;
    s.x = 300 + (gStkN % 4) * 24; s.y = 90 + (gStkN % 4) * 24;
    gStkN++;
    return true;
}
static void StkRemove(int i)
{
    if (i < 0 || i >= gStkN) return;
    PicClose(gStk[i].img);
    for (int k = i; k < gStkN - 1; k++) gStk[k] = gStk[k + 1];
    gStk[gStkN - 1] = {};
    gStkN--;
    if (gStkSel >= gStkN) gStkSel = Imax(0, gStkN - 1);
}
static void StkLoadAll()                        // from the settings file
{
    for (int i = gStkN - 1; i >= 0; i--) StkRemove(i);
    int n = Iclamp(PICINT(L"pic_count", 0), 0, STK_MAX);
    for (int i = 0; i < n; i++) {
        wchar_t k[32], path[MAX_PATH];
        wsprintfW(k, L"pic_%d_path", i); GetPrivateProfileStringW(L"settings", k, L"", path, MAX_PATH, gIni);
        if (!StkAdd(path)) continue;
        Sticker& s = gStk[gStkN - 1];
        wsprintfW(k, L"pic_%d_x", i);       s.x = Iclamp(PICINT(k, s.x), -2000, 4000);
        wsprintfW(k, L"pic_%d_y", i);       s.y = Iclamp(PICINT(k, s.y), -2000, 4000);
        wsprintfW(k, L"pic_%d_size", i);    s.size = Iclamp(PICINT(k, s.size), 5, 400);
        wsprintfW(k, L"pic_%d_opacity", i); s.opacity = Iclamp(PICINT(k, 100), 5, 100);
    }
}
static void StkSaveAll()
{
    SaveInt(L"pic_count", gStkN);
    for (int i = 0; i < STK_MAX; i++) {
        wchar_t k[32];
        wsprintfW(k, L"pic_%d_path", i); IniSet(k, i < gStkN ? gStk[i].path : nullptr);
        const wchar_t* names[] = { L"x", L"y", L"size", L"opacity" };
        for (int f = 0; f < 4; f++) {
            wsprintfW(k, L"pic_%d_%s", i, names[f]);
            if (i < gStkN) SaveInt(k, f == 0 ? gStk[i].x : f == 1 ? gStk[i].y : f == 2 ? gStk[i].size : gStk[i].opacity);
            else IniSet(k, nullptr);
        }
    }
}


static void SaveSettings()
{
    IniBatchBegin();                            // everything below is written to the file in one go (IniBatchEnd)
    for (Range& r : gRanges) SaveInt(r.key, *r.var);
    SaveInt(L"hotkey", gHotkeys[0]); SaveInt(L"hotkey2", gHotkeys[1]); SaveInt(L"hotkey3", gHotkeys[2]);
    SaveInt(L"toggle", gToggleMode);
    SaveInt(L"gate", gGateMode != GATE_OFF); SaveInt(L"talkover", gTalkOver);
    SaveInt(L"gate_mode", gGateMode); SaveInt(L"gate_last_mode", gGateLastMode); SaveInt(L"ns_on", gNsOn);
    SaveInt(L"voc_style", gVocStyle); SaveInt(L"voc_key", gVocKey); SaveInt(L"voc_scale", gVocScale); SaveInt(L"voc_range", gVocRange);
    IniSet(L"voc_song_app", gSongApp);
    IniSet(L"voc_song_file", gSongFile);
    SaveInt(L"voc_song_use_file", gSongUseFile);
    SaveInt(L"voc_synth_other", gVocSynthSaved);
    SaveInt(L"pad_master", gPadMaster);
    for (int i = 0; i < PAD_N; i++) {
        wchar_t key[32];
        wsprintfW(key, L"pad%d_file", i + 1);   IniSet(key, gPadFile[i]);
        wsprintfW(key, L"pad%d_volume", i + 1); SaveInt(key, gPads[i].vol);
    }
    SaveInt(L"rec_seconds", gRecSeconds);
    SaveInt(L"pad_page", gPadBank);
    SaveInt(L"push_to_talk_mode", gPttMode); SaveInt(L"overlay", gOverlayOn); SaveInt(L"hotkey_beeps", gBeeps);
    SaveInt(L"overlay_x", gOverlayX); SaveInt(L"overlay_y", gOverlayY);
    SaveInt(L"ui_scale", gUiScale); SaveInt(L"compact", gCompact); SaveInt(L"command_line_control", gCmdLine);
    SaveInt(L"settings_subtab", gSetSub);
    for (int i = 0; i < USERCOL_N; i++) { wchar_t k[32]; wsprintfW(k, L"color_custom_%d", i); SaveInt(k, (int)gUserCol[i]); }
    IniSet(L"background_picture", gPicPath);
    SaveInt(L"background_fit", gPicFit); SaveInt(L"background_dim", gPicDim);
    SaveInt(L"background_x", gPicX); SaveInt(L"background_y", gPicY); SaveInt(L"background_size", gPicSize);
    SaveInt(L"gif_fps_limit", gGifFps); SaveInt(L"gif_pause_in_background", gGifPauseBg);
    StkSaveAll();
    LayoutSave(gIni);
    IniSet(L"font", gFontName);
    SaveInt(L"font_px", gFontPx);
    SaveInt(L"window_opacity", gOpacity);
    SaveInt(L"fx_hotkey_hold", gFxHold[0]);
    for (int g = 0; g < FX_GROUPS; g++) { wchar_t k[64]; wsprintfW(k, L"%s_hold", gFxGroups[g].hotkeyKey); SaveInt(k, gFxHold[1 + g]); }
    ProfileKeysSave();
    IniSet(L"profile_current", gProfCur >= 0 ? gProfNames[gProfCur] : L"");
    SaveInt(L"pads_through_fx", gPadsFx);
    SaveInt(L"clips_through_fx", gClipsFx);
    SaveInt(L"clip_auto_trim", gClipAutoTrim);
    SaveInt(L"random_lag", gRandLagOn);
    SaveInt(L"remote_on", gWsOn); SaveInt(L"remote_port", gWsPort); IniSet(L"remote_password", gWsPass);
    SaveInt(L"feat_lag", gFeatLag); SaveInt(L"feat_voicefx", gFeatFx); SaveInt(L"feat_soundboard", gFeatSound); SaveInt(L"feat_clips", gFeatClips);
    SaveInt(L"random_lag_every_s", gRandLagSec);

    SaveInt(L"repeat_word_times", gRepeatN);
    IniSet(L"tts_voice", gTtsVoice);
    SaveInt(L"tts_accent", gTtsAccent);
    for (int c = 0; c < CH_MAX; c++) {
        wchar_t k[32];
        wsprintfW(k, L"ch_%d_type", c);   SaveInt(k, gCh[c].type);
        wsprintfW(k, L"ch_%d_src", c);    IniSet(k, gCh[c].src);
        wsprintfW(k, L"ch_%d_db", c);     SaveInt(k, gCh[c].db10);
        wsprintfW(k, L"ch_%d_duck", c);   SaveInt(k, gCh[c].duck);
        wsprintfW(k, L"ch_%d_color", c);  SaveInt(k, gCh[c].color);
        wsprintfW(k, L"ch_%d_name", c);   IniSet(k, gCh[c].name);
        wsprintfW(k, L"ch_%d_holdtalk", c); SaveInt(k, gCh[c].holdTalk);
        wsprintfW(k, L"ch_%d_mute", c);   SaveInt(k, gCh[c].mute);
        wsprintfW(k, L"ch_%d_routes", c); SaveInt(k, (int)gCh[c].routes);
    }
    for (int k = 0; k < MAX_OUT; k++) { wchar_t key[24]; wsprintfW(key, L"out_%d_mute", k); SaveInt(key, gOutMute[k]); } SaveInt(L"tts_volume", gTtsVol);
    SaveInt(L"mixer_duck_db", gDuckDb); SaveInt(L"mixer_key_step", gMixStep);
    for (int c = 0; c < CH_MAX; c++) MixMemStore(c);   // (remember each app's settings for next time)
    for (int k = 0; k < MAX_OUT; k++) { wchar_t key[24]; wsprintfW(key, L"out_%d_name", k); IniSet(key, gOutName[k]); }
    for (int c = 0; c < CH_MAX; c++)  { wchar_t key[24]; wsprintfW(key, L"ch_%d_width", c);  SaveInt(key, gChW[c]); }
    for (int k = 0; k < MAX_OUT; k++) { wchar_t key[24]; wsprintfW(key, L"out_%d_width", k); SaveInt(key, gOutW[k]); }
    SaveInt(L"tts_speed", gTtsRate); SaveInt(L"tts_pitch", gTtsPitch); SaveInt(L"tts_room", gTtsRoom);
    SaveInt(L"tts_pauses", gTtsPause); SaveInt(L"tts_natural", gTtsNatural);
    SaveInt(L"fx_echo_style", gEchoStyle);
    SaveInt(L"fx_harm_style", gHarmStyle);
    SaveInt(L"beat_sync", gBeatSync); SaveInt(L"bpm", gBpm); SaveInt(L"beat_division", gBeatDiv);
    SaveInt(L"pitch_dive_semitones", gDiveSemis);
    SaveInt(L"broadcast_voice", gBroadcast);
    SaveInt(L"fx_harm_mute", gHarmMute);
    SaveInt(L"mic_subtab", gMicSub);
    SaveInt(L"fx_dist_style", gDistStyle);
    SaveInt(L"fx_chorus_style", gChoStyle);
    SaveInt(L"fx_muffle_style", gMufStyle);
    SaveInt(L"fx_subtab", gFxSub);
    SaveInt(L"rec_source", gRecSource);
    SaveInt(L"clip_master", gClipMaster);
    SaveInt(L"clip_page", gClipBank); SaveInt(L"clip_separate_tracks", gClipSeparate); SaveInt(L"clip_replace_oldest", gClipReplace);
    SaveInt(L"pads_one_at_a_time", gPadChoke); SaveInt(L"pads_duck_voice", gPadDuck); SaveInt(L"always_hear_sounds_on", gHearOut); SaveInt(L"clip_stamp_next", (int)gClipStampNext);
    for (int i = 0; i < PAD_N; i++) {
        wchar_t key[32]; const Pad& p = gPads[i];
        wsprintfW(key, L"pad%d_mode", i + 1);     SaveInt(key, p.mode);
        wsprintfW(key, L"pad%d_speed", i + 1);    SaveInt(key, p.speed ? p.speed : 100);
        wsprintfW(key, L"pad%d_pitch", i + 1);    SaveInt(key, p.pitch);
        wsprintfW(key, L"pad%d_fade_in", i + 1);  SaveInt(key, p.fadeInMs);
        wsprintfW(key, L"pad%d_fade_out", i + 1); SaveInt(key, p.fadeOutMs);
        wsprintfW(key, L"pad%d_name", i + 1);     IniSet(key, gPadName[i]);
        wsprintfW(key, L"pad%d_color", i + 1);    SaveInt(key, (int)gPadColor[i]);
    }
    for (int i = 0; i < CLIP_N; i++) {
        wchar_t key[32];
        const Clip& c = gClips[i];
        wsprintfW(key, L"clip%d_pinned", i + 1); SaveInt(key, gClipPinned[i]);
        wsprintfW(key, L"clip%d_stamp", i + 1);  SaveInt(key, (int)gClipStamp[i]);
        bool loaded = c.base != nullptr;
        wsprintfW(key, L"clip%d_file", i + 1);   IniSet(key, gPadFile[CLIP0 + i]);
        wsprintfW(key, L"clip%d_volume", i + 1); SaveInt(key, gPads[CLIP0 + i].vol);
        wsprintfW(key, L"clip%d_start", i + 1);  SaveInt(key, (int)(loaded ? c.ts : c.pendTs));
        wsprintfW(key, L"clip%d_end", i + 1);    SaveInt(key, (int)(loaded ? (c.te >= c.baseLen ? 0 : c.te) : c.pendTe));
    }
    SaveInt(L"radio_preset", gRadioPreset);
    SaveInt(L"buffer", gBufIdx); SaveInt(L"exclusive", gExclusive); SaveInt(L"hide_from_share", gHideShare);
    SaveInt(L"hotkey_popup", gShowOsd); SaveInt(L"always_on_top", gTopMost); SaveInt(L"autostart", gAutoStart);
    SaveInt(L"theme", gThemeMode); SaveInt(L"color_theme", gColorTheme); SaveInt(L"color_theme_custom", (int)gCustomAccent); SaveInt(L"update_on_start", gUpdateOnStart);
    SaveInt(L"fx_on", gFxOn);
    for (int slot = 0; slot < KEY_SLOTS; slot++) {
        wchar_t b[64];
        if (!FxKeyIniName(slot)) continue;
        wsprintfW(b, L"%d,%d,%d", gFxKeys[slot][0], gFxKeys[slot][1], gFxKeys[slot][2]);
        IniSet(FxKeyIniName(slot), b);
    }
    for (FxGroup& g : gFxGroups) SaveInt(g.key, *g.on);
    for (Knob& k : gKnobs) SaveInt(k.key, *k.var);
    IniSet(L"update_repo", gUpdateRepo);
    wchar_t name[512], key[32];
    SelectedName(IDC_MIC, gCapDevs, gCapCount, name, 512);
    IniSet(L"mic", name);
    SaveInt(L"out_count", gRows);
    for (int k = 0; k < gRows; k++) {
        SelectedName(IDC_ROWDEV + k, gPlayDevs, gPlayCount, name, 512);
        wsprintfW(key, L"out%d_device", k + 1); IniSet(key, name);
        wsprintfW(key, L"out%d_mode", k + 1);   SaveInt(key, gRowMode[k]);
        wsprintfW(key, L"out%d_volume", k + 1); SaveInt(key, gRowVol[k]);
    }
    IniBatchEnd();
}

// ======================= audio start/stop =======================
static void NotifyCallback(const ma_device_notification* n)
{
    // A device was unplugged or disabled. An extra output: reopen just that one (the rest keep playing).
    // Output 1 / the mic: let the window restart audio.
    if (n->type != ma_device_notification_type_stopped || gStopping || !gWantRunning) return;
    for (int k = 1; k < MAX_OUT; k++)
        if (n->pDevice == &gExtraDev[k]) { PostMessageW(gWnd, WM_OUTPUT_LOST, (WPARAM)k, 0); return; }
    PostMessageW(gWnd, WM_DEVICE_LOST, 0, 0);
}

static int ComboIndex(int id) { return (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0) - 1; }

// "Hide from screen share": Discord (and OBS, recorders...) record what apps play through Windows' shared
// audio mixer. A stream opened in exclusive mode skips that mixer, so it can't be recorded. We only do this
// for virtual cables (VB-Cable, VoiceMeeter): locking real speakers would mute every other app.
static bool RowIsCable(int k)
{
    int i = ComboIndex(IDC_ROWDEV + k);
    if (i < 0 || i >= (int)gPlayCount) return false;
    wchar_t n[512];
    Widen(gPlayDevs[i].name, n, 512);
    return ContainsNoCase(n, L"CABLE") || ContainsNoCase(n, L"VB-Audio") || ContainsNoCase(n, L"VoiceMeeter");
}

static bool RowHidden(int k) { return gHideShare && RowIsCable(k); }
static unsigned gHideFailed = 0;                // outputs (bits) that couldn't be locked, so play normally

static bool StartExtraOutput(int k)
{
    ma_device_config cfg = ma_device_config_init(ma_device_type_playback);
    cfg.playback.format    = ma_format_f32;
    cfg.playback.channels  = 2;
    cfg.sampleRate         = RATE;
    cfg.periodSizeInFrames = BUFFERS[gBufIdx];
    cfg.performanceProfile = ma_performance_profile_low_latency;
    cfg.dataCallback       = ExtraOutputCallback;
    cfg.resampling.linear.lpfOrder = MA_MAX_FILTER_ORDER;
    cfg.notificationCallback = NotifyCallback;
    cfg.pUserData          = (void*)(INT_PTR)k;
    int i = ComboIndex(IDC_ROWDEV + k);
    if (i >= 0 && i < (int)gPlayCount) cfg.playback.pDeviceID = &gPlayDevs[i].id;

    ringW[k] = ringR[k] = 0;
    gExtPrimed[k] = false; gExtL[k] = gExtR[k] = 0;
    bool hide = RowHidden(k);
    if (hide) cfg.playback.shareMode = ma_share_mode_exclusive;
    ma_result r = ma_device_init(&gCtx, &cfg, &gExtraDev[k]);
    if (r != MA_SUCCESS && hide) {             // the cable wouldn't lock: play normally instead of going silent
        gHideFailed |= 1u << k;
        cfg.playback.shareMode = ma_share_mode_shared;
        r = ma_device_init(&gCtx, &cfg, &gExtraDev[k]);
    }
    if (r != MA_SUCCESS) return false;
    if (ma_device_start(&gExtraDev[k]) != MA_SUCCESS) { ma_device_uninit(&gExtraDev[k]); return false; }
    gExtraRunning[k] = true;
    ringOn[k] = true;
    return true;
}

static void StopDevices()
{
    gStopping = true;
    ChanStopAll();
    for (int k = 0; k < MAX_OUT; k++) ringOn[k] = false;
    if (gRunning) { ma_device_uninit(&gDev); gRunning = false; }
    for (int k = 0; k < MAX_OUT; k++)
        if (gExtraRunning[k]) { ma_device_uninit(&gExtraDev[k]); gExtraRunning[k] = false; }
    if (gSongRunning) { SongDevStop(); gSongRunning = false; }
    if (gRecRunning)  { RecDevStop();  gRecRunning = false; }
    gSongRetryNow = true;
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
    cfg.resampling.linear.lpfOrder = MA_MAX_FILTER_ORDER;   // cleanest resampling if a device isn't at 48 kHz
    cfg.notificationCallback = NotifyCallback;
    if (gExclusive) {
        cfg.capture.shareMode  = ma_share_mode_exclusive;
        cfg.playback.shareMode = ma_share_mode_exclusive;
    }
    gHideFailed = 0;
    const bool hide1 = !gExclusive && RowHidden(0);
    if (hide1) cfg.playback.shareMode = ma_share_mode_exclusive;   // output 1 locked, mic stays shared
    int mi = ComboIndex(IDC_MIC), oi = ComboIndex(IDC_ROWDEV);
    if (mi >= 0 && mi < (int)gCapCount)  cfg.capture.pDeviceID  = &gCapDevs[mi].id;
    if (oi >= 0 && oi < (int)gPlayCount) cfg.playback.pDeviceID = &gPlayDevs[oi].id;

    memset(hist, 0, sizeof(hist));
    wpos = 0; frozenLen = 1; looping = false; toggled = false; prevDown = false;
    MicReset();
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
    if (!ok && hide1) {                         // couldn't lock output 1: open it normally
        gHideFailed |= 1u;
        cfg.playback.shareMode = ma_share_mode_shared;
        ok = ma_device_init(&gCtx, &cfg, &gDev) == MA_SUCCESS;
    }
    if (ok && ma_device_start(&gDev) != MA_SUCCESS) { ma_device_uninit(&gDev); ok = false; }
    if (!ok) {
        StopDevices();
        if (!quiet) { gWantRunning = false; MessageBoxW(gWnd, err, L"Lag Effect", MB_ICONWARNING); }
        return false;
    }
    gRunning = true;
    ChanStartAll();                             // the mixer's apps / devices
    if (gHideFailed && !quiet) {
        wchar_t list[64] = L"";
        for (int k = 0; k < MAX_OUT; k++)
            if (gHideFailed & (1u << k)) { wchar_t n[8]; wsprintfW(n, list[0] ? L", %d" : L"%d", k + 1); lstrcatW(list, n); }
        wchar_t msg[700];
        wsprintfW(msg, L"Couldn't hide output %s from screen shares, so it's playing normally (people may hear you twice "
                       L"when you share your whole screen).\n\n"
                       L"Usually another app is also playing into that cable. Or, in Windows Sound settings > Playback > "
                       L"CABLE Input > Properties > Advanced, tick \"Allow applications to take exclusive control\". "
                       L"A bigger buffer (Settings tab) can help too.", list);
        MessageBoxW(gWnd, msg, L"Lag Effect - Hide from screen share", MB_ICONWARNING);
    }
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
// Controls also belong to a page (tab): Main, Mic, Voice FX, Settings. Only the current page is shown.
#define CLIENT_W  560
#define BASE_H    592                          // window height with one output
#define COMPACT_H 84                           // compact mode: status + a few buttons
#define ROW_Y0    134
#define ROW_H     30
#define TAB_COUNT 7
#define TAB_SHOWN TAB_COUNT
static const int TAB_ORDER[TAB_SHOWN] = { 0, 6, 1, 2, 3, 4, 5 };   // left to right (Mixer sits after Main)
enum { PAGE_MAIN = 0, PAGE_MIC = 1, PAGE_FX = 2, PAGE_SOUND = 3, PAGE_CLIPS = 4, PAGE_SETTINGS = 5, PAGE_MIXER = 6 };
static bool PageOn(int page)                    // Voice FX, Soundboard and Clips only exist while their feature is on
{
    return page == PAGE_FX ? gFeatFx : page == PAGE_SOUND ? gFeatSound : page == PAGE_CLIPS ? gFeatClips : true;
}

struct Section { int x, y, w, h; const wchar_t* title; bool shifts; int page; int sub; int ox, oy; int feat; };   // feat: shown only with that feature on   // ox/oy: moved by you (design px)
struct Framed  { HWND edit, ud; };
struct Paged   { HWND h; int page; int sub; int feat; };   // sub: Voice FX sub-tab (-1 = every sub-tab)
// Every control's position as laid out (scaled), how far FitText moved / widened it, and how far you moved it.
// PlaceAll puts each control at: layout + FitText + (moves with the output list) + your offset + its section's offset.
struct Design  {
    HWND h; int x, y, w, ht, page, sub, dx, dw;
    int  rx, ry;                                // layout position in design px (unscaled): names it in saved layouts
    bool shifted, combo;                        // moves down as outputs are added / is a dropdown (height = list)
    HWND ud; int udx, udy;                      // number box: its arrows and where they sit relative to it
    int  sec, ox, oy;                           // the section it's in (-1 none), your offset (design px)
    int  s0, x0, y0, w0, ht0, hh0, ww0, udx0, udy0, udw0, udh0;   // (resizing) its size at the UI size s0, kept so sizes never drift
    bool free;                                  // placed by its own code (the Mixer's strips), not from the layout
};
#define MAX_DESIGN 1400
static void LayoutSave(const wchar_t* path);
static bool LayoutLoad(const wchar_t* path, bool apply);
static void EdFollow();
static Design  gDesign[MAX_DESIGN];  static int gDesignN = 0;
#define MAX_SECTIONS 48
#define MAX_FRAMED   48
#define MAX_PAGED    800
static Section gSections[MAX_SECTIONS]; static int gSectionN = 0;
static Framed  gFramed[MAX_FRAMED];     static int gFramedN = 0;
static Paged   gPaged[MAX_PAGED];       static int gPagedN = 0;
static bool    gRecordShift = false;
static int     gDevSectionIdx = 0;
static int     gBuildPage = -1;                // page new controls go on (-1 = always shown, e.g. the tabs)
static int     gBuildSub = -1;                 // Voice FX sub-tab new controls go on (-1 = all)
static int     gPage = 0;                      // page being shown

static void RecordPage(HWND h) { if (gBuildPage >= 0 && gPagedN < MAX_PAGED) gPaged[gPagedN++] = { h, gBuildPage, gBuildSub, gBuildFeat }; }

static int RowsDelta() { return ROW_H * (gRows - 1); }
static int DesignH() { return gCompact ? COMPACT_H : BASE_H + RowsDelta(); }

static HWND Ctl(const wchar_t* cls, const wchar_t* text, DWORD style, int x, int y, int w, int h, int id, DWORD ex = 0)
{
    x = SC(x); y = SC(y); w = SC(w); h = SC(h);
    HWND c = CreateWindowExW(ex, cls, text, WS_CHILD | WS_VISIBLE | style, x, y, w, h,
                             gWnd, (HMENU)(INT_PTR)id, gInst, nullptr);
    SendMessageW(c, WM_SETFONT, (WPARAM)gFont, TRUE);
    RecordPage(c);
    if (gDesignN < MAX_DESIGN) {
        Design& d = gDesign[gDesignN++];
        d = {};
        d.h = c; d.x = x; d.y = y; d.w = w; d.ht = h; d.page = gBuildPage; d.sub = gBuildSub;
        d.rx = UNSC(x); d.ry = UNSC(y); d.shifted = gRecordShift; d.combo = !lstrcmpiW(cls, L"COMBOBOX"); d.sec = -1;
    }
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
    for (int i = gDesignN - 1; i >= 0; i--)
        if (gDesign[i].h == e) {                // the arrows follow the box wherever it goes
            RECT er, ur; GetWindowRect(e, &er); GetWindowRect(u, &ur);
            gDesign[i].ud = u; gDesign[i].udx = ur.left - er.left; gDesign[i].udy = ur.top - er.top;
            break;
        }
    if (gFramedN < MAX_FRAMED) gFramed[gFramedN++] = { e, u };
    RecordPage(u);
    return u;
}

static void AddSection(int x, int y, int w, int h, const wchar_t* title)
{
    if (gSectionN < MAX_SECTIONS) gSections[gSectionN++] = { x, y, w, h, title, gRecordShift, gBuildPage, gBuildSub, 0, 0, gBuildFeat };
}


// ======================= placing controls =======================
static int CtlOffX(const Design& d) { return d.ox + (d.sec >= 0 ? gSections[d.sec].ox : 0); }
static int CtlOffY(const Design& d) { return d.oy + (d.sec >= 0 ? gSections[d.sec].oy : 0); }
static void PlaceAll()
{
    if (!gWnd) return;
    const int rows = RowsDelta();
    HWND keep[3] = { GetDlgItem(gWnd, IDC_STATUS), GetDlgItem(gWnd, IDC_START), GetDlgItem(gWnd, IDC_MUTEBTN) };
    { RECT c; GetClientRect(gWnd, &c); gOrgX = gCompact ? 0 : Imax(0, ((int)c.right - SC(CLIENT_W)) / 2); }
    for (int i = 0; i < gDesignN; i++) {
        Design& d = gDesign[i];
        if (gCompact && (d.h == keep[0] || d.h == keep[1] || d.h == keep[2])) continue;   // compact mode places these
        if (d.page >= 0 && d.page != gPage) continue;   // other pages are placed when you switch to them
        if (d.free) continue;
        int x = gOrgX + d.x + d.dx + SC(CtlOffX(d)), y = d.y + (d.shifted ? SC(rows) : 0) + SC(CtlOffY(d));
        RECT r; GetWindowRect(d.h, &r); MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2);
        int w = d.ud ? r.right - r.left : d.w + d.dw;          // a number box keeps the width its arrows left it
        int h = d.combo ? d.ht : r.bottom - r.top;              // a dropdown's height is its list
        if (r.left != x || r.top != y || r.right - r.left != w)
            SetWindowPos(d.h, nullptr, x, y, w, h, SWP_NOZORDER | SWP_NOACTIVATE | SWP_NOCOPYBITS);
        if (d.ud) {
            RECT u; GetWindowRect(d.ud, &u); MapWindowPoints(nullptr, gWnd, (POINT*)&u, 2);
            if (u.left != x + d.udx || u.top != y + d.udy)
                SetWindowPos(d.ud, nullptr, x + d.udx, y + d.udy, 0, 0, SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE | SWP_NOCOPYBITS);
        }
    }
}
static void AssignSections()                    // which section each control sits in (it moves with it)
{
    for (int i = 0; i < gDesignN; i++) {
        Design& d = gDesign[i];
        d.sec = -1;
        if (d.page < 0) continue;
        for (int k = 0; k < gSectionN; k++) {
            const Section& s = gSections[k];
            if (s.page != d.page || !(s.sub == d.sub || s.sub < 0 || d.sub < 0)) continue;
            // the Outputs box grows with the list: all its rows belong to it (the "+ Add output" row too)
            const bool dev = k == gDevSectionIdx;
            if (!dev && d.shifted != s.shifts) continue;
            const int bottom = dev && !d.shifted ? ROW_Y0 + ROW_H * MAX_OUT + 6 : s.y + s.h;
            if (d.rx >= s.x && d.rx < s.x + s.w && d.ry >= s.y - 10 && d.ry < bottom) { d.sec = k; break; }
        }
    }
}

// ======================= fitting text to its space =======================
// The layout uses fixed sizes that suit Segoe UI. Wider fonts (Verdana, Comic Sans, ...) or different text
// rendering would push labels under the box next to them or past the end of a note, so after building the
// window (and whenever the font changes) every label is measured:
//  1. a one-line label or checkbox that is too narrow gets wider, and everything to its right on that row moves along;
//  2. if that runs a row past its section's edge, dropdowns on the row give up some width, then trailing notes are cut;
//  3. text that still does not fit (wrapped notes, squeezed labels) gets a slightly smaller font.
static bool FitSameGroup(const Design& a, const Design& b)
{
    return a.page >= 0 && a.page == b.page && (a.sub == b.sub || a.sub < 0 || b.sub < 0);
}
static int gFitKinds[MAX_DESIGN];               // FitKind of each control, worked out once per FitText
static int FitVisH(const Design& d)
{
    return gFitKinds[&d - gDesign] == 4 ? SC(24) : d.ht;   // a combo's height includes its drop-down list
}
static bool FitSameRow(const Design& a, const Design& b)
{
    if (a.shifted != b.shifted) return false;   // (one moves down as outputs are added, the other doesn't)
    int ah = FitVisH(a), bh = FitVisH(b);
    int ov = Imin(a.y + ah, b.y + bh) - Imax(a.y, b.y);
    return ov > 0 && ov * 10 >= Imin(ah, bh) * 6;
}
static int FitKind(const Design& d)            // 0 = other, 1 = one-line label, 2 = checkbox / radio, 3 = wrapped note, 4 = combo, 5 = push button
{
    wchar_t cls[16]; GetClassNameW(d.h, cls, 16);
    LONG st = GetWindowLongW(d.h, GWL_STYLE);
    if (!lstrcmpiW(cls, L"ComboBox")) return 4;
    if (!lstrcmpiW(cls, L"Button")) {
        LONG t = st & BS_TYPEMASK;
        if (t == BS_PUSHBUTTON || t == BS_DEFPUSHBUTTON) return 5;
        return t == BS_AUTOCHECKBOX || t == BS_CHECKBOX || t == BS_AUTORADIOBUTTON || t == BS_RADIOBUTTON ? 2 : 0;
    }
    if (!lstrcmpiW(cls, L"Static")) {
        int id = GetDlgCtrlID(d.h);
        if ((st & SS_TYPEMASK) != SS_LEFT || !((id & 0xFFFF) == 0xFFFF || id == IDC_HDR || id == IDC_RADIODESC || id == IDC_HEARLBL)) return 0;
        return d.ht <= SC(24) ? 1 : 3;
    }
    return 0;
}
static SIZE FitMeasure(HWND h, HFONT f, int wrapW)   // wrapW = 0: one line
{
    wchar_t t[600]; SIZE sz = { 0, 0 };
    if (GetWindowTextW(h, t, 600) <= 0) return sz;
    HDC dc = GetDC(h);
    HGDIOBJ of = SelectObject(dc, f);
    RECT r = { 0, 0, wrapW > 0 ? wrapW : 0, 0 };
    DrawTextW(dc, t, -1, &r, DT_CALCRECT | (wrapW > 0 ? DT_WORDBREAK | DT_EXPANDTABS : DT_SINGLELINE));
    SelectObject(dc, of); ReleaseDC(h, dc);
    sz.cx = r.right; sz.cy = r.bottom;
    return sz;
}
static int FitNeed(const Design& d, int kind, HFONT f)
{
    int tw = FitMeasure(d.h, f, 0).cx;
    if (!tw) return 0;
    if (kind == 2) return tw + Imax(21, GetSystemMetrics(SM_CXMENUCHECK) + SC(6)) + SC(3);   // box + gap + text
    if (kind == 5) return tw + SC(12);                                                      // button edges
    return tw + SC(2);
}
static int FitLimit(const Design& d)            // right edge of the section the control sits in
{
    for (int i = 0; i < gSectionN; i++) {
        const Section& s = gSections[i];
        if (s.page != d.page || !(s.sub == d.sub || s.sub < 0 || d.sub < 0)) continue;
        if (d.x >= SC(s.x) && d.x < SC(s.x + s.w) && d.y >= SC(s.y) && d.y < SC(s.y + s.h)) return SC(s.x + s.w) - SC(6);
    }
    return SC(CLIENT_W) - SC(10);
}
static void FitPush(int from, int depth = 0)   // gDesign[from] got wider or moved: push whatever it now runs into
{
    if (depth > 12) return;
    const Design& a = gDesign[from];
    int right = a.x + a.dx + a.w + a.dw;
    for (int j = 0; j < gDesignN; j++) {
        Design& b = gDesign[j];
        if (j == from || !FitSameGroup(a, b) || !FitSameRow(a, b) || b.x < a.x + a.w - SC(4)) continue;
        int gap  = Imax(0, b.x - (a.x + a.w));            // the space the layout left between them, up to 6 px
        int push = right + Imin(gap, SC(6)) - (b.x + b.dx);
        if (push > 0) { b.dx += push; FitPush(j, depth + 1); }
    }
}
static HFONT FitFont(int level)                 // level 0 = the normal font, 1-3 = 1-3 px smaller
{
    if (level <= 0) return gFont;
    HFONT& f = gFontFit[level - 1];
    if (!f) f = CreateFontW(-SC(gFontPx - level), 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, gFontName);
    return f ? f : gFont;
}
static void FitFontOf(int i, int kind)
{
    if (kind != 1 && kind != 2 && kind != 3 && kind != 5) return;
    Design& d = gDesign[i];
    int w = d.w + d.dw, lvl = 0;
    for (; lvl < 3; lvl++) {
        HFONT f = FitFont(lvl);
        bool fits = kind == 3 ? FitMeasure(d.h, f, w).cy <= d.ht : FitNeed(d, kind, f) <= w;
        if (fits) break;
    }
    HFONT want = FitFont(lvl);
    if ((HFONT)SendMessageW(d.h, WM_GETFONT, 0, 0) != want) SendMessageW(d.h, WM_SETFONT, (WPARAM)want, TRUE);
    if (kind == 1) {                            // a one-line note that still doesn't fit: "..." rather than a cut-off 2nd line
        LONG st = GetWindowLongW(d.h, GWL_STYLE);
        bool fits = FitNeed(d, kind, want) <= w;
        LONG nst = fits ? (st & ~SS_ENDELLIPSIS) : (st | SS_ENDELLIPSIS);
        if (nst != st) { SetWindowLongW(d.h, GWL_STYLE, nst); InvalidateRect(d.h, nullptr, TRUE); }
    }
}
static void FitText()
{
    if (!gWnd || !gFont) return;
    int* kinds = gFitKinds;
    for (int i = 0; i < gDesignN; i++) { gDesign[i].dx = 0; gDesign[i].dw = 0; kinds[i] = gDesign[i].page >= 0 ? FitKind(gDesign[i]) : 0; }
    // (GetDlgCtrlID gives -1 for the many "no id" labels: (id & 0xFFFF) == 0xFFFF catches both spellings)

    // 1. widen labels, left to right, pushing the rest of the row along
    for (int pass = 0; pass < 2; pass++)        // twice, so a label pushed by an earlier one is measured at its final place
        for (int i = 0; i < gDesignN; i++) {
            if (kinds[i] != 1 && kinds[i] != 2) continue;
            Design& d = gDesign[i];
            int lack = FitNeed(d, kinds[i], gFont) - (d.w + d.dw);
            if (lack > 0) { d.dw += lack; FitPush(i); }
        }

    // 2. rows that now run past their section: dropdowns give up width, then trailing notes are cut short
    for (int pass = 0; pass < 3; pass++)
        for (int i = 0; i < gDesignN; i++) {
            Design& c = gDesign[i];
            if (c.page < 0) continue;
            int over = c.x + c.dx + c.w + c.dw - FitLimit(c);
            if (over <= 0) continue;
            for (int k = gDesignN - 1; k >= 0 && over > 0; k--) {
                Design& cb = gDesign[k];
                if (kinds[k] != 4 || !FitSameGroup(c, cb) || !FitSameRow(c, cb) || cb.x > c.x) continue;
                int slack = cb.w + cb.dw - Imax(SC(70), cb.w * 55 / 100);
                int take = Imin(slack, over);
                if (take <= 0) continue;
                cb.dw -= take; over -= take;
                for (int j = 0; j < gDesignN; j++) {
                    Design& b = gDesign[j];
                    if (j != k && FitSameGroup(cb, b) && FitSameRow(cb, b) && b.x > cb.x) b.dx -= take;
                }
            }
            // still too wide: labels / checkboxes on the row (left of it, or it) give up width; their font shrinks to fit later
            for (int k = gDesignN - 1; k >= 0 && over > 0; k--) {
                Design& lb = gDesign[k];
                if ((kinds[k] != 1 && kinds[k] != 2 && kinds[k] != 3) || !FitSameGroup(c, lb) || !FitSameRow(c, lb) || lb.x > c.x) continue;
                int slack = lb.w + lb.dw - Imax(SC(30), (lb.w + lb.dw) * 70 / 100);
                int take = Imin(slack, over);
                if (take <= 0) continue;
                lb.dw -= take; over -= take;
                for (int j = 0; j < gDesignN; j++) {
                    Design& b = gDesign[j];
                    if (j != k && FitSameGroup(lb, b) && FitSameRow(lb, b) && b.x > lb.x) b.dx -= take;
                }
            }
        }

    // 3. put everything where it now belongs
    PlaceAll();

    // 4. still too big for its space: a slightly smaller font (down to 3 px smaller)
    for (int i = 0; i < gDesignN; i++) FitFontOf(i, kinds[i]);
}

// Text of one control changed (a hotkey name, a description): just pick the font size it needs.
static void FitOne(HWND h)
{
    if (!h || !gFont) return;
    for (int i = 0; i < gDesignN; i++)
        if (gDesign[i].h == h) { FitFontOf(i, gDesign[i].page >= 0 ? FitKind(gDesign[i]) : 0); return; }
}

// ======================= knob control (Voice FX page) =======================
// Drag up/down (Shift = fine), scroll the wheel, or use the arrow keys / Page Up/Down / Home / End.
// Double-click or Delete resets to the default. Writes straight into the knob's setting.
#define KNOB_W 96
#define KNOB_H 106
static int    gKnobLastY = 0;
static double gKnobAccum = 0;
static int    gWheelAccum = 0;

static bool KnobActive(int i)
{
    const Knob& k = gKnobs[i];
    if (k.offText && *k.var == k.lo) return false;
    switch (k.group) {
    case KG_NS:   return gNsOn;
    case KG_GATE:
        if (gGateMode == GATE_OFF) return false;
        if (k.var == &gGateThrDb)    return gGateMode == GATE_VOLUME || gGateMode == GATE_BOTH;
        if (k.var == &gGateVoicePct) return gGateMode == GATE_VOICE  || gGateMode == GATE_BOTH;
        return true;
    case KG_TONE: case KG_EQ: return true;
    }
    if (k.var == &gVocSynth && gVocStyle == VOC_TUNE) return false;   // Tune style has no synth
    if (k.var == &gVocRetuneMs && gVocStyle == VOC_SONG) return false; // Song style doesn't tune
    if (k.group == KG_RADIO) {                  // dim what the chosen preset doesn't have
        const RadioPreset& rp = RADIO_PRESETS[Iclamp(gRadioPreset, 0, RADIO_N - 1)];
        if (k.var == &gRadioSquelch && rp.squelch == SQ_NONE) return false;
        if (k.var == &gRadioStatic && rp.hiss == 0 && rp.crackle == 0 && rp.hum == 0) return false;
        if (k.var == &gRadioDrive && rp.driveDb == 0) return false;
    }
    return gFxOn && *gFxGroups[k.group].on;
}
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
    for (int i = 0; i < FX_SUBS; i++) InvalidateRect(GetDlgItem(gWnd, IDC_FXSUB0 + i), nullptr, FALSE);   // their "on" counts
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
    const int  cx = rc.right / 2, cy = 47, r = 26;     // fits knobs 96 px tall (Voice FX) and taller
    double frac = (double)(*k.var - k.lo) / (double)(k.hi - k.lo);
    double ang  = 225.0 - 270.0 * frac;         // 225 = minimum (bottom left), -45 = maximum (bottom right)

    COLORREF track = gDark ? DK_TRACK : LT_TRACK;
    COLORREF value = on ? ACCENT : (gDark ? RGB(112, 112, 112) : RGB(158, 158, 158));
    KnobArc(dc, cx, cy, r, 225.0, -45.0, track, 5);
    if (k.bipolar) {                            // fills from the middle (12 o'clock) toward the value
        if (ang < 90.0) KnobArc(dc, cx, cy, r, 90.0, ang, value, 5);
        else            KnobArc(dc, cx, cy, r, ang, 90.0, value, 5);
    } else {
        KnobArc(dc, cx, cy, r, 225.0, ang, value, 5);
    }

    HBRUSH body = CreateSolidBrush(KNOB_C);
    HPEN   edge = CreatePen(PS_SOLID, 1, focus ? ACCENT : gDark ? RGB(88, 88, 88) : RGB(186, 186, 186));
    HGDIOBJ ob = SelectObject(dc, body), op = SelectObject(dc, edge);
    Ellipse(dc, cx - 18, cy - 18, cx + 19, cy + 19);
    SelectObject(dc, ob); SelectObject(dc, op);
    DeleteObject(body); DeleteObject(edge);

    int x1, y1, x2, y2;                         // pointer
    KnobPoint(cx, cy, 6, ang, &x1, &y1);
    KnobPoint(cx, cy, 15, ang, &x2, &y2);
    LOGBRUSH lb = { BS_SOLID, on ? (TXT_C) : (gDark ? DK_DIM : RGB(130, 130, 130)), 0 };
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
    if (k.offText && *k.var == k.lo) lstrcpynW(txt, k.offText, 32);
    else wsprintfW(txt, k.bipolar && *k.var > 0 ? L"+%d%s" : L"%d%s", *k.var, k.unit);
    SelectObject(dc, gFontBold);
    SetTextColor(dc, on ? (TXT_C) : (gDark ? DK_DIM : RGB(130, 130, 130)));
    RECT vr = { 0, cy + 29, rc.right, rc.bottom };
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
        if (gBrPicture) { POINT pt = { 0, 0 }; MapWindowPoints(h, gWnd, &pt, 1); SetBrushOrgEx(mem, -pt.x, -pt.y, nullptr); }
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

static void Layout();
static int  MixerNeedW();
static void MixerPlace();
static void SetFxGroupOn(int g, bool on);
static void SetFxOn(bool on);
static void UpdateStatus(bool force);

// ======================= vocode to song (capture + UI) =======================
// Windows can record one app's sound, or everything except one app (Windows 11 / build 20348+).
// "All PC sound" leaves Lag Effect itself out, so its own output never feeds back in. On older
// Windows we fall back to recording the speakers, which can echo if you monitor on them.
static const GUID kCLSID_MMDeviceEnumerator  = { 0xBCDE0395, 0xE52F, 0x467C, { 0x8E, 0x3D, 0xC4, 0x57, 0x92, 0x91, 0x69, 0x2E } };
static const GUID kIID_IMMDeviceEnumerator   = { 0xA95664D2, 0x9614, 0x4F35, { 0xA7, 0x46, 0xDE, 0x8D, 0xB6, 0x36, 0x17, 0xE6 } };
static const GUID kIID_IAudioSessionManager2 = { 0x77AA99A0, 0x1BD6, 0x484F, { 0x8B, 0xC7, 0x2C, 0x65, 0x4C, 0x9A, 0x9B, 0x6F } };
static const GUID kIID_IAudioSessionControl2 = { 0xBFB7FF88, 0x7239, 0x4FC9, { 0x8F, 0xA2, 0x07, 0xC9, 0x50, 0xBE, 0x9C, 0x6D } };

struct AudioApp { DWORD pid; wchar_t name[64]; };

// ---- which apps can be picked ----
// Windows' process list gives every process's name and parent without needing to open it, which matters
// for browsers: Chrome, Edge, Brave etc. play sound from a separate, locked-down helper process.
struct ProcInfo { DWORD pid, parent; wchar_t exe[64]; };
static int SnapProcs(ProcInfo* p, int cap)
{
    int n = 0;
    HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snap == INVALID_HANDLE_VALUE) return 0;
    PROCESSENTRY32W e = {}; e.dwSize = sizeof(e);
    for (BOOL ok = Process32FirstW(snap, &e); ok && n < cap; ok = Process32NextW(snap, &e)) {
        p[n].pid = e.th32ProcessID; p[n].parent = e.th32ParentProcessID;
        lstrcpynW(p[n].exe, e.szExeFile, 64);
        n++;
    }
    CloseHandle(snap);
    return n;
}

static int ProcIndex(const ProcInfo* p, int n, DWORD pid)
{
    for (int i = 0; i < n; i++) if (p[i].pid == pid) return i;
    return -1;
}

// Top of the tree of same-named processes (the main browser process): recording it includes all its helpers.
static DWORD ProcRoot(const ProcInfo* p, int n, DWORD pid)
{
    for (int guard = 0; guard < 64; guard++) {
        int i = ProcIndex(p, n, pid);
        if (i < 0) return pid;
        int up = ProcIndex(p, n, p[i].parent);
        if (up < 0 || lstrcmpiW(p[up].exe, p[i].exe)) return pid;
        pid = p[up].pid;
    }
    return pid;
}

// Browsers are always offered when running, even before they've played anything.
static const wchar_t* KNOWN_BROWSERS[] = {
    L"chrome.exe", L"msedge.exe", L"firefox.exe", L"opera.exe", L"brave.exe", L"vivaldi.exe", L"arc.exe",
    L"chromium.exe", L"librewolf.exe", L"waterfox.exe", L"zen.exe", L"floorp.exe", L"thorium.exe",
};

// Apps with sound sessions on any output (Spotify, browsers, games...), plus running browsers; minus Lag Effect.
// pid = the app's main process, so recording it covers all of its helper processes.
static int ListAudioApps(AudioApp* out, int cap)
{
    static ProcInfo procs[2048];
    int np = SnapProcs(procs, 2048);
    const DWORD self = GetCurrentProcessId();
    int n = 0;
    auto add = [&](DWORD pid) {
        int i = ProcIndex(procs, np, pid);
        if (i < 0 || pid == self || n >= cap) return;
        for (int k = 0; k < n; k++) if (!lstrcmpiW(out[k].name, procs[i].exe)) return;   // one entry per app
        out[n].pid = ProcRoot(procs, np, pid);
        lstrcpynW(out[n].name, procs[i].exe, 64);
        n++;
    };

    HRESULT co = CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    IMMDeviceEnumerator* en = nullptr;
    if (SUCCEEDED(CoCreateInstance(kCLSID_MMDeviceEnumerator, nullptr, CLSCTX_ALL, kIID_IMMDeviceEnumerator, (void**)&en))) {
        IMMDeviceCollection* devs = nullptr;
        if (SUCCEEDED(en->EnumAudioEndpoints(eRender, DEVICE_STATE_ACTIVE, &devs))) {
            UINT dc = 0; devs->GetCount(&dc);
            for (UINT d = 0; d < dc; d++) {
                IMMDevice* dev = nullptr;
                if (FAILED(devs->Item(d, &dev))) continue;
                IAudioSessionManager2* mgr = nullptr;
                if (SUCCEEDED(dev->Activate(kIID_IAudioSessionManager2, CLSCTX_ALL, nullptr, (void**)&mgr))) {
                    IAudioSessionEnumerator* se = nullptr;
                    if (SUCCEEDED(mgr->GetSessionEnumerator(&se))) {
                        int sc = 0; se->GetCount(&sc);
                        for (int i = 0; i < sc; i++) {
                            IAudioSessionControl* c = nullptr;
                            if (FAILED(se->GetSession(i, &c))) continue;
                            IAudioSessionControl2* c2 = nullptr;
                            if (SUCCEEDED(c->QueryInterface(kIID_IAudioSessionControl2, (void**)&c2))) {
                                DWORD pid = 0;
                                c2->GetProcessId(&pid);  // may report "several processes": then pid stays usable or 0
                                if (pid) add(pid);
                                c2->Release();
                            }
                            c->Release();
                        }
                        se->Release();
                    }
                    mgr->Release();
                }
                dev->Release();
            }
            devs->Release();
        }
        en->Release();
    }
    if (SUCCEEDED(co)) CoUninitialize();

    for (const wchar_t* b : KNOWN_BROWSERS)       // running browsers, even if silent so far
        for (int i = 0; i < np; i++)
            if (!lstrcmpiW(procs[i].exe, b)) { add(procs[i].pid); break; }
    return n;
}

// ======================= mixer channels (capture) =======================
static ProcLoop      gChPL[CH_MAX];
static ma_device     gChDev[CH_MAX];
static bool          gChRun[CH_MAX], gChOnPL[CH_MAX];
static volatile bool gChLost[CH_MAX];           // its app closed / its device went away: try again later
template <int N> static void ChanPLCb(ma_device*, void*, const void* in, ma_uint32 n) { ChanPush(N, (const float*)in, n, 2); }
static ma_device_data_proc CH_PL_CB[CH_MAX] = { ChanPLCb<0>, ChanPLCb<1>, ChanPLCb<2>, ChanPLCb<3>, ChanPLCb<4>, ChanPLCb<5>, ChanPLCb<6>, ChanPLCb<7> };
static void ChanDevCb(ma_device* d, void*, const void* in, ma_uint32 n) { ChanPush((int)(INT_PTR)d->pUserData, (const float*)in, n, 2); }
static void ChanDevNote(const ma_device_notification* n)
{
    if (n->type == ma_device_notification_type_stopped) gChLost[(int)(INT_PTR)n->pDevice->pUserData] = true;
}
static void ChanStop(int c)
{
    gChA[c].live = false;
    if (gChRun[c]) { if (gChOnPL[c]) ProcLoopStop(&gChPL[c]); else ma_device_uninit(&gChDev[c]); }
    gChRun[c] = false; gChLost[c] = false;
    gChA[c].w = gChA[c].r = 0; gChA[c].peakL = gChA[c].peakR = 0;
}
static DWORD ChanFindApp(const wchar_t* exe)    // the running app's main process (0: not running)
{
    static ProcInfo procs[2048];
    int np = SnapProcs(procs, 2048);
    for (int i = 0; i < np; i++)
        if (!lstrcmpiW(procs[i].exe, exe) && procs[i].pid != GetCurrentProcessId()) return ProcRoot(procs, np, procs[i].pid);
    return 0;
}
static bool ChanStartPid(int c, DWORD pid);
static bool ChanStart(int c)                    // (audio must be running)
{
    if (gCh[c].type == CH_APP) {
        DWORD pid = ChanFindApp(gCh[c].src);
        if (!pid) { ChanStop(c); return false; } // not running yet: looked for again in the background
        return ChanStartPid(c, pid);
    }
    return ChanStartPid(c, 0);
}
static bool ChanStartPid(int c, DWORD pid)
{
    ChanStop(c);
    const ChanSet& cs = gCh[c];
    if (cs.type == CH_APP) {
        if (!pid) return false;
        gChA[c].live = true;                    // (before starting: the first packets mustn't be thrown away)
        gChPL[c].priority = THREAD_PRIORITY_ABOVE_NORMAL;   // (not "highest": it's music, not your voice)
        if (!ProcLoopStart(&gChPL[c], pid, false, CH_PL_CB[c], &gChLost[c])) { gChA[c].live = false; return false; }
        gChOnPL[c] = true;
    } else if (cs.type == CH_DEV || cs.type == CH_OUT) {
        const bool out = cs.type == CH_OUT;     // an output: record what it plays (loopback)
        ma_device_info* devs = out ? gPlayDevs : gCapDevs; const ma_uint32 nd = out ? gPlayCount : gCapCount;
        int di = -1;
        for (ma_uint32 i = 0; i < nd; i++) {
            wchar_t n[256]; MultiByteToWideChar(CP_UTF8, 0, devs[i].name, -1, n, 256);
            if (!lstrcmpiW(n, cs.src)) { di = (int)i; break; }
        }
        if (di < 0) return false;
        ma_device_config cfg = ma_device_config_init(out ? ma_device_type_loopback : ma_device_type_capture);
        cfg.capture.format = ma_format_f32; cfg.capture.channels = 2; cfg.sampleRate = RATE;
        cfg.capture.pDeviceID = &devs[di].id;
        cfg.dataCallback = ChanDevCb; cfg.notificationCallback = ChanDevNote; cfg.pUserData = (void*)(INT_PTR)c;
        cfg.periodSizeInMilliseconds = 10;
        gChA[c].live = true;
        if (ma_device_init(&gCtx, &cfg, &gChDev[c]) != MA_SUCCESS) { gChA[c].live = false; return false; }
        if (ma_device_start(&gChDev[c]) != MA_SUCCESS) { ma_device_uninit(&gChDev[c]); gChA[c].live = false; return false; }
        gChOnPL[c] = false;
    } else return false;
    gChRun[c] = true;
    return true;
}
static void ChanStartAll() { for (int c = 0; c < CH_MAX; c++) if (gCh[c].type != CH_NONE) ChanStart(c); }
static void ChanStopAll()  { for (int c = 0; c < CH_MAX; c++) ChanStop(c); }
static void AppScanStart();
static DWORD gChNextTry[CH_MAX], gChWait[CH_MAX];
static void ChanTick()                          // (every ~2 s) apps that started / closed, devices that came back
{
    if (!gRunning) return;
    bool scan = false;
    const DWORD now = GetTickCount();
    for (int c = 0; c < CH_MAX; c++) {
        if (gCh[c].type == CH_NONE) continue;
        if (!gChLost[c] && gChRun[c]) { gChWait[c] = 0; continue; }
        if (gCh[c].type == CH_APP) { scan = true; continue; }   // apps: looked for in the background (no hitch here)
        if ((int)(now - gChNextTry[c]) < 0) continue;             // inputs: tried less and less often (2 s .. 30 s)
        if (ChanStart(c)) gChWait[c] = 0;
        else { gChWait[c] = gChWait[c] ? Imin((int)gChWait[c] * 2, 30000) : 2000; gChNextTry[c] = now + gChWait[c]; }
    }
    if (scan) AppScanStart();
}

static void AppDisplayName(const wchar_t* exe, wchar_t* out, int cap)   // "spotify.exe" -> "Spotify"
{
    static const wchar_t* nice[][2] = {         // friendlier names for common apps
        { L"msedge.exe", L"Edge" }, { L"chrome.exe", L"Chrome" }, { L"firefox.exe", L"Firefox" },
        { L"opera.exe", L"Opera" }, { L"brave.exe", L"Brave" }, { L"vivaldi.exe", L"Vivaldi" },
    };
    for (auto& m : nice) if (!lstrcmpiW(exe, m[0])) { lstrcpynW(out, m[1], cap); return; }
    lstrcpynW(out, exe, cap);
    int n = lstrlenW(out);
    if (n > 4 && !lstrcmpiW(out + n - 4, L".exe")) out[n - 4] = 0;
    if (out[0] >= L'a' && out[0] <= L'z') out[0] = (wchar_t)(out[0] - 32);
}

static wchar_t gSongList[32][64];               // exe names behind the "Music from" entries
static int     gSongListN = 0;
static int     gPrevVocStyle = VOC_HARMONY;     // style to go back to when Vocode to song is switched off
static int     gSongState = 0;                  // 0 off, 1 one app, 2 all PC sound, 3 speakers (fallback), 4 waiting, 5 failed
static wchar_t gSongActiveApp[64] = L"";
static bool    gSongHeard = false;

#define SONGSRC_FILE   1000                      // item data in "Music from": the loaded file
#define SONGSRC_BROWSE 999                       // "Audio file..."

static void FillSongSources()
{
    HWND c = GetDlgItem(gWnd, IDC_SONGSRC);
    if (!c) return;
    AudioApp apps[32];
    int n = ListAudioApps(apps, 32);
    SendMessageW(c, CB_RESETCONTENT, 0, 0);
    int sel = 0;
    LRESULT i0 = SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"Music: all PC sound");
    SendMessageW(c, CB_SETITEMDATA, i0, 0);
    gSongListN = 0;
    bool found = gSongApp[0] == 0;
    for (int i = 0; i < n && gSongListN < 31; i++) {
        lstrcpynW(gSongList[gSongListN], apps[i].name, 64);
        wchar_t disp[64], label[96];
        AppDisplayName(apps[i].name, disp, 64);
        wsprintfW(label, L"Music: %s", disp);
        LRESULT it = SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)label);
        SendMessageW(c, CB_SETITEMDATA, it, gSongListN + 1);
        if (!lstrcmpiW(apps[i].name, gSongApp)) { sel = (int)it; found = true; }
        gSongListN++;
    }
    if (!found) {                                // the saved app isn't playing right now: keep it listed
        lstrcpynW(gSongList[gSongListN], gSongApp, 64);
        wchar_t disp[64], label[96];
        AppDisplayName(gSongApp, disp, 64);
        wsprintfW(label, L"Music: %s (not playing)", disp);
        LRESULT it = SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)label);
        SendMessageW(c, CB_SETITEMDATA, it, gSongListN + 1);
        sel = (int)it;
        gSongListN++;
    }
    if (gSongFile[0]) {                          // the audio file, if one was picked
        const wchar_t* base = wcsrchr(gSongFile, L'\\');
        wchar_t label[MAX_PATH + 16];
        wsprintfW(label, L"File: %s", base ? base + 1 : gSongFile);
        LRESULT it = SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)label);
        SendMessageW(c, CB_SETITEMDATA, it, SONGSRC_FILE);
        if (gSongUseFile) sel = (int)it;
    }
    LRESULT ib = SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"Audio file...");
    SendMessageW(c, CB_SETITEMDATA, ib, SONGSRC_BROWSE);
    SendMessageW(c, CB_SETCURSEL, sel, 0);
}

// ---- audio file ----
struct SongFileJob { wchar_t path[MAX_PATH]; short* data; unsigned len; bool ok, quiet; int target; unsigned maxLen; };
// target: -1 = Vocode to song, 0..PADS-1 = soundboard pad

static DWORD WINAPI SongDecodeThread(LPVOID arg)  // decode to 48 kHz mono, up to 20 minutes
{
    SongFileJob* j = (SongFileJob*)arg;
    ma_decoder_config dc = ma_decoder_config_init(ma_format_s16, 1, RATE);
    ma_decoder dec;
    if (ma_decoder_init_file_w(j->path, &dc, &dec) == MA_SUCCESS) {
        const unsigned maxLen = j->maxLen;
        unsigned cap = maxLen < RATE * 30 ? maxLen + 8192 : RATE * 30, len = 0;
        short* buf = (short*)HeapAlloc(GetProcessHeap(), 0, cap * sizeof(short));
        while (buf && len < maxLen) {
            if (len + 8192 > cap) {
                unsigned nc = cap * 2 > maxLen ? maxLen + 8192 : cap * 2;
                short* nb = (short*)HeapReAlloc(GetProcessHeap(), 0, buf, nc * sizeof(short));
                if (!nb) break;
                buf = nb; cap = nc;
            }
            ma_uint64 got = 0;
            if (ma_decoder_read_pcm_frames(&dec, buf + len, 8192, &got) != MA_SUCCESS || got == 0) break;
            len += (unsigned)got;
        }
        ma_decoder_uninit(&dec);
        j->data = buf; j->len = len; j->ok = buf && len > RATE / 50;
        if (!j->ok && buf) { HeapFree(GetProcessHeap(), 0, buf); j->data = nullptr; }
    }
    PostMessageW(gWnd, WM_SONGFILE_LOADED, 0, (LPARAM)j);
    return 0;
}

static bool gSongLoading = false;

static void LoadSongFile(const wchar_t* path, bool quiet = false)
{
    SongFileJob* j = (SongFileJob*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(SongFileJob));
    if (!j) return;
    lstrcpynW(j->path, path, MAX_PATH);
    j->quiet = quiet;
    j->target = -1;
    j->maxLen = RATE * 60 * 20;                  // songs: up to 20 minutes
    gSongLoading = true;
    HANDLE t = CreateThread(nullptr, 0, SongDecodeThread, j, 0, nullptr);
    if (t) CloseHandle(t); else { gSongLoading = false; HeapFree(GetProcessHeap(), 0, j); }
}

static void UpdateSongStatusText();
static void UpdateSongCapture();

static void OnPadLoaded(SongFileJob* j);
static void OnSongFileLoaded(SongFileJob* j)
{
    if (j->target >= 0) { OnPadLoaded(j); return; }
    const bool quiet = j->quiet;
    gSongLoading = false;
    if (j->ok) {
        short* old = gFileData;
        gUseFile = false;                       // let the audio thread stop reading the old one
        Sleep(30);
        gFileData = j->data; gFileLen = j->len; gFileRestart = true;
        if (old) HeapFree(GetProcessHeap(), 0, old);
        lstrcpynW(gSongFile, j->path, MAX_PATH);
        gSongUseFile = true;
    } else {
        gSongUseFile = gFileData != nullptr && gSongUseFile;
        if (!quiet) MessageBoxW(gWnd, L"Couldn't open that audio file.\n\nMP3, WAV and FLAC files work.",
                                L"Lag Effect - Vocode to song", MB_ICONWARNING);
    }
    HeapFree(GetProcessHeap(), 0, j);
    FillSongSources();
    UpdateSongCapture();
}

static void BrowseSongFile()
{
    wchar_t path[MAX_PATH] = L"";
    OPENFILENAMEW o = {};
    o.lStructSize = sizeof(o);
    o.hwndOwner   = gWnd;
    o.lpstrFilter = L"Audio files (MP3, WAV, FLAC)\0*.mp3;*.wav;*.flac\0All files\0*.*\0";
    o.lpstrFile   = path;
    o.nMaxFile    = MAX_PATH;
    o.lpstrTitle  = L"Pick a song to vocode to";
    o.Flags       = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (GetOpenFileNameW(&o)) { LoadSongFile(path); UpdateSongStatusText(); }
    else FillSongSources();                     // cancelled: put the selection back
}

static void SongNotify(const ma_device_notification* n)
{
    if (n->type == ma_device_notification_type_stopped && !gStopping) gSongLost = true;   // e.g. the app closed
}

static bool SongStartDevice(DWORD pid, bool exclude)
{
    if (pid) {                                  // one app / everything but Lag Effect: Windows' process loopback
        gSongLost = false;
        if (!ProcLoopStart(&gSongPL, pid, exclude, SongCallback, &gSongLost)) return false;
        gSongPLOn = true;
        gSongRunning = true;
        return true;
    }
    ma_device_config cfg = ma_device_config_init(ma_device_type_loopback);
    cfg.capture.format   = ma_format_f32;
    cfg.capture.channels = 2;
    cfg.sampleRate       = RATE;
    cfg.dataCallback     = SongCallback;
    cfg.notificationCallback = SongNotify;
    cfg.wasapi.loopbackProcessID      = pid;     // 0 = the whole default output
    cfg.wasapi.loopbackProcessExclude = exclude;
    if (ma_device_init(&gCtx, &cfg, &gSongDev) != MA_SUCCESS) return false;
    if (ma_device_start(&gSongDev) != MA_SUCCESS) { ma_device_uninit(&gSongDev); return false; }
    gSongRunning = true;
    gSongLost = false;
    return true;
}

static bool SongModeOn() { return gFxOn && gFeatFx && gFxVocOn && gVocStyle == VOC_SONG; }

static void UpdateSongStatusText()
{
    wchar_t t[96], disp[64];
    AppDisplayName(gSongActiveApp, disp, 64);
    switch (gSongState) {
    case 1:  wsprintfW(t, gSongHeard ? L"Hearing %s" : L"%s is silent: press play", disp); break;
    case 2:  lstrcpynW(t, gSongHeard ? L"Hearing your PC" : L"No music playing yet", 96); break;
    case 3:  lstrcpynW(t, L"Using speaker sound (older Windows): turn off monitoring to avoid echo", 96); break;
    case 4:  wsprintfW(t, L"Waiting for %s to play...", disp); break;
    case 5:  lstrcpynW(t, L"Couldn't record PC sound", 96); break;
    case 6: {
        const wchar_t* base = wcsrchr(gSongFile, L'\\');
        wchar_t name[64]; lstrcpynW(name, base ? base + 1 : gSongFile, 40);
        wsprintfW(t, L"Playing %s (loops)", name);
        break;
    }
    default: lstrcpynW(t, gRunning ? L"Turn on to vocode music" : L"Press Start on the Main tab", 96); break;
    }
    if (gSongLoading) lstrcpynW(t, L"Loading the song...", 96);
    wchar_t cur[96];
    GetDlgItemTextW(gWnd, IDC_SONGSTATUS, cur, 96);
    if (lstrcmpW(cur, t)) SetDlgItemTextW(gWnd, IDC_SONGSTATUS, t);
}

// Starts / stops / re-targets the music capture to match the settings.
static void UpdateSongCapture()
{
    bool want = gRunning && SongModeOn();
    gUseFile = gSongUseFile && gFileData != nullptr;    // file: no capture needed
    if (gSongRunning && (!want || gSongLost || gSongUseFile || lstrcmpiW(gSongActiveApp, gSongApp))) {
        SongDevStop();
        gSongRunning = false;
    }
    if (!want) { gSongState = 0; UpdateSongStatusText(); return; }
    if (gSongUseFile) { gSongState = 6; UpdateSongStatusText(); return; }
    if (gSongRunning) { UpdateSongStatusText(); return; }

    lstrcpynW(gSongActiveApp, gSongApp, 64);
    if (gSongApp[0]) {                           // one app
        AudioApp apps[32];
        int n = ListAudioApps(apps, 32);
        DWORD pid = 0;
        for (int i = 0; i < n; i++) if (!lstrcmpiW(apps[i].name, gSongApp)) pid = apps[i].pid;
        if (!pid)                               gSongState = 4;   // not playing yet: the timer tries again
        else if (SongStartDevice(pid, false))   { gSongState = 1; gSongPid = pid; }
        else if (SongStartDevice(0, false))     gSongState = 3;   // Windows too old for one-app capture
        else                                    gSongState = 5;
    } else {                                    // everything except Lag Effect
        if (SongStartDevice(GetCurrentProcessId(), true)) gSongState = 2;
        else if (SongStartDevice(0, false))               gSongState = 3;
        else                                              gSongState = 5;
    }
    UpdateSongStatusText();
}

static void SongStyleChanged()                  // style / on-off changed somewhere
{
    Layout();
    RedrawKnobs();
    InvalidateRect(GetDlgItem(gWnd, IDC_SONGBTN), nullptr, FALSE);
    UpdateSongCapture();
}

// Changing between Song and the other styles swaps the Synth knob's value, so each keeps its own.
static void VocSetStyle(int ns)
{
    if ((gVocStyle == VOC_SONG) != (ns == VOC_SONG)) {
        int t = gVocSynth; gVocSynth = gVocSynthSaved; gVocSynthSaved = t;
    }
    gVocStyle = ns;
}

static void SetSongMode(bool on)
{
    if (on) {
        if (gVocStyle != VOC_SONG) gPrevVocStyle = gVocStyle;
        VocSetStyle(VOC_SONG);
        if (!gFxVocOn) SetFxGroupOn(KG_VOCODER, true);
        if (!gFxOn) SetFxOn(true);
    } else if (gVocStyle == VOC_SONG) {
        VocSetStyle(gPrevVocStyle);
    }
    SendDlgItemMessageW(gWnd, IDC_VOCSTYLE, CB_SETCURSEL, gVocStyle, 0);
    SongStyleChanged();
    UpdateStatus(true);
}

static bool PidAlive(DWORD pid)                 // (asks about just that process: listing them all took ~120 ms)
{
    if (!pid) return false;
    HANDLE h = OpenProcess(SYNCHRONIZE, FALSE, pid);
    if (!h) return GetLastError() == ERROR_ACCESS_DENIED;   // gone: "invalid parameter"; not ours to open: still there
    const bool alive = WaitForSingleObject(h, 0) == WAIT_TIMEOUT;
    CloseHandle(h);
    return alive;
}

static void SongTick()                          // every 50 ms
{
    static bool lastWant = false, lastOn = false;
    static DWORD lastTry = 0, lastHeard = 0;
    bool on = SongModeOn(), want = on && gRunning;
    if (on != lastOn) { lastOn = on; InvalidateRect(GetDlgItem(gWnd, IDC_SONGBTN), nullptr, FALSE); }
    DWORD now = GetTickCount();
    if (want != lastWant || (!want && gSongRunning) ||
        (want && !gSongUseFile && (!gSongRunning || gSongLost) && (gSongRetryNow || now - lastTry > 1500))) {
        lastWant = want; lastTry = now; gSongRetryNow = false;
        UpdateSongCapture();
    }
    static DWORD lastAlive = 0;                 // recording one app: if it closed (or restarted), find it again
    if (gSongRunning && gSongPLOn && gSongState == 1 && now - lastAlive > 3000) {
        lastAlive = now;
        if (!PidAlive(gSongPid)) gSongLost = true;
    }
    if (gSongPeak > 0.003f) lastHeard = now;    // music in the last 1.5 s?
    gSongPeak = 0;
    bool heard = now - lastHeard < 1500;
    if (heard != gSongHeard) { gSongHeard = heard; UpdateSongStatusText(); }
}

static void DrawSongButton(DRAWITEMSTRUCT* d)
{
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    bool on = SongModeOn();
    COLORREF fill = on ? ACCENT : (gDark ? DK_CTL : LT_CARD);
    HBRUSH b = CreateSolidBrush(fill);
    HPEN   p = CreatePen(PS_SOLID, 1, on ? ACCENT : gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ ob = SelectObject(dc, b), op = SelectObject(dc, p);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 12, 12);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(b); DeleteObject(p);
    SetBkMode(dc, TRANSPARENT);
    HGDIOBJ of = SelectObject(dc, gFontBold);
    COLORREF txt = on ? (gDark ? RGB(20, 20, 20) : RGB(255, 255, 255)) : (TXT_C);
    SetTextColor(dc, txt);
    RECT t1 = { rc.left, rc.top + 5, rc.right, rc.top + 24 };
    DrawTextW(dc, L"Vocode to song", -1, &t1, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(dc, gFont);
    SetTextColor(dc, on ? txt : (gDark ? DK_DIM : RGB(105, 105, 105)));
    RECT t2 = { rc.left, rc.top + 23, rc.right, rc.bottom - 4 };
    DrawTextW(dc, on ? L"\x266A ON" : L"\x266A talk over music", -1, &t2, DT_SINGLELINE | DT_CENTER | DT_VCENTER | DT_END_ELLIPSIS);
    SelectObject(dc, of);
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) {
        RECT fr = rc; InflateRect(&fr, -4, -4);
        SetTextColor(dc, txt);
        DrawFocusRect(dc, &fr);
    }
}

// ======================= soundboard (UI side) =======================
static void SetPage(int page);
static void PadLoad(int i, const wchar_t* path, bool quiet = false)   // decode in the background
{
    SongFileJob* j = (SongFileJob*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(SongFileJob));
    if (!j) return;
    lstrcpynW(j->path, path, MAX_PATH);
    j->quiet = quiet; j->target = i; j->maxLen = RATE * 60;   // clips: up to 60 seconds
    HANDLE t = CreateThread(nullptr, 0, SongDecodeThread, j, 0, nullptr);
    if (t) CloseHandle(t); else HeapFree(GetProcessHeap(), 0, j);
}

static int SbButtonId(int s);
static void PadSetData(int i, short* data, unsigned len)   // swap a pad's clip safely
{
    short* old = gPads[i].data;
    gPads[i].stop = true;
    gPads[i].data = nullptr; gPads[i].len = 0;
    if (old) { Sleep(30); HeapFree(GetProcessHeap(), 0, old); }   // the audio thread has let go by now
    gPads[i].len = len; gPads[i].data = data;
    InvalidateRect(GetDlgItem(gWnd, SbButtonId(i)), nullptr, FALSE);
}

static int SbButtonId(int s)                    // the play button showing slot s (pads: the row on screen)
{
    return s < PAD_N ? IDC_PADPLAY + s % PADS : s < CLIP0 + CLIP_N ? IDC_CLIPPLAY + (s - CLIP0) % CLIPS : 0;
}
static void ClipSetBase(int c, short* data, unsigned len);

static void OnPadLoaded(SongFileJob* j)
{
    int i = j->target;
    if (j->ok && i >= CLIP0) {                  // a clip (imported, or last time's)
        ClipSetBase(i - CLIP0, j->data, j->len);
        lstrcpynW(gPadFile[i], j->path, MAX_PATH);
    } else if (j->ok) {
        PadSetData(i, j->data, j->len);
        lstrcpynW(gPadFile[i], j->path, MAX_PATH);
    } else {
        if (!j->quiet && !gPads[i].data && !lstrcmpiW(gPadFile[i], j->path)) gPadFile[i][0] = 0;   // free the pad again
        if (!j->quiet) MessageBoxW(gWnd, L"Couldn't open that audio file.\n\nMP3, WAV and FLAC files work (the first 60 seconds are used).",
                    L"Lag Effect - Soundboard", MB_ICONWARNING);
    }
    HeapFree(GetProcessHeap(), 0, j);
    InvalidateRect(GetDlgItem(gWnd, SbButtonId(i)), nullptr, FALSE);
}

static void PadClear(int i)
{
    PadSetData(i, nullptr, 0);
    gPadFile[i][0] = 0;
}

static void PadBrowse(int i)
{
    wchar_t path[MAX_PATH] = L"";
    OPENFILENAMEW o = {};
    o.lStructSize = sizeof(o);
    o.hwndOwner   = gWnd;
    o.lpstrFilter = L"Audio files (MP3, WAV, FLAC)\0*.mp3;*.wav;*.flac\0All files\0*.*\0";
    o.lpstrFile   = path;
    o.nMaxFile    = MAX_PATH;
    o.lpstrTitle  = L"Pick a sound for this pad";
    o.Flags       = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (GetOpenFileNameW(&o)) PadLoad(i, path);
}

static void PadName(int i, wchar_t* out, int cap)   // "C:\x\Air horn.mp3" -> "Air horn"
{
    const wchar_t* base = wcsrchr(gPadFile[i], L'\\');
    lstrcpynW(out, base ? base + 1 : gPadFile[i], cap);
    wchar_t* dot = wcsrchr(out, L'.');
    if (dot && dot != out) *dot = 0;
}

static void DrawPadButton(DRAWITEMSTRUCT* d)
{
    const bool clip = (int)d->CtlID >= IDC_CLIPPLAY;
    const int  shown = (int)d->CtlID - (clip ? IDC_CLIPPLAY : IDC_PADPLAY);   // 0..7 on its own tab
    const int  i = clip ? CLIP0 + ClipSlot(shown) : PadSlot(shown);            // slot in gPads
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    const Pad& p = gPads[i];
    bool has = p.data != nullptr, playing = p.playing && p.len;
    COLORREF cardC = gDark ? DK_CTL : LT_CARD;
    bool custom = !clip && gPadColor[i] != CLR_NONE;
    if (custom) cardC = gPadColor[i];
    bool lightCard = (GetRValue(cardC) * 299 + GetGValue(cardC) * 587 + GetBValue(cardC) * 114) / 1000 > 140;
    HBRUSH card = CreateSolidBrush(cardC);
    HPEN   pen  = CreatePen(PS_SOLID, 1, playing ? ACCENT : gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ ob = SelectObject(dc, card), op = SelectObject(dc, pen);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 10, 10);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(card); DeleteObject(pen);
    if (playing) {                              // progress bar along the bottom
        int w = (int)((rc.right - rc.left - 8) * (double)p.pos / p.len);
        RECT bar = { rc.left + 4, rc.bottom - 5, rc.left + 4 + w, rc.bottom - 3 };
        HBRUSH ab = CreateSolidBrush(ACCENT); FillRect(dc, &bar, ab); DeleteObject(ab);
    }
    SetBkMode(dc, TRANSPARENT);
    wchar_t num[8]; wsprintfW(num, L"%d", shown + 1);
    HGDIOBJ of = SelectObject(dc, gFontBold);
    SetTextColor(dc, playing ? ACCENT : gDark ? DK_DIM : RGB(120, 120, 120));
    RECT nr = { rc.left + 8, rc.top, rc.left + 26, rc.bottom - 2 };
    DrawTextW(dc, playing ? L"\x25B6" : num, -1, &nr, DT_SINGLELINE | DT_VCENTER | DT_LEFT);
    wchar_t name[MAX_PATH];
    if (has) { if (!clip && gPadName[i][0]) lstrcpynW(name, gPadName[i], MAX_PATH); else PadName(i, name, MAX_PATH); }
    else lstrcpynW(name, clip ? L"Empty: press Clip it" : L"Empty: drop a sound here", MAX_PATH);
    if (clip && gClipPinned[i - CLIP0]) { wchar_t t[MAX_PATH]; wsprintfW(t, L"\x2605 %s", name); lstrcpynW(name, t, MAX_PATH); }
    if (!clip && gPadRec && gPadRecSlot == i) {
        wsprintfW(name, L"\x25CF Recording %u s... click to stop", gPadRecPos / RATE);
        has = true;
    }
    if (!clip && has && (p.mode != PM_ONESHOT || (p.speed && p.speed != 100) || p.pitch)) {   // little tags for options
        wchar_t t[MAX_PATH]; lstrcpynW(t, name, MAX_PATH - 16);
        if (p.mode == PM_LOOP) lstrcatW(t, L"  \x221E"); else if (p.mode == PM_HOLD) lstrcatW(t, L"  [hold]"); else if (p.mode == PM_TOGGLE) lstrcatW(t, L"  [tog]");
        lstrcpynW(name, t, MAX_PATH);
    }
    SelectObject(dc, has ? gFontBold : gFont);
    COLORREF txt = has ? (TXT_C) : (gDark ? DK_DIM : RGB(120, 120, 120));
    if (custom) txt = lightCard ? RGB(20, 20, 20) : RGB(250, 250, 250);
    SetTextColor(dc, txt);
    RECT tr = { rc.left + 28, rc.top, rc.right - 6, rc.bottom - 2 };
    DrawTextW(dc, name, -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_LEFT | DT_END_ELLIPSIS);
    SelectObject(dc, of);
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) {
        RECT fr = rc; InflateRect(&fr, -3, -3);
        SetTextColor(dc, TXT_C);
        DrawFocusRect(dc, &fr);
    }
}

static void ClipTick();
static void MicTestTick();
static void PadRecordFinish();
static void OverlayUpdate();
static void AutoProfileTick();
static void PadMenu(int i, HWND anchor);
static void PadLoadFolder();
static void ClipMenu(int c, HWND anchor);
static void ClipHistory(HWND anchor);
static void SetClipBank(int b);
static void DrawClipBank(DRAWITEMSTRUCT* d);
static void PadTick()                           // every 50 ms: redraw pads that are playing or just stopped
{
    static bool was[SB_N];
    for (int i = 0; i < SB_N; i++) {
        bool now = gPads[i].playing;
        if ((now || was[i]) && i < TTS_SLOT && gPage == (i < PAD_N ? PAGE_SOUND : PAGE_CLIPS) &&
            (i < PAD_N ? i / PADS == gPadBank : (i - CLIP0) / CLIPS == gClipBank))
            InvalidateRect(GetDlgItem(gWnd, SbButtonId(i)), nullptr, FALSE);
        was[i] = now;
    }
    static bool wasPadRec = false;               // "record from my mic" finished (clicked again, or 10 s)
    if (gPadRec && !gRunning) gPadRec = false;
    if (wasPadRec && !gPadRec) PadRecordFinish();
    if (gPadRec && gPadRecSlot >= 0) InvalidateRect(GetDlgItem(gWnd, SbButtonId(gPadRecSlot)), nullptr, FALSE);
    wasPadRec = gPadRec;
    static DWORD lastBankDraw = 0;
    if (gPage == PAGE_SOUND && GetTickCount() - lastBankDraw > 200) {
        lastBankDraw = GetTickCount();
        for (int b = 0; b < PAD_BANKS; b++) InvalidateRect(GetDlgItem(gWnd, IDC_PADBANK0 + b), nullptr, FALSE);
    }
    ClipTick();
    MicTestTick();
    OverlayUpdate();
    AutoProfileTick();
    static int lastRunning = -1;                // hint line: remind to press Start
    if ((int)gRunning != lastRunning) {
        lastRunning = (int)gRunning;
        SetDlgItemTextW(gWnd, IDC_PADHINT, gRunning
            ? L"Drop MP3, WAV or FLAC files onto a pad (up to 60 s each). Plays on every output that isn't Off, "
              L"so Discord hears it. Right-click a playing pad to stop it."
            : L"Audio is stopped: press Start on the Main tab to use the soundboard.");
    }
}

static void OnDropFiles(HDROP drop)             // files dragged onto the window: load them into pads
{
    POINT pt; DragQueryPoint(drop, &pt);
    const bool clips = gPage == PAGE_CLIPS;     // on the Clips tab files become clips, otherwise pads
    const int  first = clips ? CLIP0 + gClipBank * CLIPS : gPadBank * PADS, count = clips ? CLIPS : PADS;
    int target = -1;
    if (gPage == PAGE_SOUND || clips)
        for (int i = 0; i < count; i++) {       // dropped on a row?
            RECT r; GetWindowRect(GetDlgItem(gWnd, SbButtonId(first + i)), &r);
            MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2);
            if (pt.y >= r.top - 5 && pt.y <= r.bottom + 5) { target = i; break; }
        }
    if (gPage != PAGE_SOUND && !clips) SetPage(PAGE_SOUND);
    UINT n = DragQueryFileW(drop, 0xFFFFFFFF, nullptr, 0);
    for (UINT f = 0; f < n; f++) {
        wchar_t path[MAX_PATH];
        if (!DragQueryFileW(drop, f, path, MAX_PATH)) continue;
        int slot = target;
        if (slot < 0 || f > 0) {                // next empty one (from the target onward)
            slot = -1;
            for (int k = 0; k < count && slot < 0; k++) {
                int i = ((target < 0 ? 0 : target) + k + (f > 0 && target >= 0 ? 1 : 0)) % count;
                if (!gPads[first + i].data && !gPadFile[first + i][0]) slot = i;
            }
            if (slot < 0) break;                // all full
        }
        if (clips) gClips[first - CLIP0 + slot].pendTs = gClips[first - CLIP0 + slot].pendTe = 0;
        lstrcpynW(gPadFile[first + slot], path, MAX_PATH);   // mark as taken so the next file goes elsewhere
        PadLoad(first + slot, path);
    }
    DragFinish(drop);
}

// ======================= instant replay clips =======================
static void ShowOsd(const wchar_t* text, bool on);
static wchar_t gClipDir[MAX_PATH];

static void ClipFolder()                        // %APPDATA%\LagEffect\Clips (next to the settings file)
{
    lstrcpynW(gClipDir, gIni, MAX_PATH);
    wchar_t* slash = wcsrchr(gClipDir, L'\\');
    if (slash) slash[1] = 0; else gClipDir[0] = 0;
    lstrcatW(gClipDir, L"Clips");
    CreateDirectoryW(gClipDir, nullptr);
}

static bool WriteWav(const wchar_t* path, const short* d, unsigned n)   // 48 kHz mono 16-bit
{
    HANDLE f = CreateFileW(path, GENERIC_WRITE, 0, nullptr, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, nullptr);
    if (f == INVALID_HANDLE_VALUE) {
        f = CreateFileW(path, GENERIC_WRITE, 0, nullptr, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, nullptr);
        if (f == INVALID_HANDLE_VALUE) return false;
    }
    unsigned bytes = n * 2;
    struct { char riff[4]; DWORD size; char wave[4], fmt[4]; DWORD fmtLen; WORD tag, ch; DWORD rate, bps; WORD align, bits;
             char data[4]; DWORD dataLen; } h = {
        { 'R','I','F','F' }, 36 + bytes, { 'W','A','V','E' }, { 'f','m','t',' ' }, 16, 1, 1, RATE, RATE * 2, 2, 16,
        { 'd','a','t','a' }, bytes };
    DWORD wr = 0;
    bool ok = WriteFile(f, &h, sizeof(h), &wr, nullptr) && wr == sizeof(h) &&
              WriteFile(f, d, bytes, &wr, nullptr) && wr == bytes;
    CloseHandle(f);
    if (!ok) DeleteFileW(path);
    return ok;
}

static void ClipApply(int c)                    // play the trimmed part (after a trim change)
{
    Pad& p = gPads[CLIP0 + c];
    Clip& k = gClips[c];
    p.stop = true;
    p.len = 0; p.data = nullptr;
    Sleep(30);                                  // the audio thread has let go of the old range
    if (k.base && k.te > k.ts) { p.len = k.te - k.ts; p.data = k.base + k.ts; }
    InvalidateRect(GetDlgItem(gWnd, IDC_CLIPPLAY + c % CLIPS), nullptr, FALSE);
}

static void ClipSetBase(int c, short* data, unsigned len)   // a new recording for a slot (or none)
{
    Pad& p = gPads[CLIP0 + c];
    Clip& k = gClips[c];
    short* old = k.base;
    p.stop = true;
    p.len = 0; p.data = nullptr;
    if (old) { Sleep(30); HeapFree(GetProcessHeap(), 0, old); }
    k.base = data; k.baseLen = data ? len : 0;
    k.ts = 0; k.te = k.baseLen;
    if (data && k.pendTs < len && k.pendTe <= len && (k.pendTe == 0 || k.pendTe > k.pendTs + RATE / 50)) {
        k.ts = k.pendTs;
        if (k.pendTe) k.te = k.pendTe;
    }
    k.pendTs = k.pendTe = 0;
    k.nUndo = k.nRedo = 0;
    if (data) { p.len = k.te - k.ts; p.data = k.base + k.ts; }
    InvalidateRect(GetDlgItem(gWnd, IDC_CLIPPLAY + c % CLIPS), nullptr, FALSE);
}

static bool InClipFolder(const wchar_t* path)
{
    int n = lstrlenW(gClipDir);
    return n > 0 && CompareStringOrdinal(path, Min(n, lstrlenW(path)), gClipDir, n, TRUE) == CSTR_EQUAL && path[n] == L'\\';
}

static void SetClipBank(int b);
static void ClipShiftUp(int c)                  // clip c was removed: the ones after it move up (no gaps)
{
    int last = -1;
    for (int j = CLIP_N - 1; j > c; j--) if (gClips[j].base || gPadFile[CLIP0 + j][0]) { last = j; break; }
    if (last < 0) return;                       // nothing after it
    for (int j = c; j <= last; j++) { Pad& p = gPads[CLIP0 + j]; p.stop = true; p.len = 0; p.data = nullptr; }
    Sleep(30);                                  // (the audio thread has let go of them by now)
    for (int j = c; j < last; j++) {
        Pad& d = gPads[CLIP0 + j]; const Pad& s2 = gPads[CLIP0 + j + 1];
        d.vol = s2.vol; d.mode = s2.mode; d.speed = s2.speed; d.pitch = s2.pitch; d.fadeInMs = s2.fadeInMs; d.fadeOutMs = s2.fadeOutMs;
        gClips[j] = gClips[j + 1];              // (its recording moves with it)
        lstrcpynW(gPadFile[CLIP0 + j], gPadFile[CLIP0 + j + 1], MAX_PATH);
        gClipPinned[j] = gClipPinned[j + 1]; gClipStamp[j] = gClipStamp[j + 1];
    }
    Clip& e = gClips[last];                     // the last one is empty now
    e.base = nullptr; e.baseLen = 0; e.ts = e.te = e.pendTs = e.pendTe = 0; e.nUndo = e.nRedo = 0;
    gPadFile[CLIP0 + last][0] = 0; gClipPinned[last] = false; gClipStamp[last] = 0; gPads[CLIP0 + last].vol = 100;
    for (int j = c; j < last; j++) {
        Pad& p = gPads[CLIP0 + j]; const Clip& k = gClips[j];
        if (k.base) { p.len = k.te - k.ts; p.data = k.base + k.ts; }
    }
    SetClipBank(gClipBank);                     // (the rows on screen show their new clips)
}
static void ClipClear(int c)                    // remove from the board; our own recordings go to the Recycle Bin
{
    wchar_t* path = gPadFile[CLIP0 + c];
    if (path[0] && InClipFolder(path) && GetFileAttributesW(path) != INVALID_FILE_ATTRIBUTES) {
        wchar_t from[MAX_PATH + 2] = {};        // double-null terminated
        lstrcpynW(from, path, MAX_PATH);
        SHFILEOPSTRUCTW op = {};
        op.hwnd   = gWnd;
        op.wFunc  = FO_DELETE;
        op.pFrom  = from;
        op.fFlags = FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_SILENT | FOF_NOERRORUI;
        SHFileOperationW(&op);
    }
    gClips[c].pendTs = gClips[c].pendTe = 0;
    ClipSetBase(c, nullptr, 0);
    path[0] = 0;
}

// Where the sound is in a recording: from just before the first sound to just after the last (non-destructive trim).
static bool FindSoundEnds(const short* d, unsigned n, unsigned* ts, unsigned* te)
{
    const unsigned FR = RATE / 100;             // 10 ms frames
    unsigned frames = n / FR;
    if (frames < 3) return false;
    float peak = 0;
    for (unsigned f = 0; f < frames; f++) {
        double e = 0; for (unsigned j = 0; j < FR; j++) { float v = d[f * FR + j] / 32768.0f; e += v * v; }
        float r = sqrtf((float)(e / FR)); if (r > peak) peak = r;
    }
    float thr = peak * 0.06f > 0.003f ? peak * 0.06f : 0.003f;   // 24 dB under the loudest part, or -50 dBFS
    int first = -1, last = -1;
    for (unsigned f = 0; f < frames; f++) {
        double e = 0; for (unsigned j = 0; j < FR; j++) { float v = d[f * FR + j] / 32768.0f; e += v * v; }
        if (sqrtf((float)(e / FR)) > thr) { if (first < 0) first = (int)f; last = (int)f; }
    }
    if (first < 0) return false;
    long long a = (long long)first * FR - RATE * 12 / 100, b = (long long)(last + 1) * FR + RATE / 5;   // keep 120 ms before, 200 ms after
    if (a < 0) a = 0; if (b > n) b = n;
    if (b - a < RATE / 10) return false;
    *ts = (unsigned)a; *te = (unsigned)b;
    return true;
}

static void ClipNow()                           // save the last N seconds as a clip
{
    if (!gFeatClips) return;
    if (gRecSource == REC_OFF) { ShowOsd(L"Clip recording is off", false); return; }
    if (!gRunning)             { ShowOsd(L"Press Start to record clips", false); return; }
    const unsigned N = (unsigned)gRecSeconds * RATE;
    const bool useV = RecHasVoice(gRecSource) && gRecVoice.buf;
    const bool useP = RecHasOther(gRecSource) && gRecRunning && gRecPc.buf;
    // snapshot where each ring is (the audio threads keep writing behind us)
    const unsigned wv = gRecVoice.w, fv = gRecVoice.fill, wp = gRecPc.w, fp = gRecPc.fill;
    const unsigned nv = useV ? Min(N, fv) : 0, np = useP ? Min(N, fp) : 0;
    const unsigned len = Max(nv, np);
    if (len < RATE / 4) { ShowOsd(L"Nothing recorded yet", false); return; }
    short* out = (short*)HeapAlloc(GetProcessHeap(), 0, len * sizeof(short));
    if (!out) return;
    auto at = [&](const RecRing& r, unsigned w, unsigned n, unsigned k) -> float {   // k-th sample of the clip
        if (k < len - n) return 0.0f;           // this source has less history: pad the start with silence
        unsigned idx = (w + REC_LEN - n + (k - (len - n))) % REC_LEN;
        return r.buf[idx] * (1.0f / 32768.0f);
    };
    float peak = 0;                             // voice + PC can add up past full scale: scale down if needed
    for (unsigned k = 0; k < len; k++) {
        float v = (nv ? at(gRecVoice, wv, nv, k) : 0.0f) + (np ? at(gRecPc, wp, np, k) : 0.0f);
        float a = v < 0 ? -v : v; if (a > peak) peak = a;
    }
    const float g = peak > 0.98f ? 0.98f / peak : 1.0f;
    for (unsigned k = 0; k < len; k++) {
        float v = ((nv ? at(gRecVoice, wv, nv, k) : 0.0f) + (np ? at(gRecPc, wp, np, k) : 0.0f)) * g;
        out[k] = (short)(v * 32767.0f);
    }
    for (unsigned k = 0; k < 96 && k < len; k++) { out[k] = (short)(out[k] * (k / 96.0f)); out[len - 1 - k] = (short)(out[len - 1 - k] * (k / 96.0f)); }

    ClipFolder();
    SYSTEMTIME t; GetLocalTime(&t);
    wchar_t path[MAX_PATH];
    wsprintfW(path, L"%s\\Clip %02d-%02d %02d.%02d.%02d.wav", gClipDir, t.wMonth, t.wDay, t.wHour, t.wMinute, t.wSecond);
    for (int n = 2; GetFileAttributesW(path) != INVALID_FILE_ATTRIBUTES && n < 100; n++)
        wsprintfW(path, L"%s\\Clip %02d-%02d %02d.%02d.%02d (%d).wav", gClipDir, t.wMonth, t.wDay, t.wHour, t.wMinute, t.wSecond, n);
    bool saved = WriteWav(path, out, len);

    if (gClipSeparate && nv && np) {            // also: your voice and the PC / Discord sound on their own
        short* tr = (short*)HeapAlloc(GetProcessHeap(), 0, len * sizeof(short));
        if (tr) {
            wchar_t base[MAX_PATH], tp[MAX_PATH]; lstrcpynW(base, path, MAX_PATH);
            wchar_t* dot = wcsrchr(base, L'.'); if (dot) *dot = 0;
            for (unsigned k = 0; k < len; k++) tr[k] = (short)(at(gRecVoice, wv, nv, k) * 32767.0f);
            wsprintfW(tp, L"%s (voice).wav", base); WriteWav(tp, tr, len);
            for (unsigned k = 0; k < len; k++) tr[k] = (short)(at(gRecPc, wp, np, k) * 32767.0f);
            wsprintfW(tp, L"%s (%s).wav", base, RecIsDiscord(gRecSource) ? L"discord" : L"pc"); WriteWav(tp, tr, len);
            HeapFree(GetProcessHeap(), 0, tr);
        }
    }
    int slot = -1;
    for (int k = 0; k < CLIP_N && slot < 0; k++) {   // first empty slot, starting on the page you're looking at
        int c = (gClipBank * CLIPS + k) % CLIP_N;
        if (!gClips[c].base && !gPadFile[CLIP0 + c][0]) slot = c;
    }
    if (slot < 0 && gClipReplace) {             // full: replace the oldest clip that isn't pinned
        unsigned oldest = 0xFFFFFFFF;
        for (int c = 0; c < CLIP_N; c++) if (!gClipPinned[c] && gClipStamp[c] < oldest) { oldest = gClipStamp[c]; slot = c; }
        if (slot >= 0) {
            ClipSetBase(slot, nullptr, 0);      // its file stays in the Clips folder (see History)
            gPadFile[CLIP0 + slot][0] = 0;
        }
    }
    wchar_t msg[64];
    if (slot >= 0) {
        gClipStamp[slot] = gClipStampNext++;
        gClipPinned[slot] = false;
        gClips[slot].pendTs = gClips[slot].pendTe = 0;
        unsigned a, b;                          // Auto-trim: start where the sound starts (Reset in Trim undoes it)
        if (gClipAutoTrim && FindSoundEnds(out, len, &a, &b)) { gClips[slot].pendTs = a; gClips[slot].pendTe = b >= len ? 0 : b; }
        ClipSetBase(slot, out, len);
        if (slot / CLIPS != gClipBank) SetClipBank(slot / CLIPS);   // show the page it landed on
        if (saved) lstrcpynW(gPadFile[CLIP0 + slot], path, MAX_PATH);
        else       wsprintfW(gPadFile[CLIP0 + slot], L"%s\\Clip %02d.%02d.%02d (not saved)", gClipDir, t.wHour, t.wMinute, t.wSecond);
        wsprintfW(msg, L"Clipped the last %d s", (len + RATE / 2) / RATE);
    } else {
        HeapFree(GetProcessHeap(), 0, out);
        lstrcpynW(msg, saved ? L"Clip saved (all slots pinned / full)" : L"Couldn't save the clip", 64);
    }
    ShowOsd(msg, slot >= 0 || saved);
}

// PC sound for clips: everything playing on the PC except Lag Effect itself.
static void RecPcCallback(ma_device*, void*, const void* input, ma_uint32 frames)
{
    const float* in = (const float*)input;      // stereo
    for (ma_uint32 f = 0; f < frames; f++) RecPut(gRecPc, in ? (in[f * 2] + in[f * 2 + 1]) * 0.5f : 0.0f);
}

static void RecNotify(const ma_device_notification* n)
{
    if (n->type == ma_device_notification_type_stopped && !gStopping) gRecLost = true;
}

static bool RecStartDevice(DWORD pid, bool exclude)
{
    if (pid) {                                  // everything but Lag Effect: Windows' process loopback
        gRecLost = false;
        if (!ProcLoopStart(&gRecPL, pid, exclude, RecPcCallback, &gRecLost)) return false;
        gRecPLOn = true;
        gRecRunning = true;
        return true;
    }
    ma_device_config cfg = ma_device_config_init(ma_device_type_loopback);
    cfg.capture.format   = ma_format_f32;
    cfg.capture.channels = 2;
    cfg.sampleRate       = RATE;
    cfg.dataCallback     = RecPcCallback;
    cfg.notificationCallback = RecNotify;
    cfg.wasapi.loopbackProcessID      = pid;
    cfg.wasapi.loopbackProcessExclude = exclude;
    if (ma_device_init(&gCtx, &cfg, &gRecDev) != MA_SUCCESS) return false;
    if (ma_device_start(&gRecDev) != MA_SUCCESS) { ma_device_uninit(&gRecDev); return false; }
    gRecRunning = true;
    gRecLost = false;
    return true;
}

static void RecRestart()                        // source changed or audio (re)started: begin a fresh buffer
{
    gRecVoice.fill = 0; gRecPc.fill = 0;
}

// Discord runs as several Discord.exe processes; the first one started is the parent of the rest, so
// recording its process tree gets everyone's voices (and Discord's own sounds) and nothing else.
static DWORD FindDiscordPid()
{
    static ProcInfo procs[2048];
    int n = SnapProcs(procs, 2048);
    auto isDiscord = [](const wchar_t* exe) {
        return !lstrcmpiW(exe, L"Discord.exe") || !lstrcmpiW(exe, L"DiscordPTB.exe") || !lstrcmpiW(exe, L"DiscordCanary.exe");
    };
    for (int i = 0; i < n; i++) {
        if (!isDiscord(procs[i].exe)) continue;
        bool parentIsDiscord = false;
        for (int k = 0; k < n; k++)
            if (procs[k].pid == procs[i].parent && isDiscord(procs[k].exe)) { parentIsDiscord = true; break; }
        if (!parentIsDiscord) return procs[i].pid;
    }
    return 0;
}

static void UpdateRecCapture()                  // every 50 ms: keep the PC-sound / Discord capture matching the settings
{
    static bool wasRunning = false;
    static DWORD retryAt = 0, lastAlive = 0, target = 0;
    static int targetSrc = -1;                  // which kind of capture is running (0 PC sound, 1 Discord)
    static int fallbackRetries = 0;
    if (gRunning && !wasRunning) RecRestart();
    wasRunning = gRunning;
    gRecVoiceOn = gRunning && gFeatClips && RecHasVoice(gRecSource);
    const bool want = gRunning && gCtxOk && gFeatClips && RecHasOther(gRecSource);
    const bool discord = RecIsDiscord(gRecSource);
    const DWORD now = GetTickCount();
    if (gRecRunning && discord && now - lastAlive > 3000) {   // Discord closed or restarted? find it again
        lastAlive = now;
        if (!PidAlive(target)) gRecLost = true;
    }
    if (gRecRunning && (!want || gRecLost || targetSrc != (int)discord)) {
        RecDevStop();
        gRecRunning = false;
        if (gRecLost) retryAt = now + 1000;
        if (targetSrc != (int)discord) { gRecPc.fill = 0; retryAt = now; fallbackRetries = 0; }
    }
    if (!want) { gRecPcState = 0; fallbackRetries = 0; targetSrc = -1; return; }
    if (targetSrc != (int)discord && !gRecRunning) retryAt = Min(retryAt, now);   // switched kind: start right away
    // Recording the whole output (state 2) also picks up Lag Effect itself: try leaving it out again a few times.
    if (gRecRunning && !discord && gRecPcState == 2 && fallbackRetries < 3 && (int)(now - retryAt) >= 0) {
        fallbackRetries++;
        RecDevStop();
        gRecRunning = false;
        if (RecStartDevice(GetCurrentProcessId(), true)) { gRecPcState = 1; return; }
        if (!RecStartDevice(0, false)) { gRecPcState = 3; retryAt = now + 5000; return; }
        retryAt = now + 5000;
        return;
    }
    if (gRecRunning || (int)(now - retryAt) < 0) return;
    gRecPc.fill = 0;
    targetSrc = discord;
    if (discord) {                              // only Discord's sound: no speaker fallback (that would be everything)
        target = FindDiscordPid();
        lastAlive = now;
        if (!target)                            { gRecPcState = 4; retryAt = now + 2000; }
        else if (RecStartDevice(target, false)) gRecPcState = 1;
        else                                    { gRecPcState = 3; retryAt = now + 5000; }
        return;
    }
    if (RecStartDevice(GetCurrentProcessId(), true)) gRecPcState = 1;
    else if (RecStartDevice(0, false))               { gRecPcState = 2; retryAt = now + 5000; }   // the whole output
    else { gRecPcState = 3; retryAt = now + 5000; }
}

static void ClipTick()                          // every 50 ms
{
    UpdateRecCapture();
    wchar_t t[256];
    static const wchar_t* what[REC_N] = { L"your voice + PC sound", L"your voice", L"PC sound", L"", L"Discord", L"your voice + Discord" };
    const wchar_t* other = RecIsDiscord(gRecSource) ? L"Discord" : L"PC sound";
    if (gRecSource == REC_OFF)  lstrcpynW(t, L"Recording is off: pick what to record above.", 256);
    else if (!gRunning)         lstrcpynW(t, L"Audio is stopped: press Start on the Main tab to record clips.", 256);
    else if (RecHasOther(gRecSource) && gRecPcState == 4)
        lstrcpynW(t, RecHasVoice(gRecSource) ? L"Discord isn't open: clips will have your voice only until it is."
                                             : L"Waiting for Discord to open...", 256);
    else if (RecHasOther(gRecSource) && gRecPcState == 3)
        wsprintfW(t, RecHasVoice(gRecSource) ? L"Couldn't record %s: clips will have your voice only." : L"Couldn't record %s. Retrying...", other);
    else {
        wsprintfW(t, L"Holding the last %d s of %s in memory. Nothing is saved until you clip.", gRecSeconds, what[gRecSource]);
        if (RecHasOther(gRecSource) && !RecIsDiscord(gRecSource) && gRecPcState == 2)
            wsprintfW(t, L"Holding the last %d s of %s in memory. Note: PC sound also includes Lag Effect's own output here.",
                      gRecSeconds, what[gRecSource]);
    }
    wchar_t cur[256];
    GetDlgItemTextW(gWnd, IDC_RECSTATUS, cur, 256);
    if (lstrcmpW(cur, t)) SetDlgItemTextW(gWnd, IDC_RECSTATUS, t);
}

static void ClipBrowse(int c)                   // import a sound file into an empty clip slot
{
    wchar_t path[MAX_PATH] = L"";
    OPENFILENAMEW o = {};
    o.lStructSize = sizeof(o);
    o.hwndOwner   = gWnd;
    o.lpstrFilter = L"Audio files (MP3, WAV, FLAC)\0*.mp3;*.wav;*.flac\0All files\0*.*\0";
    o.lpstrFile   = path;
    o.nMaxFile    = MAX_PATH;
    o.lpstrTitle  = L"Pick a sound for this clip slot";
    o.Flags       = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (GetOpenFileNameW(&o)) { gClips[c].pendTs = gClips[c].pendTe = 0; PadLoad(CLIP0 + c, path); }
}

// ---------------- trim editor: waveform, listen back privately, undo ----------------
enum { IDT_WAVE = 101, IDT_PLAY, IDT_UNDO, IDT_REDO, IDT_RESET, IDT_EXPORT, IDT_DONE, IDT_INFO, IDT_NAME, IDT_HINT, IDT_NAMELBL, IDT_AUTO };
#define TRIM_W     620
#define TRIM_H     292
#define WAVE_X     16
#define WAVE_Y     52
#define WAVE_W     588
#define WAVE_H     130
static int      gTrimClip = -1;
static int      gTrimDrag = 0;                  // 1 = dragging start, 2 = end
static int      gTrimActive = 1;                // handle the arrow keys move
static int      gTrimLastNudge = 0;             // coalesces arrow-key nudges into one undo step
static TrimState gTrimFrom;
static bool     gTrimDirty = false;
static short    gWaveMin[WAVE_W], gWaveMax[WAVE_W];
static wchar_t  gTrimOrigName[MAX_PATH];
// private preview: plays on your default speakers/headphones only
static ma_device         gPrevDev;
static bool              gPrevRunning = false;
static const short*      gPrevData = nullptr;
static volatile unsigned gPrevPos = 0, gPrevEnd = 0;
static volatile float    gPrevGain = 1.0f;

static void PrevCallback(ma_device*, void* output, const void*, ma_uint32 frames)
{
    float* out = (float*)output;
    unsigned pos = gPrevPos, end = gPrevEnd;
    for (ma_uint32 f = 0; f < frames; f++) {
        float v = 0;
        if (pos < end) {
            v = gPrevData[pos] * (1.0f / 32768.0f) * gPrevGain;
            if (end - pos < 240) v *= (end - pos) / 240.0f;
            pos++;
        }
        out[f * 2] = out[f * 2 + 1] = v;
    }
    gPrevPos = pos;
}

static void PrevStop()
{
    if (gPrevRunning) { ma_device_uninit(&gPrevDev); gPrevRunning = false; }
    if (gTrimWnd) { SetDlgItemTextW(gTrimWnd, IDT_PLAY, L"\x25B6  Listen"); InvalidateRect(GetDlgItem(gTrimWnd, IDT_WAVE), nullptr, FALSE); }
}

static bool PrevPlay(const short* d, unsigned from, unsigned to, float gain)   // play on your default speakers only
{
    PrevStop();
    if (!gCtxOk || !d || to <= from) return false;
    gPrevData = d; gPrevPos = from; gPrevEnd = to; gPrevGain = gain;
    ma_device_config cfg = ma_device_config_init(ma_device_type_playback);
    cfg.playback.format   = ma_format_f32;
    cfg.playback.channels = 2;
    cfg.sampleRate        = RATE;
    cfg.dataCallback      = PrevCallback;
    if (ma_device_init(&gCtx, &cfg, &gPrevDev) != MA_SUCCESS) return false;
    if (ma_device_start(&gPrevDev) != MA_SUCCESS) { ma_device_uninit(&gPrevDev); return false; }
    gPrevRunning = true;
    return true;
}

static void PrevStart()                         // trim editor: listen to the trimmed part
{
    const Clip& k = gClips[gTrimClip];
    if (PrevPlay(k.base, k.ts, k.te, gPads[CLIP0 + gTrimClip].vol / 100.0f)) SetDlgItemTextW(gTrimWnd, IDT_PLAY, L"\x25A0  Stop");
}

static void TrimInfo()                          // "Start 1.20 s  ·  End 9.85 s  ·  Length 8.65 s" + button states
{
    const Clip& k = gClips[gTrimClip];
    auto sec = [](unsigned smp, wchar_t* b) { unsigned cs = (unsigned)((smp * 100ull + RATE / 2) / RATE); wsprintfW(b, L"%u.%02u", cs / 100, cs % 100); };
    wchar_t a[16], b[16], c[16], t[128];
    sec(k.ts, a); sec(k.te, b); sec(k.te - k.ts, c);
    wsprintfW(t, L"Start %s s     End %s s     Length %s s", a, b, c);
    SetDlgItemTextW(gTrimWnd, IDT_INFO, t);
    EnableWindow(GetDlgItem(gTrimWnd, IDT_UNDO), k.nUndo > 0);
    EnableWindow(GetDlgItem(gTrimWnd, IDT_REDO), k.nRedo > 0);
    EnableWindow(GetDlgItem(gTrimWnd, IDT_RESET), k.ts != 0 || k.te != k.baseLen);
    InvalidateRect(GetDlgItem(gTrimWnd, IDT_WAVE), nullptr, FALSE);
}

static void TrimChanged()                       // the clip on the board follows shortly after (not on every pixel)
{
    gTrimDirty = true;
    SetTimer(gTrimWnd, 2, 250, nullptr);
    TrimInfo();
}

static void TrimPushUndo(int c, TrimState st)
{
    Clip& k = gClips[c];
    if (k.nUndo == TRIM_HIST) { memmove(k.undo, k.undo + 1, sizeof(TrimState) * (TRIM_HIST - 1)); k.nUndo--; }
    k.undo[k.nUndo++] = st;
    k.nRedo = 0;
}

static void TrimUndo(bool redo)
{
    Clip& k = gClips[gTrimClip];
    TrimState* from = redo ? k.redo : k.undo; int& nf = redo ? k.nRedo : k.nUndo;
    TrimState* to   = redo ? k.undo : k.redo; int& nt = redo ? k.nUndo : k.nRedo;
    if (!nf) return;
    if (nt == TRIM_HIST) { memmove(to, to + 1, sizeof(TrimState) * (TRIM_HIST - 1)); nt--; }
    to[nt++] = { k.ts, k.te };
    TrimState st = from[--nf];
    k.ts = st.s; k.te = st.e;
    gTrimLastNudge = 0;
    TrimChanged();
}

static void TrimReset()
{
    Clip& k = gClips[gTrimClip];
    if (k.ts == 0 && k.te == k.baseLen) return;
    TrimPushUndo(gTrimClip, { k.ts, k.te });
    k.ts = 0; k.te = k.baseLen;
    gTrimLastNudge = 0;
    TrimChanged();
}

static void TrimSetHandle(int handle, long long smp)   // keeps at least 50 ms selected
{
    Clip& k = gClips[gTrimClip];
    const long long minLen = RATE / 20;
    if (handle == 1) k.ts = (unsigned)Max(0LL, Min(smp, (long long)k.te - minLen));
    else             k.te = (unsigned)Min((long long)k.baseLen, Max(smp, (long long)k.ts + minLen));
}

static void TrimNudge(int dir, bool big)        // arrow keys: move the last-used edge by 10 ms (Shift: 100 ms)
{
    Clip& k = gClips[gTrimClip];
    if (gTrimLastNudge != gTrimActive) TrimPushUndo(gTrimClip, { k.ts, k.te });
    gTrimLastNudge = gTrimActive;
    long long step = (big ? RATE / 10 : RATE / 100) * dir;
    TrimSetHandle(gTrimActive, (long long)(gTrimActive == 1 ? k.ts : k.te) + step);
    TrimChanged();
}

static void TrimExport()                        // save just the trimmed part as a new WAV
{
    const Clip& k = gClips[gTrimClip];
    wchar_t path[MAX_PATH], name[MAX_PATH];
    GetDlgItemTextW(gTrimWnd, IDT_NAME, name, MAX_PATH - 20);
    wsprintfW(path, L"%s (trimmed).wav", name);
    for (wchar_t* q = path; *q; q++) if (wcschr(L"\\/:*?\"<>|", *q)) *q = L'_';
    OPENFILENAMEW o = {};
    o.lStructSize = sizeof(o);
    o.hwndOwner   = gTrimWnd;
    o.lpstrFilter = L"WAV audio\0*.wav\0";
    o.lpstrFile   = path;
    o.nMaxFile    = MAX_PATH;
    o.lpstrDefExt = L"wav";
    o.lpstrTitle  = L"Export the trimmed clip";
    o.Flags       = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (!GetSaveFileNameW(&o)) return;
    DeleteFileW(path);                          // overwrite was confirmed
    if (!WriteWav(path, k.base + k.ts, k.te - k.ts))
        MessageBoxW(gTrimWnd, L"Couldn't save the file there.", L"Lag Effect - Clips", MB_ICONWARNING);
}

static void TrimRename()                        // the Name box renames the clip's file
{
    int i = CLIP0 + gTrimClip;
    wchar_t name[MAX_PATH];
    GetDlgItemTextW(gTrimWnd, IDT_NAME, name, MAX_PATH - 8);
    for (wchar_t* q = name; *q; q++) if (wcschr(L"\\/:*?\"<>|", *q)) *q = L'_';
    while (name[0] == L' ') memmove(name, name + 1, lstrlenW(name) * sizeof(wchar_t));
    if (!name[0] || !lstrcmpW(name, gTrimOrigName) || !InClipFolder(gPadFile[i])) return;   // never rename your own files
    wchar_t* old = gPadFile[i];
    const wchar_t* slash = wcsrchr(old, L'\\');
    const wchar_t* dot = wcsrchr(old, L'.');
    if (!slash) return;
    wchar_t np[MAX_PATH];
    int dirLen = (int)(slash - old) + 1;
    lstrcpynW(np, old, dirLen + 1);
    if (dirLen + lstrlenW(name) + 6 >= MAX_PATH) return;
    lstrcatW(np, name);
    lstrcatW(np, dot && dot > slash ? dot : L".wav");
    if (GetFileAttributesW(old) == INVALID_FILE_ATTRIBUTES || MoveFileW(old, np)) lstrcpynW(old, np, MAX_PATH);
    else MessageBoxW(gTrimWnd, L"Couldn't rename the clip (is that name already taken?).", L"Lag Effect - Clips", MB_ICONWARNING);
    InvalidateRect(GetDlgItem(gWnd, IDC_CLIPPLAY + gTrimClip % CLIPS), nullptr, FALSE);
}

static void TrimClose()
{
    if (!gTrimWnd) return;
    PrevStop();
    TrimRename();
    if (gTrimDirty) { gTrimDirty = false; ClipApply(gTrimClip); }
    EnableWindow(gWnd, TRUE);
    HWND w = gTrimWnd;
    gTrimWnd = nullptr;
    DestroyWindow(w);
    SetForegroundWindow(gWnd);
    SetFocus(GetDlgItem(gWnd, IDC_CLIPTRIM + gTrimClip % CLIPS));
    gTrimClip = -1;
}

static int WaveX(unsigned smp) { const Clip& k = gClips[gTrimClip]; return k.baseLen ? (int)((double)smp / k.baseLen * WAVE_W) : 0; }
static long long WaveSample(int x) { const Clip& k = gClips[gTrimClip]; return (long long)((double)x / WAVE_W * k.baseLen); }

static LRESULT CALLBACK WaveProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC pdc = BeginPaint(h, &ps);
        RECT rc; GetClientRect(h, &rc);
        HDC dc = CreateCompatibleDC(pdc);
        HBITMAP bmp = CreateCompatibleBitmap(pdc, rc.right, rc.bottom);
        HGDIOBJ obmp = SelectObject(dc, bmp);
        FillRect(dc, &rc, BgSolid());
        HBRUSH card = CreateSolidBrush(gDark ? DK_CTL : LT_CARD);
        HPEN   cpen = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : LT_BORDER);
        HGDIOBJ ob = SelectObject(dc, card), op = SelectObject(dc, cpen);
        RoundRect(dc, 0, 0, rc.right, rc.bottom, 10, 10);
        SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(card); DeleteObject(cpen);
        if (gTrimClip >= 0) {
            const Clip& k = gClips[gTrimClip];
            const int x0 = WaveX(k.ts), x1 = WaveX(k.te), mid = rc.bottom / 2, half = rc.bottom / 2 - 8;
            HPEN in  = CreatePen(PS_SOLID, 1, ACCENT);
            HPEN out = CreatePen(PS_SOLID, 1, gDark ? RGB(80, 80, 80) : RGB(190, 190, 190));
            for (int x = 0; x < WAVE_W && x < rc.right; x++) {
                SelectObject(dc, x >= x0 && x <= x1 ? in : out);
                int y0 = mid - gWaveMax[x] * half / 32768, y1 = mid - gWaveMin[x] * half / 32768;
                if (y1 <= y0) y1 = y0 + 1;
                MoveToEx(dc, x, y0, nullptr); LineTo(dc, x, y1 + 1);
            }
            HBRUSH hb = CreateSolidBrush(ACCENT);
            for (int e = 0; e < 2; e++) {       // the two edges, with grab tabs
                int x = e ? x1 : x0;
                RECT line = { x - 1, 2, x + 1, rc.bottom - 2 };
                FillRect(dc, &line, hb);
                RECT tab = e ? RECT{ x - 9, 2, x + 1, 16 } : RECT{ x - 1, 2, x + 9, 16 };
                FillRect(dc, &tab, hb);
                tab = e ? RECT{ x - 9, rc.bottom - 16, x + 1, rc.bottom - 2 } : RECT{ x - 1, rc.bottom - 16, x + 9, rc.bottom - 2 };
                FillRect(dc, &tab, hb);
            }
            DeleteObject(hb);
            if (gPrevRunning) {                 // where the preview is
                int x = WaveX(gPrevPos);
                HPEN pp = CreatePen(PS_SOLID, 2, gDark ? RGB(240, 240, 240) : RGB(20, 20, 20));
                SelectObject(dc, pp);
                MoveToEx(dc, x, 4, nullptr); LineTo(dc, x, rc.bottom - 4);
                SelectObject(dc, op); DeleteObject(pp);
            }
            SelectObject(dc, op);
            DeleteObject(in); DeleteObject(out);
        }
        BitBlt(pdc, 0, 0, rc.right, rc.bottom, dc, 0, 0, SRCCOPY);
        SelectObject(dc, obmp); DeleteObject(bmp); DeleteDC(dc);
        EndPaint(h, &ps);
        return 0;
    }
    case WM_ERASEBKGND: return 1;
    case WM_SETCURSOR: {
        POINT pt; GetCursorPos(&pt); ScreenToClient(h, &pt);
        const Clip& k = gClips[gTrimClip];
        bool nearEdge = abs(pt.x - WaveX(k.ts)) <= 8 || abs(pt.x - WaveX(k.te)) <= 8;
        SetCursor(LoadCursorW(nullptr, nearEdge || gTrimDrag ? IDC_SIZEWE : IDC_HAND));
        return TRUE;
    }
    case WM_LBUTTONDOWN: {
        SetFocus(h);
        int x = (short)LOWORD(l);
        const Clip& k = gClips[gTrimClip];
        int ds = abs(x - WaveX(k.ts)), de = abs(x - WaveX(k.te));
        gTrimDrag = ds < de || (ds == de && x < WaveX(k.ts)) ? 1 : 2;   // whichever edge is closer
        gTrimActive = gTrimDrag;
        gTrimFrom = { k.ts, k.te };
        TrimSetHandle(gTrimDrag, WaveSample(x));
        SetCapture(h);
        TrimInfo();
        return 0;
    }
    case WM_MOUSEMOVE:
        if (gTrimDrag) { TrimSetHandle(gTrimDrag, WaveSample((short)LOWORD(l))); TrimInfo(); }
        return 0;
    case WM_LBUTTONUP: case WM_CAPTURECHANGED:
        if (gTrimDrag) {
            gTrimDrag = 0;
            if (m == WM_LBUTTONUP) ReleaseCapture();
            const Clip& k = gClips[gTrimClip];
            if (k.ts != gTrimFrom.s || k.te != gTrimFrom.e) { TrimPushUndo(gTrimClip, gTrimFrom); gTrimLastNudge = 0; TrimChanged(); }
        }
        return 0;
    case WM_GETDLGCODE: return DLGC_WANTARROWS;
    }
    return DefWindowProcW(h, m, w, l);
}

static LRESULT CtlColor(HWND h, UINT m, WPARAM w, LPARAM l);
static LRESULT CALLBACK TrimProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_COMMAND:
        switch (LOWORD(w)) {
        case IDT_PLAY:   if (gPrevRunning) PrevStop(); else PrevStart(); break;
        case IDT_UNDO:   TrimUndo(false); break;
        case IDT_REDO:   TrimUndo(true); break;
        case IDT_RESET:  TrimReset(); break;
        case IDT_AUTO: {                        // trim the silence off both ends (undoable)
            Clip& k = gClips[gTrimClip];
            unsigned a, b;
            if (FindSoundEnds(k.base, k.baseLen, &a, &b) && (a != k.ts || b != k.te)) {
                TrimPushUndo(gTrimClip, { k.ts, k.te });
                k.ts = a; k.te = b; gTrimLastNudge = 0;
                TrimChanged();
            }
            break;
        }
        case IDT_EXPORT: TrimExport(); break;
        case IDT_DONE: case IDCANCEL: TrimClose(); break;
        }
        return 0;
    case WM_TIMER:
        if (w == 1 && gPrevRunning) {           // follow the preview; stop at the end
            InvalidateRect(GetDlgItem(h, IDT_WAVE), nullptr, FALSE);
            if (gPrevPos >= gPrevEnd) PrevStop();
        } else if (w == 2) {
            KillTimer(h, 2);
            if (gTrimDirty && !gTrimDrag) { gTrimDirty = false; ClipApply(gTrimClip); }
        }
        return 0;
    case WM_CLOSE: TrimClose(); return 0;
    case WM_ERASEBKGND: { RECT rc; GetClientRect(h, &rc); FillRect((HDC)w, &rc, BgSolid()); return 1; }
    case WM_CTLCOLORSTATIC: case WM_CTLCOLORBTN: case WM_CTLCOLOREDIT: case WM_CTLCOLORLISTBOX:
        return CtlColor(h, m, w, l);
    }
    return DefWindowProcW(h, m, w, l);
}

static bool TrimKey(MSG* msg)                   // keyboard shortcuts in the trim editor
{
    if (!gTrimWnd || msg->message != WM_KEYDOWN || !(msg->hwnd == gTrimWnd || IsChild(gTrimWnd, msg->hwnd))) return false;
    bool ctrl = (GetKeyState(VK_CONTROL) & 0x8000) != 0, shift = (GetKeyState(VK_SHIFT) & 0x8000) != 0;
    if (msg->wParam == VK_ESCAPE) { TrimClose(); return true; }
    if (msg->hwnd == GetDlgItem(gTrimWnd, IDT_NAME)) {   // typing a name: only Enter is ours
        if (msg->wParam == VK_RETURN) { SetFocus(GetDlgItem(gTrimWnd, IDT_WAVE)); return true; }
        return false;
    }
    switch (msg->wParam) {
    case VK_SPACE: if (gPrevRunning) PrevStop(); else PrevStart(); return true;
    case 'Z': if (ctrl) { TrimUndo(shift); return true; } break;
    case 'Y': if (ctrl) { TrimUndo(true); return true; } break;
    case VK_LEFT:  TrimNudge(-1, shift); return true;
    case VK_RIGHT: TrimNudge(+1, shift); return true;
    case VK_HOME:  gTrimActive = 1; return true;
    case VK_END:   gTrimActive = 2; return true;
    }
    return false;
}

static void ThemeTitleBar(HWND w);
static void OpenTrim(int c)
{
    if (gTrimWnd || !gClips[c].base) return;
    gTrimClip = c;
    gTrimDirty = false; gTrimDrag = 0; gTrimActive = 1; gTrimLastNudge = 0;
    const Clip& k = gClips[c];
    for (int x = 0; x < WAVE_W; x++) {          // peak overview, one column per pixel
        unsigned a = (unsigned)((unsigned long long)x * k.baseLen / WAVE_W), b = (unsigned)((unsigned long long)(x + 1) * k.baseLen / WAVE_W);
        if (b <= a) b = a + 1;
        if (b > k.baseLen) b = k.baseLen;
        short lo = 0, hi = 0;
        for (unsigned i = a; i < b; i++) { short v = k.base[i]; if (v < lo) lo = v; if (v > hi) hi = v; }
        gWaveMin[x] = lo; gWaveMax[x] = hi;
    }
    DWORD style = WS_POPUP | WS_CAPTION | WS_SYSMENU | WS_CLIPCHILDREN;
    RECT r = { 0, 0, TRIM_W, TRIM_H };
    AdjustWindowRect(&r, style, FALSE);
    RECT mr; GetWindowRect(gWnd, &mr);
    int ww = r.right - r.left, wh = r.bottom - r.top;
    int x = (mr.left + mr.right - ww) / 2, y = mr.top + 90;
    gTrimWnd = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LagTrim", L"Trim clip", style, x, y, ww, wh, gWnd, nullptr, gInst, nullptr);
    if (!gTrimWnd) { gTrimClip = -1; return; }
    auto mk = [&](const wchar_t* cls, const wchar_t* text, DWORD st, int cx, int cy, int cw, int ch, int id, DWORD ex = 0) {
        HWND c2 = CreateWindowExW(ex, cls, text, WS_CHILD | WS_VISIBLE | st, cx, cy, cw, ch, gTrimWnd, (HMENU)(INT_PTR)id, gInst, nullptr);
        SendMessageW(c2, WM_SETFONT, (WPARAM)gFont, TRUE);
        return c2;
    };
    PadName(CLIP0 + c, gTrimOrigName, MAX_PATH);
    mk(L"STATIC", L"Name:", 0, 16, 18, 44, 20, IDT_NAMELBL);
    HWND nm = mk(L"EDIT", gTrimOrigName, WS_TABSTOP | ES_AUTOHSCROLL, 62, 15, 300, 23, IDT_NAME, WS_EX_CLIENTEDGE);
    SendMessageW(nm, EM_LIMITTEXT, 120, 0);
    if (!InClipFolder(gPadFile[CLIP0 + c])) SendMessageW(nm, EM_SETREADONLY, TRUE, 0);   // an imported file: leave its name alone
    mk(L"LagWave", L"", WS_TABSTOP, WAVE_X, WAVE_Y, WAVE_W, WAVE_H, IDT_WAVE);
    mk(L"STATIC", L"", SS_CENTER, 16, 190, WAVE_W, 20, IDT_INFO);
    mk(L"BUTTON", L"\x25B6  Listen", WS_TABSTOP, 16, 218, 92, 30, IDT_PLAY);
    mk(L"BUTTON", L"Undo", WS_TABSTOP, 114, 218, 68, 30, IDT_UNDO);
    mk(L"BUTTON", L"Redo", WS_TABSTOP, 188, 218, 68, 30, IDT_REDO);
    mk(L"BUTTON", L"Reset", WS_TABSTOP, 262, 218, 68, 30, IDT_RESET);
    mk(L"BUTTON", L"Cut silence", WS_TABSTOP, 336, 218, 92, 30, IDT_AUTO);
    mk(L"BUTTON", L"Export...", WS_TABSTOP, 434, 218, 80, 30, IDT_EXPORT);
    mk(L"BUTTON", L"Done", WS_TABSTOP | BS_DEFPUSHBUTTON, 520, 218, 84, 30, IDT_DONE);
    mk(L"STATIC", L"Drag the edges to trim. Listen plays only to you. Space plays, Ctrl+Z undoes, arrows nudge the edge. "
                  L"The full recording is always kept, so Reset brings it all back.", 0, 16, 254, WAVE_W, 34, IDT_HINT);
    ThemeTitleBar(gTrimWnd);
    EnumChildWindows(gTrimWnd, ThemeChild, 0);
    EnableWindow(gWnd, FALSE);
    TrimInfo();
    SetTimer(gTrimWnd, 1, 30, nullptr);
    ShowWindow(gTrimWnd, SW_SHOW);
    SetFocus(GetDlgItem(gTrimWnd, IDT_WAVE));
}

// ======================= profiles =======================
static void SetGateMode(int m);
static void FxKeyButtonText(int slot, wchar_t* buf, int cap);
// A profile is a snapshot of how you sound: the stutter effect, every Voice FX effect and knob, and the
// Mic tab. Not included: devices / outputs, hotkeys, soundboard, clips, theme and window settings.
// Saved as %APPDATA%\LagEffect\Profiles\<name>.ini; a profile's hotkey is saved under its name.
struct ProfVar { const wchar_t* key; volatile int* i; volatile bool* b; int* n; };
static const ProfVar PROF_VARS[] = {
    { L"fx_on", nullptr, &gFxOn, nullptr },         { L"voc_style", &gVocStyle, nullptr, nullptr },
    { L"voc_key", &gVocKey, nullptr, nullptr },     { L"voc_scale", &gVocScale, nullptr, nullptr },
    { L"voc_range", &gVocRange, nullptr, nullptr }, { L"voc_synth_other", nullptr, nullptr, &gVocSynthSaved },
    { L"radio_preset", &gRadioPreset, nullptr, nullptr },
    { L"fx_echo_style", &gEchoStyle, nullptr, nullptr }, { L"fx_dist_style", &gDistStyle, nullptr, nullptr },
    { L"fx_chorus_style", &gChoStyle, nullptr, nullptr }, { L"fx_muffle_style", &gMufStyle, nullptr, nullptr },
    { L"gate_mode", &gGateMode, nullptr, nullptr }, { L"ns_on", nullptr, &gNsOn, nullptr },
    { L"talkover", nullptr, &gTalkOver, nullptr },  { L"toggle", nullptr, &gToggleMode, nullptr },
    { L"random_lag", nullptr, &gRandLagOn, nullptr }, { L"random_lag_every_s", &gRandLagSec, nullptr, nullptr },
    { L"fx_harm_style", &gHarmStyle, nullptr, nullptr }, { L"broadcast_voice", nullptr, &gBroadcast, nullptr },
    { L"fx_harm_mute", nullptr, &gHarmMute, nullptr },
    { L"beat_sync", nullptr, &gBeatSync, nullptr }, { L"bpm", &gBpm, nullptr, nullptr }, { L"beat_division", &gBeatDiv, nullptr, nullptr },
};

static void ProfileDir(wchar_t* out)
{
    lstrcpynW(out, gIni, MAX_PATH);
    wchar_t* slash = wcsrchr(out, L'\\');
    if (slash) slash[1] = 0; else out[0] = 0;
    lstrcatW(out, L"Profiles");
    CreateDirectoryW(out, nullptr);
}
static void ProfilePath(const wchar_t* name, wchar_t* out)
{
    wchar_t dir[MAX_PATH]; ProfileDir(dir);
    wsprintfW(out, L"%s\\%s.ini", dir, name);
}
static void ProfileKeyName(const wchar_t* name, wchar_t* out) { wsprintfW(out, L"profile_hotkey_%s", name); }

static void ProfilesScan()                      // list profiles; their hotkeys follow their names
{
    int oldKeys[PROF_MAX][MAX_KEYS]; wchar_t oldNames[PROF_MAX][64]; int oldN = gProfCount;
    for (int i = 0; i < oldN; i++) { lstrcpynW(oldNames[i], gProfNames[i], 64); memcpy(oldKeys[i], gFxKeys[SLOT_PROF0 + i], sizeof(oldKeys[i])); }
    wchar_t dir[MAX_PATH], pat[MAX_PATH]; ProfileDir(dir);
    wsprintfW(pat, L"%s\\*.ini", dir);
    gProfCount = 0;
    WIN32_FIND_DATAW fd;
    HANDLE f = FindFirstFileW(pat, &fd);
    if (f != INVALID_HANDLE_VALUE) {
        do {
            if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) continue;
            wchar_t n[64]; lstrcpynW(n, fd.cFileName, 64);
            wchar_t* dot = wcsrchr(n, L'.'); if (dot) *dot = 0;
            if (!n[0] || gProfCount >= PROF_MAX) continue;
            int at = gProfCount;                // keep the list in alphabetical order
            while (at > 0 && lstrcmpiW(gProfNames[at - 1], n) > 0) { lstrcpynW(gProfNames[at], gProfNames[at - 1], 64); at--; }
            lstrcpynW(gProfNames[at], n, 64);
            gProfCount++;
        } while (FindNextFileW(f, &fd));
        FindClose(f);
    }
    for (int i = 0; i < PROF_MAX; i++) {
        memset(gFxKeys[SLOT_PROF0 + i], 0, sizeof(gFxKeys[0]));
        if (i >= gProfCount) continue;
        bool found = false;
        for (int k = 0; k < oldN && !found; k++)
            if (!lstrcmpiW(oldNames[k], gProfNames[i])) { memcpy(gFxKeys[SLOT_PROF0 + i], oldKeys[k], sizeof(oldKeys[k])); found = true; }
        if (!found) {                           // first time: read it from the settings file
            wchar_t key[96], b[64]; ProfileKeyName(gProfNames[i], key);
            GetPrivateProfileStringW(L"settings", key, L"", b, 64, gIni);
            const wchar_t* q = b;
            for (int j = 0; j < MAX_KEYS; j++) {
                gFxKeys[SLOT_PROF0 + i][j] = *q ? Iclamp(_wtoi(q), 0, 255) : 0;
                while (*q && *q != L',') q++;
                if (*q == L',') q++;
            }
        }
    }
}

static void ProfileKeysSave()
{
    for (int i = 0; i < gProfCount; i++) {
        wchar_t key[96], b[64]; ProfileKeyName(gProfNames[i], key);
        const int* k = gFxKeys[SLOT_PROF0 + i];
        if (k[0] || k[1] || k[2]) { wsprintfW(b, L"%d,%d,%d", k[0], k[1], k[2]); IniSet(key, b); }
        else IniSet(key, nullptr);
    }
}

static bool ProfileSave(const wchar_t* name)
{
    wchar_t path[MAX_PATH]; ProfilePath(name, path);
    auto put = [&](const wchar_t* key, int v) { wchar_t b[16]; wsprintfW(b, L"%d", v); WritePrivateProfileStringW(L"profile", key, b, path); };
    for (const ProfVar& v : PROF_VARS) put(v.key, v.i ? *v.i : v.b ? (int)*v.b : *v.n);
    for (const Range& r : gRanges) put(r.key, *r.var);
    for (const FxGroup& g : gFxGroups) put(g.key, *g.on ? 1 : 0);
    for (const Knob& k : gKnobs) put(k.key, *k.var);
    LayoutSave(path);                           // each profile keeps where you moved things to
    return GetFileAttributesW(path) != INVALID_FILE_ATTRIBUTES;
}

static void RefreshSoundUI()                    // after a profile changed lots of settings at once
{
    for (const Range& r : gRanges) SetDlgItemInt(gWnd, r.id, (UINT)*r.var, TRUE);
    for (int g = 0; g < FX_GROUPS; g++) CheckDlgButton(gWnd, IDC_FXGRP_ON + g, *gFxGroups[g].on ? BST_CHECKED : BST_UNCHECKED);
    SendDlgItemMessageW(gWnd, IDC_VOCSTYLE, CB_SETCURSEL, gVocStyle, 0);
    SendDlgItemMessageW(gWnd, IDC_VOCKEY, CB_SETCURSEL, gVocKey, 0);
    SendDlgItemMessageW(gWnd, IDC_VOCSCALE, CB_SETCURSEL, gVocScale, 0);
    SendDlgItemMessageW(gWnd, IDC_VOCRANGE, CB_SETCURSEL, gVocRange, 0);
    SendDlgItemMessageW(gWnd, IDC_RADIOPRESET, CB_SETCURSEL, gRadioPreset, 0);
    { SetDlgItemTextW(gWnd, IDC_RADIODESC, RADIO_DESC[Iclamp(gRadioPreset, 0, RADIO_N - 1)]); FitOne(GetDlgItem(gWnd, IDC_RADIODESC)); }
    SendDlgItemMessageW(gWnd, IDC_ECHOSTYLE, CB_SETCURSEL, gEchoStyle, 0);
    SendDlgItemMessageW(gWnd, IDC_DISTSTYLE, CB_SETCURSEL, gDistStyle, 0);
    SendDlgItemMessageW(gWnd, IDC_CHOSTYLE, CB_SETCURSEL, gChoStyle, 0);
    SendDlgItemMessageW(gWnd, IDC_MUFSTYLE, CB_SETCURSEL, gMufStyle, 0);
    gHarmStyle = Iclamp(gHarmStyle, 0, HARM_N - 1);
    SendDlgItemMessageW(gWnd, IDC_HARMSTYLE, CB_SETCURSEL, gHarmStyle, 0);
    SetDlgItemTextW(gWnd, IDC_HARMMUTE, HarmMuteText());
    CheckDlgButton(gWnd, IDC_BROADCAST, gBroadcast ? BST_CHECKED : BST_UNCHECKED);
    SetGateMode(gGateMode);
    CheckDlgButton(gWnd, IDC_NSON, gNsOn ? BST_CHECKED : BST_UNCHECKED);
    CheckDlgButton(gWnd, IDC_TALKON, gTalkOver ? BST_CHECKED : BST_UNCHECKED);
    CheckRadioButton(gWnd, IDC_HOLD, IDC_TOGGLE, gToggleMode ? IDC_TOGGLE : IDC_HOLD);
    CheckDlgButton(gWnd, IDC_RANDLAG, gRandLagOn ? BST_CHECKED : BST_UNCHECKED);
    SetDlgItemInt(gWnd, IDC_RANDSEC, (UINT)gRandLagSec, FALSE);
    CheckDlgButton(gWnd, IDC_BEATSYNC, gBeatSync ? BST_CHECKED : BST_UNCHECKED);
    SetDlgItemInt(gWnd, IDC_BPM, (UINT)gBpm, FALSE);
    SendDlgItemMessageW(gWnd, IDC_BEATDIV, CB_SETCURSEL, gBeatDiv, 0);
    InvalidateRect(GetDlgItem(gWnd, IDC_FXON), nullptr, FALSE);
    gFxResetReq = true;                         // start the effects clean
    SongStyleChanged();                         // Song style shows different controls; also redraws knobs
    UpdateStatus(true);
}

static bool ProfileLoad(int idx, bool osd)
{
    if (idx < 0 || idx >= gProfCount) return false;
    wchar_t path[MAX_PATH]; ProfilePath(gProfNames[idx], path);
    if (GetFileAttributesW(path) == INVALID_FILE_ATTRIBUTES) return false;
    auto get = [&](const wchar_t* key, int cur, int lo, int hi) {   // missing = keep what you have
        wchar_t b[32]; GetPrivateProfileStringW(L"profile", key, L"", b, 32, path);
        return b[0] ? Iclamp(_wtoi(b), lo, hi) : cur;
    };
    for (const ProfVar& v : PROF_VARS) {
        if (v.i) *v.i = get(v.key, *v.i, -100000, 100000);
        else if (v.b) *v.b = get(v.key, *v.b, 0, 1) != 0;
        else *v.n = get(v.key, *v.n, 0, 100);
    }
    gVocStyle = Iclamp(gVocStyle, 0, VOC_STYLES - 1); gVocKey = Iclamp(gVocKey, 0, 11);
    gVocScale = Iclamp(gVocScale, 0, VOC_SCALES - 1); gVocRange = Iclamp(gVocRange, 0, 2);
    gRadioPreset = Iclamp(gRadioPreset, 0, RADIO_N - 1); gGateMode = Iclamp(gGateMode, 0, 3);
    gEchoStyle = Iclamp(gEchoStyle, 0, ECHO_N - 1); gDistStyle = Iclamp(gDistStyle, 0, DIST_N - 1);
    gChoStyle = Iclamp(gChoStyle, 0, CHO_N - 1); gMufStyle = Iclamp(gMufStyle, 0, MUF_N - 1);
    gRandLagSec = Iclamp(gRandLagSec, 2, 120);
    for (const Range& r : gRanges) *r.var = get(r.key, *r.var, r.lo, r.hi);
    for (const FxGroup& g : gFxGroups) *g.on = get(g.key, *g.on, 0, 1) != 0;
    for (const Knob& k : gKnobs) *k.var = get(k.key, *k.var, k.lo, k.hi);
    gProfCur = idx;
    if (LayoutLoad(path, true)) LayoutSave(gIni);   // its layout (older profiles have none: keep the current one)
    RefreshSoundUI();
    if (osd) { wchar_t m[96]; wsprintfW(m, L"Profile: %s", gProfNames[idx]); ShowOsd(m, true); }
    return true;
}

static void ProfilesFill(const wchar_t* select)   // refresh the Settings dropdown
{
    HWND c = GetDlgItem(gWnd, IDC_PROFILE);
    SendMessageW(c, CB_RESETCONTENT, 0, 0);
    gProfSel = -1;
    for (int i = 0; i < gProfCount; i++) {
        SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)gProfNames[i]);
        if (select && !lstrcmpiW(gProfNames[i], select)) gProfSel = i;
    }
    if (gProfSel >= 0) SendMessageW(c, CB_SETCURSEL, gProfSel, 0); else SetWindowTextW(c, select ? select : L"");
    wchar_t kn[120];
    if (gProfSel >= 0) FxKeyButtonText(SLOT_PROF0 + gProfSel, kn, 120); else lstrcpynW(kn, L"This profile: (save one first)", 120);
    SetDlgItemTextW(gWnd, IDC_PROFKEY, kn); FitOne(GetDlgItem(gWnd, IDC_PROFKEY));
    EnableWindow(GetDlgItem(gWnd, IDC_PROFKEY), gProfSel >= 0);
    EnableWindow(GetDlgItem(gWnd, IDC_PROFDEL), gProfSel >= 0);
}

static void ProfileAppsLoad();
static void ProfileAutoInfo();
static void ProfileSaveClicked()
{
    wchar_t name[64];
    GetDlgItemTextW(gWnd, IDC_PROFILE, name, 64);
    for (wchar_t* q = name; *q; q++) if (wcschr(L"\\/:*?\"<>|.", *q)) *q = L'_';
    while (name[0] == L' ') memmove(name, name + 1, lstrlenW(name) * sizeof(wchar_t));
    for (int n = lstrlenW(name); n > 0 && name[n - 1] == L' '; n--) name[n - 1] = 0;
    if (!name[0]) { MessageBoxW(gWnd, L"Type a name for the profile first (like Gaming or Streaming).", L"Lag Effect - Profiles", MB_ICONINFORMATION); return; }
    bool exists = false;
    for (int i = 0; i < gProfCount; i++) if (!lstrcmpiW(gProfNames[i], name)) exists = true;
    if (!exists && gProfCount >= PROF_MAX) {
        MessageBoxW(gWnd, L"You can have up to 8 profiles. Delete one to make room.", L"Lag Effect - Profiles", MB_ICONINFORMATION);
        return;
    }
    if (exists) {
        wchar_t q[160]; wsprintfW(q, L"Replace \"%s\" with how you sound right now?", name);
        if (MessageBoxW(gWnd, q, L"Lag Effect - Profiles", MB_YESNO | MB_ICONQUESTION) != IDYES) return;
    }
    if (!ProfileSave(name)) { MessageBoxW(gWnd, L"Couldn't save the profile.", L"Lag Effect - Profiles", MB_ICONWARNING); return; }
    ProfilesScan();
    ProfileAppsLoad();
    for (int i = 0; i < gProfCount; i++) if (!lstrcmpiW(gProfNames[i], name)) gProfCur = i;
    ProfilesFill(name);
    ProfileAutoInfo();
}

static void ProfileDeleteClicked()
{
    if (gProfSel < 0) return;
    wchar_t q[160]; wsprintfW(q, L"Delete the profile \"%s\"?", gProfNames[gProfSel]);
    if (MessageBoxW(gWnd, q, L"Lag Effect - Profiles", MB_YESNO | MB_ICONQUESTION) != IDYES) return;
    wchar_t path[MAX_PATH], key[96]; ProfilePath(gProfNames[gProfSel], path); ProfileKeyName(gProfNames[gProfSel], key);
    DeleteFileW(path);
    IniSet(key, nullptr);
    gProfCur = -1;
    ProfilesScan();
    ProfilesFill(nullptr);
}

// ---- hold-to-activate effect hotkeys ----
// Holding the key turns the effect (and the Voice effects switch) on; letting go puts both back as they were.
static bool gHoldActive[1 + FX_GROUPS], gHoldPrevOn[1 + FX_GROUPS];
static bool gHoldMasterPrev = false;
static int  gHoldCount = 0;

static void HoldPress(int slot)                 // slot 0 = the Voice effects switch, 1+g = effect g
{
    if (gHoldActive[slot]) return;
    gHoldActive[slot] = true;
    if (gHoldCount++ == 0) gHoldMasterPrev = gFxOn;
    if (slot > 0) { gHoldPrevOn[slot] = *gFxGroups[slot - 1].on; SetFxGroupOn(slot - 1, true); }
    if (!gFxOn) SetFxOn(true);
    UpdateStatus(true);
}

static void HoldRelease(int slot)
{
    if (!gHoldActive[slot]) return;
    gHoldActive[slot] = false;
    if (slot > 0) SetFxGroupOn(slot - 1, gHoldPrevOn[slot]);
    if (--gHoldCount <= 0) { gHoldCount = 0; if (!gHoldMasterPrev) SetFxOn(false); }
    UpdateStatus(true);
}

// ---- mic test ----
static void MicTestStart()
{
    if (!gRunning) {
        MessageBoxW(gWnd, L"Press Start on the Main tab first, then test.", L"Lag Effect - Mic test", MB_ICONINFORMATION);
        return;
    }
    PrevStop();
    gTestPos = 0; gTestLen = 0;
    gTestRec = true;
}

static void MicTestTick()                       // every 50 ms: countdown, then play it back
{
    static bool wasRec = false;
    static wchar_t last[48];
    if (gTestRec && !gRunning) {                // audio stopped mid-test: keep what we got
        gTestRec = false;
        gTestLen = gTestPos > (unsigned)RATE / 2 ? gTestPos : 0;
        if (!gTestLen) wasRec = false;
    }
    wchar_t t[48];
    if (gTestRec) wsprintfW(t, L"Recording... %u", (TEST_LEN - gTestPos) / RATE + 1);
    else if (gPrevRunning && gPrevData == gTestBuf) lstrcpynW(t, L"\x25A0  Stop", 48);
    else lstrcpynW(t, L"\x25CF  Record 5 s", 48);
    if (lstrcmpW(t, last)) { lstrcpynW(last, t, 48); SetDlgItemTextW(gWnd, IDC_MICTEST, t); }
    if (wasRec && !gTestRec && gTestLen) PrevPlay(gTestBuf, 0, gTestLen, 1.0f);   // done: hear it
    wasRec = gTestRec;
    EnableWindow(GetDlgItem(gWnd, IDC_MICPLAY), gTestLen > 0 && !gTestRec);
    if (gPrevRunning && !gTrimWnd && gPrevPos >= gPrevEnd) PrevStop();       // finished playing
}

static void SetFxStyle(int g, int style);
static void ApplyCharacter(int c);
static void ResetFxGroup(int g);
static void SetKnobVar(volatile int* var, int v);
// ======================= small text prompt (name a character, rename a pad...) =======================
static HWND gInputWnd = nullptr;
static bool gInputDone = false, gInputOk = false;
static wchar_t* gInputBuf = nullptr; static int gInputCap = 0;
static LRESULT CALLBACK InputProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_COMMAND:
        if (LOWORD(w) == IDOK)     { GetDlgItemTextW(h, 101, gInputBuf, gInputCap); gInputOk = true; gInputDone = true; }
        if (LOWORD(w) == IDCANCEL) { gInputOk = false; gInputDone = true; }
        return 0;
    case WM_CLOSE: gInputOk = false; gInputDone = true; return 0;
    case WM_ERASEBKGND: { RECT rc; GetClientRect(h, &rc); FillRect((HDC)w, &rc, BgSolid()); return 1; }
    case WM_CTLCOLORSTATIC: case WM_CTLCOLORBTN: case WM_CTLCOLOREDIT: return CtlColor(h, m, w, l);
    }
    return DefWindowProcW(h, m, w, l);
}
static bool InputBox(const wchar_t* title, const wchar_t* prompt, wchar_t* buf, int cap)
{
    static bool reg = false;
    if (!reg) { WNDCLASSW wc = {}; wc.lpfnWndProc = InputProc; wc.hInstance = gInst; wc.hCursor = LoadCursorW(nullptr, IDC_ARROW);
                wc.hIcon = gIcon; wc.lpszClassName = L"LagInput"; RegisterClassW(&wc); reg = true; }
    DWORD style = WS_POPUP | WS_CAPTION | WS_SYSMENU;
    RECT r = { 0, 0, 360, 128 }; AdjustWindowRect(&r, style, FALSE);
    RECT mr; GetWindowRect(gWnd, &mr);
    int ww = r.right - r.left, wh = r.bottom - r.top;
    gInputWnd = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LagInput", title, style, (mr.left + mr.right - ww) / 2, mr.top + 150, ww, wh,
                                gWnd, nullptr, gInst, nullptr);
    if (!gInputWnd) return false;
    auto mk = [&](const wchar_t* cls, const wchar_t* t, DWORD st, int x, int y, int w2, int h2, int id, DWORD ex = 0) {
        HWND c = CreateWindowExW(ex, cls, t, WS_CHILD | WS_VISIBLE | st, x, y, w2, h2, gInputWnd, (HMENU)(INT_PTR)id, gInst, nullptr);
        SendMessageW(c, WM_SETFONT, (WPARAM)gFont, TRUE); return c;
    };
    mk(L"STATIC", prompt, 0, 16, 14, 328, 20, 100);
    HWND e = mk(L"EDIT", buf, WS_TABSTOP | ES_AUTOHSCROLL, 16, 40, 328, 24, 101, WS_EX_CLIENTEDGE);
    SendMessageW(e, EM_LIMITTEXT, cap - 1, 0);
    SendMessageW(e, EM_SETSEL, 0, -1);
    mk(L"BUTTON", L"OK", WS_TABSTOP | BS_DEFPUSHBUTTON, 168, 82, 84, 28, IDOK);
    mk(L"BUTTON", L"Cancel", WS_TABSTOP, 260, 82, 84, 28, IDCANCEL);
    ThemeTitleBar(gInputWnd);
    EnumChildWindows(gInputWnd, ThemeChild, 0);
    gInputBuf = buf; gInputCap = cap; gInputDone = false; gInputOk = false;
    EnableWindow(gWnd, FALSE);
    ShowWindow(gInputWnd, SW_SHOW);
    SetFocus(e);
    MSG msg;
    while (!gInputDone && GetMessageW(&msg, nullptr, 0, 0) > 0) {
        if (IsDialogMessageW(gInputWnd, &msg)) continue;
        TranslateMessage(&msg); DispatchMessageW(&msg);
    }
    EnableWindow(gWnd, TRUE);
    DestroyWindow(gInputWnd); gInputWnd = nullptr;
    SetForegroundWindow(gWnd);
    return gInputOk && buf[0];
}

// ======================= your own characters =======================
// Saved as %APPDATA%\LagEffect\Characters\<name>.ini: every Voice FX effect (on/off, knobs, styles), nothing else.
static void MyCharDir(wchar_t* out)
{
    lstrcpynW(out, gIni, MAX_PATH);
    wchar_t* slash = wcsrchr(out, L'\\'); if (slash) slash[1] = 0; else out[0] = 0;
    lstrcatW(out, L"Characters"); CreateDirectoryW(out, nullptr);
}
static void MyCharsScan()
{
    wchar_t dir[MAX_PATH], pat[MAX_PATH]; MyCharDir(dir); wsprintfW(pat, L"%s\\*.ini", dir);
    gMyCharN = 0;
    WIN32_FIND_DATAW fd; HANDLE f = FindFirstFileW(pat, &fd);
    if (f == INVALID_HANDLE_VALUE) return;
    do {
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY || gMyCharN >= MAX_MYCHARS) continue;
        wchar_t n[64]; lstrcpynW(n, fd.cFileName, 64); wchar_t* dot = wcsrchr(n, L'.'); if (dot) *dot = 0;
        if (n[0]) lstrcpynW(gMyChars[gMyCharN++], n, 64);
    } while (FindNextFileW(f, &fd));
    FindClose(f);
}
// FX-only settings: the effects' on/off, every Voice FX knob, and the styles
static void MyCharSave(const wchar_t* name)
{
    wchar_t dir[MAX_PATH], path[MAX_PATH]; MyCharDir(dir); wsprintfW(path, L"%s\\%s.ini", dir, name);
    auto put = [&](const wchar_t* key, int v) { wchar_t b[16]; wsprintfW(b, L"%d", v); WritePrivateProfileStringW(L"character", key, b, path); };
    for (const FxGroup& g : gFxGroups) put(g.key, *g.on ? 1 : 0);
    for (const Knob& k : gKnobs) if (k.group < FX_GROUPS) put(k.key, *k.var);
    put(L"voc_style", gVocStyle); put(L"voc_key", gVocKey); put(L"voc_scale", gVocScale); put(L"voc_range", gVocRange);
    put(L"radio_preset", gRadioPreset); put(L"fx_echo_style", gEchoStyle); put(L"fx_dist_style", gDistStyle);
    put(L"fx_chorus_style", gChoStyle); put(L"fx_muffle_style", gMufStyle); put(L"fx_harm_style", gHarmStyle);
}
static void MyCharLoad(const wchar_t* name)
{
    wchar_t dir[MAX_PATH], path[MAX_PATH]; MyCharDir(dir); wsprintfW(path, L"%s\\%s.ini", dir, name);
    auto get = [&](const wchar_t* key, int cur, int lo, int hi) {
        wchar_t b[32]; GetPrivateProfileStringW(L"character", key, L"", b, 32, path);
        return b[0] ? Iclamp(_wtoi(b), lo, hi) : cur;
    };
    for (const FxGroup& g : gFxGroups) *g.on = get(g.key, 0, 0, 1) != 0;   // effects it doesn't mention: off
    for (const Knob& k : gKnobs) if (k.group < FX_GROUPS) *k.var = get(k.key, k.def, k.lo, k.hi);
    gVocStyle = get(L"voc_style", gVocStyle, 0, VOC_STYLES - 1); gVocKey = get(L"voc_key", gVocKey, 0, 11);
    gVocScale = get(L"voc_scale", gVocScale, 0, VOC_SCALES - 1); gVocRange = get(L"voc_range", gVocRange, 0, 2);
    gRadioPreset = get(L"radio_preset", gRadioPreset, 0, RADIO_N - 1);
    gEchoStyle = get(L"fx_echo_style", gEchoStyle, 0, ECHO_N - 1); gDistStyle = get(L"fx_dist_style", gDistStyle, 0, DIST_N - 1);
    gChoStyle = get(L"fx_chorus_style", gChoStyle, 0, CHO_N - 1); gMufStyle = get(L"fx_muffle_style", gMufStyle, 0, MUF_N - 1);
    gHarmStyle = get(L"fx_harm_style", gHarmStyle, 0, HARM_N - 1);
    gFxOn = true;
    RefreshSoundUI();
    wchar_t m[96]; wsprintfW(m, L"Character: %s", name); ShowOsd(m, true);
}
static void FillCharCombo()                     // built-ins, then yours, then the actions
{
    HWND c = GetDlgItem(gWnd, IDC_FXCHAR);
    SendMessageW(c, CB_RESETCONTENT, 0, 0);
    for (int i = 0; i < CHAR_N; i++) SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)CHARACTERS[i]);
    for (int i = 0; i < gMyCharN; i++) { wchar_t t[80]; wsprintfW(t, L"\x2605 %s", gMyChars[i]); SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)t); }
    SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"Save my current voice...");
    if (gMyCharN) SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"Delete one of mine...");
    SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"Clear all effects");
    SendMessageW(c, CB_SETCURSEL, 0, 0);
}
static void OnCharacterPicked(int sel)
{
    int saveAt = CHAR_N + gMyCharN, delAt = gMyCharN ? saveAt + 1 : -1, clearAt = saveAt + (gMyCharN ? 2 : 1);
    if (sel > 0 && sel < CHAR_N) ApplyCharacter(sel);
    else if (sel >= CHAR_N && sel < saveAt) MyCharLoad(gMyChars[sel - CHAR_N]);
    else if (sel == saveAt) {
        wchar_t name[64] = L"";
        if (InputBox(L"Save my voice", L"Name for this character (it goes in the Character list):", name, 40)) {
            for (wchar_t* q = name; *q; q++) if (wcschr(L"\\/:*?\"<>|.", *q)) *q = L'_';
            if (gMyCharN >= MAX_MYCHARS) MessageBoxW(gWnd, L"You can save up to 16 characters. Delete one first.", L"Lag Effect", MB_ICONINFORMATION);
            else { MyCharSave(name); MyCharsScan(); wchar_t m[96]; wsprintfW(m, L"Saved: %s", name); ShowOsd(m, true); }
        }
    } else if (sel == delAt) {
        HMENU menu = CreatePopupMenu();
        for (int i = 0; i < gMyCharN; i++) AppendMenuW(menu, MF_STRING, 1 + i, gMyChars[i]);
        POINT pt; GetCursorPos(&pt);
        int pick = TrackPopupMenu(menu, TPM_RETURNCMD | TPM_NONOTIFY, pt.x, pt.y, 0, gWnd, nullptr);
        DestroyMenu(menu);
        if (pick > 0) {
            wchar_t q[128]; wsprintfW(q, L"Delete your character \"%s\"?", gMyChars[pick - 1]);
            if (MessageBoxW(gWnd, q, L"Lag Effect", MB_YESNO | MB_ICONQUESTION) == IDYES) {
                wchar_t dir[MAX_PATH], path[MAX_PATH]; MyCharDir(dir); wsprintfW(path, L"%s\\%s.ini", dir, gMyChars[pick - 1]);
                DeleteFileW(path); MyCharsScan();
            }
        }
    } else if (sel == clearAt) {
        for (int g = 0; g < FX_GROUPS; g++) SetFxGroupOn(g, false);
        ShowOsd(L"All voice effects cleared", false);
    }
    FillCharCombo();
}

// Surprise me: a random but sensible voice.
static void SurpriseMe()
{
    static unsigned seed = GetTickCount() | 1;
    auto rnd = [&](int n) { seed = seed * 1664525u + 1013904223u; return (int)((seed >> 8) % (unsigned)n); };
    for (int g = 0; g < FX_GROUPS; g++) SetFxGroupOn(g, false);
    static const int pool[] = { KG_PITCH, KG_FORMANT, KG_GENDER, KG_HARM, KG_WHISPER, KG_GROWL, KG_RING, KG_DIST, KG_WAH,
                                KG_CHORUS, KG_WOBBLE, KG_MUFFLE, KG_ECHO, KG_GHOST, KG_SHIMMER, KG_REVERB, KG_RADIO };
    const int poolN = (int)(sizeof(pool) / sizeof(pool[0]));
    int want = 2 + rnd(3), picked[5], n = 0;
    wchar_t msg[160] = L"Surprise: ";
    while (n < want) {
        int g = pool[rnd(poolN)];
        bool dup = false; for (int i = 0; i < n; i++) if (picked[i] == g) dup = true;
        if (dup) continue;
        picked[n++] = g;
        ResetFxGroup(g);
        for (int i = 0; i < KNOB_N; i++) {      // near the default, within a sensible part of the range
            const Knob& k = gKnobs[i];
            if (k.group != g) continue;
            int span = k.hi - k.lo, v = k.def + (rnd(1001) - 500) * span * 6 / 10000;
            if (k.offText && v <= k.lo) v = k.lo + span / 4;            // don't pick "off"
            SetKnobValue(GetDlgItem(gWnd, IDC_KNOB + i), i, Iclamp(v, k.lo, k.hi));
        }
        if (g == KG_ECHO)  SetFxStyle(KG_ECHO, rnd(ECHO_N));
        if (g == KG_DIST)  SetFxStyle(KG_DIST, rnd(DIST_N));
        if (g == KG_CHORUS) SetFxStyle(KG_CHORUS, rnd(CHO_N));
        if (g == KG_MUFFLE) SetFxStyle(KG_MUFFLE, rnd(MUF_N));
        if (g == KG_HARM)  { gHarmStyle = rnd(HARM_N); SendDlgItemMessageW(gWnd, IDC_HARMSTYLE, CB_SETCURSEL, gHarmStyle, 0); }
        if (g == KG_RADIO) { gRadioPreset = rnd(RADIO_N); SendDlgItemMessageW(gWnd, IDC_RADIOPRESET, CB_SETCURSEL, gRadioPreset, 0);
                             { SetDlgItemTextW(gWnd, IDC_RADIODESC, RADIO_DESC[gRadioPreset]); FitOne(GetDlgItem(gWnd, IDC_RADIODESC)); } }
        SetFxGroupOn(g, true);
        if (n > 1) lstrcatW(msg, L" + ");
        lstrcatW(msg, gFxGroups[g].title);
    }
    SetFxOn(true);
    ShowOsd(msg, true);
    UpdateStatus(true);
}

static void UpdateUi();
static void SaveSettings();
static bool gNoSaveOnExit = false;
static void ApplyTheme();
static bool PictureLoad(const wchar_t* path);
static void PictureRebuild();
static void ApplyOpacity();
static void ApplyFont();
static void MyCharLoad(const wchar_t* name);
static void MyCharDir(wchar_t* out);
static void ApplyCharacter(int c);
static void SetMute(bool on);
static bool StartAudio(bool quiet);
static void StopAudio();
static void PadKey(int i, bool pressed, bool released);
static void SetPadBank(int b);
// ======================= overlay, beeps, conflicts, auto-profiles, command line, export =======================
static HWND gOverlay = nullptr;
static wchar_t gOverlayText[3][64];

static void OverlayTexts(wchar_t t[3][64])
{
    lstrcpynW(t[0], !gRunning ? L"\x25CB  Stopped" : gMicMuted ? L"\x25CF  Muted" :
                    (gPttMode == 1 && !gPttHeld) ? L"\x25CF  Push to talk" : gLooping ? L"\x25CF  LAGGING" : L"\x25CF  Live", 64);
    int on = 0; wchar_t names[64] = L"";
    for (int g = 0; g < FX_GROUPS; g++) if (*gFxGroups[g].on) { if (on < 3) { if (on) lstrcatW(names, L", "); lstrcatW(names, gFxGroups[g].title); } on++; }
    if (!gFxOn || !on) lstrcpynW(t[1], L"Voice FX off", 64);
    else if (on > 3) wsprintfW(t[1], L"FX: %s +%d", names, on - 3);
    else wsprintfW(t[1], L"FX: %s", names);
    if (gProfCur >= 0) wsprintfW(t[2], L"Profile: %s", gProfNames[gProfCur]); else lstrcpynW(t[2], L"", 64);
}

static LRESULT CALLBACK OverlayProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_NCHITTEST: return HTCAPTION;        // drag it anywhere
    case WM_EXITSIZEMOVE: { RECT r; GetWindowRect(h, &r); gOverlayX = r.left; gOverlayY = r.top; return 0; }
    case WM_ERASEBKGND: return 1;
    case WM_NCRBUTTONUP: gOverlayOn = false; ShowWindow(h, SW_HIDE); CheckDlgButton(gWnd, IDC_OVERLAY, BST_UNCHECKED); return 0;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps);
        RECT rc; GetClientRect(h, &rc);
        HBRUSH bg = CreateSolidBrush(RGB(24, 24, 28)); FillRect(dc, &rc, bg); DeleteObject(bg);
        HBRUSH ab = CreateSolidBrush(gMicMuted || gLooping ? RGB(220, 60, 60) : ACCENT);
        RECT bar = { 0, 0, 4, rc.bottom }; FillRect(dc, &bar, ab); DeleteObject(ab);
        SetBkMode(dc, TRANSPARENT);
        HGDIOBJ of = SelectObject(dc, gFontBold);
        for (int i = 0; i < 3; i++) {
            SetTextColor(dc, i == 0 ? RGB(250, 250, 250) : RGB(190, 190, 195));
            if (i == 1) SelectObject(dc, gFont);
            RECT tr = { 12, 6 + i * 18, rc.right - 6, 24 + i * 18 };
            DrawTextW(dc, gOverlayText[i], -1, &tr, DT_SINGLELINE | DT_LEFT | DT_END_ELLIPSIS);
        }
        SelectObject(dc, of);
        EndPaint(h, &ps);
        return 0;
    }
    }
    return DefWindowProcW(h, m, w, l);
}

static void OverlayUpdate()                      // every 50 ms (cheap): show/hide, repaint when the text changes
{
    if (!gOverlayOn) { if (gOverlay && IsWindowVisible(gOverlay)) ShowWindow(gOverlay, SW_HIDE); return; }
    if (!gOverlay) {
        WNDCLASSW wc = {}; wc.lpfnWndProc = OverlayProc; wc.hInstance = gInst; wc.hCursor = LoadCursorW(nullptr, IDC_SIZEALL);
        wc.lpszClassName = L"LagOverlay"; RegisterClassW(&wc);
        int x = gOverlayX, y = gOverlayY;
        if (x == INT_MIN || !MonitorFromPoint(POINT{ x + 10, y + 10 }, MONITOR_DEFAULTTONULL)) { x = 24; y = 24; }
        gOverlay = CreateWindowExW(WS_EX_TOPMOST | WS_EX_TOOLWINDOW | WS_EX_LAYERED | WS_EX_NOACTIVATE, L"LagOverlay", L"",
                                   WS_POPUP, x, y, SC(230), SC(64), nullptr, nullptr, gInst, nullptr);
        if (!gOverlay) return;
        SetLayeredWindowAttributes(gOverlay, 0, 225, LWA_ALPHA);
        SetWindowRgn(gOverlay, CreateRoundRectRgn(0, 0, SC(230) + 1, SC(64) + 1, 12, 12), FALSE);
    }
    if (!IsWindowVisible(gOverlay)) ShowWindow(gOverlay, SW_SHOWNOACTIVATE);
    wchar_t t[3][64]; OverlayTexts(t);
    if (memcmp(t, gOverlayText, sizeof(t))) { memcpy(gOverlayText, t, sizeof(t)); InvalidateRect(gOverlay, nullptr, FALSE); }
}

// Beeps: a short, quiet blip only you hear (your default speakers / headphones) when a hotkey switches something.
static void HotkeyBeep(bool on)
{
    static short buf[RATE / 8];
    const int n = RATE * 7 / 100;
    for (int i = 0; i < n; i++) {
        float f = on ? (i < n / 2 ? 880.0f : 1320.0f) : (i < n / 2 ? 660.0f : 440.0f);
        float env = i < 96 ? i / 96.0f : (n - i < 480 ? (n - i) / 480.0f : 1.0f);
        buf[i] = (short)(sinf(6.2831853f * f * i / RATE) * env * 6000.0f);
    }
    if (!gPrevRunning || gPrevData == buf) PrevPlay(buf, 0, n, 1.0f);   // never interrupt a clip being previewed
}

// Who else uses a key combination (for the conflict warning).
static void SlotName(int slot, wchar_t* out, int cap)
{
    if (slot == 0) lstrcpynW(out, L"Voice effects", cap);
    else if (slot < FX_KEY_SLOTS) wsprintfW(out, L"%s (Voice FX)", gFxGroups[slot - 1].title);
    else if (slot == SLOT_MUTE) lstrcpynW(out, L"Mute mic", cap);
    else if (slot >= SLOT_PAD0 && slot < SLOT_PAD0 + PADS) wsprintfW(out, L"Pad %d", slot - SLOT_PAD0 + 1);
    else if (slot == SLOT_CLIPNOW) lstrcpynW(out, L"Clip it", cap);
    else if (slot >= SLOT_CLIP0 && slot < SLOT_CLIP0 + CLIPS) wsprintfW(out, L"Clip %d", slot - SLOT_CLIP0 + 1);
    else if (slot == SLOT_REWIND) lstrcpynW(out, L"Rewind", cap);
    else if (slot == SLOT_REPEAT) lstrcpynW(out, L"Repeat word", cap);
    else if (slot == SLOT_PADBANK) lstrcpynW(out, L"Next soundboard page", cap);
    else if (slot == SLOT_PROFNEXT) lstrcpynW(out, L"Next profile", cap);
    else if (slot == SLOT_TAPESTOP) lstrcpynW(out, L"Tape stop", cap);
    else if (slot == SLOT_DIVE) lstrcpynW(out, L"Pitch dive", cap);
    else if (slot == SLOT_PTT) lstrcpynW(out, L"Push-to-talk", cap);
    else if (slot >= SLOT_PROF0 && slot - SLOT_PROF0 < PROF_MAX) {
        if (slot - SLOT_PROF0 < gProfCount) wsprintfW(out, L"Profile \"%s\"", gProfNames[slot - SLOT_PROF0]); else lstrcpynW(out, L"a profile", cap);
    }
    else if (slot >= SLOT_MIX0 && slot < SLOT_MIXOUT0) {
        static const wchar_t* ca[MIXA_N] = { L"volume up", L"volume down", L"mute", L"solo", L"duck", L"hold" };
        wsprintfW(out, L"Mixer channel %d %s", (slot - SLOT_MIX0) / MIXA_N + 1, ca[(slot - SLOT_MIX0) % MIXA_N]);
    }
    else if (slot >= SLOT_MIXOUT0 && slot < KEY_SLOTS) {
        static const wchar_t* oa[MIXO_N] = { L"volume up", L"volume down", L"mute" };
        wsprintfW(out, L"Mixer output %d %s", (slot - SLOT_MIXOUT0) / MIXO_N + 1, oa[(slot - SLOT_MIXOUT0) % MIXO_N]);
    }
    else lstrcpynW(out, L"another hotkey", cap);
}

static bool SameCombo(const volatile int* a, const volatile int* b)
{
    int x[MAX_KEYS], y[MAX_KEYS], nx = 0, ny = 0;
    for (int i = 0; i < MAX_KEYS; i++) { if (a[i]) x[nx++] = a[i]; if (b[i]) y[ny++] = b[i]; }
    if (!nx || nx != ny) return false;
    for (int i = 0; i < nx; i++) { bool f = false; for (int k = 0; k < ny; k++) if (x[i] == y[k]) f = true; if (!f) return false; }
    return true;
}

static void CheckHotkeyConflict(volatile int* target)   // right after a hotkey was set
{
    wchar_t who[128] = L"";
    if (target != gHotkeys && SameCombo(target, gHotkeys)) lstrcpynW(who, L"the stutter effect", 128);
    for (int slot = 0; slot < KEY_SLOTS && !who[0]; slot++)
        if ((volatile int*)gFxKeys[slot] != target && SameCombo(target, gFxKeys[slot])) SlotName(slot, who, 128);
    if (!who[0]) return;
    wchar_t q[256]; wsprintfW(q, L"That key is already used for %s. Pressing it will do both.\n\nKeep it anyway?", who);
    if (MessageBoxW(gWnd, q, L"Lag Effect - Hotkey in use", MB_YESNO | MB_ICONWARNING) == IDNO)
        for (int i = 0; i < MAX_KEYS; i++) target[i] = 0;
}

// ---- auto-switch profiles when an app runs ----
static wchar_t gProfApp[PROF_MAX][64];
static int gAutoProf = -1, gAutoPrev = -1;
static void ProfileAppsLoad()
{
    for (int i = 0; i < PROF_MAX; i++) {
        gProfApp[i][0] = 0;
        if (i >= gProfCount) continue;
        wchar_t key[96]; wsprintfW(key, L"profile_app_%s", gProfNames[i]);
        GetPrivateProfileStringW(L"settings", key, L"", gProfApp[i], 64, gIni);
    }
}
static void AutoProfileTick()                   // every ~2 s
{
    static DWORD last = 0;
    if (GetTickCount() - last < 2000) return;
    last = GetTickCount();
    bool any = false; for (int i = 0; i < gProfCount; i++) if (gProfApp[i][0]) any = true;
    if (!any) return;
    static ProcInfo procs[2048];
    int n = SnapProcs(procs, 2048), hit = -1;
    for (int i = 0; i < gProfCount && hit < 0; i++) {
        if (!gProfApp[i][0]) continue;
        for (int k = 0; k < n; k++) if (!lstrcmpiW(procs[k].exe, gProfApp[i])) { hit = i; break; }
    }
    if (hit >= 0 && gAutoProf != hit) {
        if (gAutoProf < 0) gAutoPrev = gProfCur;
        gAutoProf = hit;
        ProfileLoad(hit, true);
        ProfilesFill(gProfNames[hit]);
    } else if (hit < 0 && gAutoProf >= 0) {     // the app closed: back to what you had
        gAutoProf = -1;
        if (gAutoPrev >= 0 && gAutoPrev < gProfCount) { ProfileLoad(gAutoPrev, true); ProfilesFill(gProfNames[gAutoPrev]); }
        gAutoPrev = -1;
    }
}
static void ProfileAutoInfo()
{
    wchar_t t[160] = L"";
    if (gProfSel >= 0 && gProfApp[gProfSel][0]) wsprintfW(t, L"Switches to this profile while %s is running.", gProfApp[gProfSel]);
    else if (gProfSel >= 0) lstrcpynW(t, L"Not tied to an app.", 160);
    SetDlgItemTextW(gWnd, IDC_PROFAUTOINFO, t);
}
static void ProfileAutoClicked()
{
    if (gProfSel < 0) { MessageBoxW(gWnd, L"Save or pick a profile first.", L"Lag Effect - Profiles", MB_ICONINFORMATION); return; }
    wchar_t exe[64]; lstrcpynW(exe, gProfApp[gProfSel], 64);
    if (!InputBox(L"Switch automatically", L"Program to watch, e.g. valorant.exe (leave empty to stop):", exe, 60)) {
        if (exe[0]) return;                     // cancelled
    }
    if (exe[0] && !wcschr(exe, L'.')) lstrcatW(exe, L".exe");
    lstrcpynW(gProfApp[gProfSel], exe, 64);
    wchar_t key[96]; wsprintfW(key, L"profile_app_%s", gProfNames[gProfSel]);
    IniSet(key, exe[0] ? exe : nullptr);
    ProfileAutoInfo();
}

// ---- command-line control (hidden; for Stream Deck buttons and scripts) ----
// LagEffect.exe /mute | /unmute | /togglemute | /fx on|off|toggle | /profile "Name" | /nextprofile | /character "Name"
//               /pad 1-32 | /clipnow | /clip 1-32 | /stopall | /rewind | /repeat | /tapestop | /start | /stop | /page A-D
static void ExecCommandLine(const wchar_t* cmd)
{
    if (!gCmdLine) return;
    int argc = 0; LPWSTR* argv = CommandLineToArgvW(cmd, &argc);
    if (!argv) return;
    for (int i = 0; i < argc; i++) {
        const wchar_t* a = argv[i]; const wchar_t* v = i + 1 < argc ? argv[i + 1] : L"";
        if (a[0] != L'/' && a[0] != L'-') continue;
        a += a[0] == L'-' && a[1] == L'-' ? 2 : 1;
        if (!lstrcmpiW(a, L"mute")) SetMute(true);
        else if (!lstrcmpiW(a, L"unmute")) SetMute(false);
        else if (!lstrcmpiW(a, L"togglemute")) SetMute(!gMicMuted);
        else if (!lstrcmpiW(a, L"fx")) { SetFxOn(!lstrcmpiW(v, L"on") ? true : !lstrcmpiW(v, L"off") ? false : !gFxOn); i++; }
        else if (!lstrcmpiW(a, L"profile")) { for (int k = 0; k < gProfCount; k++) if (!lstrcmpiW(gProfNames[k], v)) { ProfileLoad(k, true); ProfilesFill(gProfNames[k]); } i++; }
        else if (!lstrcmpiW(a, L"nextprofile")) { if (gProfCount) { int k = (gProfCur + 1) % gProfCount; ProfileLoad(k, true); ProfilesFill(gProfNames[k]); } }
        else if (!lstrcmpiW(a, L"character")) {
            for (int k = 1; k < CHAR_N; k++) if (!lstrcmpiW(CHARACTERS[k], v)) ApplyCharacter(k);
            for (int k = 0; k < gMyCharN; k++) if (!lstrcmpiW(gMyChars[k], v)) MyCharLoad(gMyChars[k]);
            i++;
        }
        else if (!lstrcmpiW(a, L"pad"))  { int k = _wtoi(v) - 1; if (k >= 0 && k < PAD_N) PadKey(k, true, false); i++; }
        else if (!lstrcmpiW(a, L"clip")) { int k = _wtoi(v) - 1; if (k >= 0 && k < CLIP_N && gClips[k].base) gPads[CLIP0 + k].trigger = true; i++; }
        else if (!lstrcmpiW(a, L"clipnow")) ClipNow();
        else if (!lstrcmpiW(a, L"stopall")) for (int k = 0; k < SB_N; k++) gPads[k].stop = true;
        else if (!lstrcmpiW(a, L"rewind")) gRewindReq = true;
        else if (!lstrcmpiW(a, L"repeat")) gRepeatReq = true;
        else if (!lstrcmpiW(a, L"tapestop")) gTapeReq = true;
        else if (!lstrcmpiW(a, L"start")) { if (!gWantRunning) StartAudio(false); }
        else if (!lstrcmpiW(a, L"stop")) { if (gWantRunning) StopAudio(); }
        else if (!lstrcmpiW(a, L"page")) { int k = towupper(v[0]) - L'A'; if (k >= 0 && k < PAD_BANKS) SetPadBank(k); i++; }
    }
    LocalFree(argv);
    UpdateUi();
}

// ---- export / import every setting (one file) ----
static void ExportSettings()
{
    wchar_t path[MAX_PATH] = L"Lag Effect settings.ini";
    OPENFILENAMEW o = {};
    o.lStructSize = sizeof(o); o.hwndOwner = gWnd; o.lpstrFilter = L"Lag Effect settings\0*.ini\0"; o.lpstrFile = path; o.nMaxFile = MAX_PATH;
    o.lpstrDefExt = L"ini"; o.lpstrTitle = L"Export all settings"; o.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (!GetSaveFileNameW(&o)) return;
    SaveSettings();
    DeleteFileW(path);
    static wchar_t buf[65536];
    if (GetPrivateProfileSectionW(L"settings", buf, 65536, gIni)) WritePrivateProfileSectionW(L"settings", buf, path);
    wchar_t dir[MAX_PATH], pat[MAX_PATH];
    for (int kind = 0; kind < 2; kind++) {      // profiles, then your characters
        if (kind == 0) ProfileDir(dir); else MyCharDir(dir);
        wsprintfW(pat, L"%s\\*.ini", dir);
        WIN32_FIND_DATAW fd; HANDLE f = FindFirstFileW(pat, &fd);
        if (f == INVALID_HANDLE_VALUE) continue;
        do {
            wchar_t file[MAX_PATH], name[64], sec[96];
            wsprintfW(file, L"%s\\%s", dir, fd.cFileName);
            lstrcpynW(name, fd.cFileName, 64); wchar_t* dot = wcsrchr(name, L'.'); if (dot) *dot = 0;
            wsprintfW(sec, kind == 0 ? L"profile:%s" : L"character:%s", name);
            if (GetPrivateProfileSectionW(kind == 0 ? L"profile" : L"character", buf, 65536, file)) WritePrivateProfileSectionW(sec, buf, path);
        } while (FindNextFileW(f, &fd));
        FindClose(f);
    }
    ShowOsd(L"Settings exported", true);
}

static void ImportSettings()
{
    wchar_t path[MAX_PATH] = L"";
    OPENFILENAMEW o = {};
    o.lStructSize = sizeof(o); o.hwndOwner = gWnd; o.lpstrFilter = L"Lag Effect settings\0*.ini\0All files\0*.*\0"; o.lpstrFile = path;
    o.nMaxFile = MAX_PATH; o.lpstrTitle = L"Import settings"; o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (!GetOpenFileNameW(&o)) return;
    if (MessageBoxW(gWnd, L"Replace your settings, profiles and characters with the ones in this file? Lag Effect will restart.",
                    L"Lag Effect - Import", MB_YESNO | MB_ICONQUESTION) != IDYES) return;
    static wchar_t names[16384], buf[65536];
    if (!GetPrivateProfileSectionNamesW(names, 16384, path)) { MessageBoxW(gWnd, L"That file has no Lag Effect settings in it.", L"Lag Effect", MB_ICONWARNING); return; }
    for (wchar_t* sec = names; *sec; sec += lstrlenW(sec) + 1) {
        if (!GetPrivateProfileSectionW(sec, buf, 65536, path)) continue;
        wchar_t dir[MAX_PATH], file[MAX_PATH];
        if (!lstrcmpiW(sec, L"settings")) WritePrivateProfileSectionW(L"settings", buf, gIni);
        else if (!wcsncmp(sec, L"profile:", 8)) { ProfileDir(dir); wsprintfW(file, L"%s\\%s.ini", dir, sec + 8); WritePrivateProfileSectionW(L"profile", buf, file); }
        else if (!wcsncmp(sec, L"character:", 10)) { MyCharDir(dir); wsprintfW(file, L"%s\\%s.ini", dir, sec + 10); WritePrivateProfileSectionW(L"character", buf, file); }
    }
    gNoSaveOnExit = true;                       // keep what was just imported
    wchar_t exe[MAX_PATH]; GetModuleFileNameW(nullptr, exe, MAX_PATH);
    ShellExecuteW(nullptr, L"open", exe, L"--updated", nullptr, SW_SHOWNORMAL);   // --updated: waits for this copy to close
    PostMessageW(gWnd, WM_CLOSE, 0, 0);
}

// ======================= hex colour picker =======================
// Type a colour as #RRGGBB (or #RGB), see it, or open Windows' palette. Used by "Your colours" and the Custom theme.
static struct { HWND wnd, edit, sw; COLORREF col; bool done, ok; HBRUSH br; } gHex;
static bool HexParse(const wchar_t* t, COLORREF* out)
{
    while (*t == L' ' || *t == L'#') t++;
    wchar_t h[8] = {}; int n = 0;
    for (; *t && n < 7; t++) { if (iswxdigit(*t)) h[n++] = *t; else if (*t != L' ') return false; }
    if (n == 3) { wchar_t e[7] = { h[0], h[0], h[1], h[1], h[2], h[2], 0 }; lstrcpyW(h, e); n = 6; }
    if (n != 6) return false;
    unsigned v = (unsigned)wcstoul(h, nullptr, 16);
    *out = RGB((v >> 16) & 255, (v >> 8) & 255, v & 255);
    return true;
}
static void HexShow(bool setText)
{
    if (gHex.br) DeleteObject(gHex.br);
    gHex.br = CreateSolidBrush(gHex.col);
    if (setText) { wchar_t t[16]; wsprintfW(t, L"#%02X%02X%02X", GetRValue(gHex.col), GetGValue(gHex.col), GetBValue(gHex.col)); SetWindowTextW(gHex.edit, t); }
    InvalidateRect(gHex.sw, nullptr, TRUE);
}
static LRESULT CALLBACK HexProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_COMMAND:
        if (LOWORD(w) == 11 && HIWORD(w) == EN_CHANGE) {
            wchar_t t[32]; GetWindowTextW(gHex.edit, t, 32);
            COLORREF c; if (HexParse(t, &c)) { gHex.col = c; HexShow(false); }
        } else if (LOWORD(w) == 13) {
            static COLORREF custom[16];
            CHOOSECOLORW cc = {}; cc.lStructSize = sizeof(cc); cc.hwndOwner = h; cc.lpCustColors = custom;
            cc.rgbResult = gHex.col; cc.Flags = CC_FULLOPEN | CC_RGBINIT;
            if (ChooseColorW(&cc)) { gHex.col = cc.rgbResult; HexShow(true); }
        } else if (LOWORD(w) == IDOK) {
            wchar_t t[32]; GetWindowTextW(gHex.edit, t, 32);
            COLORREF c; if (HexParse(t, &c)) { gHex.col = c; gHex.ok = true; gHex.done = true; } else MessageBeep(MB_ICONWARNING);
        } else if (LOWORD(w) == IDCANCEL) gHex.done = true;
        return 0;
    case WM_CTLCOLORSTATIC:
        if ((HWND)l == gHex.sw) return (LRESULT)gHex.br;
        return CtlColor(h, m, w, l);
    case WM_CTLCOLORBTN: case WM_CTLCOLOREDIT: case WM_CTLCOLORLISTBOX:
        return CtlColor(h, m, w, l);
    case WM_ERASEBKGND: { RECT rc; GetClientRect(h, &rc); FillRect((HDC)w, &rc, BgSolid()); return 1; }
    case WM_CLOSE: gHex.done = true; return 0;
    }
    return DefWindowProcW(h, m, w, l);
}
static bool HexColorPick(const wchar_t* title, COLORREF init, COLORREF* out)
{
    static bool reg = false;
    if (!reg) { WNDCLASSW wc = {}; wc.lpfnWndProc = HexProc; wc.hInstance = gInst; wc.hIcon = gIcon; wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
                wc.lpszClassName = L"LagHexColor"; RegisterClassW(&wc); reg = true; }
    RECT pr; GetWindowRect(gWnd, &pr);
    RECT r = { 0, 0, SC(300), SC(132) };
    DWORD st = WS_POPUP | WS_CAPTION | WS_SYSMENU;
    AdjustWindowRect(&r, st, FALSE);
    int ww = r.right - r.left, wh = r.bottom - r.top;
    gHex = {}; gHex.col = init;
    gHex.wnd = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LagHexColor", title, st, (pr.left + pr.right - ww) / 2, (pr.top + pr.bottom - wh) / 2,
                               ww, wh, gWnd, nullptr, gInst, nullptr);
    if (!gHex.wnd) return false;
    auto mk = [&](const wchar_t* cls, const wchar_t* txt, DWORD sty, int x, int y, int w, int hh, int id, DWORD ex = 0) {
        HWND c = CreateWindowExW(ex, cls, txt, WS_CHILD | WS_VISIBLE | sty, SC(x), SC(y), SC(w), SC(hh), gHex.wnd, (HMENU)(INT_PTR)id, gInst, nullptr);
        SendMessageW(c, WM_SETFONT, (WPARAM)gFont, TRUE); return c;
    };
    mk(L"STATIC", L"Hex colour:", 0, 14, 18, 80, 20, -1);
    gHex.edit = mk(L"EDIT", L"", WS_TABSTOP | ES_AUTOHSCROLL, 96, 14, 104, 24, 11, WS_EX_CLIENTEDGE);
    SendMessageW(gHex.edit, EM_LIMITTEXT, 9, 0);
    gHex.sw = mk(L"STATIC", L"", WS_BORDER, 210, 12, 76, 28, 12);
    mk(L"BUTTON", L"Pick from a palette...", WS_TABSTOP, 14, 52, 272, 28, 13);
    mk(L"BUTTON", L"OK", WS_TABSTOP | BS_DEFPUSHBUTTON, 110, 92, 84, 28, IDOK);
    mk(L"BUTTON", L"Cancel", WS_TABSTOP, 202, 92, 84, 28, IDCANCEL);
    HexShow(true);
    ThemeTitleBar(gHex.wnd); EnumChildWindows(gHex.wnd, ThemeChild, 0);
    EnableWindow(gWnd, FALSE);
    ShowWindow(gHex.wnd, SW_SHOW);
    SetFocus(gHex.edit); SendMessageW(gHex.edit, EM_SETSEL, 1, -1);
    MSG msg;
    while (!gHex.done && GetMessageW(&msg, nullptr, 0, 0) > 0) {
        if (IsDialogMessageW(gHex.wnd, &msg)) continue;   // Tab, Enter = OK, Esc = Cancel
        TranslateMessage(&msg); DispatchMessageW(&msg);
    }
    if (!gHex.done) PostQuitMessage(0);          // (the app is closing)
    EnableWindow(gWnd, TRUE);
    DestroyWindow(gHex.wnd); gHex.wnd = nullptr;
    if (gHex.br) { DeleteObject(gHex.br); gHex.br = nullptr; }
    SetForegroundWindow(gWnd);
    if (gHex.ok) *out = gHex.col;
    return gHex.ok;
}

static bool gPicUiBusy = false;                 // (filling the Pictures page: not a change by you)
static void PicUiRefresh()
{
    if (!gWnd) return;
    gPicUiBusy = true;
    HWND c = GetDlgItem(gWnd, IDC_STKLIST);
    SendMessageW(c, CB_RESETCONTENT, 0, 0);
    for (int i = 0; i < gStkN; i++) {
        const wchar_t* b = wcsrchr(gStk[i].path, L'\\');
        wchar_t t[MAX_PATH + 8]; wsprintfW(t, L"%d. %s%s", i + 1, b ? b + 1 : gStk[i].path, gStk[i].img.nAll > 1 ? L" (GIF)" : L"");
        SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)t);
    }
    if (!gStkN) SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"(none yet)");
    gStkSel = Iclamp(gStkSel, 0, Imax(0, gStkN - 1));
    SendMessageW(c, CB_SETCURSEL, gStkSel, 0);
    const bool has = gStkN > 0;
    SendDlgItemMessageW(gWnd, SPIN_UD(IDC_STKSIZE), UDM_SETPOS32, 0, has ? gStk[gStkSel].size : 100);
    SendDlgItemMessageW(gWnd, SPIN_UD(IDC_STKOPAC), UDM_SETPOS32, 0, has ? gStk[gStkSel].opacity : 100);
    const int ids[] = { IDC_STKLIST, IDC_STKDEL, IDC_STKSIZE, IDC_STKOPAC, SPIN_UD(IDC_STKSIZE), SPIN_UD(IDC_STKOPAC) };
    for (int id : ids) EnableWindow(GetDlgItem(gWnd, id), has);
    EnableWindow(GetDlgItem(gWnd, IDC_STKADD), gStkN < STK_MAX);
    gPicUiBusy = false;
}


// ======================= mixer page =======================
// A channel's dropdown shows only its own source until it's opened; opening it lists what's there right now.
struct ChanOpt { int type; wchar_t src[128]; };
struct AppScan {
    AudioApp apps[64]; int n;                   // apps playing sound (the channel menu)
    wchar_t  want[CH_MAX][128];                 // each app channel's .exe (as asked) ...
    DWORD    pid[CH_MAX];                       // ... its process (0: not running) ...
    wchar_t  path[CH_MAX][MAX_PATH];            // ... and where its .exe is (for the icon)
    wchar_t  win[96][64]; int nWin;             // apps with a window open (not playing sound yet, maybe)
};
static BOOL CALLBACK AppWinProc(HWND w, LPARAM l)
{
    AppScan* sc = (AppScan*)l;
    if (sc->nWin >= 96 || !IsWindowVisible(w) || GetWindow(w, GW_OWNER) || (GetWindowLongW(w, GWL_EXSTYLE) & WS_EX_TOOLWINDOW)) return TRUE;
    if (GetWindowTextLengthW(w) == 0) return TRUE;
    DWORD pid = 0; GetWindowThreadProcessId(w, &pid);
    if (!pid || pid == GetCurrentProcessId()) return TRUE;
    HANDLE ph = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (!ph) return TRUE;
    wchar_t path[MAX_PATH]; DWORD n = MAX_PATH;
    if (QueryFullProcessImageNameW(ph, 0, path, &n)) {
        const wchar_t* b = wcsrchr(path, L'\\'); b = b ? b + 1 : path;
        static const wchar_t* skip[] = { L"explorer.exe", L"ApplicationFrameHost.exe", L"TextInputHost.exe", L"SystemSettings.exe", L"ShellExperienceHost.exe" };
        bool keep = true; for (auto k : skip) if (!lstrcmpiW(b, k)) keep = false;
        for (int i = 0; i < sc->nWin && keep; i++) if (!lstrcmpiW(sc->win[i], b)) keep = false;
        if (keep) lstrcpynW(sc->win[sc->nWin++], b, 64);
    }
    CloseHandle(ph);
    return TRUE;
}
static AppScan gAppCache; static bool gAppCacheOk = false; static volatile LONG gAppScanBusy = 0;
static DWORD WINAPI AppScanThread(LPVOID arg)
{
    AppScan* sc = (AppScan*)arg;
    sc->n = ListAudioApps(sc->apps, 64);
    EnumWindows(AppWinProc, (LPARAM)sc);
    ProcInfo* procs = (ProcInfo*)HeapAlloc(GetProcessHeap(), 0, sizeof(ProcInfo) * 2048);
    if (procs) {
        const int np = SnapProcs(procs, 2048);  // one snapshot for every channel
        for (int c = 0; c < CH_MAX; c++) {
            if (!sc->want[c][0]) continue;
            for (int i = 0; i < np; i++)
                if (!lstrcmpiW(procs[i].exe, sc->want[c]) && procs[i].pid != GetCurrentProcessId()) { sc->pid[c] = ProcRoot(procs, np, procs[i].pid); break; }
            if (!sc->pid[c]) continue;
            HANDLE ph = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, sc->pid[c]);
            if (ph) { DWORD n = MAX_PATH; if (!QueryFullProcessImageNameW(ph, 0, sc->path[c], &n)) sc->path[c][0] = 0; CloseHandle(ph); }
        }
        HeapFree(GetProcessHeap(), 0, procs);
    }
    if (!PostMessageW(gWnd, WM_APPS_SCANNED, 0, (LPARAM)sc)) HeapFree(GetProcessHeap(), 0, sc);
    InterlockedExchange(&gAppScanBusy, 0);
    return 0;
}
static void AppScanStart()                      // (in the background: listing apps and processes takes a while)
{
    if (InterlockedCompareExchange(&gAppScanBusy, 1, 0) != 0) return;
    AppScan* sc = (AppScan*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(AppScan));
    if (!sc) { InterlockedExchange(&gAppScanBusy, 0); return; }
    for (int c = 0; c < CH_MAX; c++) if (gCh[c].type == CH_APP) lstrcpynW(sc->want[c], gCh[c].src, 128);
    HANDLE t = CreateThread(nullptr, 0, AppScanThread, sc, 0, nullptr);
    if (t) CloseHandle(t); else { HeapFree(GetProcessHeap(), 0, sc); InterlockedExchange(&gAppScanBusy, 0); }
}
static ChanOpt gChOpts[200]; static int gChOptN = 0;
static const COLORREF CH_COLORS[8] = { RGB(43, 184, 165), RGB(140, 124, 240), RGB(240, 136, 62), RGB(229, 83, 75),
                                       RGB(76, 160, 255), RGB(63, 185, 80), RGB(255, 110, 190), RGB(217, 165, 32) };
static const wchar_t* CH_COLOR_NAMES[8] = { L"Teal", L"Purple", L"Orange", L"Red", L"Blue", L"Green", L"Pink", L"Yellow" };
#define SOLO_C RGB(217, 165, 32)
static HICON   gChIcon[CH_MAX];                 // the app's own icon (16 px)
static wchar_t gChIconSrc[CH_MAX][128];
static int     gSecChan = -1, gSecOut = -1;     // the Mixer's two sections (the strips are drawn inside them)
static int     gSecKeys = -1;                   // ... and its hotkeys view
static void MixerRedraw() { RedrawWindow(gWnd, nullptr, nullptr, RDW_INVALIDATE | RDW_ALLCHILDREN); }

static void ChanLabel(int c, wchar_t* out, int cap)   // what its strip calls it
{
    if (gCh[c].name[0]) lstrcpynW(out, gCh[c].name, cap);
    else if (gCh[c].type == CH_APP) AppDisplayName(gCh[c].src, out, cap);
    else if (gCh[c].type == CH_DEV || gCh[c].type == CH_OUT) lstrcpynW(out, gCh[c].src, cap);
    else lstrcpynW(out, L"", cap);
}
static void ChanIconFromPath(int c, const wchar_t* path)
{
    if (gChIcon[c] && !lstrcmpiW(gChIconSrc[c], gCh[c].src)) return;
    if (gChIcon[c]) { DestroyIcon(gChIcon[c]); gChIcon[c] = nullptr; }
    HICON sm = nullptr;
    if (ExtractIconExW(path, 0, nullptr, &sm, 1) > 0 && sm) gChIcon[c] = sm;
    lstrcpynW(gChIconSrc[c], gCh[c].src, 128);  // (tried: not again for this app, even with no icon)
    InvalidateRect(GetDlgItem(gWnd, IDC_CHSRC0 + c), nullptr, FALSE);
}
static void ChanIconUpdate(int c)               // the app's icon, from its .exe (when it's running)
{
    if (gCh[c].type != CH_APP) {
        if (gChIcon[c]) { DestroyIcon(gChIcon[c]); gChIcon[c] = nullptr; }
        gChIconSrc[c][0] = 0;
        return;
    }
    if (gChIcon[c] && !lstrcmpiW(gChIconSrc[c], gCh[c].src)) return;
    if (gChIcon[c]) { DestroyIcon(gChIcon[c]); gChIcon[c] = nullptr; }
    DWORD pid = ChanFindApp(gCh[c].src);
    if (!pid) return;                           // not running: tried again later
    HANDLE ph = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (!ph) return;
    wchar_t path[MAX_PATH]; DWORD n = MAX_PATH;
    if (QueryFullProcessImageNameW(ph, 0, path, &n)) {
        HICON sm = nullptr;
        if (ExtractIconExW(path, 0, nullptr, &sm, 1) > 0 && sm) { gChIcon[c] = sm; lstrcpynW(gChIconSrc[c], gCh[c].src, 128); }
    }
    CloseHandle(ph);
    InvalidateRect(GetDlgItem(gWnd, IDC_CHSRC0 + c), nullptr, FALSE);
}
static bool gChOptOff[200];                     // (greyed: an output Lag Effect plays to: recording it would echo)
static int  gChOptPlaying = 0;                  // the first gChOptPlaying-1 apps are playing sound; the rest just have a window
static void ChanOptsFill(int c)                 // what a channel can play
{
    gChOptN = 0;
    auto add = [&](int type, const wchar_t* src) {
        if (gChOptN >= 200) return;
        for (int i = 0; i < gChOptN; i++) if (gChOpts[i].type == type && !lstrcmpiW(gChOpts[i].src, src)) return;
        gChOptOff[gChOptN] = false;
        gChOpts[gChOptN].type = type; lstrcpynW(gChOpts[gChOptN].src, src, 128); gChOptN++;
    };
    add(CH_NONE, L"");
    if (!gAppCacheOk) { gAppCache.n = ListAudioApps(gAppCache.apps, 64); gAppCache.nWin = 0; gAppCacheOk = true; }   // (only the very first time)
    for (int i = 0; i < gAppCache.n; i++) add(CH_APP, gAppCache.apps[i].name);
    if (gCh[c].type == CH_APP) add(CH_APP, gCh[c].src);   // (its own, even if not running now)
    gChOptPlaying = gChOptN;
    for (int i = 0; i < gAppCache.nWin; i++) add(CH_APP, gAppCache.win[i]);
    AppScanStart();                             // fresh for next time
    for (ma_uint32 i = 0; i < gCapCount; i++) { wchar_t n[128]; MultiByteToWideChar(CP_UTF8, 0, gCapDevs[i].name, -1, n, 128); add(CH_DEV, n); }
    if (gCh[c].type == CH_DEV) add(CH_DEV, gCh[c].src);
    for (ma_uint32 i = 0; i < gPlayCount; i++) {
        wchar_t n[128]; MultiByteToWideChar(CP_UTF8, 0, gPlayDevs[i].name, -1, n, 128);
        const int at = gChOptN; add(CH_OUT, n);
        if (at < gChOptN)
            for (int k = 0; k < gRows; k++) if (ComboIndex(IDC_ROWDEV + k) == (int)i) gChOptOff[at] = true;
    }
    if (gCh[c].type == CH_OUT) add(CH_OUT, gCh[c].src);
}
// ---- remembering apps: a channel's settings are kept (per app / device) when it's removed or swapped,
// and come back when you add it again: volume, duck, routing, colour, name, width, hold mode and its hotkeys.
static int  FxKeyButtonId(int slot);
static void FaderLabel(int id);
static void MixMemKey(int c, wchar_t* key)
{
    wsprintfW(key, L"%s|%s", gCh[c].type == CH_APP ? L"app" : gCh[c].type == CH_DEV ? L"in" : L"out", gCh[c].src);
    CharLowerBuffW(key, lstrlenW(key));
    for (wchar_t* q = key; *q; q++) if (*q == L'=' || *q == L'[' || *q == L']') *q = L'_';
}
static void MixMemStore(int c)
{
    if (gCh[c].type == CH_NONE || !gIni[0]) return;
    wchar_t key[200], v[400]; MixMemKey(c, key);
    int n = wsprintfW(v, L"%d,%d,%u,%d,%d,%d", (int)gCh[c].db10, gCh[c].duck ? 1 : 0, (unsigned)gCh[c].routes, gCh[c].color, gChW[c], gCh[c].holdTalk);
    for (int a = 0; a < MIXA_N; a++) for (int i = 0; i < MAX_KEYS; i++) n += wsprintfW(v + n, L",%d", gFxKeys[SLOT_MIX0 + c * MIXA_N + a][i]);
    wsprintfW(v + n, L"|%s", gCh[c].name);
    WritePrivateProfileStringW(L"mixer_memory", key, v, gIni);
}
static bool MixMemLoad(int c)
{
    wchar_t key[200], v[400]; MixMemKey(c, key);
    if (!GetPrivateProfileStringW(L"mixer_memory", key, L"", v, 400, gIni) || !v[0]) return false;
    int f[6 + MIXA_N * MAX_KEYS] = {}; int nf = 0;
    const wchar_t* q = v;
    while (*q && *q != L'|' && nf < 6 + MIXA_N * MAX_KEYS) { f[nf++] = _wtoi(q); while (*q && *q != L',' && *q != L'|') q++; if (*q == L',') q++; }
    if (nf < 6) return false;
    gCh[c].db10 = Iclamp(f[0], -600, 60); gCh[c].duck = f[1] != 0; gCh[c].routes = (unsigned)f[2] & ((1u << MAX_OUT) - 1);
    gCh[c].color = Iclamp(f[3], 0, 7); gChW[c] = f[4] ? Iclamp(f[4], 52, 240) : 0; gCh[c].holdTalk = f[5] != 0;
    for (int a = 0; a < MIXA_N; a++) for (int i = 0; i < MAX_KEYS; i++) gFxKeys[SLOT_MIX0 + c * MIXA_N + a][i] = Iclamp(f[6 + a * MAX_KEYS + i], 0, 255);
    const wchar_t* nm = wcschr(v, L'|');
    lstrcpynW(gCh[c].name, nm ? nm + 1 : L"", 32);
    return true;
}
static void MixKeysShow(int c)                  // (its hotkey buttons and hold mode, after they changed)
{
    for (int a = 0; a < MIXA_N; a++) {
        wchar_t t[120]; FxKeyButtonText(SLOT_MIX0 + c * MIXA_N + a, t, 120);
        SetDlgItemTextW(gWnd, FxKeyButtonId(SLOT_MIX0 + c * MIXA_N + a), t);
    }
    SetDlgItemTextW(gWnd, IDC_MIXHOLDMODE0 + c, gCh[c].holdTalk ? L"Talk" : L"Mute");
}
static void ChanSetSource(int c, int type, const wchar_t* src)
{
    if (gCh[c].type == type && !lstrcmpiW(gCh[c].src, src)) return;
    const bool wasEmpty = gCh[c].type == CH_NONE;
    if (gRunning) ChanStop(c);
    MixMemStore(c);                             // (the one leaving: remembered for next time)
    gCh[c].type = type; lstrcpynW(gCh[c].src, type == CH_NONE ? L"" : src, 128);
    gCh[c].solo = false; gCh[c].held = false;
    if (type == CH_NONE || !MixMemLoad(c)) {    // new to the mixer (or cleared): fresh settings, no hotkeys
        gCh[c].name[0] = 0; gCh[c].db10 = 0; gCh[c].duck = false; gCh[c].holdTalk = 0; gChW[c] = 0;
        for (int a = 0; a < MIXA_N; a++) for (int i = 0; i < MAX_KEYS; i++) gFxKeys[SLOT_MIX0 + c * MIXA_N + a][i] = 0;
        if (type != CH_NONE && (wasEmpty || !gCh[c].routes)) gCh[c].routes = (1u << gRows) - 1;   // to every output
    }
    MixKeysShow(c);
    FaderLabel(IDC_CHVOL0 + c);
    if (gRunning && type != CH_NONE) ChanStart(c);
    ChanIconUpdate(c);
    Layout();                                   // its controls show / hide
}

// ---- renaming a channel: a little box over its name (Enter keeps it, Esc doesn't)
static HWND gRenEdit = nullptr; static int gRenCh = -1;
static void SaveSettings();
static void FillHearList();
static bool gHearListStale = false;
static LRESULT CALLBACK RenEditProc(HWND h, UINT m, WPARAM w, LPARAM l, UINT_PTR, DWORD_PTR)
{
    if (m == WM_GETDLGCODE) return DLGC_WANTALLKEYS;
    if (m == WM_KEYDOWN && (w == VK_RETURN || w == VK_ESCAPE)) { PostMessageW(gWnd, WM_RENAME_DONE, w == VK_RETURN, 0); return 0; }
    if (m == WM_CHAR && (w == L'\r' || w == 27)) return 0;   // (no beep)
    if (m == WM_KILLFOCUS) PostMessageW(gWnd, WM_RENAME_DONE, 1, 0);
    return DefSubclassProc(h, m, w, l);
}
static void DbText(int db10, wchar_t* t);
static int  FaderGet(int id);
static void FaderSet(int id, int db10);
static void FaderValueEdit(int id)              // right-click a fader: type its exact volume (in dB) over its dB text
{
    if (gRenEdit) return;
    const bool ch = id >= IDC_CHVOL0 && id < IDC_CHVOL0 + CH_MAX;
    HWND b = GetDlgItem(gWnd, ch ? IDC_CHDB0 + (id - IDC_CHVOL0) : IDC_ODB0 + (id - IDC_OVOL0));
    RECT r; GetWindowRect(b, &r); MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2);
    r.right = Imax((int)r.right, (int)r.left + SC(60));
    wchar_t t[24]; const int v = FaderGet(id);
    if (v <= -600) lstrcpyW(t, L"-60"); else { const int a = v < 0 ? -v : v; wsprintfW(t, L"%s%d.%d", v < 0 ? L"-" : L"", a / 10, a % 10); }
    gRenCh = 1000 + id;
    gRenEdit = CreateWindowExW(0, L"EDIT", t, WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL | ES_CENTER, r.left, r.top - SC(2),
                               r.right - r.left, SC(22), gWnd, (HMENU)(INT_PTR)IDC_CHNAMEED, gInst, nullptr);
    if (!gRenEdit) return;
    SendMessageW(gRenEdit, WM_SETFONT, (WPARAM)gFont, TRUE);
    SendMessageW(gRenEdit, EM_LIMITTEXT, 10, 0);
    SetWindowSubclass(gRenEdit, RenEditProc, 1, 0);
    SetWindowPos(gRenEdit, HWND_TOP, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE);
    SetFocus(gRenEdit);
    SendMessageW(gRenEdit, EM_SETSEL, 0, -1);
}
static void ChanRename(int c)                   // c < CH_MAX: a channel; CH_MAX + k: output k
{
    if (gRenEdit) return;
    HWND b = GetDlgItem(gWnd, c < CH_MAX ? IDC_CHSRC0 + c : IDC_OLBL0 + (c - CH_MAX));
    RECT r; GetWindowRect(b, &r); MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2);
    if (c >= CH_MAX) r.right = Imax((int)r.right, (int)r.left + SC(90));   // (room to type)
    wchar_t t[64];
    if (c < CH_MAX) ChanLabel(c, t, 32); else OutName(c - CH_MAX, t, 32);
    gRenCh = c;
    gRenEdit = CreateWindowExW(0, L"EDIT", t, WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL, r.left, r.top + (r.bottom - r.top - SC(22)) / 2,
                               r.right - r.left, SC(22), gWnd, (HMENU)(INT_PTR)IDC_CHNAMEED, gInst, nullptr);
    if (!gRenEdit) return;
    SendMessageW(gRenEdit, WM_SETFONT, (WPARAM)gFont, TRUE);
    SendMessageW(gRenEdit, EM_LIMITTEXT, 31, 0);
    SetWindowSubclass(gRenEdit, RenEditProc, 1, 0);
    SetWindowPos(gRenEdit, HWND_TOP, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE);
    SetFocus(gRenEdit);
    SendMessageW(gRenEdit, EM_SETSEL, 0, -1);
}
static void ChanRenameDone(bool keep)
{
    if (!gRenEdit) return;
    HWND e = gRenEdit; gRenEdit = nullptr;      // (first: destroying it loses focus, which asks again)
    if (keep && gRenCh >= 1000) {               // a typed volume: "-12.5", "+3", "off"
        wchar_t t[32]; GetWindowTextW(e, t, 32);
        for (wchar_t* q = t; *q; q++) if (*q == 0x2212) *q = L'-';   // (the minus sign this app shows)
        wchar_t* end = nullptr; const double v = wcstod(t, &end);
        if (!lstrcmpiW(t, L"off") || !lstrcmpiW(t, L"-inf")) FaderSet(gRenCh - 1000, -600);
        else if (end != t) FaderSet(gRenCh - 1000, (int)lround(v * 10));
    }
    if (keep && gRenCh >= CH_MAX && gRenCh < CH_MAX + MAX_OUT) {   // an output
        const int k = gRenCh - CH_MAX;
        wchar_t t[64]; GetWindowTextW(e, t, 32);
        wchar_t* p = t; while (*p == L' ') p++;
        int n = lstrlenW(p); while (n > 0 && p[n - 1] == L' ') p[--n] = 0;
        wchar_t def[16]; wsprintfW(def, L"Out %d", k + 1);
        lstrcpynW(gOutName[k], !lstrcmpW(p, def) ? L"" : p, 32);   // empty or "Out 2": back to the number
        gHearListStale = true; FillHearList();
        InvalidateRect(GetDlgItem(gWnd, IDC_OLBL0 + k), nullptr, FALSE);
        InvalidateRect(GetDlgItem(gWnd, IDC_ROWLBL + k), nullptr, FALSE);
        SaveSettings();
    }
    if (keep && gRenCh >= 0 && gRenCh < CH_MAX) {
        wchar_t t[64]; GetWindowTextW(e, t, 32);
        wchar_t* p = t; while (*p == L' ') p++;
        int n = lstrlenW(p); while (n > 0 && p[n - 1] == L' ') p[--n] = 0;
        wchar_t own[64]; wchar_t keepName[32]; lstrcpynW(keepName, gCh[gRenCh].name, 32);
        gCh[gRenCh].name[0] = 0; ChanLabel(gRenCh, own, 64);
        lstrcpynW(gCh[gRenCh].name, !lstrcmpW(p, own) ? L"" : p, 32);   // empty or its own name: back to automatic
        (void)keepName;
        InvalidateRect(GetDlgItem(gWnd, IDC_CHSRC0 + gRenCh), nullptr, FALSE);
        SaveSettings();
    }
    DestroyWindow(e);
}

// ---- the channel menu (like OBS's audio sources): apps, inputs, outputs; rename, colour
static void ChanPickExe(int c, bool browse)     // an app that isn't in the lists: type its name, or find its .exe
{
    wchar_t name[MAX_PATH] = L"";
    if (browse) {
        OPENFILENAMEW o = { sizeof(o) };
        o.hwndOwner = gWnd; o.lpstrFilter = L"Programs (*.exe)\0*.exe\0"; o.lpstrFile = name; o.nMaxFile = MAX_PATH;
        o.lpstrTitle = L"Lag Effect - pick the app"; o.Flags = OFN_FILEMUSTEXIST | OFN_HIDEREADONLY;
        if (!GetOpenFileNameW(&o)) return;
        const wchar_t* b = wcsrchr(name, L'\\'); if (b) lstrcpynW(name, b + 1, MAX_PATH);
    } else {
        if (!InputBox(L"Lag Effect - add an app", L"The app's program name, like spotify.exe. It's picked up whenever it's running.", name, 64)) return;
        wchar_t* p = name; while (*p == L' ') p++;
        if (p != name) lstrcpynW(name, p, MAX_PATH);
        int n = lstrlenW(name); while (n > 0 && name[n - 1] == L' ') name[--n] = 0;
        if (!n) return;
        if (n < 4 || lstrcmpiW(name + n - 4, L".exe")) lstrcatW(name, L".exe");
    }
    ChanSetSource(c, CH_APP, name);
}
static void ChanMenu(int c, HWND from)
{
    HCURSOR old = SetCursor(LoadCursor(nullptr, IDC_WAIT));
    ChanOptsFill(c);
    SetCursor(old);
    HMENU m = CreatePopupMenu();
    const bool used = gCh[c].type != CH_NONE;
    if (used) {
        AppendMenuW(m, MF_STRING, 1, L"Rename...");
        HMENU cm = CreatePopupMenu();
        for (int i = 0; i < 8; i++) AppendMenuW(cm, MF_STRING | (gCh[c].color == i ? MF_CHECKED : 0), 10 + i, CH_COLOR_NAMES[i]);
        AppendMenuW(m, MF_POPUP, (UINT_PTR)cm, L"Colour");
        AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    }
    HMENU more = CreatePopupMenu(), ins = CreatePopupMenu(), outs = CreatePopupMenu();
    AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"Apps playing sound");
    int playing = 0, others = 0, nIn = 0, nOut = 0;
    for (int i = 1; i < gChOptN; i++) {
        const ChanOpt& o = gChOpts[i];
        const bool cur = o.type == gCh[c].type && !lstrcmpiW(o.src, gCh[c].src);
        const UINT fl = MF_STRING | (cur ? MF_CHECKED : 0) | (gChOptOff[i] ? MF_GRAYED : 0);
        wchar_t t[200];
        if (o.type == CH_APP) {
            AppDisplayName(o.src, t, 140);
            if (cur && !ChanFindApp(o.src)) lstrcatW(t, L"  (not running)");
            if (i < gChOptPlaying) { AppendMenuW(m, fl, 100 + i, t); playing++; }
            else { AppendMenuW(more, fl, 100 + i, t); others++; }
        } else if (o.type == CH_DEV) { lstrcpynW(t, o.src, 160); AppendMenuW(ins, fl, 100 + i, t); nIn++; }
        else {
            lstrcpynW(t, o.src, 160);
            if (gChOptOff[i]) lstrcatW(t, L"  (Lag Effect plays here)");
            AppendMenuW(outs, fl, 100 + i, t); nOut++;
        }
    }
    if (!playing) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"   (none right now)");
    if (!others) AppendMenuW(more, MF_STRING | MF_GRAYED, 0, L"(no other apps open)");
    AppendMenuW(more, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(more, MF_STRING, 3, L"Type its name...");
    AppendMenuW(more, MF_STRING, 4, L"Find its program...");
    if (!nIn)  AppendMenuW(ins, MF_STRING | MF_GRAYED, 0, L"(none found)");
    if (!nOut) AppendMenuW(outs, MF_STRING | MF_GRAYED, 0, L"(none found)");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(m, MF_POPUP, (UINT_PTR)more, L"More apps");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)ins,  L"Input (a mic, line-in...)");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)outs, L"Output (what a device plays)");
    if (used) { AppendMenuW(m, MF_SEPARATOR, 0, nullptr); AppendMenuW(m, MF_STRING, 2, L"Clear this channel"); }
    RECT r; GetWindowRect(from, &r);
    int cmd = (int)TrackPopupMenu(m, TPM_RETURNCMD | TPM_LEFTALIGN | TPM_TOPALIGN | TPM_NONOTIFY, r.left, r.bottom, 0, gWnd, nullptr);
    DestroyMenu(m);
    if (cmd == 1) ChanRename(c);
    else if (cmd == 2) ChanSetSource(c, CH_NONE, L"");
    else if (cmd == 3 || cmd == 4) ChanPickExe(c, cmd == 4);
    else if (cmd >= 10 && cmd < 18) { gCh[c].color = cmd - 10; MixerRedraw(); }
    else if (cmd >= 100 && cmd - 100 < gChOptN) ChanSetSource(c, gChOpts[cmd - 100].type, gChOpts[cmd - 100].src);
}

// ---- faders (volume in dB): drag (Shift = fine), scroll wheel = 1 dB (Shift = 0.1), double-click = 0 dB
static bool FaderIsChan(int id) { return id >= IDC_CHVOL0 && id < IDC_CHVOL0 + CH_MAX; }
static int FaderGet(int id)                     // tenths of a dB
{
    if (FaderIsChan(id)) return gCh[id - IDC_CHVOL0].db10;
    const int v = gRowVol[Iclamp(id - IDC_OVOL0, 0, MAX_OUT - 1)];
    return v <= 0 ? -600 : Iclamp((int)lroundf(200.0f * log10f(v / 100.0f)), -600, 60);
}
static void DbText(int db10, wchar_t* t)        // "-8.5 dB", "Off"
{
    if (db10 <= -600) { lstrcpyW(t, L"Off"); return; }
    const int a = db10 < 0 ? -db10 : db10;
    wsprintfW(t, L"%s%d.%d dB", db10 > 0 ? L"+" : db10 < 0 ? L"\x2212" : L"", a / 10, a % 10);
}
static void FaderLabel(int id)
{
    wchar_t t[24]; DbText(FaderGet(id), t);
    HWND lb = GetDlgItem(gWnd, FaderIsChan(id) ? IDC_CHDB0 + (id - IDC_CHVOL0) : IDC_ODB0 + (id - IDC_OVOL0));
    if (!lb) return;
    wchar_t o[24]; GetWindowTextW(lb, o, 24);
    if (lstrcmpW(o, t)) SetWindowTextW(lb, t);
}
static void FaderSet(int id, int db10)
{
    db10 = Iclamp(db10, -600, 60);
    if (FaderIsChan(id)) gCh[id - IDC_CHVOL0].db10 = db10;
    else {                                      // an output: the same volume (%) as its row on the Main tab
        const int k = Iclamp(id - IDC_OVOL0, 0, MAX_OUT - 1);
        const int was = FaderGet(id);
        int v = db10 <= -600 ? 0 : Iclamp((int)lroundf(100.0f * powf(10.0f, db10 / 200.0f)), 0, 200);
        if (v == gRowVol[k] && db10 != was) v = Iclamp(v + (db10 > was ? 1 : -1), 0, 200);   // (% is coarse when quiet: still move)
        gRowVol[k] = v;
        SendDlgItemMessageW(gWnd, SPIN_UD(IDC_ROWVOL + k), UDM_SETPOS32, 0, v);
    }
    InvalidateRect(GetDlgItem(gWnd, id), nullptr, FALSE);
    FaderLabel(id);
}
static float FaderPos(int db10)                 // 0..1: the top 70% covers -20..+6 dB, where you actually set things
{
    if (db10 <= -600) return 0;
    const float db = db10 / 10.0f;
    return db >= -20 ? 0.3f + 0.7f * (db + 20) / 26.0f : 0.3f * (db + 60) / 40.0f;
}
static int FaderDb10(float p)
{
    p = p < 0 ? 0 : p > 1 ? 1 : p;
    const float db = p >= 0.3f ? -20 + (p - 0.3f) / 0.7f * 26 : -60 + p / 0.3f * 40;
    return (int)lroundf(db * 10);
}
static int FaderSnap(int db10) { const int st = db10 > -200 ? 5 : 10; return (int)lroundf(db10 / (float)st) * st; }
static int FaderY(int h, int th, float p) { return (h - th / 2) - (int)(p * (h - th)); }
static float FaderP(int h, int th, int y) { return h - th > 0 ? (float)((h - th / 2) - y) / (h - th) : 0; }
static bool ChanQuiet(int c)                    // muted, held quiet, or another channel is soloed
{
    if (gCh[c].mute || gCh[c].held) return true;
    if (gCh[c].solo) return false;
    for (int i = 0; i < CH_MAX; i++) if (gCh[i].solo && gCh[i].type != CH_NONE) return true;
    return false;
}
static void FaderDraw(HWND h, HDC dc, const RECT& rc, int id)
{
    FillRect(dc, &rc, BgBrush());
    const int th = SC(10), H = rc.bottom, cx = rc.right / 2, tw = Imax(2, SC(4));
    const int ty = FaderY(H, th, FaderPos(FaderGet(id)));
    RECT tr = { cx - tw / 2, th / 2, cx - tw / 2 + tw, H - th / 2 };
    HBRUSH tb = CreateSolidBrush(gDark ? DK_TRACK : LT_TRACK); FillRect(dc, &tr, tb); DeleteObject(tb);
    const bool quiet = FaderIsChan(id) ? ChanQuiet(id - IDC_CHVOL0) : gOutMute[Iclamp(id - IDC_OVOL0, 0, MAX_OUT - 1)];
    RECT fr = tr; fr.top = ty;
    HBRUSH fb = CreateSolidBrush(quiet ? (gDark ? RGB(90, 90, 90) : RGB(175, 175, 175)) : ACCENT); FillRect(dc, &fr, fb); DeleteObject(fb);
    {                                           // scale marks at -6, -12, -24 and -48 dB
        HBRUSH mb = CreateSolidBrush(gDark ? RGB(85, 85, 85) : RGB(185, 185, 185));
        static const int marks[4] = { -60, -120, -240, -480 };
        for (int db : marks) {
            const int my = FaderY(H, th, FaderPos(db));
            RECT a = { 0, my, Imax(2, SC(4)), my + 1 }, b2 = { rc.right - Imax(2, SC(4)), my, rc.right, my + 1 };
            FillRect(dc, &a, mb); FillRect(dc, &b2, mb);
        }
        DeleteObject(mb);
    }
    const int y0 = FaderY(H, th, FaderPos(0));  // a mark at 0 dB
    RECT zr = { 0, y0, rc.right, y0 + 1 };
    HBRUSH zb = CreateSolidBrush(gDark ? RGB(110, 110, 110) : RGB(150, 150, 150)); FillRect(dc, &zr, zb); DeleteObject(zb);
    HBRUSH kb = CreateSolidBrush(gDark ? RGB(214, 214, 214) : RGB(252, 252, 252));
    HPEN   kp = CreatePen(PS_SOLID, 1, gDark ? RGB(150, 150, 150) : RGB(130, 130, 130));
    HGDIOBJ ob = SelectObject(dc, kb), op = SelectObject(dc, kp);
    RoundRect(dc, 0, ty - th / 2, rc.right, ty - th / 2 + th, SC(4), SC(4));
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(kb); DeleteObject(kp);
    RECT gr = { SC(4), ty, rc.right - SC(4), ty + 1 };   // grip line
    HBRUSH gb = CreateSolidBrush(RGB(120, 120, 120)); FillRect(dc, &gr, gb); DeleteObject(gb);
    if (GetFocus() == h) { RECT f = { 0, ty - th / 2 - 2, rc.right, ty - th / 2 + th + 2 }; DrawFocusRect(dc, &f); }
}
static int  gFadGrab = 0, gFadStartY = 0, gFadStartV = 0; static bool gFadFine = false;
static LRESULT CALLBACK FaderProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    const int id = GetDlgCtrlID(h);
    switch (m) {
    case WM_GETDLGCODE: return DLGC_WANTARROWS;
    case WM_SETFOCUS: case WM_KILLFOCUS: InvalidateRect(h, nullptr, FALSE); return 0;
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        HitchTimer ht(m, id);
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps);
        RECT rc; GetClientRect(h, &rc);
        { OffScreen os(dc, rc.right, rc.bottom); FaderDraw(h, os.dc, rc, id); BitBlt(dc, 0, 0, rc.right, rc.bottom, os.dc, 0, 0, SRCCOPY); }
        EndPaint(h, &ps);
        return 0;
    }
    case WM_LBUTTONDBLCLK: SetFocus(h); FaderSet(id, 0); return 0;
    case WM_LBUTTONDOWN: {
        SetFocus(h);
        RECT rc; GetClientRect(h, &rc);
        const int th = SC(10), y = (short)HIWORD(l), ty = FaderY(rc.bottom, th, FaderPos(FaderGet(id)));
        if (y >= ty - th && y <= ty + th) gFadGrab = y - ty;          // on the knob: drag it from where you hold it
        else { gFadGrab = 0; FaderSet(id, FaderSnap(FaderDb10(FaderP(rc.bottom, th, y)))); }   // elsewhere: jump there
        gFadStartY = y; gFadStartV = FaderGet(id); gFadFine = (w & MK_SHIFT) != 0;
        SetCapture(h);
        return 0;
    }
    case WM_MOUSEMOVE:
        if (GetCapture() == h) {
            RECT rc; GetClientRect(h, &rc);
            const int th = SC(10), y = (short)HIWORD(l);
            const bool fine = (w & MK_SHIFT) != 0;
            if (fine != gFadFine) { gFadFine = fine; gFadStartY = y; gFadStartV = FaderGet(id);
                                    gFadGrab = y - FaderY(rc.bottom, th, FaderPos(gFadStartV)); }
            if (fine) FaderSet(id, gFadStartV + (gFadStartY - y));   // 0.1 dB a pixel
            else FaderSet(id, FaderSnap(FaderDb10(FaderP(rc.bottom, th, y - gFadGrab))));
        }
        return 0;
    case WM_LBUTTONUP: if (GetCapture() == h) ReleaseCapture(); return 0;
    case WM_RBUTTONUP: FaderValueEdit(id); return 0;   // right-click: type an exact value
    case WM_MOUSEWHEEL: {
        const int d = GET_WHEEL_DELTA_WPARAM(w), st = (GET_KEYSTATE_WPARAM(w) & MK_SHIFT) ? 1 : 10;
        int v = FaderGet(id); if (v <= -600 && d > 0) v = -610;   // (from Off, the first step lands on -60 dB)
        FaderSet(id, v + (d > 0 ? st : -st) * Imax(1, (d < 0 ? -d : d) / WHEEL_DELTA));
        return 0;
    }
    case WM_KEYDOWN: {
        int v = FaderGet(id);
        switch (w) {
        case VK_UP: case VK_RIGHT: FaderSet(id, v + 10); return 0;
        case VK_DOWN: case VK_LEFT: FaderSet(id, v - 10); return 0;
        case VK_PRIOR: FaderSet(id, v + 60); return 0;
        case VK_NEXT: FaderSet(id, v - 60); return 0;
        case VK_HOME: FaderSet(id, 0); return 0;
        case VK_END: FaderSet(id, -600); return 0;
        }
        break;
    }
    }
    return DefWindowProcW(h, m, w, l);
}

// ---- drawing the strips' parts
static void DrawToggleC(DRAWITEMSTRUCT* d, bool on, COLORREF fillOn, COLORREF textOn)
{
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    COLORREF fill = on ? fillOn : (gDark ? DK_CTL : LT_CARD);
    HBRUSH b = CreateSolidBrush(fill);
    HPEN p = CreatePen(PS_SOLID, 1, on ? fill : (gDark ? DK_SECTION : LT_BORDER));
    HGDIOBJ ob = SelectObject(dc, b), op = SelectObject(dc, p);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, SC(5), SC(5));
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(b); DeleteObject(p);
    wchar_t t[16]; GetWindowTextW(d->hwndItem, t, 16);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, on ? textOn : (IsWindowEnabled(d->hwndItem) ? TXT_C : (gDark ? DK_DIM : gLtDim)));
    HGDIOBJ of = SelectObject(dc, gFontBold);
    DrawTextW(dc, t, -1, &rc, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(dc, of);
    if (d->itemState & ODS_FOCUS) { RECT f = rc; InflateRect(&f, -2, -2); DrawFocusRect(dc, &f); }
}
static void DrawToggle(DRAWITEMSTRUCT* d, bool on, bool danger)   // Mute (red) / routing (accent)
{
    DrawToggleC(d, on, danger ? RGB(205, 60, 60) : ACCENT, RGB(255, 255, 255));
}
static void DrawChanSrc(DRAWITEMSTRUCT* d, int c)   // icon, name, and a little arrow: click for the menu
{
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    const int is = SC(16), x = (rc.left + rc.right - is) / 2, y = rc.top + SC(3);
    const COLORREF col = CH_COLORS[Iclamp(gCh[c].color, 0, 7)];
    if (gChIcon[c]) DrawIconEx(dc, x, y, gChIcon[c], is, is, 0, nullptr, DI_NORMAL);
    else {                                      // no icon: a microphone for inputs, a window for apps
        HPEN p = CreatePen(PS_SOLID, Imax(1, SC(2) - 1), col);
        HGDIOBJ op = SelectObject(dc, p), ob = SelectObject(dc, GetStockObject(NULL_BRUSH));
        if (gCh[c].type == CH_OUT) {            // a speaker
            POINT sp[6] = { { x + SC(2), y + SC(6) }, { x + SC(5), y + SC(6) }, { x + SC(9), y + SC(2) },
                            { x + SC(9), y + SC(14) }, { x + SC(5), y + SC(10) }, { x + SC(2), y + SC(10) } };
            Polygon(dc, sp, 6);
            Arc(dc, x + SC(7), y + SC(4), x + SC(14), y + SC(12), x + SC(12), y + SC(4), x + SC(12), y + SC(12));
        } else if (gCh[c].type == CH_DEV) {
            RoundRect(dc, x + SC(5), y + SC(1), x + SC(11), y + SC(10), SC(6), SC(6));
            Arc(dc, x + SC(2), y + SC(3), x + SC(14), y + SC(13), x + SC(2), y + SC(8), x + SC(14), y + SC(8));
            MoveToEx(dc, x + SC(8), y + SC(13), nullptr); LineTo(dc, x + SC(8), y + SC(16));
        } else {
            RoundRect(dc, x + SC(1), y + SC(2), x + SC(15), y + SC(14), SC(3), SC(3));
            MoveToEx(dc, x + SC(1), y + SC(5), nullptr); LineTo(dc, x + SC(15), y + SC(5));
        }
        SelectObject(dc, op); SelectObject(dc, ob); DeleteObject(p);
    }
    wchar_t t[64]; ChanLabel(c, t, 64);
    RECT tr = { rc.left + SC(3), y + is + SC(1), rc.right - SC(3), rc.bottom - SC(1) };
    SetBkMode(dc, TRANSPARENT); SetTextColor(dc, TXT_C);
    HGDIOBJ of = SelectObject(dc, gFont);
    DrawTextW(dc, t, -1, &tr, DT_SINGLELINE | DT_CENTER | DT_VCENTER | DT_END_ELLIPSIS | DT_NOPREFIX);
    SelectObject(dc, of);
    const int ax = rc.right - SC(8), ay = y + is / 2;   // the arrow
    POINT tri[3] = { { ax - SC(3), ay - SC(1) }, { ax + SC(3), ay - SC(1) }, { ax, ay + SC(2) } };
    HBRUSH ab = CreateSolidBrush(gDark ? DK_DIM : gLtDim); HPEN ap = CreatePen(PS_SOLID, 1, gDark ? DK_DIM : gLtDim);
    HGDIOBJ o1 = SelectObject(dc, ab), o2 = SelectObject(dc, ap);
    Polygon(dc, tri, 3);
    SelectObject(dc, o1); SelectObject(dc, o2); DeleteObject(ab); DeleteObject(ap);
    if (d->itemState & ODS_FOCUS) { RECT f = rc; InflateRect(&f, -1, -1); DrawFocusRect(dc, &f); }
}
static void DrawChanAdd(DRAWITEMSTRUCT* d)      // an empty channel: a dashed "+ Add" box
{
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    HPEN p = CreatePen(PS_DOT, 1, gDark ? RGB(95, 95, 95) : RGB(160, 160, 160));
    HGDIOBJ op = SelectObject(dc, p), ob = SelectObject(dc, GetStockObject(NULL_BRUSH));
    SetBkMode(dc, TRANSPARENT);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, SC(8), SC(8));
    SelectObject(dc, op); SelectObject(dc, ob); DeleteObject(p);
    SetTextColor(dc, (d->itemState & ODS_SELECTED) ? TXT_C : (gDark ? DK_DIM : gLtDim));
    HGDIOBJ of = SelectObject(dc, gFont);
    RECT t1 = rc; t1.bottom = (rc.top + rc.bottom) / 2; RECT t2 = rc; t2.top = t1.bottom;
    DrawTextW(dc, L"+", -1, &t1, DT_SINGLELINE | DT_CENTER | DT_BOTTOM);
    DrawTextW(dc, L"Add", -1, &t2, DT_SINGLELINE | DT_CENTER | DT_TOP);
    SelectObject(dc, of);
    if (d->itemState & ODS_FOCUS) { RECT f = rc; InflateRect(&f, -3, -3); DrawFocusRect(dc, &f); }
}
static void DrawVMeter2(DRAWITEMSTRUCT* d, float l, float r, bool live, float holdL, float holdR, bool clip);
static void DrawVMeter(DRAWITEMSTRUCT* d, float l, float r, bool live) { DrawVMeter2(d, l, r, live, 0, 0, false); }
static void DrawVMeter2(DRAWITEMSTRUCT* d, float l, float r, bool live, float holdL, float holdR, bool clip)   // upright; r < 0: one bar
{
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    const int n = r < 0 ? 1 : 2, gap = n > 1 ? Imax(1, SC(2)) : 0, bw = (rc.right - rc.left - gap * (n - 1)) / n;
    for (int i = 0; i < n; i++) {
        RECT b = { rc.left + i * (bw + gap), rc.top, rc.left + i * (bw + gap) + bw, rc.bottom };
        HBRUSH tb = CreateSolidBrush(gDark ? DK_TRACK : LT_TRACK); FillRect(dc, &b, tb); DeleteObject(tb);
        if (!live) continue;
        const float v = i == 0 ? l : r;
        const float db = v > 0.00001f ? 20.0f * log10f(v) : -100.0f;
        const float pos = (db + 60.0f) / 60.0f < 0 ? 0.0f : (db + 60.0f) / 60.0f > 1 ? 1.0f : (db + 60.0f) / 60.0f;
        const int H = b.bottom - b.top, top = b.bottom - (int)(H * pos);
        const int yY = b.bottom - (int)(H * 51.0f / 60), yR = b.bottom - (int)(H * 57.0f / 60);   // -9 dB, -3 dB
        auto seg = [&](int y0, int y1, COLORREF c) { if (y1 <= y0) return; RECT s2 = { b.left, y0, b.right, y1 }; HBRUSH br = CreateSolidBrush(c); FillRect(dc, &s2, br); DeleteObject(br); };
        seg(Imax(top, yY), b.bottom, METER_C);
        if (top < yY) seg(Imax(top, yR), yY, RGB(217, 165, 32));
        if (top < yR) seg(top, yR, RGB(229, 83, 75));
        const float hv = i == 0 ? holdL : holdR;   // peak hold: a thin line where it last peaked
        if (hv > 0.001f) {
            const float hdb = 20.0f * log10f(hv), hp = (hdb + 60.0f) / 60.0f;
            if (hp > 0.02f) { const int hy = b.bottom - (int)(H * (hp > 1 ? 1 : hp)); seg(Imax((int)b.top, hy - 1), Imin((int)b.bottom, hy + 1), hdb > -3 ? RGB(229, 83, 75) : RGB(230, 230, 230)); }
        }
        if (clip) seg(b.top, b.top + Imax(2, SC(3)), RGB(255, 60, 60));   // it hit the top (0 dB): red for 2 s
    }
}
static int gLimShow[MAX_OUT];
static void DrawLimit(DRAWITEMSTRUCT* d, bool on)   // a little light: the limiter is catching peaks
{
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    const int ds = SC(8), y = (rc.top + rc.bottom - ds) / 2;
    HBRUSH b = CreateSolidBrush(on ? SOLO_C : (gDark ? RGB(70, 70, 70) : RGB(200, 200, 200)));
    HGDIOBJ ob = SelectObject(dc, b), op = SelectObject(dc, GetStockObject(NULL_PEN));
    Ellipse(dc, rc.left, y, rc.left + ds + 1, y + ds + 1);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(b);
    RECT tr = rc; tr.left += ds + SC(4);
    SetBkMode(dc, TRANSPARENT); SetTextColor(dc, on ? TXT_C : (gDark ? DK_DIM : gLtDim));
    HGDIOBJ of = SelectObject(dc, gFont);
    DrawTextW(dc, L"Limit", -1, &tr, DT_SINGLELINE | DT_VCENTER);
    SelectObject(dc, of);
}
// ---- strip widths: drag a strip's right edge (double-click it: back to normal)
static RECT gStripRc[CH_MAX + MAX_OUT];         // where each strip is now (px)
static HWND gMixHint = nullptr, gDuckLbl = nullptr, gDuckDbLbl = nullptr;
static int ChW(int c)  { return gCh[c].type == CH_NONE ? 50 : (gChW[c] ? gChW[c] : 66); }
static int OutW(int k) { return gOutW[k] ? gOutW[k] : 100; }
static int MixerNeedW()                         // px: how wide the window must be for the strips
{
    int a = SC(42), b = SC(42);
    for (int c = 0; c < CH_MAX; c++) if (gCh[c].type != CH_NONE) a += SC(ChW(c)) + SC(3);
    for (int k = 0; k < gRows && k < MAX_OUT; k++) b += SC(OutW(k)) + (k ? SC(5) : 0);
    return Imax(a, b);
}
static void PlaceFree(HWND c, int x, int y, int w, int h)
{
    if (!c) return;
    RECT r; GetWindowRect(c, &r); MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2);
    const bool resized = r.right - r.left != w || r.bottom - r.top != h;
    if (r.left != x || r.top != y || resized) {
        SetWindowPos(c, nullptr, x, y, w, h, SWP_NOZORDER | SWP_NOACTIVATE | SWP_NOCOPYBITS);
        if (resized) InvalidateRect(c, nullptr, FALSE);   // (labels only repaint their new part by themselves: all of it)
    }
}
static void PlaceTabs()                         // the tabs whose feature is on, side by side (wider when there are fewer)
{
    int n = 0; for (int i = 0; i < TAB_SHOWN; i++) if (PageOn(TAB_ORDER[i])) n++;
    const int tw = Imin(130, (532 - (n - 1) * 2) / Imax(1, n));
    int slot = 0;
    for (int i = 0; i < TAB_SHOWN; i++) {
        const int pg = TAB_ORDER[i];
        HWND t = GetDlgItem(gWnd, IDC_TAB0 + pg);
        if (!t) continue;
        if (!PageOn(pg)) { ShowWindow(t, SW_HIDE); continue; }
        PlaceFree(t, gOrgX + SC(14 + slot * (tw + 2)), SC(10), SC(tw), SC(32));
        if (!gCompact) ShowWindow(t, SW_SHOWNA);
        slot++;
    }
}
static void MixerPlace()                        // the Mixer fills the window: strips side by side, taller faders when there's room
{
    if (!gWnd || gSecChan < 0 || gSecOut < 0 || gCompact) return;
    RECT cr; GetClientRect(gWnd, &cr);
    const int W = Imax((int)cr.right, MixerNeedW()), H = cr.bottom;
    const int extraH = Imax(0, H - SC(DesignH()));
    const int cx0 = SC(14), cw = W - SC(28);
    const int chTop = SC(54), chH = SC(330) + extraH * 2 / 3;
    const int oTop = chTop + chH + SC(16), oH = SC(184) + (extraH - extraH * 2 / 3);
    Section& sc = gSections[gSecChan]; sc.x = UNSC(cx0); sc.y = UNSC(chTop); sc.w = UNSC(cw); sc.h = UNSC(chH); sc.ox = sc.oy = 0;
    Section& so = gSections[gSecOut];  so.x = UNSC(cx0); so.y = UNSC(oTop);  so.w = UNSC(cw); so.h = UNSC(oH);  so.ox = so.oy = 0;

    // the top row: hint on the left; Duck by [ ] dB and Restart audio on the right
    const int rx = cx0 + cw - SC(12) - SC(104);
    PlaceFree(GetDlgItem(gWnd, IDC_RESTARTAUD), rx, chTop + SC(8), SC(104), SC(26));
    const int dbx = rx - SC(10) - SC(22);
    PlaceFree(gDuckDbLbl, dbx, chTop + SC(13), SC(22), SC(18));
    {
        HWND e = GetDlgItem(gWnd, IDC_DUCKDB), u = GetDlgItem(gWnd, SPIN_UD(IDC_DUCKDB));
        RECT ur = {}; if (u) GetWindowRect(u, &ur);
        const int uw = ur.right - ur.left, sw = SC(52), sx = dbx - SC(4) - sw;
        PlaceFree(e, sx, chTop + SC(10), sw - uw, SC(23));
        if (u) PlaceFree(u, sx + sw - uw, chTop + SC(10), uw, SC(23));
        PlaceFree(gDuckLbl, sx - SC(4) - SC(50), chTop + SC(13), SC(50), SC(18));
    }
    PlaceFree(GetDlgItem(gWnd, IDC_CHADDBTN), cx0 + SC(12), chTop + SC(8), SC(116), SC(26));
    {
        bool full = true; for (int c = 0; c < CH_MAX; c++) if (gCh[c].type == CH_NONE) full = false;
        EnableWindow(GetDlgItem(gWnd, IDC_CHADDBTN), !full);
    }
    PlaceFree(gMixHint, cx0 + SC(40), chTop + chH / 2 - SC(20), cw - SC(80), SC(40));

    // channel strips
    const int sy = chTop + SC(36), sh = chH - SC(52);
    int x = SC(21);
    const int n = Imax(1, Imin(gRows, MAX_OUT));
    for (int c = 0; c < CH_MAX; c++) {
        if (gCh[c].type == CH_NONE) { gStripRc[c] = { 0, 0, 0, 0 }; continue; }   // (empty: no strip; "+ Add channel" fills it)
        const int w = SC(ChW(c));
        gStripRc[c] = { x, sy, x + w, sy + sh };
        PlaceFree(GetDlgItem(gWnd, IDC_CHSRC0 + c), x + SC(3), sy + SC(6), w - SC(6), SC(40));
        PlaceFree(GetDlgItem(gWnd, IDC_CHDB0 + c), x + SC(2), sy + SC(47), w - SC(4), SC(16));
        // from the bottom up: output buttons (as many rows as they need), Duck, Mute / Solo
        const int rg = SC(2), inner = w - SC(8);
        const int perRow = Iclamp((inner + rg) / (SC(15) + rg), 1, n), rows = (n + perRow - 1) / perRow;
        const int rh = SC(18), routesTop = sy + sh - SC(6) - rows * rh - (rows - 1) * rg;
        const int duckTop = routesTop - SC(4) - SC(20), msTop = duckTop - SC(3) - SC(20);
        const int gx = x + (w - SC(38)) / 2, ft = sy + SC(65), fb = Imax(ft + SC(40), msTop - SC(6));
        PlaceFree(GetDlgItem(gWnd, IDC_CHVOL0 + c), gx, ft, SC(22), fb - ft);
        PlaceFree(GetDlgItem(gWnd, IDC_CHMETER0 + c), gx + SC(26), ft + SC(2), SC(12), fb - ft - SC(4));
        const int bw = (inner - SC(3)) / 2;
        PlaceFree(GetDlgItem(gWnd, IDC_CHMUTE0 + c), x + SC(4), msTop, bw, SC(20));
        PlaceFree(GetDlgItem(gWnd, IDC_CHSOLO0 + c), x + SC(4) + bw + SC(3), msTop, bw, SC(20));
        PlaceFree(GetDlgItem(gWnd, IDC_CHDUCK0 + c), x + SC(4), duckTop, inner, SC(20));
        for (int k = 0; k < MAX_OUT; k++) {
            const int kk = Imin(k, n - 1), row = kk / perRow, col = kk % perRow;
            const int inRow = Imin(perRow, n - row * perRow);           // (the last row may be shorter: same button size)
            (void)inRow;
            const int rw = (inner - rg * (perRow - 1)) / perRow;
            PlaceFree(GetDlgItem(gWnd, IDC_CHRT0 + c * MAX_OUT + k), x + SC(4) + col * (rw + rg), routesTop + row * (rh + rg), rw, rh);
        }
        PlaceFree(GetDlgItem(gWnd, IDC_CHADD0 + c), x + SC(4), sy + SC(6), w - SC(8), sh - SC(12));
        x += w + SC(3);
    }
    // output strips
    const int oy = oTop + SC(14), oh = oH - SC(22);
    x = SC(21);
    for (int k = 0; k < MAX_OUT; k++) {
        const int w = SC(OutW(k));
        gStripRc[CH_MAX + k] = { x, oy, x + w, oy + oh };
        PlaceFree(GetDlgItem(gWnd, IDC_OVOL0 + k), x + SC(4), oy + SC(6), SC(20), oh - SC(12));
        PlaceFree(GetDlgItem(gWnd, IDC_OMETER0 + k), x + SC(27), oy + SC(8), SC(8), oh - SC(16));
        const int tx = x + SC(40), tw = w - SC(44);
        PlaceFree(GetDlgItem(gWnd, IDC_OLBL0 + k), tx, oy + SC(6), tw, SC(18));
        PlaceFree(GetDlgItem(gWnd, IDC_ODEV0 + k), tx, oy + SC(25), tw, SC(18));
        PlaceFree(GetDlgItem(gWnd, IDC_ODB0 + k),  tx, oy + SC(44), tw, SC(18));
        PlaceFree(GetDlgItem(gWnd, IDC_OLIM0 + k), tx, oy + oh - SC(54), tw, SC(16));
        PlaceFree(GetDlgItem(gWnd, IDC_OMUTE0 + k), tx, oy + oh - SC(30), tw, SC(22));
        if (k < gRows) x += w + SC(5);
    }
    // the hotkeys view: a row per channel in use, then per output
    PlaceFree(GetDlgItem(gWnd, IDC_MIXKEYSBTN), cx0 + SC(136), chTop + SC(8), SC(116), SC(26));
    if (gSecKeys >= 0) {
        Section& sk = gSections[gSecKeys];
        sk.x = UNSC(cx0); sk.y = UNSC(chTop); sk.w = UNSC(cw); sk.h = UNSC(oTop + oH - chTop); sk.ox = sk.oy = 0;
        const int x0 = cx0 + SC(16), nameW = SC(100), modeW = SC(62), gap = SC(4);
        const int colW = Imax(SC(40), (cw - SC(32) - nameW - modeW - gap * 7) / 6);
        const int hy = chTop + SC(46);
        for (int i = 1; i < 7; i++) PlaceFree(GetDlgItem(gWnd, IDC_MIXKCOL0 + i), x0 + nameW + gap + (i - 1) * (colW + gap), hy, colW, SC(18));
        const int mx = x0 + nameW + gap + 6 * (colW + gap);
        PlaceFree(GetDlgItem(gWnd, IDC_MIXKCOL0), mx, hy, modeW, SC(18));
        int y = hy + SC(24);
        for (int r = 0; r < CH_MAX + MAX_OUT; r++) {
            const bool out = r >= CH_MAX;
            const int c = r, k = r - CH_MAX;
            if (!out && gCh[c].type == CH_NONE) continue;
            if (out && k >= gRows) continue;
            if (out && k == 0) y += SC(10);     // (a little gap before the outputs)
            HWND lb = GetDlgItem(gWnd, IDC_MIXKROW0 + r);
            wchar_t t[64], o[64]; if (out) OutName(k, t, 64); else ChanLabel(c, t, 64);
            GetWindowTextW(lb, o, 64); if (lstrcmpW(t, o)) SetWindowTextW(lb, t);
            PlaceFree(lb, x0, y + SC(3), nameW, SC(20));
            const int n = out ? MIXO_N : MIXA_N;
            for (int a = 0; a < n; a++) {
                const int slot = out ? SLOT_MIXOUT0 + k * MIXO_N + a : SLOT_MIX0 + c * MIXA_N + a;
                PlaceFree(GetDlgItem(gWnd, FxKeyButtonId(slot)), x0 + nameW + gap + a * (colW + gap), y, colW, SC(24));
            }
            if (!out) PlaceFree(GetDlgItem(gWnd, IDC_MIXHOLDMODE0 + c), mx, y, modeW, SC(24));
            y += SC(28);
        }
        PlaceFree(GetDlgItem(gWnd, IDC_MIXKEYHDR), x0, y + SC(16), SC(160), SC(20));
        HWND e = GetDlgItem(gWnd, IDC_MIXSTEP), u = GetDlgItem(gWnd, SPIN_UD(IDC_MIXSTEP));
        RECT ur = {}; if (u) GetWindowRect(u, &ur);
        const int uw = ur.right - ur.left;
        PlaceFree(e, x0 + SC(166), y + SC(13), SC(56) - uw, SC(23));
        if (u) PlaceFree(u, x0 + SC(166) + SC(56) - uw, y + SC(13), uw, SC(23));
        PlaceFree(GetDlgItem(gWnd, IDC_MIXSTEPDB), x0 + SC(228), y + SC(16), SC(200), SC(20));
    }
    if (gPage == PAGE_MIXER) InvalidateRect(gWnd, nullptr, FALSE);
}
static bool MixerStripRect(int i, RECT* r)      // i < CH_MAX: a channel's strip; CH_MAX + k: output k's
{
    if (i < 0 || i >= CH_MAX + MAX_OUT || gStripRc[i].right <= gStripRc[i].left) return false;
    *r = gStripRc[i];
    return true;
}
static int  gEdgeDrag = -1, gEdgeX0 = 0, gEdgeW0 = 0;   // dragging a strip's edge
static int  gEdgeLast = -1; static DWORD gEdgeLastT = 0;
static int MixerEdgeAt(int x, int y)            // the strip whose right edge is under the mouse (-1: none)
{
    if (gCompact || gPage != PAGE_MIXER || gMixSub != 0) return -1;
    for (int i = 0; i < CH_MAX + gRows && i < CH_MAX + MAX_OUT; i++) {
        if (i < CH_MAX && gCh[i].type == CH_NONE) continue;   // (empty ones stay small)
        const RECT& r = gStripRc[i];
        if (r.right <= r.left) continue;
        if (y >= r.top && y < r.bottom && x >= r.right - SC(4) && x <= r.right + SC(5)) return i;
    }
    return -1;
}
static void MixerEdgeSet(int i, int w)          // design px; 0 = normal
{
    if (i < CH_MAX) gChW[i] = w ? Iclamp(w, 52, 240) : 0;
    else gOutW[i - CH_MAX] = w ? Iclamp(w, 84, 320) : 0;
    const int need = MixerNeedW();              // wider than the window: the window grows
    RECT c; GetClientRect(gWnd, &c);
    if (need > c.right && !IsZoomed(gWnd)) Layout();
    MixerPlace();
    RedrawWindow(gWnd, nullptr, nullptr, RDW_INVALIDATE | RDW_ALLCHILDREN | RDW_UPDATENOW);   // (shows straight away while you drag)
}
static void MixerPaintStrips(HDC dc)            // (from the window's paint) the strips' outlines and colours
{
    if (gCompact || gPage != PAGE_MIXER || gMixSub != 0) return;
    for (int i = 0; i < CH_MAX + gRows; i++) {
        RECT r; if (!MixerStripRect(i, &r)) continue;
        if (i < CH_MAX && gCh[i].type == CH_NONE) continue;   // (an empty one is just its Add box)
        const bool solo = i < CH_MAX && gCh[i].solo;
        HPEN sp = CreatePen(PS_SOLID, 1, solo ? SOLO_C : (gDark ? DK_SECTION : LT_BORDER));
        HGDIOBJ op = SelectObject(dc, sp), ob = SelectObject(dc, GetStockObject(NULL_BRUSH));
        RoundRect(dc, r.left, r.top, r.right, r.bottom, SC(10), SC(10));
        SelectObject(dc, op); SelectObject(dc, ob); DeleteObject(sp);
        if (i < CH_MAX) {
            RECT bar = { r.left + SC(5), r.top + SC(2), r.right - SC(5), r.top + SC(5) };
            HBRUSH b = CreateSolidBrush(CH_COLORS[Iclamp(gCh[i].color, 0, 7)]); FillRect(dc, &bar, b); DeleteObject(b);
        }
    }
}

static float gChShownL[CH_MAX], gChShownR[CH_MAX], gOutShown[MAX_OUT];   // meters (falling slowly)
static float gChHoldL[CH_MAX], gChHoldR[CH_MAX], gOutHold[MAX_OUT];       // peak hold (1.5 s, then it falls)
static DWORD gChHoldT[CH_MAX], gChHoldTR[CH_MAX], gOutHoldT[MAX_OUT], gChClipT[CH_MAX], gOutClipT[MAX_OUT];
static void MeterHold(float v, float& hold, DWORD& t, DWORD now)
{
    if (v >= hold) { hold = v; t = now; }
    else if (now - t > 1500) hold *= 0.85f;
}
static void MixerMeterTick()                    // (50 ms) meters and limit lights on the Mixer page
{
    if (gPage != PAGE_MIXER || !IsWindowVisible(gWnd) || IsIconic(gWnd)) return;
    for (int c = 0; c < CH_MAX; c++) {
        float pl = gChA[c].peakL, pr = gChA[c].peakR; gChA[c].peakL = gChA[c].peakR = 0;
        if (gCh[c].type == CH_NONE) continue;
        const float g = gCh[c].mute ? 0.0f : DbGain10(gCh[c].db10);
        pl *= g; pr *= g;
        gChShownL[c] = pl > gChShownL[c] ? pl : gChShownL[c] * 0.82f;
        gChShownR[c] = pr > gChShownR[c] ? pr : gChShownR[c] * 0.82f;
        const DWORD tn = GetTickCount();
        MeterHold(pl, gChHoldL[c], gChHoldT[c], tn);
        MeterHold(pr, gChHoldR[c], gChHoldTR[c], tn);
        if (pl >= 0.99f || pr >= 0.99f) gChClipT[c] = tn;
        static int last[CH_MAX] = { -999, -999, -999, -999, -999, -999, -999, -999 };
        auto q = [](float v) { return v > 0.001f ? (int)(20.0f * log10f(v)) : -60; };   // whole dB: what the bar can show
        const int now = q(gChShownL[c]) * 100 + q(gChShownR[c]) + (q(gChHoldL[c]) + 60) * 10000 + (q(gChHoldR[c]) + 60) * 1000000
                      + (tn - gChClipT[c] < 2000 ? 1 << 30 : 0);
        if (now != last[c]) { last[c] = now; InvalidateRect(GetDlgItem(gWnd, IDC_CHMETER0 + c), nullptr, FALSE); }
    }
    for (int k = 0; k < MAX_OUT && k < gRows; k++) {
        // (UpdateMeter, just before this, already took this tick's peak into gOutShow: use that, in dB)
        gOutShown[k] = gOutShow[k] > -79.0f ? powf(10.0f, gOutShow[k] / 20.0f) : 0.0f;
        const DWORD tn = GetTickCount();
        MeterHold(gOutShown[k], gOutHold[k], gOutHoldT[k], tn);
        if (gOutShow[k] > -0.2f) gOutClipT[k] = tn;
        static int lastO[MAX_OUT] = { -999, -999, -999, -999, -999 };
        const int now = (gOutShown[k] > 0.001f ? (int)(20.0f * log10f(gOutShown[k])) : -60)
                      + ((gOutHold[k] > 0.001f ? (int)(20.0f * log10f(gOutHold[k])) : -60) + 60) * 1000 + (tn - gOutClipT[k] < 2000 ? 1 << 30 : 0);
        if (now != lastO[k]) { lastO[k] = now; InvalidateRect(GetDlgItem(gWnd, IDC_OMETER0 + k), nullptr, FALSE); }
        if (gLimHit[k]) {                       // lit for a moment after each catch
            gLimHit[k] = false;
            if (!gLimShow[k]) InvalidateRect(GetDlgItem(gWnd, IDC_OLIM0 + k), nullptr, FALSE);
            gLimShow[k] = 8;
        } else if (gLimShow[k] > 0 && --gLimShow[k] == 0) InvalidateRect(GetDlgItem(gWnd, IDC_OLIM0 + k), nullptr, FALSE);
    }
}
static void MixerOutNames()                     // each output strip shows its device
{
    for (int k = 0; k < MAX_OUT; k++) {
        HWND lb = GetDlgItem(gWnd, IDC_ODEV0 + k), cb = GetDlgItem(gWnd, IDC_ROWDEV + k);
        if (!lb || !cb) continue;
        wchar_t t[160] = L"", o[160] = L"";
        if (k < gRows) GetWindowTextW(cb, t, 160);
        GetWindowTextW(lb, o, 160);
        if (lstrcmpW(t, o)) SetWindowTextW(lb, t);
    }
}
static void MixerRefresh()                      // after a profile / settings change
{
    for (int c = 0; c < CH_MAX; c++) FaderLabel(IDC_CHVOL0 + c);
    AppScanStart();
    for (int k = 0; k < MAX_OUT; k++) FaderLabel(IDC_OVOL0 + k);
    SendDlgItemMessageW(gWnd, SPIN_UD(IDC_DUCKDB), UDM_SETPOS32, 0, gDuckDb);
    MixerOutNames();
    Layout();
    MixerRedraw();
}

static void PictureInfo()
{
    const wchar_t* base = wcsrchr(gPicPath, L'\\');
    wchar_t t[MAX_PATH]; wsprintfW(t, gPicPath[0] ? L"%s" : L"No picture", base ? base + 1 : gPicPath);
    SetDlgItemTextW(gWnd, IDC_PICINFO, t);
    EnableWindow(GetDlgItem(gWnd, IDC_PICREMOVE), gPicPath[0] != 0);
    EnableWindow(GetDlgItem(gWnd, IDC_PICPLACE), gPicPath[0] != 0 && gPicFit == 4);
    PicUiRefresh();
}

static void SetCompact(bool on)
{
    gCompact = on;
    Layout();
    InvalidateRect(gWnd, nullptr, TRUE);
}

// ======================= soundboard: play modes, options, recording, folders =======================
static void PadSetData(int i, short* data, unsigned len);
static void PadBrowse(int i);
static void PadClear(int i);

static void PadTrigger(int i)
{
    if (gPadChoke && i < PAD_N) for (int k = 0; k < PAD_N; k++) if (k != i && gPads[k].playing) gPads[k].stop = true;   // one at a time
    gPads[i].trigger = true;
}

static void PadKey(int i, bool pressed, bool released)   // hotkey or click, by the pad's play mode
{
    Pad& p = gPads[i];
    if (!p.data) return;
    switch (p.mode) {
    case PM_HOLD:   if (pressed) PadTrigger(i); else if (released) p.stop = true; break;
    case PM_LOOP:
    case PM_TOGGLE: if (pressed) { if (p.playing) p.stop = true; else PadTrigger(i); } break;
    default:        if (pressed) PadTrigger(i); break;
    }
}

static void PadsFolder(wchar_t* out)
{
    lstrcpynW(out, gIni, MAX_PATH);
    wchar_t* slash = wcsrchr(out, L'\\'); if (slash) slash[1] = 0; else out[0] = 0;
    lstrcatW(out, L"Pads"); CreateDirectoryW(out, nullptr);
}

static void PadRecordStart(int i)
{
    if (!gRunning) { MessageBoxW(gWnd, L"Press Start on the Main tab first, then record.", L"Lag Effect - Soundboard", MB_ICONINFORMATION); return; }
    gPadRecSlot = i; gPadRecPos = 0; gPadRec = true;
    InvalidateRect(GetDlgItem(gWnd, SbButtonId(i)), nullptr, FALSE);
}

static void PadRecordFinish()                   // trim, save as a WAV in %APPDATA%\LagEffect\Pads, put on the pad
{
    int i = gPadRecSlot; gPadRecSlot = -1;
    unsigned n = gPadRecPos;
    if (i < 0 || n < RATE / 4) return;
    unsigned a = 0, b = n;
    FindSoundEnds(gPadRecBuf, n, &a, &b);
    short* d = (short*)HeapAlloc(GetProcessHeap(), 0, (b - a) * sizeof(short));
    if (!d) return;
    memcpy(d, gPadRecBuf + a, (b - a) * sizeof(short));
    wchar_t dir[MAX_PATH], path[MAX_PATH]; PadsFolder(dir);
    SYSTEMTIME t; GetLocalTime(&t);
    wsprintfW(path, L"%s\\Recording %02d-%02d %02d.%02d.%02d.wav", dir, t.wMonth, t.wDay, t.wHour, t.wMinute, t.wSecond);
    WriteWav(path, d, b - a);
    PadSetData(i, d, b - a);
    lstrcpynW(gPadFile[i], path, MAX_PATH);
    gPadName[i][0] = 0;
    InvalidateRect(GetDlgItem(gWnd, SbButtonId(i)), nullptr, FALSE);
}

static void PadLoadFolder()                     // fill empty pads (this page onward) from a folder of sounds
{
    BROWSEINFOW bi = {};
    bi.hwndOwner = gWnd;
    bi.lpszTitle = L"Pick a folder of sounds (MP3, WAV, FLAC). They fill your empty pads.";
    bi.ulFlags = BIF_RETURNONLYFSDIRS | BIF_NEWDIALOGSTYLE;
    LPITEMIDLIST pidl = SHBrowseForFolderW(&bi);
    if (!pidl) return;
    wchar_t dir[MAX_PATH];
    BOOL ok = SHGetPathFromIDListW(pidl, dir);
    CoTaskMemFree(pidl);
    if (!ok) return;
    int loaded = 0, next = gPadBank * PADS;
    static const wchar_t* exts[] = { L"*.mp3", L"*.wav", L"*.flac" };
    for (const wchar_t* e : exts) {
        wchar_t pat[MAX_PATH]; wsprintfW(pat, L"%s\\%s", dir, e);
        WIN32_FIND_DATAW fd; HANDLE f = FindFirstFileW(pat, &fd);
        if (f == INVALID_HANDLE_VALUE) continue;
        do {
            while (next < PAD_N && (gPads[next].data || gPadFile[next][0])) next++;
            if (next >= PAD_N) break;
            wchar_t full[MAX_PATH]; wsprintfW(full, L"%s\\%s", dir, fd.cFileName);
            lstrcpynW(gPadFile[next], full, MAX_PATH); gPadName[next][0] = 0;
            PadLoad(next, full);
            loaded++; next++;
        } while (FindNextFileW(f, &fd));
        FindClose(f);
    }
    wchar_t m[96]; wsprintfW(m, loaded ? L"Loaded %d sounds" : L"No empty pads (or no sounds in that folder)", loaded);
    ShowOsd(m, loaded > 0);
}

static const COLORREF PAD_COLORS[8] = { RGB(214, 69, 65), RGB(232, 126, 4), RGB(241, 196, 15), RGB(46, 160, 67),
                                        RGB(22, 160, 133), RGB(52, 120, 220), RGB(142, 68, 173), RGB(230, 90, 160) };
static const wchar_t* PAD_COLOR_NAMES[8] = { L"Red", L"Orange", L"Yellow", L"Green", L"Teal", L"Blue", L"Purple", L"Pink" };

static void PadMenu(int i, HWND anchor)          // the "..." menu on a pad row
{
    Pad& p = gPads[i];
    HMENU m = CreatePopupMenu(), mode = CreatePopupMenu(), spd = CreatePopupMenu(), pit = CreatePopupMenu(),
          fin = CreatePopupMenu(), fout = CreatePopupMenu(), col = CreatePopupMenu();
    const wchar_t* modes[4] = { L"One-shot (click restarts)", L"Loop (click again to stop)", L"Hold (plays while the hotkey is held)", L"Toggle (click again to stop)" };
    for (int k = 0; k < 4; k++) AppendMenuW(mode, MF_STRING | (p.mode == k ? MF_CHECKED : 0), 1 + k, modes[k]);
    static const int speeds[] = { 50, 75, 90, 100, 110, 125, 150, 200 };
    for (int k = 0; k < 8; k++) { wchar_t t[24]; wsprintfW(t, L"%d%%", speeds[k]); AppendMenuW(spd, MF_STRING | ((p.speed ? p.speed : 100) == speeds[k] ? MF_CHECKED : 0), 10 + k, t); }
    static const int pitches[] = { -12, -7, -5, -3, 0, 3, 5, 7, 12 };
    for (int k = 0; k < 9; k++) { wchar_t t[24]; if (pitches[k]) wsprintfW(t, L"%s%d semitones", pitches[k] > 0 ? L"+" : L"", pitches[k]); else lstrcpyW(t, L"Normal"); AppendMenuW(pit, MF_STRING | (p.pitch == pitches[k] ? MF_CHECKED : 0), 30 + k, t); }
    static const int fades[] = { 0, 20, 100, 300, 1000 };
    for (int k = 0; k < 5; k++) {
        wchar_t t[24]; wsprintfW(t, fades[k] ? L"%d ms" : L"None", fades[k]);
        AppendMenuW(fin,  MF_STRING | (p.fadeInMs == fades[k] ? MF_CHECKED : 0), 50 + k, t);
        AppendMenuW(fout, MF_STRING | (p.fadeOutMs == fades[k] ? MF_CHECKED : 0), 60 + k, t);
    }
    for (int k = 0; k < 8; k++) AppendMenuW(col, MF_STRING | (gPadColor[i] == PAD_COLORS[k] ? MF_CHECKED : 0), 80 + k, PAD_COLOR_NAMES[k]);
    AppendMenuW(col, MF_STRING, 89, L"Pick a colour...");
    AppendMenuW(col, MF_STRING | (gPadColor[i] == CLR_NONE ? MF_CHECKED : 0), 90, L"Default");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)mode, L"Play mode");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)spd, L"Speed");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)pit, L"Pitch");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)fin, L"Fade in");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)fout, L"Fade out");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(m, MF_STRING, 70, L"Rename...");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)col, L"Colour");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(m, MF_STRING, 95, L"Record from my mic (up to 10 s)");
    AppendMenuW(m, MF_STRING, 96, L"Load a sound...");
    AppendMenuW(m, MF_STRING | (p.data ? 0 : MF_GRAYED), 97, L"Clear");
    RECT r; GetWindowRect(anchor, &r);
    int cmd = TrackPopupMenu(m, TPM_RETURNCMD | TPM_NONOTIFY, r.left, r.bottom, 0, gWnd, nullptr);
    DestroyMenu(m);
    if (cmd >= 1 && cmd <= 4)        p.mode = cmd - 1;
    else if (cmd >= 10 && cmd < 18)  p.speed = speeds[cmd - 10];
    else if (cmd >= 30 && cmd < 39)  p.pitch = pitches[cmd - 30];
    else if (cmd >= 50 && cmd < 55)  p.fadeInMs = fades[cmd - 50];
    else if (cmd >= 60 && cmd < 65)  p.fadeOutMs = fades[cmd - 60];
    else if (cmd >= 80 && cmd < 88)  gPadColor[i] = PAD_COLORS[cmd - 80];
    else if (cmd == 90)              gPadColor[i] = CLR_NONE;
    else if (cmd == 89) {
        static COLORREF custom[16];
        CHOOSECOLORW cc = {}; cc.lStructSize = sizeof(cc); cc.hwndOwner = gWnd; cc.lpCustColors = custom;
        cc.rgbResult = gPadColor[i] == CLR_NONE ? PAD_COLORS[5] : gPadColor[i]; cc.Flags = CC_FULLOPEN | CC_RGBINIT;
        if (ChooseColorW(&cc)) gPadColor[i] = cc.rgbResult;
    } else if (cmd == 70) {
        wchar_t nm[48]; lstrcpynW(nm, gPadName[i], 48);
        if (!nm[0] && p.data) PadName(i, nm, 48);
        if (InputBox(L"Rename pad", L"Name shown on this pad (leave empty for the file name):", nm, 40)) lstrcpynW(gPadName[i], nm, 48);
        else if (!nm[0]) gPadName[i][0] = 0;
    }
    else if (cmd == 95) PadRecordStart(i);
    else if (cmd == 96) PadBrowse(i);
    else if (cmd == 97) { PadClear(i); gPadName[i][0] = 0; }
    InvalidateRect(GetDlgItem(gWnd, SbButtonId(i)), nullptr, FALSE);
}

// ======================= clips: pages, copy, MP3, history =======================
static void SetClipBank(int b)
{
    gClipBank = Iclamp(b, 0, CLIP_BANKS - 1);
    for (int r = 0; r < CLIPS; r++) {
        SetDlgItemInt(gWnd, IDC_CLIPVOL + r, (UINT)gPads[CLIP0 + ClipSlot(r)].vol, FALSE);
        InvalidateRect(GetDlgItem(gWnd, IDC_CLIPPLAY + r), nullptr, FALSE);
    }
    for (int k = 0; k < CLIP_BANKS; k++) InvalidateRect(GetDlgItem(gWnd, IDC_CLIPBANK0 + k), nullptr, FALSE);
}

static bool ClipTrimmedFile(int c, wchar_t* out)  // the clip as you hear it (trimmed): the file itself, or a temp copy
{
    const Clip& k = gClips[c];
    if (!k.base) return false;
    if (k.ts == 0 && k.te >= k.baseLen && GetFileAttributesW(gPadFile[CLIP0 + c]) != INVALID_FILE_ATTRIBUTES) {
        lstrcpynW(out, gPadFile[CLIP0 + c], MAX_PATH); return true;
    }
    wchar_t tmp[MAX_PATH], name[MAX_PATH];
    GetTempPathW(MAX_PATH, tmp);
    PadName(CLIP0 + c, name, MAX_PATH);
    wsprintfW(out, L"%s%s.wav", tmp, name);
    DeleteFileW(out);
    return WriteWav(out, k.base + k.ts, k.te - k.ts);
}

static void ClipCopy(int c)                     // copy as a file: paste it straight into Discord
{
    wchar_t path[MAX_PATH];
    if (!ClipTrimmedFile(c, path)) return;
    size_t chars = lstrlenW(path) + 2;
    HGLOBAL h = GlobalAlloc(GMEM_MOVEABLE | GMEM_ZEROINIT, sizeof(DROPFILES) + chars * sizeof(wchar_t));
    if (!h) return;
    DROPFILES* df = (DROPFILES*)GlobalLock(h);
    df->pFiles = sizeof(DROPFILES); df->fWide = TRUE;
    lstrcpyW((wchar_t*)(df + 1), path);
    GlobalUnlock(h);
    if (OpenClipboard(gWnd)) {
        EmptyClipboard();
        if (!SetClipboardData(CF_HDROP, h)) GlobalFree(h);
        CloseClipboard();
        ShowOsd(L"Clip copied: paste it in Discord", true);
    } else GlobalFree(h);
}

// MP3 through Windows' own encoder (Media Foundation, Windows 8+), loaded at run time.
static const GUID kMFMediaType_Audio  = { 0x73647561, 0x0000, 0x0010, { 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71 } };
static const GUID kMFAudioFormat_MP3  = { 0x00000055, 0x0000, 0x0010, { 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71 } };
static const GUID kMFAudioFormat_PCM  = { 0x00000001, 0x0000, 0x0010, { 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71 } };
static const GUID kMF_MT_MAJOR_TYPE   = { 0x48eba18e, 0xf8c9, 0x4687, { 0xbf, 0x11, 0x0a, 0x74, 0xc9, 0xf9, 0x6a, 0x8f } };
static const GUID kMF_MT_SUBTYPE      = { 0xf7e34c9a, 0x42e8, 0x4714, { 0xb7, 0x4b, 0xcb, 0x29, 0xd7, 0x2c, 0x35, 0xe5 } };
static const GUID kMF_MT_AUDIO_SAMPLES_PER_SECOND = { 0x5faeeae7, 0x0290, 0x4c31, { 0x9e, 0x8a, 0xc5, 0x34, 0xf6, 0x8d, 0x9d, 0xba } };
static const GUID kMF_MT_AUDIO_NUM_CHANNELS       = { 0x37e48bf5, 0x645e, 0x4c5b, { 0x89, 0xde, 0xad, 0xa9, 0xe2, 0x9b, 0x69, 0x6a } };
static const GUID kMF_MT_AUDIO_BITS_PER_SAMPLE    = { 0xf2deb57f, 0x40fa, 0x4764, { 0xaa, 0x33, 0xed, 0x4f, 0x2d, 0x1f, 0xf6, 0x69 } };
static const GUID kMF_MT_AUDIO_AVG_BYTES_PER_SECOND = { 0x1aab75c8, 0xcfef, 0x451c, { 0xab, 0x95, 0xac, 0x03, 0x4b, 0x8e, 0x17, 0x31 } };
static const GUID kMF_MT_AUDIO_BLOCK_ALIGNMENT    = { 0x322de230, 0x9eeb, 0x43bd, { 0xab, 0x7a, 0xff, 0x41, 0x22, 0x51, 0x54, 0x1d } };
static const GUID kMF_TRANSCODE_CONTAINERTYPE     = { 0x150ff23f, 0x4abc, 0x478b, { 0xac, 0x4f, 0xe1, 0x91, 0x6f, 0xba, 0x1c, 0xca } };
static const GUID kMFTranscodeContainerType_MP3   = { 0xe438b912, 0x83f1, 0x4de6, { 0x9e, 0x3a, 0x9f, 0xfb, 0xc6, 0xdd, 0x24, 0xd1 } };

static bool WriteMp3(const wchar_t* path, const short* d, unsigned n)
{
    HMODULE plat = LoadLibraryW(L"mfplat.dll"), rw = LoadLibraryW(L"mfreadwrite.dll");
    if (!plat || !rw) return false;
    typedef HRESULT (WINAPI* PStartup)(ULONG, DWORD);
    typedef HRESULT (WINAPI* PShutdown)();
    typedef HRESULT (WINAPI* PCreateAttr)(IMFAttributes**, UINT32);
    typedef HRESULT (WINAPI* PCreateType)(IMFMediaType**);
    typedef HRESULT (WINAPI* PCreateBuf)(DWORD, IMFMediaBuffer**);
    typedef HRESULT (WINAPI* PCreateSample)(IMFSample**);
    typedef HRESULT (WINAPI* PCreateWriter)(LPCWSTR, IMFByteStream*, IMFAttributes*, IMFSinkWriter**);
    auto startup = (PStartup)(void*)GetProcAddress(plat, "MFStartup");
    auto shutdown = (PShutdown)(void*)GetProcAddress(plat, "MFShutdown");
    auto mkAttr = (PCreateAttr)(void*)GetProcAddress(plat, "MFCreateAttributes");
    auto mkType = (PCreateType)(void*)GetProcAddress(plat, "MFCreateMediaType");
    auto mkBuf = (PCreateBuf)(void*)GetProcAddress(plat, "MFCreateMemoryBuffer");
    auto mkSample = (PCreateSample)(void*)GetProcAddress(plat, "MFCreateSample");
    auto mkWriter = (PCreateWriter)(void*)GetProcAddress(rw, "MFCreateSinkWriterFromURL");
    if (!startup || !shutdown || !mkAttr || !mkType || !mkBuf || !mkSample || !mkWriter) return false;
    if (FAILED(startup(0x00020070, 0))) return false;           // MF_VERSION, full startup
    bool ok = false;
    IMFAttributes* at = nullptr; IMFSinkWriter* w = nullptr; IMFMediaType *outT = nullptr, *inT = nullptr;
    DWORD stream = 0;
    if (SUCCEEDED(mkAttr(&at, 1)) && SUCCEEDED(at->SetGUID(kMF_TRANSCODE_CONTAINERTYPE, kMFTranscodeContainerType_MP3)) &&
        SUCCEEDED(mkWriter(path, nullptr, at, &w)) && SUCCEEDED(mkType(&outT)) && SUCCEEDED(mkType(&inT))) {
        outT->SetGUID(kMF_MT_MAJOR_TYPE, kMFMediaType_Audio); outT->SetGUID(kMF_MT_SUBTYPE, kMFAudioFormat_MP3);
        outT->SetUINT32(kMF_MT_AUDIO_SAMPLES_PER_SECOND, RATE); outT->SetUINT32(kMF_MT_AUDIO_NUM_CHANNELS, 1);
        outT->SetUINT32(kMF_MT_AUDIO_AVG_BYTES_PER_SECOND, 128000 / 8);
        inT->SetGUID(kMF_MT_MAJOR_TYPE, kMFMediaType_Audio); inT->SetGUID(kMF_MT_SUBTYPE, kMFAudioFormat_PCM);
        inT->SetUINT32(kMF_MT_AUDIO_SAMPLES_PER_SECOND, RATE); inT->SetUINT32(kMF_MT_AUDIO_NUM_CHANNELS, 1);
        inT->SetUINT32(kMF_MT_AUDIO_BITS_PER_SAMPLE, 16); inT->SetUINT32(kMF_MT_AUDIO_BLOCK_ALIGNMENT, 2);
        inT->SetUINT32(kMF_MT_AUDIO_AVG_BYTES_PER_SECOND, RATE * 2);
        if (SUCCEEDED(w->AddStream(outT, &stream)) && SUCCEEDED(w->SetInputMediaType(stream, inT, nullptr)) && SUCCEEDED(w->BeginWriting())) {
            ok = true;
            const unsigned CH = RATE / 10;      // 100 ms per sample
            for (unsigned off = 0; off < n && ok; off += CH) {
                unsigned cnt = Min(CH, n - off);
                IMFMediaBuffer* b = nullptr; IMFSample* smp = nullptr; BYTE* dst = nullptr;
                ok = SUCCEEDED(mkBuf(cnt * 2, &b)) && SUCCEEDED(b->Lock(&dst, nullptr, nullptr));
                if (ok) { memcpy(dst, d + off, cnt * 2); b->Unlock(); b->SetCurrentLength(cnt * 2); }
                ok = ok && SUCCEEDED(mkSample(&smp)) && SUCCEEDED(smp->AddBuffer(b)) &&
                     SUCCEEDED(smp->SetSampleTime((LONGLONG)off * 10000000 / RATE)) &&
                     SUCCEEDED(smp->SetSampleDuration((LONGLONG)cnt * 10000000 / RATE)) && SUCCEEDED(w->WriteSample(stream, smp));
                if (smp) smp->Release(); if (b) b->Release();
            }
            ok = SUCCEEDED(w->Finalize()) && ok;
        }
    }
    if (inT) inT->Release(); if (outT) outT->Release(); if (w) w->Release(); if (at) at->Release();
    shutdown();
    if (!ok) DeleteFileW(path);
    return ok;
}

static void ClipSaveMp3(int c)
{
    const Clip& k = gClips[c];
    if (!k.base) return;
    wchar_t path[MAX_PATH], name[MAX_PATH];
    PadName(CLIP0 + c, name, MAX_PATH);
    wsprintfW(path, L"%s.mp3", name);
    OPENFILENAMEW o = {};
    o.lStructSize = sizeof(o); o.hwndOwner = gWnd; o.lpstrFilter = L"MP3 audio\0*.mp3\0"; o.lpstrFile = path; o.nMaxFile = MAX_PATH;
    o.lpstrDefExt = L"mp3"; o.lpstrTitle = L"Save the clip as MP3"; o.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (!GetSaveFileNameW(&o)) return;
    DeleteFileW(path);
    if (WriteMp3(path, k.base + k.ts, k.te - k.ts)) ShowOsd(L"Saved as MP3", true);
    else MessageBoxW(gWnd, L"Windows' MP3 encoder isn't available here, so the MP3 couldn't be made. "
                           L"Use Copy or the WAV in the Clips folder instead.", L"Lag Effect - Clips", MB_ICONWARNING);
}

static void ClipRename(int c)
{
    wchar_t* old = gPadFile[CLIP0 + c];
    if (!old[0] || !InClipFolder(old)) { MessageBoxW(gWnd, L"Only clips you recorded can be renamed here.", L"Lag Effect - Clips", MB_ICONINFORMATION); return; }
    wchar_t name[64]; PadName(CLIP0 + c, name, 64);
    if (!InputBox(L"Rename clip", L"New name for this clip:", name, 60)) return;
    for (wchar_t* q = name; *q; q++) if (wcschr(L"\\/:*?\"<>|", *q)) *q = L'_';
    wchar_t np[MAX_PATH]; wsprintfW(np, L"%s\\%s.wav", gClipDir, name);
    if (MoveFileW(old, np)) lstrcpynW(old, np, MAX_PATH);
    else MessageBoxW(gWnd, L"Couldn't rename the clip (is that name already taken?).", L"Lag Effect - Clips", MB_ICONWARNING);
    InvalidateRect(GetDlgItem(gWnd, IDC_CLIPPLAY + c % CLIPS), nullptr, FALSE);
}

static void OpenTrim(int c);
static void ClipMenu(int c, HWND anchor)
{
    bool has = gClips[c].base != nullptr;
    HMENU m = CreatePopupMenu();
    UINT g = has ? 0 : MF_GRAYED;
    AppendMenuW(m, MF_STRING | g, 1, L"Copy (paste into Discord)");
    AppendMenuW(m, MF_STRING | g, 2, L"Save as MP3...");
    AppendMenuW(m, MF_STRING | g, 3, L"Show in folder");
    AppendMenuW(m, MF_STRING | g, 4, L"Rename...");
    AppendMenuW(m, MF_STRING | g | (gClipPinned[c] ? MF_CHECKED : 0), 5, L"Pin (never replaced when full)");
    AppendMenuW(m, MF_STRING | g, 6, L"Trim...");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(m, MF_STRING | g, 7, L"Remove");
    RECT r; GetWindowRect(anchor, &r);
    int cmd = TrackPopupMenu(m, TPM_RETURNCMD | TPM_NONOTIFY, r.left, r.bottom, 0, gWnd, nullptr);
    DestroyMenu(m);
    if (cmd == 1) ClipCopy(c);
    else if (cmd == 2) ClipSaveMp3(c);
    else if (cmd == 3) { wchar_t a[MAX_PATH + 16]; wsprintfW(a, L"/select,\"%s\"", gPadFile[CLIP0 + c]); ShellExecuteW(nullptr, L"open", L"explorer.exe", a, nullptr, SW_SHOWNORMAL); }
    else if (cmd == 4) ClipRename(c);
    else if (cmd == 5) gClipPinned[c] = !gClipPinned[c];
    else if (cmd == 6) OpenTrim(c);
    else if (cmd == 7) { ClipClear(c); gClipPinned[c] = false; ClipShiftUp(c); }
    InvalidateRect(GetDlgItem(gWnd, IDC_CLIPPLAY + c % CLIPS), nullptr, FALSE);
}

static void ClipHistory(HWND anchor)            // every clip ever saved: load one back onto the board
{
    ClipFolder();
    struct Item { wchar_t name[MAX_PATH]; FILETIME t; } items[24]; int n = 0;
    wchar_t pat[MAX_PATH]; wsprintfW(pat, L"%s\\*.wav", gClipDir);
    WIN32_FIND_DATAW fd; HANDLE f = FindFirstFileW(pat, &fd);
    if (f != INVALID_HANDLE_VALUE) {
        do {                                    // keep the 24 newest
            int at = n < 24 ? n++ : 23;
            if (at == 23 && n == 24 && CompareFileTime(&fd.ftLastWriteTime, &items[23].t) <= 0) continue;
            lstrcpynW(items[at].name, fd.cFileName, MAX_PATH); items[at].t = fd.ftLastWriteTime;
            for (int k = at; k > 0 && CompareFileTime(&items[k].t, &items[k - 1].t) > 0; k--) { Item tmp = items[k]; items[k] = items[k - 1]; items[k - 1] = tmp; }
        } while (FindNextFileW(f, &fd));
        FindClose(f);
    }
    HMENU m = CreatePopupMenu();
    for (int k = 0; k < n; k++) {
        wchar_t t[MAX_PATH]; lstrcpynW(t, items[k].name, MAX_PATH); wchar_t* dot = wcsrchr(t, L'.'); if (dot) *dot = 0;
        AppendMenuW(m, MF_STRING, 1 + k, t);
    }
    if (!n) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"No clips saved yet");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(m, MF_STRING, 100, L"Open the Clips folder");
    RECT r; GetWindowRect(anchor, &r);
    int cmd = TrackPopupMenu(m, TPM_RETURNCMD | TPM_NONOTIFY, r.left, r.bottom, 0, gWnd, nullptr);
    DestroyMenu(m);
    if (cmd == 100) { ShellExecuteW(nullptr, L"open", gClipDir, nullptr, nullptr, SW_SHOWNORMAL); return; }
    if (cmd < 1 || cmd > n) return;
    int slot = -1;
    for (int k = 0; k < CLIP_N && slot < 0; k++) { int c = (gClipBank * CLIPS + k) % CLIP_N; if (!gClips[c].base && !gPadFile[CLIP0 + c][0]) slot = c; }
    if (slot < 0) { MessageBoxW(gWnd, L"All clip slots are full. Remove one first.", L"Lag Effect - Clips", MB_ICONINFORMATION); return; }
    wchar_t full[MAX_PATH]; wsprintfW(full, L"%s\\%s", gClipDir, items[cmd - 1].name);
    gClips[slot].pendTs = gClips[slot].pendTe = 0;
    gClipStamp[slot] = gClipStampNext++;
    lstrcpynW(gPadFile[CLIP0 + slot], full, MAX_PATH);
    PadLoad(CLIP0 + slot, full);
    if (slot / CLIPS != gClipBank) SetClipBank(slot / CLIPS);
}

static void DrawClipBank(DRAWITEMSTRUCT* d)     // clip page button (same look as the pad pages)
{
    int b = (int)d->CtlID - IDC_CLIPBANK0;
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    bool active = b == gClipBank, any = false;
    for (int r = 0; r < CLIPS; r++) any |= gClips[b * CLIPS + r].base != nullptr;
    HBRUSH br = CreateSolidBrush(active ? ACCENT : gDark ? DK_CTL : LT_CARD);
    HPEN pn = CreatePen(PS_SOLID, 1, active ? ACCENT : gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ ob = SelectObject(dc, br), op = SelectObject(dc, pn);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 10, 10);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(br); DeleteObject(pn);
    wchar_t t[8]; wsprintfW(t, any ? L"%c \x2022" : L"%c", L'A' + b);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, active ? RGB(255, 255, 255) : TXT_C);
    HGDIOBJ of = SelectObject(dc, active ? gFontBold : gFont);
    DrawTextW(dc, t, -1, &rc, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(dc, of);
}

// ======================= soundboard pages =======================
static void SetPadBank(int b)
{
    gPadBank = Iclamp(b, 0, PAD_BANKS - 1);
    for (int i = 0; i < PADS; i++) {            // show this page's volumes (the box writes back the same value)
        SetDlgItemInt(gWnd, IDC_PADVOL + i, (UINT)gPads[PadSlot(i)].vol, FALSE);
        InvalidateRect(GetDlgItem(gWnd, IDC_PADPLAY + i), nullptr, FALSE);
    }
    for (int i = 0; i < PAD_BANKS; i++) InvalidateRect(GetDlgItem(gWnd, IDC_PADBANK0 + i), nullptr, FALSE);
}

static void DrawPadBank(DRAWITEMSTRUCT* d)      // page button: A-D, filled when showing, dot if it has sounds
{
    int b = (int)d->CtlID - IDC_PADBANK0;
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    bool active = b == gPadBank, any = false, playing = false;
    for (int i = 0; i < PADS; i++) { any |= gPads[b * PADS + i].data != nullptr; playing |= gPads[b * PADS + i].playing; }
    HBRUSH br = CreateSolidBrush(active ? ACCENT : gDark ? DK_CTL : LT_CARD);
    HPEN   pn = CreatePen(PS_SOLID, 1, active || playing ? ACCENT : gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ ob = SelectObject(dc, br), op = SelectObject(dc, pn);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 12, 12);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(br); DeleteObject(pn);
    wchar_t t[8]; wsprintfW(t, any ? L"%c \x2022" : L"%c", L'A' + b);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, active ? RGB(255, 255, 255) : TXT_C);
    HGDIOBJ of = SelectObject(dc, active ? gFontBold : gFont);
    DrawTextW(dc, t, -1, &rc, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(dc, of);
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) { RECT fr = rc; InflateRect(&fr, -3, -3); DrawFocusRect(dc, &fr); }
}

// ======================= text to speech (Windows voices, SAPI) =======================
// The line is rendered to 48 kHz audio in the background, then played like a pad (and through the
// voice effects if the soundboard is set to). Voices: the classic SAPI list plus the newer OneCore ones.
static const GUID kCLSID_SpVoice   = { 0x96749377, 0x3391, 0x11D2, { 0x9E, 0xE3, 0x00, 0xC0, 0x4F, 0x79, 0x73, 0x96 } };
static const GUID kIID_ISpVoice    = { 0x6C44DF74, 0x72B9, 0x4992, { 0xA1, 0xEC, 0xEF, 0x99, 0x6E, 0x04, 0x22, 0xD4 } };
static const GUID kCLSID_SpStream  = { 0x715D9C59, 0x4442, 0x11D2, { 0x96, 0x05, 0x00, 0xC0, 0x4F, 0x8E, 0xE6, 0x28 } };
static const GUID kIID_ISpStream   = { 0x12E3CCA9, 0x7518, 0x44C5, { 0xA5, 0xE7, 0xBA, 0x5A, 0x79, 0xCB, 0x92, 0x9E } };
static const GUID kSPDFID_WaveFormatEx = { 0xC31ADBAE, 0x527F, 0x4FF5, { 0xA2, 0x30, 0xF6, 0x2B, 0xB6, 0x1F, 0xF7, 0x0C } };
static const GUID kCLSID_SpObjectTokenCategory = { 0xA910187F, 0x0C7A, 0x45AC, { 0x92, 0xCC, 0x59, 0xED, 0xAF, 0xB7, 0x7B, 0x53 } };
static const GUID kIID_ISpObjectTokenCategory  = { 0x2D3D3845, 0x39AF, 0x4850, { 0xBB, 0xF9, 0x40, 0xB4, 0x97, 0x80, 0x01, 0x1D } };
static const GUID kCLSID_SpObjectToken = { 0xEF411752, 0x3736, 0x4CB4, { 0x9C, 0x8C, 0x8E, 0xF4, 0xCC, 0xB5, 0x8E, 0xFE } };
static const GUID kIID_ISpObjectToken  = { 0x14056589, 0xE16C, 0x11D2, { 0xBB, 0x90, 0x00, 0xC0, 0x4F, 0x8E, 0xE6, 0xC0 } };

#define TTS_MAX_VOICES 1000                  // the natural-voices add-on alone brings hundreds (Edge has most languages)
static wchar_t gTtsNames[TTS_MAX_VOICES][128], gTtsIds[TTS_MAX_VOICES][512];
static int     gTtsLang[TTS_MAX_VOICES];        // each voice's language (Windows LCID, e.g. 0x080A = Spanish, Mexico)
static int     gTtsCount = 0;
static volatile LONG gTtsBusy = 0;

struct VoiceList { wchar_t names[TTS_MAX_VOICES][128], ids[TTS_MAX_VOICES][512]; int lang[TTS_MAX_VOICES]; int count; };
static void TtsEnum(VoiceList& v)               // every installed voice (any thread)
{
    CoInitializeEx(nullptr, COINIT_MULTITHREADED); // usually already done by the audio library; harmless if so
    v.count = 0;
    static const wchar_t* cats[] = { L"HKEY_LOCAL_MACHINE\\SOFTWARE\\Microsoft\\Speech\\Voices",
                                     L"HKEY_LOCAL_MACHINE\\SOFTWARE\\Microsoft\\Speech_OneCore\\Voices" };
    for (const wchar_t* catId : cats) {
        ISpObjectTokenCategory* cat = nullptr;
        if (FAILED(CoCreateInstance(kCLSID_SpObjectTokenCategory, nullptr, CLSCTX_ALL, kIID_ISpObjectTokenCategory, (void**)&cat))) continue;
        IEnumSpObjectTokens* en = nullptr;
        if (SUCCEEDED(cat->SetId(catId, FALSE)) && SUCCEEDED(cat->EnumTokens(nullptr, nullptr, &en)) && en) {
            ISpObjectToken* tok = nullptr;
            while (v.count < TTS_MAX_VOICES && en->Next(1, &tok, nullptr) == S_OK) {
                LPWSTR id = nullptr, name = nullptr;
                if (SUCCEEDED(tok->GetId(&id)) && SUCCEEDED(tok->GetStringValue(nullptr, &name)) && name) {
                    bool dup = false;
                    for (int i = 0; i < v.count; i++) if (!lstrcmpiW(v.names[i], name)) dup = true;
                    if (!dup) {
                        lstrcpynW(v.names[v.count], name, 128); lstrcpynW(v.ids[v.count], id, 512);
                        v.lang[v.count] = 0;
                        ISpDataKey* attr = nullptr; LPWSTR lang = nullptr;   // "Language" = hex LCID(s), e.g. "409;9"
                        if (SUCCEEDED(tok->OpenKey(L"Attributes", &attr)) && attr) {
                            if (SUCCEEDED(attr->GetStringValue(L"Language", &lang)) && lang) {
                                v.lang[v.count] = (int)wcstol(lang, nullptr, 16);
                                CoTaskMemFree(lang);
                            }
                            attr->Release();
                        }
                        v.count++;
                    }
                }
                if (id) CoTaskMemFree(id);
                if (name) CoTaskMemFree(name);
                tok->Release();
            }
            en->Release();
        }
        cat->Release();
    }
}
static bool TtsIsNatural(const wchar_t* name) { return wcsstr(name, L"Natural") || wcsstr(name, L"Neural") || wcsstr(name, L"Online"); }
static bool gTtsListed = false;                  // the voice list has been read (it's read in the background at startup)
static void TtsAdopt(const VoiceList& v)        // (natural-sounding voices first: accents pick them before older ones)
{
    int o = 0;
    for (int pass = 0; pass < 3; pass++)        // natural English voices, other natural ones, then the older ones
        for (int i = 0; i < v.count; i++) {
            const bool nat = TtsIsNatural(v.names[i]), en = (v.lang[i] & 0x3FF) == 0x09;
            if ((pass == 0 && !(nat && en)) || (pass == 1 && !(nat && !en)) || (pass == 2 && nat)) continue;
            memcpy(gTtsNames[o], v.names[i], sizeof(gTtsNames[o])); memcpy(gTtsIds[o], v.ids[i], sizeof(gTtsIds[o]));
            gTtsLang[o] = v.lang[i]; o++;
        }
    gTtsCount = o; gTtsListed = true;
}
static void TtsListVoices()                     // now, on this thread
{
    VoiceList* v = (VoiceList*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(VoiceList));
    if (!v) return;
    TtsEnum(*v); TtsAdopt(*v);
    HeapFree(GetProcessHeap(), 0, v);
}
static DWORD WINAPI TtsListThread(LPVOID)       // at startup, so opening the window doesn't wait for Windows' voice list
{
    CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    VoiceList* v = (VoiceList*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(VoiceList));
    if (v) { TtsEnum(*v); if (!PostMessageW(gWnd, WM_VOICES_LISTED, 0, (LPARAM)v)) HeapFree(GetProcessHeap(), 0, v); }
    CoUninitialize();
    return 0;
}
static void TtsShortName(const wchar_t* in, wchar_t* out, int cap)
{
    if (!wcsncmp(in, L"Microsoft ", 10)) in += 10;
    int o = 0;
    for (const wchar_t* q = in; *q && o < cap - 1; ) {
        if (!wcsncmp(q, L" Online", 7)) { q += 7; continue; }
        out[o++] = *q++;
    }
    out[o] = 0;
}
static void TtsFillVoices();
static void TtsEnsureListed() { if (!gTtsListed) { TtsListVoices(); TtsFillVoices(); } }

struct TtsJob { wchar_t text[600]; wchar_t xml[3000]; wchar_t voice[512]; int rate, pitch, room, srcRate; bool natural, split, vary; short* data; unsigned len; bool ok; };

// Accents: your words read by a real Windows voice for that language / region (a Spanish (Mexico) voice reading
// English sounds Mexican, and so on), at that accent's own pace (a little different every line), with some of
// the words swapped for that language's own (picked at random, so it doesn't say the same thing every time).
// Windows only has voices for some places; missing ones can be installed from here. American and Canadian are
// deliberately stereotypical.
struct TtsSwap { const wchar_t* from; const wchar_t* to[4]; };     // a word / phrase and what it can become
struct TtsAccent {
    const wchar_t* name; int lang, alt, primary; const wchar_t* voiceName; const wchar_t* tag;   // tag: e.g. es-MX
    int rate; const TtsSwap* swaps; int nSwaps; const wchar_t* open[5]; const wchar_t* close[5];
};
static const TtsSwap SW_US[] = {
    { L"very much", { L"so much", L"a ton" } }, { L"very", { L"super", L"so", L"totally" } }, { L"good", { L"awesome", L"rad", L"sick" } },
    { L"great", { L"awesome", L"epic", L"amazing" } }, { L"hello", { L"hey", L"what's up", L"yo" } }, { L"hi", { L"hey", L"yo" } },
    { L"yes", { L"yeah", L"yep", L"totally" } }, { L"friend", { L"dude", L"bro", L"buddy" } } };
static const TtsSwap SW_CA[] = {
    { L"thank you very much", { L"thanks a bunch", L"thank you kindly" } }, { L"about", { L"aboot" } }, { L"out", { L"oot" } }, { L"sorry", { L"soary", L"sorry", L"soary" } },
    { L"friend", { L"buddy", L"bud" } }, { L"hello", { L"hey there", L"hello there" } }, { L"yes", { L"yeah", L"you bet", L"for sure" } } };
static const TtsSwap SW_IE[] = {
    { L"thank you very much", { L"thanks a million", L"thanks a mill" } }, { L"thanks", { L"thanks a million", L"cheers" } },
    { L"very much", { L"a million", L"loads" } }, { L"good", { L"grand", L"deadly", L"savage" } }, { L"great", { L"grand", L"deadly" } }, { L"very", { L"fierce", L"wicked", L"very" } },
    { L"hello", { L"how's the form", L"hiya", L"how's it going" } }, { L"hi", { L"hiya" } }, { L"friend", { L"pal", L"lad" } },
    { L"yes", { L"yeah", L"it is" } } };
static const TtsSwap SW_IN[] = {
    { L"thank you very much", { L"bahut dhanyavaad", L"thank you so much ji" } }, { L"very much", { L"very very much", L"bahut" } },
    { L"hello", { L"namaste", L"hello ji" } }, { L"hi", { L"namaste" } }, { L"thank you", { L"dhanyavaad", L"thank you ji" } },
    { L"thanks", { L"dhanyavaad", L"shukriya" } }, { L"friend", { L"dost", L"yaar" } }, { L"yes", { L"haan", L"haan ji" } },
    { L"very", { L"very very", L"bahut" } } };
static const TtsSwap SW_MX[] = {
    { L"thank you very much", { L"muchas gracias", L"mil gracias" } }, { L"very much", { L"mucho" } }, { L"hello", { L"hola", L"qué onda" } }, { L"hi", { L"hola" } }, { L"thank you", { L"gracias", L"muchas gracias" } },
    { L"thanks", { L"gracias" } }, { L"friend", { L"amigo", L"compadre" } }, { L"yes", { L"sí", L"órale" } },
    { L"very", { L"muy" } }, { L"goodbye", { L"adiós", L"nos vemos" } }, { L"bye", { L"adiós", L"nos vemos" } } };
static const TtsSwap SW_FR[] = {
    { L"thank you very much", { L"merci beaucoup", L"merci mille fois" } }, { L"very much", { L"beaucoup" } }, { L"hello", { L"bonjour", L"salut" } }, { L"hi", { L"salut" } }, { L"thank you", { L"merci", L"merci beaucoup" } },
    { L"thanks", { L"merci" } }, { L"yes", { L"oui", L"ouais" } }, { L"no", { L"non" } }, { L"friend", { L"mon ami", L"mon pote" } },
    { L"very", { L"très" } }, { L"goodbye", { L"au revoir", L"à plus" } }, { L"bye", { L"salut", L"à plus" } } };
static const TtsSwap SW_RU[] = {
    { L"thank you very much", { L"большое спасибо", L"спасибо огромное" } }, { L"very much", { L"очень" } }, { L"hello", { L"привет", L"здравствуй" } }, { L"hi", { L"привет" } }, { L"thank you", { L"спасибо", L"большое спасибо" } },
    { L"thanks", { L"спасибо" } }, { L"yes", { L"да", L"конечно" } }, { L"no", { L"нет" } }, { L"friend", { L"друг", L"братан" } },
    { L"very", { L"очень" } }, { L"goodbye", { L"пока", L"до свидания" } }, { L"bye", { L"пока" } } };
static const TtsSwap SW_SY[] = {
    { L"thank you very much", { L"يسلمو كتير", L"ألف شكر" } }, { L"very much", { L"كتير" } }, { L"hello", { L"مرحبا", L"أهلين" } }, { L"hi", { L"مرحبا" } }, { L"thank you", { L"يسلمو", L"شكراً" } }, { L"thanks", { L"يسلمو" } },
    { L"yes", { L"إي", L"أكيد" } }, { L"no", { L"لأ" } }, { L"friend", { L"حبيبي", L"خيي" } }, { L"bye", { L"يلا باي", L"مع السلامة" } } };
static const TtsSwap SW_AR[] = {
    { L"thank you very much", { L"شكراً جزيلاً", L"ألف شكر" } }, { L"very much", { L"جداً" } }, { L"hello", { L"مرحبا", L"السلام عليكم" } }, { L"hi", { L"مرحبا" } }, { L"thank you", { L"شكراً", L"شكراً جزيلاً" } },
    { L"thanks", { L"شكراً" } }, { L"yes", { L"نعم", L"أيوه" } }, { L"no", { L"لا" } }, { L"friend", { L"صديقي", L"حبيبي" } },
    { L"goodbye", { L"مع السلامة" } }, { L"bye", { L"مع السلامة" } } };
static const TtsSwap SW_SC[] = {
    { L"thank you very much", { L"cheers, pal", L"ta very much" } }, { L"thanks", { L"cheers", L"ta" } },
    { L"hello", { L"awright", L"how's it gaun" } }, { L"hi", { L"awright", L"hiya" } }, { L"yes", { L"aye", L"aye, nae bother" } },
    { L"no", { L"naw", L"nae chance" } }, { L"don't", { L"dinnae", L"don't" } }, { L"can't", { L"cannae" } }, { L"won't", { L"willnae" } },
    { L"isn't", { L"isnae" } }, { L"didn't", { L"didnae" } }, { L"going to", { L"gonnae" } }, { L"small", { L"wee" } },
    { L"little", { L"wee" } }, { L"know", { L"ken" } }, { L"very", { L"pure", L"dead" } }, { L"good", { L"braw", L"pure brilliant" } },
    { L"great", { L"braw", L"pure dead brilliant" } }, { L"friend", { L"pal", L"mate" } }, { L"what", { L"whit" } },
    { L"nothing", { L"hee haw", L"nothin'" } }, { L"child", { L"wean", L"bairn" } } };
static const TtsSwap SW_MEM[] = {
    { L"thank you very much", { L"thank ya kindly", L"much obliged" } }, { L"thanks", { L"thank ya", L"preciate it" } },
    { L"you all", { L"y'all" } }, { L"you guys", { L"y'all" } }, { L"everyone", { L"all y'all", L"everybody" } },
    { L"going to", { L"fixin' to", L"gonna" } }, { L"think", { L"reckon" } }, { L"hello", { L"hey y'all", L"howdy" } },
    { L"hi", { L"hey", L"howdy" } }, { L"very", { L"mighty", L"real" } }, { L"friend", { L"buddy", L"darlin'" } },
    { L"yes", { L"yes sir", L"yeah", L"sure enough" } }, { L"isn't", { L"ain't" } }, { L"great", { L"mighty fine" } },
    { L"good", { L"real good", L"fine" } } };
#define SWN(a) a, (int)(sizeof(a) / sizeof(a[0]))
static const TtsAccent TTS_ACCENTS[] = {
    { L"No accent", 0, 0, 0, nullptr, nullptr, 0, nullptr, 0, {}, {} },
    { L"American", 0x0409, 0, 0, L"English (United States)", L"en-US", 1, SWN(SW_US),
      { L"Dude, ", L"Bro, ", L"Okay so, ", L"Oh my gosh, ", L"" }, { L". Like, totally.", L". For real.", L". Let's go!", L". No cap.", L"." } },
    { L"Memphis", 0x0409, 0, 0, L"English (United States)", L"en-US", -1, SWN(SW_MEM),
      { L"", L"Well, ", L"Now, ", L"Lord, ", L"" }, { L".", L", y'all.", L", bless your heart.", L", I tell ya.", L"." } },
    { L"Canadian", 0x1009, 0x0409, 0, L"English (Canada)", L"en-CA", 0, SWN(SW_CA),
      { L"", L"Oh, ", L"Sorry, but ", L"Well, ", L"" }, { L", eh?", L", eh.", L", eh buddy?", L", bud.", L"." } },
    { L"Scottish", 0x0809, 0, 0, L"English (United Kingdom)", L"en-GB", 0, SWN(SW_SC),
      { L"", L"Och, ", L"Listen, ", L"Aye, ", L"" }, { L".", L", ken?", L", pal.", L", so it is.", L"." } },
    { L"Irish", 0x1809, 0, 0, L"English (Ireland)", L"en-IE", 1, SWN(SW_IE),
      { L"", L"Ah sure, ", L"Ah here, ", L"Well, ", L"" }, { L".", L", so it is.", L", sure look.", L", like.", L"." } },
    { L"Indian", 0x4009, 0x0439, 0, L"English (India)", L"en-IN", 1, SWN(SW_IN),
      { L"", L"Arre, ", L"Accha, ", L"", L"" }, { L".", L", na?", L", yaar.", L".", L"." } },
    { L"Mexican", 0x080A, 0, 0x0A, L"Spanish (Mexico)", L"es-MX", 1, SWN(SW_MX),
      { L"", L"Órale, ", L"Oye, ", L"Ándale, ", L"" }, { L".", L", amigo.", L", ¿no?", L".", L"." } },
    { L"French", 0x040C, 0x0C0C, 0x0C, L"French (France)", L"fr-FR", 0, SWN(SW_FR),
      { L"", L"Alors, ", L"Eh bien, ", L"Bon, ", L"" }, { L".", L", voilà.", L", hein?", L", n'est-ce pas?", L"." } },
    { L"Russian", 0x0419, 0, 0x19, L"Russian", L"ru-RU", -1, SWN(SW_RU),
      { L"", L"Ну, ", L"Слушай, ", L"Короче, ", L"" }, { L".", L", да?", L", понимаешь?", L".", L"." } },
    { L"Syrian", 0x2801, 0x0C01, 0x01, L"Arabic (Egypt)", L"ar-EG", 0, SWN(SW_SY),
      { L"", L"يلا، ", L"والله، ", L"شو، ", L"" }, { L".", L"، يا حبيبي.", L"، والله.", L".", L"." } },
    { L"Arabic", 0x0401, 0x0C01, 0x01, L"Arabic (Saudi Arabia)", L"ar-SA", 0, SWN(SW_AR),
      { L"", L"يلا، ", L"والله، ", L"طيب، ", L"" }, { L".", L"، يا صديقي.", L"، إن شاء الله.", L".", L"." } },
};
#undef SWN
#define TTS_ACCENT_N ((int)(sizeof(TTS_ACCENTS) / sizeof(TTS_ACCENTS[0])))
static unsigned TtsRand(unsigned n)             // a different pick every line
{
    static unsigned s = GetTickCount() | 1;
    s = s * 1664525u + 1013904223u;
    return n ? (s >> 8) % n : 0;
}
// Natural voices each accent likes best (first found wins), so it doesn't land on a child's or a novelty voice.
static const struct { const wchar_t* accent; const wchar_t* names[6]; } TTS_PREFER[] = {
    { L"American", { L"Andrew", L"Guy", L"Brian", L"Christopher", L"Aria", L"Jenny" } },
    { L"Memphis",  { L"Roger", L"Guy", L"Steffan", L"Eric", L"Ava", L"Michelle" } },
    { L"Canadian", { L"Liam", L"Clara" } },
    { L"Scottish", { L"Ryan", L"Thomas", L"Sonia", L"Libby" } },
    { L"Irish",    { L"Connor", L"Emily" } },
    { L"Indian",   { L"Prabhat", L"Neerja" } },
    { L"Mexican",  { L"Jorge", L"Dalia" } },
    { L"French",   { L"Henri", L"Remy", L"Denise", L"Vivienne" } },
    { L"Russian",  { L"Dmitry", L"Svetlana" } },
    { L"Syrian",   { L"Laith", L"Amany" } },
    { L"Arabic",   { L"Hamed", L"Zariyah" } },
};
static int TtsVoiceFor(int accent)              // index into the voice list, -1 if none installed
{
    if (accent <= 0 || accent >= TTS_ACCENT_N) return -1;
    const TtsAccent& a = TTS_ACCENTS[accent];
    for (const auto& pr : TTS_PREFER) {         // 1. a favourite natural voice in exactly that language / region
        if (lstrcmpiW(pr.accent, a.name)) continue;
        for (const wchar_t* nm : pr.names) {
            if (!nm) break;
            for (int i = 0; i < gTtsCount; i++)
                if (gTtsLang[i] == a.lang && TtsIsNatural(gTtsNames[i]) && wcsstr(gTtsNames[i], nm)) return i;
        }
    }
    for (int pass = 0; pass < 3; pass++)
        for (int i = 0; i < gTtsCount; i++) {
            int l = gTtsLang[i];
            if (pass == 0 && l == a.lang) return i;
            if (pass == 1 && a.alt && l == a.alt) return i;
            if (pass == 2 && a.primary && (l & 0x3FF) == a.primary) return i;
        }
    return -1;
}
static bool TtsIsWordChar(wchar_t c) { return iswalnum(c) || c == L'\''; }
static void TtsSwapWord(wchar_t* t, int cap, const TtsSwap& sw)   // whole words, any case, a random choice each time
{
    int nOpt = 0; while (nOpt < 4 && sw.to[nOpt]) nOpt++;
    if (!nOpt) return;
    wchar_t out[1200]; int o = 0; const int fl = lstrlenW(sw.from);
    for (int i = 0; t[i] && o < 1190;) {
        if (t[i] == 1) {                        // already swapped: \1...\2 isn't touched again
            while (t[i] && t[i] != 2 && o < 1190) out[o++] = t[i++];
            if (t[i] == 2) out[o++] = t[i++];
            continue;
        }
        bool start = i == 0 || !TtsIsWordChar(t[i - 1]);
        if (start && !_wcsnicmp(t + i, sw.from, fl) && !TtsIsWordChar(t[i + fl])) {
            const wchar_t* to = sw.to[TtsRand(nOpt)];
            out[o++] = 1;
            for (int k = 0; to[k] && o < 1188; k++) out[o++] = k == 0 && iswupper(t[i]) ? towupper(to[0]) : to[k];
            out[o++] = 2;
            i += fl;
        } else out[o++] = t[i++];
    }
    out[o] = 0;
    lstrcpynW(t, out, cap);
}
static int TtsPhrase(wchar_t* t, int cap, int accent)   // the accent's words, opener and ending; returns its speaking rate
{
    if (accent <= 0 || accent >= TTS_ACCENT_N) return 0;
    const TtsAccent& a = TTS_ACCENTS[accent];
    for (int i = 0; i < a.nSwaps; i++) TtsSwapWord(t, cap, a.swaps[i]);
    { int o = 0; for (int i = 0; t[i]; i++) if (t[i] != 1 && t[i] != 2) t[o++] = t[i]; t[o] = 0; }   // drop the markers
    int n = lstrlenW(t);
    while (n > 0 && t[n - 1] == L' ') t[--n] = 0;
    if (n) {
        bool question = t[n - 1] == L'?';
        if (!question && (t[n - 1] == L'.' || t[n - 1] == L'!')) t[--n] = 0;
        const wchar_t* op = a.open[TtsRand(5)];   const wchar_t* cl = question ? L"" : a.close[TtsRand(5)];
        if (!op) op = L""; if (!cl) cl = L".";
        wchar_t b[1300];
        if (op[0] && n > 1 && iswupper(t[0]) && !iswupper(t[1]) && t[1] != L' ') t[0] = towlower(t[0]);   // "Dude, this..."
        wsprintfW(b, L"%s%s%s", op, t, cl);
        lstrcpynW(t, b, cap);
    }
    return Iclamp(a.rate + (int)TtsRand(3) - 1, -3, 4);   // its own pace, a little different every line
}

// ---- sounding less like a robot ----
// 1. Prosody: every sentence gets a slightly different pace and pitch, with a natural pause after it
//    (SAPI XML; if a voice won't take it, the plain text is spoken instead).
static void TtsProsody(const wchar_t* in, wchar_t* out, int cap, bool vary = true)
{
    int o = 0;
    auto put = [&](const wchar_t* t) { while (*t && o < cap - 1) out[o++] = *t++; };
    auto sentence = [&](const wchar_t* a, const wchar_t* b) {
        wchar_t open[96];
        wsprintfW(open, L"<rate speed=\"%d\"><pitch middle=\"%d\">", vary ? (int)TtsRand(3) - 1 : 0, vary ? (int)TtsRand(5) - 2 : 0);
        put(open);
        for (const wchar_t* q = a; q < b && o < cap - 8; q++) {
            if (*q == L'&') put(L"&amp;"); else if (*q == L'<') put(L"&lt;"); else if (*q == L'>') put(L"&gt;");
            else out[o++] = *q;
        }
        put(L"</pitch></rate>");
    };
    const wchar_t* a = in;
    for (const wchar_t* q = in; ; q++) {
        bool end = !*q || ((*q == L'.' || *q == L'!' || *q == L'?') && (q[1] == L' ' || !q[1]));
        if (!end) continue;
        const wchar_t* b = *q ? q + 1 : q;
        if (b > a) {
            sentence(a, b);
            wchar_t sil[40]; wsprintfW(sil, L"<silence msec=\"%d\"/>", (140 + (int)TtsRand(180)) * gTtsPause / 100); put(sil);
        }
        if (!*q) break;
        a = q + 1;
    }
    out[o] = 0;
}
// 2. Sound: warmer, less harsh and less "in your skull" (a touch of room), evened out like a voice-over.
static void TtsHumanize(short* d, unsigned n, int room)
{
    Biquad hp, lowS, pres, highS; BqSet(hp, 2, 70, 0.707);
    BqShelf(lowS, false, 180, 2.5); BqPeak(pres, 3200, 1.5, 1.0); BqShelf(highS, true, 9000, -3.0);
    lowS.z1 = lowS.z2 = highS.z1 = highS.z2 = 0;
    static const int tapMs[4] = { 11, 17, 23, 31 }; static const float tapG[4] = { 0.12f, 0.09f, 0.07f, 0.05f };
    float* x = (float*)HeapAlloc(GetProcessHeap(), 0, n * sizeof(float));
    if (!x) return;
    // Level: a slow, smooth 2:1 above -18 dB (power follower ~10 ms in / 150 ms out, gain smoothed again),
    // so the gain never moves within a wave cycle (a fast one distorts: that was the crackle).
    float pw = 0, g = 1.0f, peak = 0;
    const float aIn = 1.0f - expf(-1.0f / (0.010f * RATE)), aOut = 1.0f - expf(-1.0f / (0.150f * RATE)), aG = 1.0f - expf(-1.0f / (0.005f * RATE));
    for (unsigned i = 0; i < n; i++) {
        float v = d[i] / 32768.0f;
        v = BqRun(highS, BqRun(pres, BqRun(lowS, BqRun(hp, v))));
        float p2 = v * v; pw += (p2 - pw) * (p2 > pw ? aIn : aOut);
        const float rms = sqrtf(pw) * 1.414f, thr = 0.126f;
        const float want = rms > thr ? sqrtf(thr / rms) : 1.0f;
        g += (want - g) * aG;
        x[i] = v * g;
    }
    for (unsigned i = n; i-- > 0;) {            // early reflections (from the dry signal, read backwards so it isn't reused)
        float r = 0;
        for (int t = 0; t < 4; t++) { unsigned k = (unsigned)(tapMs[t] * RATE / 1000); if (i >= k) r += x[i - k] * tapG[t] * (room / 35.0f); }
        x[i] += r;
        float a = fabsf(x[i]); if (a > peak) peak = a;
    }
    const float norm = peak > 0.0001f ? 0.708f / peak : 1.0f;  // to -3 dB: room for the volume going up to 200%
    const unsigned fade = Imin((int)n / 4, RATE / 200);          // 5 ms in / out: no click at the ends
    for (unsigned i = 0; i < n; i++) {
        float v = x[i] * norm;
        if (i < fade) v *= i / (float)fade; else if (n - i <= fade) v *= (n - i) / (float)fade;
        d[i] = (short)(v > 1 ? 32767 : v < -1 ? -32767 : v * 32767.0f);
    }
    HeapFree(GetProcessHeap(), 0, x);
}

static void TtsRepitch(short*& d, unsigned& n, int semis)   // the whole line higher / lower, same speed
{
    if (!semis || !d || !n) return;
    PShift* ps = (PShift*)calloc(1, sizeof(PShift));
    const unsigned tail = RATE / 10, m = n + tail;
    short* o = (short*)HeapAlloc(GetProcessHeap(), 0, m * sizeof(short));
    if (!ps || !o) { free(ps); if (o) HeapFree(GetProcessHeap(), 0, o); return; }
    const double r = pow(2.0, semis / 12.0);
    for (unsigned i = 0; i < m; i++) {
        float v = PitchShift(*ps, i < n ? d[i] / 32768.0f : 0.0f, r, 1440, 1.0f);
        o[i] = (short)(v > 1 ? 32767 : v < -1 ? -32767 : v * 32767.0f);
    }
    free(ps);
    HeapFree(GetProcessHeap(), 0, d);
    d = o; n = m;
}

// Band-limited (windowed-sinc, 32 taps) resampling to 48 kHz, then a peak limit: the speech never clips.
static void TtsResample(short*& d, unsigned& n, int srcRate)
{
    if (!d || !n) return;
    if (srcRate != RATE && srcRate > 0) {
        const double step = (double)srcRate / RATE;                 // source samples per output sample
        const unsigned m = (unsigned)((double)n / step);
        short* o = (short*)HeapAlloc(GetProcessHeap(), 0, (size_t)m * sizeof(short));
        if (!o) return;
        const double fc = srcRate < RATE ? 0.5 * 0.92 : 0.5 / step * 0.92;   // keep just under the lower Nyquist
        const int T = 16;
        for (unsigned i = 0; i < m; i++) {
            const double t = i * step; const int c = (int)t;
            double acc = 0, wsum = 0;
            for (int k = c - T + 1; k <= c + T; k++) {
                const double x = t - k;
                const double sx = fabs(x) < 1e-9 ? 2 * fc : sin(2 * 3.141592653589793 * fc * x) / (3.141592653589793 * x);
                const double wpos = (x + T) / (2.0 * T);              // Blackman window over the taps
                const double w = wpos <= 0 || wpos >= 1 ? 0 : 0.42 - 0.5 * cos(2 * 3.141592653589793 * wpos) + 0.08 * cos(4 * 3.141592653589793 * wpos);
                const double kk = sx * w; wsum += kk;
                if (k >= 0 && k < (int)n) acc += d[k] * kk;
            }
            const double v = wsum != 0 ? acc / wsum : 0;
            o[i] = (short)(v > 32767 ? 32767 : v < -32767 ? -32767 : v);
        }
        HeapFree(GetProcessHeap(), 0, d);
        d = o; n = m;
    }
    int peak = 0; for (unsigned i = 0; i < n; i++) peak = Imax(peak, d[i] < 0 ? -d[i] : d[i]);
    if (peak > 23170) {                         // louder than -3 dB: bring it down (room for the volume and your mic)
        const float g = 23170.0f / peak;
        for (unsigned i = 0; i < n; i++) d[i] = (short)(d[i] * g);
    }
}

static bool TtsRender(TtsJob* j, bool useVoice)
{
    bool ok = false;
    ISpVoice* v = nullptr; ISpStream* ss = nullptr; IStream* mem = nullptr;
    if (FAILED(CoCreateInstance(kCLSID_SpVoice, nullptr, CLSCTX_ALL, kIID_ISpVoice, (void**)&v))) return false;
    if (useVoice && j->voice[0]) {
        ISpObjectToken* tok = nullptr;
        if (SUCCEEDED(CoCreateInstance(kCLSID_SpObjectToken, nullptr, CLSCTX_ALL, kIID_ISpObjectToken, (void**)&tok))) {
            if (SUCCEEDED(tok->SetId(nullptr, j->voice, FALSE))) v->SetVoice(tok);
            tok->Release();
        }
    }
    // Taken at (about) the voice's own rate: Windows' converter up to 48 kHz just joins the dots, which sounds
    // crackly / harsh. TtsResample does it properly afterwards.
    const DWORD sr = j->srcRate > 0 ? (DWORD)j->srcRate : RATE;
    WAVEFORMATEX wf = { WAVE_FORMAT_PCM, 1, sr, sr * 2, 2, 16, 0 };
    if (SUCCEEDED(CreateStreamOnHGlobal(nullptr, TRUE, &mem)) &&
        SUCCEEDED(CoCreateInstance(kCLSID_SpStream, nullptr, CLSCTX_ALL, kIID_ISpStream, (void**)&ss)) &&
        SUCCEEDED(ss->SetBaseStream(mem, kSPDFID_WaveFormatEx, &wf)) &&
        SUCCEEDED(v->SetOutput(ss, TRUE)) &&
        SUCCEEDED(v->SetRate(Iclamp(j->rate, -10, 10)))) {
        // Natural sound: each sentence is spoken on its own (its own pace if the voice is an older one), then they're
        // joined here: trimmed, faded in / out and with a real pause between, so nothing clicks at the joins
        // (letting the voice make the pauses / pace changes itself split the audio mid-wave, which crackled).
        const int MAXS = 64;
        unsigned cut[MAXS + 1]; int ns = 0; cut[0] = 0;
        bool spoke = false;
        if (j->split) {
            const wchar_t* a = j->text;
            for (const wchar_t* q = j->text; ns < MAXS; q++) {
                bool end = !*q || ((*q == L'.' || *q == L'!' || *q == L'?') && (q[1] == L' ' || !q[1]));
                if (!end) continue;
                const wchar_t* b = *q ? q + 1 : q;
                wchar_t one[600]; int len = (int)(b - a); if (len > 599) len = 599;
                memcpy(one, a, len * sizeof(wchar_t)); one[len] = 0;
                bool any = false; for (int k = 0; k < len; k++) if (one[k] > L' ') any = true;
                if (any) {
                    v->SetRate(Iclamp(j->rate + (j->vary ? (int)TtsRand(3) - 1 : 0), -10, 10));
                    if (SUCCEEDED(v->Speak(one, SPF_DEFAULT | SPF_IS_NOT_XML, nullptr))) {
                        spoke = true;
                        STATSTG st = {}; mem->Stat(&st, STATFLAG_NONAME);
                        cut[++ns] = (unsigned)(st.cbSize.QuadPart / 2);
                    }
                }
                if (!*q) break;
                a = q + 1;
            }
        } else if (SUCCEEDED(v->Speak(j->text, SPF_DEFAULT | SPF_IS_NOT_XML, nullptr))) {
            spoke = true;
            STATSTG st = {}; mem->Stat(&st, STATFLAG_NONAME);
            cut[++ns] = (unsigned)(st.cbSize.QuadPart / 2);
        }
        HGLOBAL hg = nullptr;
        if (spoke && ns > 0 && SUCCEEDED(GetHGlobalFromStream(mem, &hg))) {
            const short* src = (const short*)GlobalLock(hg);
            unsigned total = cut[ns];
            if (src && total > sr / 20) {
                const unsigned pauseMax = sr * 2;
                unsigned cap = total + (unsigned)ns * pauseMax;
                if (cap > sr * 90) cap = sr * 90;
                short* out = (short*)HeapAlloc(GetProcessHeap(), 0, (size_t)cap * sizeof(short));
                unsigned o = 0;
                for (int k = 0; out && k < ns; k++) {
                    unsigned b = cut[k], e = cut[k + 1];
                    if (ns > 1) {                   // trim the voice's own silence at both ends (a little kept)
                        while (b < e && abs(src[b]) < 150) b++;
                        while (e > b && abs(src[e - 1]) < 150) e--;
                        b = b > cut[k] + sr / 50 ? b - sr / 50 : cut[k];
                        e = e + sr / 25 < cut[k + 1] ? e + sr / 25 : cut[k + 1];
                    }
                    const unsigned L = e - b, fin = Imin((int)L / 4, (int)sr / 300), fout = Imin((int)L / 4, (int)sr / 100);
                    for (unsigned i = 0; i < L && o < cap; i++) {
                        float x = src[b + i];
                        if (i < fin) x *= i / (float)fin; else if (L - i <= fout) x *= (L - i) / (float)fout;
                        out[o++] = (short)x;
                    }
                    if (k < ns - 1) {               // the pause before the next sentence
                        unsigned p = (unsigned)((120 + TtsRand(160)) * Iclamp(gTtsPause, 0, 300) / 100) * sr / 1000;
                        for (unsigned i = 0; i < p && o < cap; i++) out[o++] = 0;
                    }
                }
                if (out && o > sr / 20) { j->data = out; j->len = o; ok = true; }
                else if (out) HeapFree(GetProcessHeap(), 0, out);
            }
            if (src) GlobalUnlock(hg);
        }
    }
    if (ss) { ss->Close(); ss->Release(); }
    if (mem) mem->Release();
    v->Release();
    return ok;
}

static DWORD WINAPI TtsThread(LPVOID arg)
{
    TtsJob* j = (TtsJob*)arg;
    CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
    j->ok = TtsRender(j, true) || (j->voice[0] && TtsRender(j, false));   // newer voices can refuse: use the default
    if (j->ok) TtsResample(j->data, j->len, j->srcRate);
    if (j->ok) TtsRepitch(j->data, j->len, j->pitch);
    if (j->ok && j->natural) TtsHumanize(j->data, j->len, j->room);
    CoUninitialize();
    PostMessageW(gWnd, WM_TTS_DONE, 0, (LPARAM)j);
    return 0;
}

// ---- text to speech: voice settings window ----
static HWND gTtsDlg = nullptr;
static const struct { int id; const wchar_t* label; const wchar_t* unit; int lo, hi; int* var; } TTS_SETS[] = {
    { 21, L"Volume:", L"%", 0, 200, &gTtsVol }, { 22, L"Speed:", L"(-10 to 10)", -10, 10, &gTtsRate },
    { 23, L"Pitch:", L"semitones", -12, 12, &gTtsPitch }, { 24, L"Room sound:", L"%", 0, 100, &gTtsRoom },
    { 25, L"Pauses:", L"% (between sentences)", 0, 300, &gTtsPause } };
static void TtsSpeakText(const wchar_t* t);
static LRESULT CALLBACK TtsDlgProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_COMMAND: {
        int id = LOWORD(w), code = HIWORD(w);
        for (const auto& st : TTS_SETS)
            if (id == st.id) {
                BOOL ok = FALSE; int v = (int)GetDlgItemInt(h, id, &ok, TRUE);
                if (code == EN_CHANGE && ok) { *st.var = Iclamp(v, st.lo, st.hi); if (st.var == &gTtsVol) { gPads[TTS_SLOT].vol = gTtsVol; SetDlgItemInt(gWnd, IDC_TTSVOL, (UINT)gTtsVol, FALSE); } }
                else if (code == EN_KILLFOCUS) SetDlgItemInt(h, id, (UINT)*st.var, TRUE);
                return 0;
            }
        if (id == 30) { gTtsNatural = IsDlgButtonChecked(h, 30) == BST_CHECKED; return 0; }
        if (id == 31) { TtsSpeakText(L"Hello! This is how I sound now. Does that sound better?"); return 0; }
        if (id == 32) {                         // back to how it started
            gTtsVol = 100; gTtsRate = 0; gTtsPitch = 0; gTtsRoom = 35; gTtsPause = 100; gTtsNatural = true;
            for (const auto& st : TTS_SETS) SetDlgItemInt(h, st.id, (UINT)*st.var, TRUE);
            CheckDlgButton(h, 30, BST_CHECKED); gPads[TTS_SLOT].vol = gTtsVol; SetDlgItemInt(gWnd, IDC_TTSVOL, 100, FALSE);
            return 0;
        }
        if (id == IDOK || id == IDCANCEL) { DestroyWindow(h); return 0; }
        return 0;
    }
    case WM_CTLCOLORSTATIC: case WM_CTLCOLORBTN: case WM_CTLCOLOREDIT: case WM_CTLCOLORLISTBOX:
        return CtlColor(h, m, w, l);
    case WM_ERASEBKGND: { RECT rc; GetClientRect(h, &rc); FillRect((HDC)w, &rc, BgSolid()); return 1; }
    case WM_NOTIFY: {
        NMHDR* nh = (NMHDR*)l;
        if (gDark && nh->code == NM_CUSTOMDRAW) {
            wchar_t cls[16]; GetClassNameW(nh->hwndFrom, cls, 16);
            if (!lstrcmpiW(cls, L"Button")) return DrawDarkCheck((NMCUSTOMDRAW*)l);
        }
        break;
    }
    case WM_CLOSE: DestroyWindow(h); return 0;
    case WM_DESTROY: gTtsDlg = nullptr; return 0;
    }
    return DefWindowProcW(h, m, w, l);
}
static void TtsSettingsOpen()
{
    if (gTtsDlg) { SetForegroundWindow(gTtsDlg); return; }
    static bool reg = false;
    if (!reg) { WNDCLASSW wc = {}; wc.lpfnWndProc = TtsDlgProc; wc.hInstance = gInst; wc.hIcon = gIcon; wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
                wc.lpszClassName = L"LagTtsSettings"; RegisterClassW(&wc); reg = true; }
    RECT pr; GetWindowRect(gWnd, &pr);
    RECT r = { 0, 0, SC(330), SC(258) }; DWORD st = WS_POPUP | WS_CAPTION | WS_SYSMENU;
    AdjustWindowRect(&r, st, FALSE);
    int ww = r.right - r.left, wh = r.bottom - r.top;
    gTtsDlg = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LagTtsSettings", L"Text to speech - voice", st,
                              (pr.left + pr.right - ww) / 2, (pr.top + pr.bottom - wh) / 2, ww, wh, gWnd, nullptr, gInst, nullptr);
    if (!gTtsDlg) return;
    auto mk = [&](const wchar_t* cls, const wchar_t* txt, DWORD sty, int x, int y, int w, int hh, int id, DWORD ex = 0) {
        HWND c = CreateWindowExW(ex, cls, txt, WS_CHILD | WS_VISIBLE | sty, SC(x), SC(y), SC(w), SC(hh), gTtsDlg, (HMENU)(INT_PTR)id, gInst, nullptr);
        SendMessageW(c, WM_SETFONT, (WPARAM)gFont, TRUE); return c;
    };
    int y = 14;
    for (const auto& s2 : TTS_SETS) {
        mk(L"STATIC", s2.label, 0, 14, y + 3, 86, 20, -1);
        HWND e = mk(L"EDIT", L"", WS_TABSTOP | ES_RIGHT | ES_AUTOHSCROLL, 104, y, 66, 24, s2.id, WS_EX_CLIENTEDGE);
        HWND u = CreateWindowExW(0, UPDOWN_CLASSW, nullptr, WS_CHILD | WS_VISIBLE | UDS_SETBUDDYINT | UDS_ALIGNRIGHT | UDS_ARROWKEYS | UDS_NOTHOUSANDS,
                                 0, 0, 0, 0, gTtsDlg, nullptr, gInst, nullptr);
        SendMessageW(u, UDM_SETBUDDY, (WPARAM)e, 0); SendMessageW(u, UDM_SETRANGE32, s2.lo, s2.hi); SendMessageW(u, UDM_SETPOS32, 0, *s2.var);
        mk(L"STATIC", s2.unit, 0, 178, y + 3, 150, 20, -1);
        y += 32;
    }
    HWND nat = mk(L"BUTTON", L"Natural sound (pace, warmth, room, even level)", BS_AUTOCHECKBOX | WS_TABSTOP, 14, y + 2, 310, 22, 30);
    CheckDlgButton(gTtsDlg, 30, gTtsNatural ? BST_CHECKED : BST_UNCHECKED); (void)nat;
    y += 34;
    mk(L"BUTTON", L"Test", WS_TABSTOP, 14, y, 90, 28, 31);
    mk(L"BUTTON", L"Reset", WS_TABSTOP, 110, y, 90, 28, 32);
    mk(L"BUTTON", L"Close", WS_TABSTOP | BS_DEFPUSHBUTTON, 226, y, 90, 28, IDOK);
    ThemeTitleBar(gTtsDlg); EnumChildWindows(gTtsDlg, ThemeChild, 0);
    ShowWindow(gTtsDlg, SW_SHOW);
}

static void TtsSpeakNow(const wchar_t* given);
static void TtsSpeak() { TtsSpeakNow(nullptr); }
static void TtsSpeakText(const wchar_t* t) { TtsSpeakNow(t); }
static void TtsSpeakNow(const wchar_t* given)
{
    TtsEnsureListed();
    wchar_t text[600];
    if (given) lstrcpynW(text, given, 600); else GetDlgItemTextW(gWnd, IDC_TTSTEXT, text, 600);
    bool any = false; for (wchar_t* q = text; *q; q++) if (*q > L' ') any = true;
    if (!any || InterlockedCompareExchange(&gTtsBusy, 1, 0) != 0) return;
    TtsJob* j = (TtsJob*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(TtsJob));
    if (!j) { gTtsBusy = 0; return; }
    lstrcpynW(j->text, text, 600);
    int sel = (int)SendDlgItemMessageW(gWnd, IDC_TTSVOICE, CB_GETCURSEL, 0, 0);
    if (sel > 0 && sel - 1 < gTtsCount) lstrcpynW(j->voice, gTtsIds[sel - 1], 512);
    if (gTtsAccent > 0 && gTtsAccent < TTS_ACCENT_N) {   // the accent's voice wins (if it's installed)
        int v = TtsVoiceFor(gTtsAccent);
        if (v >= 0) lstrcpynW(j->voice, gTtsIds[v], 512);
        j->rate = TtsPhrase(j->text, 600, gTtsAccent);
    }
    j->rate += gTtsRate; j->pitch = gTtsPitch; j->room = gTtsRoom; j->natural = gTtsNatural;
    // The realistic ("Natural") voices already sound human: they only get the pauses, not the per-sentence
    // pace / pitch changes or the processing (which only made them worse, and could crackle).
    bool realVoice = false;
    for (int i = 0; i < gTtsCount; i++) if (!lstrcmpiW(gTtsIds[i], j->voice)) realVoice = TtsIsNatural(gTtsNames[i]);
    if (realVoice) j->natural = false;
    j->srcRate = realVoice ? 24000 : 22050;    // what the voices actually make (natural ones 24 kHz, older ones ~22 kHz)
    j->split = gTtsNatural; j->vary = gTtsNatural && !realVoice;   // sentence by sentence (see TtsRender)
    SetDlgItemTextW(gWnd, IDC_TTSSPEAK, L"Speaking...");
    HANDLE t = CreateThread(nullptr, 0, TtsThread, j, 0, nullptr);
    if (t) CloseHandle(t); else { HeapFree(GetProcessHeap(), 0, j); gTtsBusy = 0; SetDlgItemTextW(gWnd, IDC_TTSSPEAK, L"Speak"); }
}

static void OnTtsDone(TtsJob* j)
{
    if (j->ok) {
        PadSetData(TTS_SLOT, j->data, j->len);
        gPads[TTS_SLOT].vol = gTtsVol;
        gPads[TTS_SLOT].trigger = true;
    } else {
        MessageBoxW(gWnd, L"Windows couldn't speak that. Check that a voice is installed "
                          L"(Settings > Time & language > Speech).", L"Lag Effect - Text to speech", MB_ICONWARNING);
    }
    HeapFree(GetProcessHeap(), 0, j);
    gTtsBusy = 0;
    SetDlgItemTextW(gWnd, IDC_TTSSPEAK, L"Speak");
    if (gVoiceInstalling) VoiceProgressTick();
}

// ======================= moving things around (layout + pictures) =======================
// "Move things around" and "Move & resize pictures" put a see-through layer over the window. It catches the mouse
// (except over the tabs and sub-tabs, so you can still switch pages) and outlines what can be moved.
// Layout: drag a control, or a box by its title / empty space; right-click one to put it back.
// Pictures: drag to move, mouse wheel to resize, Delete to remove.
// Where you moved things is saved in the settings and in the profile you're using (each profile has its own).
enum { ED_NONE = 0, ED_LAYOUT = 1, ED_PICS = 2 };
static HWND  gEdWnd = nullptr;
static int   gEdMode = ED_NONE;
static int   gEdHot = -1, gEdDrag = -1;         // item: >= 0 control (gDesign index) / picture; <= -2: section -2 - k; -1 none
static POINT gEdFrom;  static int gEdOx, gEdOy;  // drag start (screen) and the item's offset / position then
static RECT  gEdDone;                           // the Done button (overlay px)

// ---- saving / loading where things were moved ----
static void LayoutKeyC(const Design& d, wchar_t* k)  { wsprintfW(k, L"c%d.%d.%d.%d", d.page, d.sub + 1, d.rx, d.ry); }
static void LayoutKeyS(const Section& s, wchar_t* k) { wsprintfW(k, L"s%d.%d.%d.%d", s.page, s.sub + 1, s.x, s.y); }
static void LayoutSave(const wchar_t* path)
{
    const int cap = 65536;
    wchar_t* buf = (wchar_t*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, cap * sizeof(wchar_t));
    if (!buf) return;
    int n = 0;
    auto add = [&](const wchar_t* line) { int l = lstrlenW(line); if (n + l + 2 < cap) { lstrcpyW(buf + n, line); n += l + 1; } };
    add(L"saved=1");
    wchar_t k[64], line[96];
    for (int i = 0; i < gDesignN; i++) {
        const Design& d = gDesign[i];
        if (d.page < 0 || (!d.ox && !d.oy)) continue;
        bool dup = false;                       // two controls can share a spot (e.g. Song style swaps): write it once
        for (int j = 0; j < i && !dup; j++) dup = gDesign[j].page == d.page && gDesign[j].sub == d.sub && gDesign[j].rx == d.rx && gDesign[j].ry == d.ry;
        if (dup) continue;
        LayoutKeyC(d, k); wsprintfW(line, L"%s=%d,%d", k, d.ox, d.oy); add(line);
    }
    for (int i = 0; i < gSectionN; i++) {
        const Section& s = gSections[i];
        if (!s.ox && !s.oy) continue;
        LayoutKeyS(s, k); wsprintfW(line, L"%s=%d,%d", k, s.ox, s.oy); add(line);
    }
    buf[n] = 0;
    WritePrivateProfileSectionW(L"layout", buf, path);
    HeapFree(GetProcessHeap(), 0, buf);
}
static void LayoutReset()
{
    for (int i = 0; i < gDesignN; i++) gDesign[i].ox = gDesign[i].oy = 0;
    for (int i = 0; i < gSectionN; i++) gSections[i].ox = gSections[i].oy = 0;
}
static bool LayoutLoad(const wchar_t* path, bool apply)   // false (and nothing changes) if the file has no layout
{
    const int cap = 65536;
    wchar_t* buf = (wchar_t*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, cap * sizeof(wchar_t));
    if (!buf) return false;
    DWORD got = GetPrivateProfileSectionW(L"layout", buf, cap, path);
    bool saved = false;
    for (wchar_t* p = buf; got && *p; p += lstrlenW(p) + 1) if (!wcsncmp(p, L"saved=", 6)) saved = true;
    if (saved) {
        LayoutReset();
        for (wchar_t* p = buf; *p; p += lstrlenW(p) + 1) {
            wchar_t* eq = wcschr(p, L'=');
            if (!eq || (p[0] != L'c' && p[0] != L's')) continue;
            int page = 0, sub = 0, x = 0, y = 0, dx = 0, dy = 0;
            if (swscanf_s(p + 1, L"%d.%d.%d.%d=%d,%d", &page, &sub, &x, &y, &dx, &dy) != 6) continue;
            dx = Iclamp(dx, -3000, 3000); dy = Iclamp(dy, -3000, 3000);
            if (p[0] == L'c') {
                for (int i = 0; i < gDesignN; i++) {
                    Design& d = gDesign[i];
                    if (d.page == page && d.sub + 1 == sub && d.rx == x && d.ry == y) { d.ox = dx; d.oy = dy; }
                }
            } else {
                for (int i = 0; i < gSectionN; i++) {
                    Section& s = gSections[i];
                    if (s.page == page && s.sub + 1 == sub && s.x == x && s.y == y) { s.ox = dx; s.oy = dy; }
                }
            }
        }
    }
    HeapFree(GetProcessHeap(), 0, buf);
    if (saved && apply && gWnd) {
        SendMessageW(gWnd, WM_SETREDRAW, FALSE, 0); PlaceAll(); SendMessageW(gWnd, WM_SETREDRAW, TRUE, 0);
        RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_FRAME | RDW_ALLCHILDREN | RDW_UPDATENOW);
    }
    return saved;
}
static void LayoutSaveNow()                     // to the settings and the profile in use
{
    LayoutSave(gIni);
    if (gProfCur >= 0 && gProfCur < gProfCount) { wchar_t path[MAX_PATH]; ProfilePath(gProfNames[gProfCur], path); LayoutSave(path); }
}

// ---- what can be moved ----
static bool EdIsSubTab(HWND h)
{
    int id = GetDlgCtrlID(h);
    return (id >= IDC_FXSUB0 && id < IDC_FXSUB0 + FX_SUBS) || id == IDC_MICSUB0 || id == IDC_MICSUB1 ||
           (id >= IDC_SETSUB0 && id <= IDC_SETSUB3);
}
static bool SectionShown(const Section& s)
{
    if (gCompact || (s.page >= 0 && s.page != gPage)) return false;
    return s.sub < 0 || s.sub == (s.page == PAGE_MIC ? gMicSub : s.page == PAGE_SETTINGS ? gSetSub : gFxSub);
}
static RECT SectionRect(const Section& s)
{
    int y = SC(s.y + s.oy + (s.shifts ? RowsDelta() : 0)), x = SC(s.x + s.ox) + ((gSecChan >= 0 && &s == &gSections[gSecChan]) || (gSecOut >= 0 && &s == &gSections[gSecOut]) || (gSecKeys >= 0 && &s == &gSections[gSecKeys]) ? 0 : gOrgX);
    RECT r = { x, y - SC(8), x + SC(s.w), y + SC(s.h) };
    return r;
}
static bool EdItemRect(int item, RECT* r)
{
    if (gEdMode == ED_PICS) {
        if (item == STK_MAX) {                  // the background picture, when you place it yourself
            if (!gBase.gp || gPicFit != 4) return false;
            int tw, th, dx, dy; BaseTarget(gCW, gCH, &tw, &th, &dx, &dy);
            SetRect(r, dx, dy, dx + tw, dy + th); return true;
        }
        if (item < 0 || item >= gStkN) return false;
        StkRect(gStk[item], r); return true;
    }
    if (item >= 0) {
        if (item >= gDesignN) return false;
        const Design& d = gDesign[item];
        if (d.page < 0 || !IsWindowVisible(d.h) || EdIsSubTab(d.h)) return false;
        GetWindowRect(d.h, r); MapWindowPoints(nullptr, gWnd, (POINT*)r, 2);
        if (d.ud) { RECT u; GetWindowRect(d.ud, &u); MapWindowPoints(nullptr, gWnd, (POINT*)&u, 2); UnionRect(r, r, &u); }
        if (d.combo) r->bottom = r->top + SC(24);
        return true;
    }
    int k = -2 - item;
    if (k < 0 || k >= gSectionN || !SectionShown(gSections[k])) return false;
    *r = SectionRect(gSections[k]);
    return true;
}
static int EdHit(POINT p)                       // client px -> item under it (smallest wins)
{
    int best = -1; long long bestA = -1;
    if (gEdMode == ED_PICS) {
        for (int i = gStkN - 1; i >= 0; i--) { RECT r; if (EdItemRect(i, &r) && PtInRect(&r, p)) return i; }
        RECT r; if (EdItemRect(STK_MAX, &r) && PtInRect(&r, p)) return STK_MAX;
        return -1;
    }
    for (int i = 0; i < gDesignN; i++) {
        RECT r; if (!EdItemRect(i, &r) || !PtInRect(&r, p)) continue;
        long long a = (long long)(r.right - r.left) * (r.bottom - r.top);
        if (bestA < 0 || a < bestA) { best = i; bestA = a; }
    }
    if (best >= 0) return best;
    for (int k = 0; k < gSectionN; k++) {
        RECT r; if (!EdItemRect(-2 - k, &r) || !PtInRect(&r, p)) continue;
        long long a = (long long)(r.right - r.left) * (r.bottom - r.top);
        if (bestA < 0 || a < bestA) { best = -2 - k; bestA = a; }
    }
    return best;
}
static void EdGetOffset(int item, int* x, int* y)
{
    if (gEdMode == ED_PICS) {
        if (item == STK_MAX) { *x = gPicX; *y = gPicY; return; }
        *x = gStk[item].x; *y = gStk[item].y; return;
    }
    if (item >= 0) { *x = gDesign[item].ox; *y = gDesign[item].oy; return; }
    *x = gSections[-2 - item].ox; *y = gSections[-2 - item].oy;
}
// Move everything to its new place without drawing half-way, then repaint the whole window at once
// (moving controls piecemeal left copies of them behind, especially while a GIF makes the window double-buffered).
static void EdReplace()
{
    SendMessageW(gWnd, WM_SETREDRAW, FALSE, 0);
    PlaceAll();
    SendMessageW(gWnd, WM_SETREDRAW, TRUE, 0);
    RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_FRAME | RDW_ALLCHILDREN | RDW_UPDATENOW);
}
static void EdSetOffset(int item, int x, int y)
{
    if (gEdMode == ED_PICS) {
        RECT before; EdItemRect(item, &before);
        if (item == STK_MAX) { gPicX = x; gPicY = y; PicComposeBase(); RECT all = { 0, 0, gCW, gCH }; PicComposeTop(all); PicMakeBrush(); PicRedraw(nullptr); return; }
        gStk[item].x = x; gStk[item].y = y;
        StkRefresh(&before);
        return;
    }
    if (item >= 0) {                            // moves every control that shares its spot (e.g. Song-style swaps) too
        Design& d = gDesign[item];
        for (int i = 0; i < gDesignN; i++) {
            Design& o = gDesign[i];
            if (o.page == d.page && o.sub == d.sub && o.rx == d.rx && o.ry == d.ry) { o.ox = x; o.oy = y; }
        }
    } else {
        gSections[-2 - item].ox = x; gSections[-2 - item].oy = y;
    }
    EdReplace();
}

// ---- the see-through layer ----
static void EdPut(DWORD* px, int W, int H, int x, int y, DWORD c) { if (x >= 0 && y >= 0 && x < W && y < H) px[(size_t)y * W + x] = c; }
static DWORD EdPm(COLORREF c, int a)            // premultiplied ARGB
{
    return ((DWORD)a << 24) | ((GetRValue(c) * a / 255) << 16) | ((GetGValue(c) * a / 255) << 8) | (GetBValue(c) * a / 255);
}
static void EdFrame(DWORD* px, int W, int H, RECT r, DWORD c, int t, bool dashed)
{
    for (int k = 0; k < t; k++) {
        for (int x = r.left; x < r.right; x++) if (!dashed || ((x / 4) & 1)) { EdPut(px, W, H, x, r.top + k, c); EdPut(px, W, H, x, r.bottom - 1 - k, c); }
        for (int y = r.top; y < r.bottom; y++) if (!dashed || ((y / 4) & 1)) { EdPut(px, W, H, r.left + k, y, c); EdPut(px, W, H, r.right - 1 - k, y, c); }
    }
}
static void EdFill(DWORD* px, int W, int H, RECT r, DWORD c)
{
    for (int y = Imax(0, (int)r.top); y < Imin(H, (int)r.bottom); y++)
        for (int x = Imax(0, (int)r.left); x < Imin(W, (int)r.right); x++) px[(size_t)y * W + x] = c;
}
static void EdRender()
{
    if (!gEdWnd) return;
    RECT rc; GetClientRect(gWnd, &rc);
    const int W = rc.right, H = rc.bottom;
    if (W <= 0 || H <= 0) return;
    BITMAPINFO bi = {}; bi.bmiHeader.biSize = sizeof(bi.bmiHeader); bi.bmiHeader.biWidth = W; bi.bmiHeader.biHeight = -H;
    bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32;
    void* bits = nullptr;
    HDC sdc = GetDC(nullptr);
    HDC mem = CreateCompatibleDC(sdc);
    HBITMAP bmp = CreateDIBSection(sdc, &bi, DIB_RGB_COLORS, &bits, nullptr, 0);
    if (!bmp) { DeleteDC(mem); ReleaseDC(nullptr, sdc); return; }
    HGDIOBJ ob = SelectObject(mem, bmp);
    DWORD* px = (DWORD*)bits;
    for (int i = 0; i < W * H; i++) px[i] = 0x01000000;   // almost invisible, but it catches the mouse
    // the tabs and sub-tabs stay clickable (fully see-through lets clicks fall through to them)
    RECT tabs = { 0, 0, W, SC(44) }; EdFill(px, W, H, tabs, 0);
    for (int i = 0; i < gDesignN; i++)
        if (EdIsSubTab(gDesign[i].h) && IsWindowVisible(gDesign[i].h)) {
            RECT r; GetWindowRect(gDesign[i].h, &r); MapWindowPoints(nullptr, gWnd, (POINT*)&r, 2); EdFill(px, W, H, r, 0);
        }
    const DWORD line = EdPm(ACCENT, 200), faint = EdPm(ACCENT, 110), hot = EdPm(ACCENT, 255), tint = EdPm(ACCENT, 40);
    if (gEdMode == ED_LAYOUT) {
        for (int k = 0; k < gSectionN; k++) { RECT r; if (EdItemRect(-2 - k, &r)) EdFrame(px, W, H, r, faint, 1, true); }
        for (int i = 0; i < gDesignN; i++) { RECT r; if (EdItemRect(i, &r)) EdFrame(px, W, H, r, line, 1, false); }
    } else {
        for (int i = 0; i < gStkN; i++) { RECT r; if (EdItemRect(i, &r)) EdFrame(px, W, H, r, line, 2, false); }
        RECT r; if (EdItemRect(STK_MAX, &r)) EdFrame(px, W, H, r, faint, 2, true);
    }
    int sel = gEdDrag != -1 ? gEdDrag : gEdHot;
    if (sel != -1) { RECT r; if (EdItemRect(sel, &r)) { EdFill(px, W, H, r, tint); EdFrame(px, W, H, r, hot, 2, false); } }
    // the bar at the bottom: what to do, and Done
    RECT bar = { 0, H - SC(34), W, H };
    COLORREF barC = gDark ? RGB(24, 24, 24) : RGB(250, 250, 250);
    HBRUSH bb = CreateSolidBrush(barC); FillRect(mem, &bar, bb); DeleteObject(bb);
    gEdDone = { W - SC(96), H - SC(30), W - SC(10), H - SC(4) };
    HBRUSH ab = CreateSolidBrush(ACCENT); FillRect(mem, &gEdDone, ab); DeleteObject(ab);
    SetBkMode(mem, TRANSPARENT);
    HGDIOBJ of = SelectObject(mem, gFontBold);
    SetTextColor(mem, RGB(255, 255, 255));
    DrawTextW(mem, L"Done", -1, &gEdDone, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(mem, gFont);
    SetTextColor(mem, gDark ? RGB(235, 235, 235) : RGB(30, 30, 30));
    RECT tr = { SC(10), bar.top, gEdDone.left - SC(8), bar.bottom };
    DrawTextW(mem, gEdMode == ED_LAYOUT ? L"Drag anything to move it (a box: drag its title or an empty part). Right-click puts it back. Esc = done."
                                        : L"Drag a picture to move it, scroll to resize, Delete removes it. Esc = done.",
              -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_END_ELLIPSIS);
    SelectObject(mem, of);
    GdiFlush();
    for (int y = bar.top; y < H; y++) for (int x = 0; x < W; x++) px[(size_t)y * W + x] |= 0xFF000000;   // GDI leaves alpha 0
    POINT org = { 0, 0 }; ClientToScreen(gWnd, &org);
    POINT zero = { 0, 0 }; SIZE sz = { W, H };
    BLENDFUNCTION bf = { AC_SRC_OVER, 0, 255, AC_SRC_ALPHA };
    UpdateLayeredWindow(gEdWnd, sdc, &org, &sz, mem, &zero, 0, &bf, ULW_ALPHA);
    SelectObject(mem, ob); DeleteObject(bmp); DeleteDC(mem); ReleaseDC(nullptr, sdc);
}
static void EdEnd();
static LRESULT CALLBACK EdProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    auto client = [&](LPARAM lp) { POINT p = { (short)LOWORD(lp), (short)HIWORD(lp) }; return p; };   // overlay px = window client px
    switch (m) {
    case WM_MOUSEMOVE: {
        POINT p = client(l);
        if (gEdDrag != -1) {
            POINT s; GetCursorPos(&s);
            int dx = UNSC(s.x - gEdFrom.x), dy = UNSC(s.y - gEdFrom.y);
            if (GetKeyState(VK_SHIFT) < 0) { dx = dx / 10 * 10; dy = dy / 10 * 10; }   // Shift: snap to 10
            EdSetOffset(gEdDrag, gEdOx + dx, gEdOy + dy);
            EdRender();
        } else {
            int hit = EdHit(p);
            if (hit != gEdHot) { gEdHot = hit; EdRender(); }
        }
        return 0;
    }
    case WM_SETCURSOR:
        SetCursor(LoadCursor(nullptr, gEdHot != -1 || gEdDrag != -1 ? IDC_SIZEALL : IDC_ARROW));
        return TRUE;
    case WM_LBUTTONDOWN: {
        POINT p = client(l);
        if (PtInRect(&gEdDone, p)) { EdEnd(); return 0; }
        gEdDrag = EdHit(p);
        if (gEdDrag != -1) {
            GetCursorPos(&gEdFrom); EdGetOffset(gEdDrag, &gEdOx, &gEdOy); SetCapture(h);
            if (gEdMode == ED_PICS && gEdDrag < gStkN) gStkSel = gEdDrag;
        }
        return 0;
    }
    case WM_LBUTTONUP:
        if (gEdDrag != -1) { gEdDrag = -1; ReleaseCapture(); EdRender(); }
        return 0;
    case WM_RBUTTONUP: {
        int hit = EdHit(client(l));
        if (gEdMode == ED_LAYOUT && hit != -1) { EdSetOffset(hit, 0, 0); EdRender(); }
        return 0;
    }
    case WM_MOUSEWHEEL:
        if (gEdMode == ED_PICS) {
            POINT p = { (short)LOWORD(l), (short)HIWORD(l) }; ScreenToClient(gWnd, &p);
            int hit = EdHit(p);
            if (hit == -1) return 0;
            int step = GET_WHEEL_DELTA_WPARAM(w) > 0 ? 1 : -1;
            int& size = hit == STK_MAX ? gPicSize : gStk[hit].size;
            RECT before; EdItemRect(hit, &before);
            size = Iclamp(size + step * Imax(1, size / 10), 5, 400);
            if (hit != STK_MAX) gStk[hit].stale = true;   // drawn stretched now, sharp again when you stop scrolling
            if (hit == STK_MAX) { PictureRebuild(); PicRedraw(nullptr); } else StkRefresh(&before);
            SetTimer(gWnd, TIMER_STKSIZE, 300, nullptr);
            if (hit < gStkN) gStkSel = hit;
            EdRender();
        }
        return 0;
    case WM_KEYDOWN:
        if (w == VK_ESCAPE || w == VK_RETURN) { EdEnd(); return 0; }
        if (w == VK_DELETE && gEdMode == ED_PICS && gEdHot >= 0 && gEdHot < gStkN) {
            RECT before; EdItemRect(gEdHot, &before);
            StkRemove(gEdHot); gEdHot = -1;
            PictureRebuild(); PicRedraw(&before); EdRender();
            return 0;
        }
        if ((w == VK_LEFT || w == VK_RIGHT || w == VK_UP || w == VK_DOWN) && gEdHot != -1) {   // nudge
            int x, y; EdGetOffset(gEdHot, &x, &y);
            int st = GetKeyState(VK_SHIFT) < 0 ? 10 : 1;
            x += w == VK_LEFT ? -st : w == VK_RIGHT ? st : 0; y += w == VK_UP ? -st : w == VK_DOWN ? st : 0;
            EdSetOffset(gEdHot, x, y); EdRender();
            return 0;
        }
        break;
    }
    return DefWindowProcW(h, m, w, l);
}
static void PicUiRefresh();
static void EdBegin(int mode)
{
    if (gEdWnd) EdEnd();
    static bool reg = false;
    if (!reg) {
        WNDCLASSW wc = {}; wc.lpfnWndProc = EdProc; wc.hInstance = gInst; wc.lpszClassName = L"LagEditLayer";
        wc.hCursor = LoadCursor(nullptr, IDC_ARROW); RegisterClassW(&wc); reg = true;
    }
    gEdMode = mode; gEdHot = gEdDrag = -1;
    gEdWnd = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOOLWINDOW, L"LagEditLayer", L"", WS_POPUP, 0, 0, 10, 10, gWnd, nullptr, gInst, nullptr);
    if (!gEdWnd) { gEdMode = ED_NONE; return; }
    EdRender();
    ShowWindow(gEdWnd, SW_SHOW);                // active, so Esc / Delete / arrow keys reach it
    SetActiveWindow(gEdWnd); SetFocus(gEdWnd);
}
static void EdEnd()
{
    if (!gEdWnd) return;
    HWND w = gEdWnd; gEdWnd = nullptr;
    if (GetCapture() == w) ReleaseCapture();
    DestroyWindow(w);
    if (gEdMode == ED_LAYOUT) LayoutSaveNow();
    else { StkSaveAll(); SaveInt(L"background_x", gPicX); SaveInt(L"background_y", gPicY); SaveInt(L"background_size", gPicSize); PicUiRefresh(); }
    gEdMode = ED_NONE;
}
static void EdFollow() { if (gEdWnd) EdRender(); }   // the window moved / changed page: redraw the layer over it

// ---- installing a voice (Windows' "Text-to-speech" feature for a language), then refreshing the list ----
struct VoiceInstall { HANDLE proc; int accent; };
static void VoiceProgressTick()                 // (every second while installing) progress bar + button text
{
    if (!gVoiceInstalling) return;
    HANDLE f = CreateFileW(gVoiceLog, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, nullptr, OPEN_EXISTING, 0, nullptr);
    if (f != INVALID_HANDLE_VALUE) {
        static char buf[65536];
        DWORD size = GetFileSize(f, nullptr), got = 0;
        if (size != INVALID_FILE_SIZE) {
            if (size > sizeof(buf) - 1) SetFilePointer(f, -(LONG)(sizeof(buf) - 1), nullptr, FILE_END);
            ReadFile(f, buf, sizeof(buf) - 1, &got, nullptr);
            buf[got] = 0;
            for (int i = (int)got - 1; i > 0; i--)       // the last "NN.N%" DISM wrote
                if (buf[i] == '%' && isdigit((unsigned char)buf[i - 1])) {
                    int j = i - 1; while (j > 0 && (isdigit((unsigned char)buf[j - 1]) || buf[j - 1] == '.')) j--;
                    gVoicePct = Iclamp(atoi(buf + j), 0, 100);
                    break;
                }
        }
        CloseHandle(f);
    }
    wchar_t t[32];
    if (gVoicePct >= 0) wsprintfW(t, L"Installing %d%%", gVoicePct);
    else { DWORD sec = (GetTickCount() - gVoiceStart) / 1000; wsprintfW(t, L"Installing %u:%02u", sec / 60, sec % 60); }
    if (!gTtsBusy) { SetDlgItemTextW(gWnd, IDC_TTSSPEAK, t); FitOne(GetDlgItem(gWnd, IDC_TTSSPEAK)); }
    InvalidateRect(GetDlgItem(gWnd, IDC_VOICEPROG), nullptr, FALSE);
}
static void DrawVoiceProgress(DRAWITEMSTRUCT* d)   // thin bar: track + accent fill (sliding while the % isn't known yet)
{
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    RECT tr = rc; tr.top += 1; tr.bottom -= 1;
    HBRUSH tb = CreateSolidBrush(gDark ? DK_TRACK : LT_TRACK); FillRect(dc, &tr, tb); DeleteObject(tb);
    RECT fr = tr; const int W = tr.right - tr.left;
    if (gVoicePct >= 0) fr.right = tr.left + W * gVoicePct / 100;
    else { int seg = W / 5, pos = (int)((GetTickCount() - gVoiceStart) / 1000 % 5); fr.left = tr.left + pos * seg; fr.right = fr.left + seg; }
    HBRUSH ab = CreateSolidBrush(ACCENT); FillRect(dc, &fr, ab); DeleteObject(ab);
}
static DWORD WINAPI VoiceInstallWait(LPVOID arg)
{
    VoiceInstall* vi = (VoiceInstall*)arg;
    WaitForSingleObject(vi->proc, 30 * 60 * 1000);
    DWORD code = 1; GetExitCodeProcess(vi->proc, &code);
    CloseHandle(vi->proc);
    PostMessageW(gWnd, WM_VOICE_INSTALLED, (WPARAM)code, (LPARAM)vi->accent);
    HeapFree(GetProcessHeap(), 0, vi);
    return 0;
}
static void TtsInstallVoice(int accent)
{
    if (accent <= 0 || accent >= TTS_ACCENT_N || gVoiceInstalling) return;
    // Windows' DISM tool installs it and writes its progress ("45.0%") to a log we read every second
    wchar_t tmp[MAX_PATH]; GetTempPathW(MAX_PATH, tmp);
    wsprintfW(gVoiceLog, L"%sLagEffect-voice.log", tmp);
    DeleteFileW(gVoiceLog);
    wchar_t args[1200];
    wsprintfW(args, L"/c dism.exe /Online /Add-Capability /CapabilityName:Language.TextToSpeech~~~%s~0.0.1.0 /NoRestart > \"%s\" 2>&1",
              TTS_ACCENTS[accent].tag, gVoiceLog);
    SHELLEXECUTEINFOW se = {}; se.cbSize = sizeof(se);
    se.fMask = SEE_MASK_NOCLOSEPROCESS | SEE_MASK_NOASYNC; se.hwnd = gWnd;
    se.lpVerb = L"runas"; se.lpFile = L"cmd.exe"; se.lpParameters = args; se.nShow = SW_HIDE;
    if (!ShellExecuteExW(&se) || !se.hProcess) return;   // (you said no to Windows' permission prompt)
    VoiceInstall* vi = (VoiceInstall*)HeapAlloc(GetProcessHeap(), 0, sizeof(VoiceInstall));
    if (!vi) { CloseHandle(se.hProcess); return; }
    vi->proc = se.hProcess; vi->accent = accent;
    HANDLE t = CreateThread(nullptr, 0, VoiceInstallWait, vi, 0, nullptr);
    if (!t) { CloseHandle(se.hProcess); HeapFree(GetProcessHeap(), 0, vi); return; }
    CloseHandle(t);
    gVoiceInstalling = true; gVoicePct = -1; gVoiceStart = GetTickCount();
    VoiceProgressTick();
    ShowWindow(GetDlgItem(gWnd, IDC_VOICEPROG), gPage == PAGE_SOUND ? SW_SHOWNA : SW_HIDE);
}
static void TtsFillVoices()                     // the voice dropdown, after the list changed
{
    HWND tv = GetDlgItem(gWnd, IDC_TTSVOICE);
    SendMessageW(tv, CB_RESETCONTENT, 0, 0);
    SendMessageW(tv, CB_ADDSTRING, 0, (LPARAM)L"Default voice");
    int sel = 0;
    bool natural = false;
    HDC dc = GetDC(tv); HGDIOBJ of = SelectObject(dc, (HFONT)SendMessageW(tv, WM_GETFONT, 0, 0));
    int widest = 0;
    for (int i = 0; i < gTtsCount; i++) {
        wchar_t shown[160]; TtsShortName(gTtsNames[i], shown, 160);   // "Microsoft Saleh Online (Natural) - ..." -> "Saleh (Natural) - ..."
        SIZE sz; GetTextExtentPoint32W(dc, shown, lstrlenW(shown), &sz); if (sz.cx > widest) widest = sz.cx;
        SendMessageW(tv, CB_ADDSTRING, 0, (LPARAM)shown);
        if (!lstrcmpiW(gTtsNames[i], gTtsVoice)) sel = i + 1;
        if (TtsIsNatural(gTtsNames[i])) natural = true;
    }
    SendMessageW(tv, CB_ADDSTRING, 0, (LPARAM)(natural ? L"More natural voices..." : L"Get natural (realistic) voices..."));
    SelectObject(dc, of); ReleaseDC(tv, dc);
    RECT wa; SystemParametersInfoW(SPI_GETWORKAREA, 0, &wa, 0);
    SendMessageW(tv, CB_SETDROPPEDWIDTH, Imin(widest + GetSystemMetrics(SM_CXVSCROLL) + SC(16), (int)(wa.right - wa.left) / 2), 0);
    SendMessageW(tv, CB_SETCURSEL, sel, 0);
}
static void AppRestart()
{
    SaveSettings(); gNoSaveOnExit = true;
    wchar_t exe[MAX_PATH]; GetModuleFileNameW(nullptr, exe, MAX_PATH);
    ShellExecuteW(nullptr, L"open", exe, gWantRunning ? L"--updated --resume" : L"--updated", nullptr, SW_SHOWNORMAL);
    PostMessageW(gWnd, WM_CLOSE, 0, 0);
}
static void OnVoiceInstalled(DWORD code, int accent)
{
    gVoiceInstalling = false;
    ShowWindow(GetDlgItem(gWnd, IDC_VOICEPROG), SW_HIDE);
    DeleteFileW(gVoiceLog);
    if (code == 3010) code = 0;                 // DISM: installed, Windows restart "suggested"
    SetDlgItemTextW(gWnd, IDC_TTSSPEAK, gTtsBusy ? L"Speaking..." : L"Speak"); FitOne(GetDlgItem(gWnd, IDC_TTSSPEAK));
    TtsListVoices();
    TtsFillVoices();
    const TtsAccent& a = TTS_ACCENTS[Iclamp(accent, 0, TTS_ACCENT_N - 1)];
    int v = TtsVoiceFor(accent);
    wchar_t m[600];
    if (v >= 0) {
        if (gTtsAccent == accent) { SendDlgItemMessageW(gWnd, IDC_TTSVOICE, CB_SETCURSEL, v + 1, 0); lstrcpynW(gTtsVoice, gTtsNames[v], 128); }
        wsprintfW(m, L"The %s voice is installed: the %s accent is ready.", a.voiceName, a.name);
        MessageBoxW(gWnd, m, L"Lag Effect - Text to speech", MB_ICONINFORMATION);
    } else if (code == 0) {
        wsprintfW(m, L"Windows installed the %s voice. Lag Effect needs a restart to start using it.\n\nRestart Lag Effect now?", a.voiceName);
        if (MessageBoxW(gWnd, m, L"Lag Effect - Text to speech", MB_YESNO | MB_ICONQUESTION) == IDYES) AppRestart();
    } else {
        wsprintfW(m, L"Windows couldn't install the %s voice (no internet, or Windows Update is blocked on this PC).\n\n"
                     L"You can add it yourself: Settings > Time & language > Speech > Manage voices > Add voices.\n\nOpen the speech settings?", a.voiceName);
        if (MessageBoxW(gWnd, m, L"Lag Effect - Text to speech", MB_YESNO | MB_ICONWARNING) == IDYES)
            ShellExecuteW(nullptr, L"open", L"ms-settings:speech", nullptr, nullptr, SW_SHOWNORMAL);
    }
}

// ======================= tooltips =======================
// Hover help for every setting. Labels get SS_NOTIFY so they can be hovered too
// (clicking one still takes focus out of text boxes, see OnCommand). gTip is declared with the theme code.

static void Tip(HWND c, const wchar_t* text)
{
    if (!gTip || !c || !text) return;
    TTTOOLINFOW ti = {};
    ti.cbSize   = sizeof(ti);
    ti.uFlags   = TTF_IDISHWND | TTF_SUBCLASS;
    ti.hwnd     = gWnd;
    ti.uId      = (UINT_PTR)c;
    ti.lpszText = (LPWSTR)text;
    SendMessageW(gTip, TTM_ADDTOOLW, 0, (LPARAM)&ti);
}

static void TipId(int id, const wchar_t* text)    // a control, plus its spin arrows if it's a number box
{
    Tip(GetDlgItem(gWnd, id), text);
    HWND ud = GetDlgItem(gWnd, SPIN_UD(id));
    wchar_t cls[32] = L"";
    if (ud) GetClassNameW(ud, cls, 32);
    if (!lstrcmpiW(cls, UPDOWN_CLASSW)) Tip(ud, text);
}

struct TipText { const wchar_t* key; const wchar_t* text; };

static const TipText gKnobTips[] = {
    { L"fx_pitch_semitones", L"How much higher or lower your voice sounds, in semitones. +12 = one octave up, -12 = one octave down." },
    { L"fx_pitch_cents",     L"Fine-tunes the pitch in cents (100 cents = 1 semitone)." },
    { L"fx_pitch_grain_ms",  L"Size of the slices used to shift pitch. Longer sounds smoother; shorter adds less delay." },
    { L"fx_pitch_mix",       L"How much of the pitched voice you hear. 100% = only the pitched voice; lower blends in your normal voice." },
    { L"fx_reverb_mix",      L"How much room echo is added. 0% = none, 100% = only the echo." },
    { L"fx_reverb_size",     L"How big the room sounds. Higher = a longer echo tail." },
    { L"fx_reverb_damping",  L"Softens the echo's high end. Higher = a darker, warmer tail." },
    { L"fx_reverb_predelay", L"Gap before the echo starts. 10-30 ms keeps your words clear." },
    { L"voc_retune_ms",      L"How fast your voice snaps to the right note. 0 ms = instant, the hard robotic auto-tune sound; "
                             L"20-60 ms = natural pitch correction; higher = gentle." },
    { L"voc_synth",          L"Tune + harmony: how loud the harmony voices are. Robot and Choir: how much of your voice is replaced by the synth. "
                             L"Song: how much of your voice is replaced by the music." },
    { L"voc_mix",            L"How much of the vocoder you hear. 100% = only the effect; lower blends your original voice back in." },
    { L"fx_formant_shift",   L"Throat size without changing pitch. Below 0 = bigger and deeper; above 0 = smaller and younger. "
                             L"Adds ~21 ms of delay while on." },
    { L"fx_formant_mix",     L"How much of the changed voice you hear. 100% = only the changed voice." },
    { L"fx_echo_ms",         L"Time between repeats. 80-120 ms = slapback; 300-500 ms = a clear echo." },
    { L"fx_echo_feedback",   L"How many repeats. Off = just one; higher = more, fading slowly." },
    { L"fx_echo_mix",        L"How loud the echoes are compared with your voice." },
    { L"fx_ghost_length",    L"Length of each backwards swell. Longer = slower, eerier." },
    { L"fx_ghost_mix",       L"How loud the ghostly swells are." },
    { L"fx_ghost_delay",     L"Delays your voice so the swells come before your words, like a real reverse reverb. "
                             L"People hear you this much later." },
    { L"fx_dist_drive",      L"How hard your voice is pushed into distortion. Lower = a little grit; higher = heavily broken up." },
    { L"fx_dist_crush",      L"Bitcrusher: fewer bits and a lower sample rate, for a crunchy 8-bit sound. Off = none." },
    { L"fx_dist_mix",        L"How much of the distorted voice you hear. Lower blends your clean voice back in." },
    { L"fx_chorus_speed",    L"How fast the sound sweeps. Low = slow shimmer; high = fast warble." },
    { L"fx_chorus_depth",    L"How far it sweeps. Higher = a stronger effect." },
    { L"fx_chorus_mix",      L"How much of the effect you hear. 50% = the classic sound." },
    { L"fx_wobble_speed",    L"How fast the wobble is, in wobbles per second." },
    { L"fx_wobble_tremolo",  L"Volume wobble: a shaky, nervous or old-amp sound." },
    { L"fx_wobble_vibrato",  L"Pitch wobble: a warbly, old-timey or singing-vibrato sound." },
    { L"fx_muffle_amount",   L"How muffled you sound. Higher = less treble, further away." },
    { L"fx_muffle_warble",   L"A slow, uneven wobble, like sound moving through water." },
    { L"fx_muffle_bubbles",  L"Little bubble blips. Best with the Underwater style." },
    { L"fx_glitch_amount",   L"How often the connection glitches. 100% = about three times a second." },
    { L"fx_glitch_drop",     L"How often a glitch is a dropout: you cut out, or go choppy like packet loss." },
    { L"fx_glitch_stutter",  L"How often a glitch repeats a bit of what you said, \"st-st-stutter\" style." },
    { L"fx_glitch_robot",    L"How often a glitch freezes into a buzzy robot sound, like a call breaking up." },
    { L"fx_ring_hz",         L"The tone your voice is multiplied by. 30-60 Hz = Dalek robot; 100-300 Hz = metallic; higher = bell-like." },
    { L"fx_ring_mix",        L"How much of the ring-mod sound you hear." },
    { L"fx_wah_sens",        L"How easily the wah opens. Higher = opens even when you talk quietly." },
    { L"fx_wah_range",       L"How far it sweeps, from a dark \"ooh\" to a bright \"aah\"." },
    { L"fx_wah_res",         L"How peaky and vocal the sweep sounds." },
    { L"fx_wah_mix",         L"How much of the wah you hear." },
    { L"fx_whisper_amount",  L"How much of you is replaced by whisper. 100% = only the whisper." },
    { L"fx_whisper_air",     L"Brighter, breathier whisper." },
    { L"fx_growl_sub",       L"A rumble an octave below your voice." },
    { L"fx_growl_rasp",      L"Vocal fry: a crackly, creaky texture." },
    { L"fx_growl_grit",      L"Gravel and distortion." },
    { L"fx_harm_level",      L"How loud the extra voices are." },
    { L"fx_harm_detune",     L"Slightly detunes the voices for a wider, more natural sound." },
    { L"fx_harm_dry",        L"How loud your own voice is underneath." },
    { L"fx_shimmer_mix",     L"How much shimmer reverb you hear." },
    { L"fx_shimmer_decay",   L"How long the tail lasts." },
    { L"fx_shimmer_amount",  L"How much the tail rises an octave (angelic). Off = a plain reverb." },
    { L"fx_gender",          L"Below 0 = deeper and more masculine; above 0 = higher and more feminine. Adds ~21 ms of delay." },
    { L"fx_gender_mix",      L"How much of the changed voice you hear." },
    { L"de_ess",             L"Tames sharp \"s\" and \"sh\" sounds. Off = none." },
    { L"eq_bass",            L"Bass (100 Hz and below): fullness and boom." },
    { L"eq_low_mid",         L"Low mids (400 Hz): warmth, or muddiness if too much." },
    { L"eq_mid",             L"Mids (1.2 kHz): body and nasal tone." },
    { L"eq_presence",        L"Presence (3.5 kHz): clarity and how close you sound." },
    { L"eq_treble",          L"Treble (8 kHz and up): air and sparkle." },
    { L"radio_drive",        L"How hard the device distorts. 50% = how the preset is designed; higher = more broken-up and crunchy." },
    { L"radio_static",       L"Background noise while you talk: radio hiss, crackle, hum. 50% = the preset's normal amount." },
    { L"radio_squelch",      L"Volume of the sounds when you start and stop talking: the walkie-talkie \"kssht\", "
                             L"the space beeps, the drive-thru click." },
    { L"ns_strength",        L"How much background noise is removed. 100% = full cleanup; lower blends some of the original back in for a more natural sound." },
    { L"gate_threshold_db",  L"How loud you must be for the gate to open. Set it just above the meter's level when you're quiet. Used when the gate opens on Volume." },
    { L"gate_voice_pct",     L"How sure the AI must be that you're speaking before the gate opens. Higher = stricter. Used when the gate opens on Voice." },
    { L"gate_hold_ms",       L"How long the gate stays open after you stop talking, so the ends of words aren't cut off." },
    { L"gate_release_ms",    L"How quickly the sound fades out when the gate closes. Longer = smoother." },
    { L"gate_range_db",      L"How much quieter it gets while the gate is closed. 80 dB = silent; 10-20 dB just turns noise down, which sounds more natural." },
    { L"mic_boost_db",       L"Turns your microphone up or down before everything else." },
    { L"low_cut_hz",         L"Removes deep rumble below this pitch: desk bumps, AC hum, wind. 80 Hz suits most voices. All the way down = Off." },
    { L"leveler",            L"Evens out your volume: loud parts get quieter, quiet parts louder. All the way down = Off." },
};

// Labels (static text) matched by their text.
static const TipText gLabelTips[] = {
    { L"Microphone:",  L"The microphone Lag Effect listens to." },
    { L"Output",       L"Where each output plays: VB-Cable (for Discord, OBS and games), your headphones or speakers." },
    { L"Plays",        L"What each output plays: Off, Effect only (just the stutter) or Everything (your voice plus the stutter)." },
    { L"Volume %",     L"Volume of each output. 100% = unchanged." },
    { L"Loop length:", L"How much of your last words gets repeated when you press the hotkey, in milliseconds." },
    { L"Speed:",       L"How fast the loop plays through. 100% = normal; lower = slower and longer." },
    { L"Pitch:",       L"How high or low the loop sounds. 100% = normal; 200% = one octave up, 50% = one octave down." },
    { L"Smoothing:",   L"Fades the loop's edges to stop clicks where it repeats. 0 = sharp and choppy." },
    { L"Voice level:", L"How loud your live voice is while the loop plays (with \"Keep talking\" ticked)." },
    { L"Style",        L"Tune: auto-tune only. Tune + harmony: your tuned voice plus synth harmonies (the Voloco sound). "
                       L"Robot: a synth that talks with your voice. Choir: a full synth chord that sings with you." },
    { L"Preset",       L"Which device you sound like: walkie-talkie, phone call, megaphone, old radio, space radio, "
                       L"drive-thru, 8-bit or the next room." },
    { L"Key / scale",  L"The key of the song you're singing to. Your voice snaps to notes of this scale, and harmonies are built from it." },
    { L"Opens on:",    L"What opens the gate. Volume: when you're louder than Threshold. Voice: when the AI hears speech. Volume + voice: both." },
    { L"Buffer:",      L"Audio chunk size. Smaller = less delay; pick a bigger one if you hear crackling." },
    { L"Theme:",       L"Light, dark, or follow Windows." },
    { L"Master volume:", L"Volume of the whole soundboard." },
    { L"Mute hotkey:", L"A hotkey that mutes / unmutes your mic from anywhere, even in a game. Right-click it to clear." },
    { L"Color:",       L"The app's color: knobs, switches, tabs and a matching tint on the background. Classic is the original look." },
    { L"Updates:",     L"The GitHub repo Lag Effect checks for new versions." },
};

static BOOL CALLBACK TipLabel(HWND h, LPARAM)
{
    wchar_t cls[16], text[64];
    GetClassNameW(h, cls, 16);
    if (lstrcmpiW(cls, L"Static")) return TRUE;
    GetWindowTextW(h, text, 64);
    for (const TipText& t : gLabelTips) {
        if (lstrcmpW(text, t.key)) continue;
        SetWindowLongW(h, GWL_STYLE, GetWindowLongW(h, GWL_STYLE) | SS_NOTIFY);   // hoverable
        Tip(h, t.text);
    }
    return TRUE;
}

static void AddTips()
{
    gTip = CreateWindowExW(WS_EX_TOPMOST, TOOLTIPS_CLASSW, nullptr, WS_POPUP | TTS_ALWAYSTIP | TTS_NOPREFIX,
                           CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT, gWnd, nullptr, gInst, nullptr);
    if (!gTip) return;
    SendMessageW(gTip, TTM_SETMAXTIPWIDTH, 0, 320);
    SendMessageW(gTip, TTM_SETDELAYTIME, TTDT_INITIAL, 450);
    SendMessageW(gTip, TTM_SETDELAYTIME, TTDT_AUTOPOP, 20000);

    // Tabs
    TipId(IDC_TAB0 + PAGE_MAIN,     L"Outputs, the stutter effect and its hotkey. (Ctrl+Tab switches tabs.)");
    TipId(IDC_TAB0 + PAGE_MIC,      L"Clean up your microphone: AI noise suppression, noise gate and voice quality.");
    TipId(IDC_TAB0 + PAGE_FX,       L"Pitch, reverb, the vocoder (auto-tune and harmonies) and radio/phone/megaphone effects on your live voice.");
    TipId(IDC_TAB0 + PAGE_SOUND,    L"Soundboard: 8 pads of short sounds on hotkeys, played to Discord and your outputs.");
    TipId(IDC_TAB0 + PAGE_CLIPS,    L"Instant replay: save the last few seconds as a clip, trim it, and play it back on a hotkey.");
    TipId(IDC_TAB0 + PAGE_SETTINGS, L"Latency, theme, updates and where settings are saved.");
    for (int k = 0; k < MAX_OUT; k++) {
        TipId(IDC_OVOL0 + k,  L"This output's volume: the same as its volume on the Main tab. Drag, or scroll (Shift = finer). Double-click = 0 dB. Right-click to type an exact value.");
        TipId(IDC_OMUTE0 + k, L"Mute: silence this output (everything going to it).");
        TipId(IDC_OMETER0 + k, L"How loud this output is right now.");
        TipId(IDC_OLIM0 + k,  L"Lights up when this output is so loud the limiter has to turn peaks down. Often lit? Lower some volumes.");
        TipId(IDC_ODEV0 + k,  L"The device this output plays on (change it on the Main tab).");
        TipId(IDC_OLBL0 + k,  L"Click to rename this output (e.g. \"Stream\" or \"Headphones\"). The name shows on the Main tab too.");
    }
    for (int c = 0; c < CH_MAX; c++) {
        TipId(IDC_CHSRC0 + c,  L"Click: pick what this channel plays (an app, an input like a second mic, or what an output device plays), rename it or change its colour. Drag the strip's right edge to make it wider.");
        TipId(IDC_CHADD0 + c,  L"Add a channel: an app (Spotify, a game, a browser...), another input, or what an output device plays.");
        TipId(IDC_CHMUTE0 + c, L"Mute: silence this channel.");
        TipId(IDC_CHSOLO0 + c, L"Solo: hear only this channel on your listening output (the \"Always hear sounds on\" one on the Main tab, else output 1). The other outputs carry on as normal.");
        TipId(IDC_CHDUCK0 + c, L"Duck: this channel gets quieter while you talk, then comes back up.");
        TipId(IDC_CHVOL0 + c,  L"This channel's volume. Drag, or scroll (Shift = finer). Double-click = 0 dB. Right-click to type an exact value.");
        TipId(IDC_CHMETER0 + c, L"How loud this channel is right now (left and right).");
        for (int k = 0; k < MAX_OUT; k++) TipId(IDC_CHRT0 + c * MAX_OUT + k, L"Send this channel to that output (lit = on).");
    }
    TipId(IDC_DUCKDB,      L"How much quieter Duck channels get while you talk.");
    TipId(IDC_CHADDBTN,    L"Add a channel: an app (Spotify, a game, a browser...), another input, or what an output device plays. Up to 8.");
    TipId(IDC_MIXKEYSBTN,  L"Hotkeys for the Mixer: each channel's volume, mute, solo, duck and a hold key; each output's volume and mute.");
    TipId(IDC_MIXSTEP,     L"How much one press of a volume key changes it (hold the key to keep going).");
    for (int sl = SLOT_MIX0; sl < KEY_SLOTS; sl++) TipId(FxKeyButtonId(sl), L"Click, then press the key(s) you want. Right-click to clear it.");
    for (int c = 0; c < CH_MAX; c++)
        TipId(IDC_MIXHOLDMODE0 + c, L"What its Hold key does. Mute: it goes quiet while you hold the key. Talk: it only plays while you hold the key (push-to-talk, e.g. for a second mic).");
    TipId(IDC_RESTARTAUD,  L"Close and reopen every sound device. Handy after plugging something in. (Outputs that drop out also come back by themselves.)");
    TipId(IDC_TAB0 + PAGE_MIXER,    L"Mixer: bring in apps (Spotify, a game, a browser) and other inputs, set their volume and send each to the outputs you want.");
    TipId(IDC_CLIPNOW,    L"Save the last few seconds as a new clip (fills the next empty slot below).");
    TipId(IDC_CLIPNOWKEY, L"A hotkey for Clip it, so you can clip from inside a game. Right-click to clear it.");
    TipId(IDC_RECSECS,    L"How many seconds each clip saves (3 to 60).");
    TipId(IDC_RECSRC,     L"What's kept for clips: your voice as Discord hears it, the sound playing on your PC (friends, game, music), "
                          L"just Discord (your friends' voices, no game or music), or a mix. It's only held in memory until you clip.");
    TipId(IDC_CLIPMASTER, L"Volume of all the clips when they're played.");
    TipId(IDC_CLIPFOLDER, L"Open the folder where clips are saved as WAV files.");
    TipId(IDC_CLIPSTOP,   L"Stop every clip that's playing.");
    for (int i = 0; i < PADS; i++) TipId(IDC_PADMORE + i, L"Options for this pad: play mode (one-shot, loop, hold, toggle), "
                                                     L"speed, pitch, fades, name, colour, record from your mic.");
    for (int i = 0; i < CLIP_BANKS; i++) TipId(IDC_CLIPBANK0 + i, L"Clip pages: 8 clips each (32 in all). Clip hotkeys play the clip in "
                                                                 L"that spot on the page showing. New clips fill this page first.");
    TipId(IDC_CLIPHIST,  L"Every clip you've saved, newest first: pick one to put it back on the board. Also opens the Clips folder.");
    TipId(IDC_CLIPSEP,   L"With a mix (your voice + PC or Discord), also save each part as its own WAV, for editing later.");
    TipId(IDC_CLIPREPLACE, L"When every slot is taken, a new clip replaces the oldest one that isn't pinned (its file is kept; see History).");
    TipId(IDC_PADCHOKE,  L"Starting a pad stops any other pad that's playing, so sounds don't pile up.");
    TipId(IDC_PADDUCK,   L"Your voice gets quieter (-10 dB) while a pad is playing, so the sound comes through.");
    TipId(IDC_PADFOLDER, L"Pick a folder of MP3 / WAV / FLAC files: they fill your empty pads, starting on this page.");
    for (int i = 0; i < CLIPS; i++) {
        TipId(IDC_CLIPMORE + i, L"Copy (paste straight into Discord), save as MP3, show in folder, rename, pin, trim.");
        TipId(IDC_CLIPPLAY + i, L"Click to play this clip on your outputs (Discord hears it). Right-click to stop.");
        TipId(IDC_CLIPVOL + i,  L"This clip's volume. 100% = as recorded, up to 200%.");
        TipId(IDC_CLIPKEY + i,  L"A hotkey that plays this clip from anywhere. Right-click to clear it.");
        TipId(IDC_CLIPTRIM + i, L"Listen back (only you hear it), trim the start and end, rename or export. Undo any time.");
        TipId(IDC_CLIPCLR + i,  L"Remove this clip. Its file goes to the Recycle Bin, in case you want it back.");
    }
    for (int i = 0; i < PADS; i++) {
        TipId(IDC_PADPLAY + i, L"Click to play (click again to restart). Right-click to stop. Empty? Click to pick a sound, or drop a file here.");
        TipId(IDC_PADVOL + i,  L"This pad's volume. 100% = as recorded, up to 200%.");
        TipId(IDC_PADKEY + i,  L"A hotkey that plays this pad from anywhere, even in a game. Right-click to clear it.");
        TipId(IDC_PADLOAD + i, L"Pick an MP3, WAV or FLAC file for this pad (up to 60 seconds are used).");
        TipId(IDC_PADCLR + i,  L"Remove this pad's sound.");
    }
    TipId(IDC_PADMASTER, L"Volume of the whole soundboard (and text to speech).");
    TipId(IDC_SETSUB0, L"Profiles, latency, updates, screen share, shortcuts and the window.");
    TipId(IDC_SETSUB1, L"Look: theme, colours, size, font, text size, opacity, and moving things around.");
    TipId(IDC_SETSUB2, L"A background picture or GIF, and pictures / GIFs on top that you place yourself.");
    TipId(IDC_SETSUB3, L"Turn on only what you use: the lag effect, Voice FX, the soundboard and clips. And remote control (Streamer.bot).");
    TipId(IDC_WSON,    L"Off: nothing can connect (no port is open). On: apps on this PC, like Streamer.bot, can send Lag Effect commands. Never websites.");
    TipId(IDC_WSPORT,  L"The port it listens on (ws://127.0.0.1:port). Change it only if another app already uses this one.");
    TipId(IDC_WSPASS,  L"Optional. If set, an app has to send {\"do\":\"auth\",\"password\":\"...\"} before anything else.");
    TipId(IDC_WSGUIDE, L"Step by step: setting up Streamer.bot, and every command you can send.");
    TipId(IDC_WSHELP,  L"Copies C# code to paste into a Streamer.bot action (Execute C# Code).");
    TipId(IDC_FONT,    L"The font for the whole window.");
    TipId(IDC_OPACITY, L"See-through window: 100% = solid. Lower lets what's behind show through.");
    TipId(IDC_COLRESET, L"Go back to the theme's colours.");
    for (int i = 0; i < USERCOL_N; i++) TipId(IDC_COLSW0 + i, L"Click to pick this colour; right-click to use the theme's again. Bold = your own colour.");
    TipId(IDC_PICCHOOSE, L"Use a picture as the window's background (PNG, JPG, BMP or GIF).");
    TipId(IDC_PICREMOVE, L"Remove the background picture.");
    TipId(IDC_PICFIT,  L"Fill: covers the window and crops the edges. Stretch: squashes to fit. Centre: actual size. Tile: repeats. "
                       L"Place it yourself: drag it anywhere and scroll to resize.");
    TipId(IDC_PICDIM,  L"How much of the theme colour is laid over the picture: higher = easier to read. 0% = the raw picture.");
    TipId(IDC_PTTMODE,   L"Push-to-talk: your mic is silent unless you hold the key. Push-to-mute: holding the key mutes you.");
    TipId(IDC_PTTKEY,    L"The push-to-talk / push-to-mute key. Right-click to clear it.");
    TipId(IDC_OVERLAY,   L"A small always-on-top badge: live / muted / lagging, your effects and profile. Drag it anywhere; "
                         L"right-click it to hide. (Shows over windowed and borderless games.)");
    TipId(IDC_BEEPS,     L"A short, quiet beep only you hear when a hotkey switches something on (high) or off (low).");
    TipId(IDC_UISCALE,   L"Make the whole window bigger, for high-resolution screens. Needs a restart.");
    TipId(IDC_EXPORT,    L"Save every setting, profile and character into one file, to back up or share with a friend.");
    TipId(IDC_IMPORT,    L"Load settings, profiles and characters from an exported file (replaces yours, then restarts).");
    TipId(IDC_COMPACT,   L"A slim window with just the status, Start, Mute and Voice FX. Ctrl+M switches back.");
    TipId(IDC_COMPACTFX, L"Turn voice effects on or off.");
    TipId(IDC_COMPACTFULL, L"Back to the full window (Ctrl+M).");
    TipId(IDC_PROFAUTO,  L"Switch to this profile automatically while a program is running (e.g. a game), and back when it closes.");
    TipId(IDC_HIDESHARE, L"When you share your whole screen with sound, Discord records every app's audio, including what "
                         L"Lag Effect sends to VB-Cable, so people hear you twice. This locks Lag Effect's VB-Cable / VoiceMeeter "
                         L"outputs so screen shares can't record them. Discord still hears you through CABLE Output.");
    for (int k = 0; k < MAX_OUT; k++) TipId(IDC_ROWMODE + k, L"What this output plays. Effect only: just the stutter. Everything: your voice with "
                                                              L"every effect. Clean voice: your voice without Voice FX or the stutter, e.g. for "
                                                              L"OBS while Discord gets the effects. Apps only: just the Mixer channels you send to it, untouched (no mic, no effects). "
                                                              L"The soundboard plays on all but Off and Apps only.");
    TipId(IDC_LAGPRESET, L"Ready-made settings for the stutter: Bad Wi-Fi, Frozen call, Robot glitch, Buffering, Slow-mo...");
    TipId(IDC_BEATSYNC,  L"Beat repeat: the stutter's loop length follows a tempo instead of Loop length, so it sounds musical.");
    TipId(IDC_BPM,       L"Tempo in beats per minute.");
    TipId(IDC_BEATDIV,   L"How long each repeat is: a quarter note, an eighth, a sixteenth or a thirty-second.");
    TipId(IDC_TAPEKEY,   L"A hotkey that makes your voice slow down to nothing, like a record being stopped. Right-click to clear it.");
    TipId(IDC_DIVEKEY,   L"Hold this hotkey and your voice bends down (or up) smoothly; let go and it springs back. Right-click to clear it.");
    TipId(IDC_DIVESEMIS, L"How far Pitch dive bends: -12 = an octave down, +12 = an octave up.");
    TipId(IDC_SURPRISE,  L"Turns on 2-4 random effects with random (but sensible) settings. Keep clicking until you like one.");
    TipId(IDC_ABTEST,    L"Hold this to hear (and send) your voice without effects for a moment, to compare.");
    TipId(IDC_PROFILE,   L"Profiles save how you sound: the stutter effect, every Voice FX effect and knob, and the Mic tab. "
                         L"Pick one to switch to it. To make one, type a name and click Save (or press Enter). "
                         L"Devices, hotkeys, soundboard and clips aren't part of profiles.");
    TipId(IDC_PROFSAVE,  L"Save how you sound right now under the name in the box (replaces it if it already exists).");
    TipId(IDC_PROFDEL,   L"Delete the selected profile.");
    TipId(IDC_PROFKEY,   L"A hotkey that switches to this profile from anywhere. Right-click to clear it.");
    TipId(IDC_PROFNEXTKEY, L"A hotkey that cycles through your profiles in order. Right-click to clear it.");
    TipId(IDC_FXHOLD,    L"Hold to use: the Voice effects hotkey turns effects on only while you hold it. "
                         L"Set up a Character, then hold the key to talk as it.");
    for (int g = 0; g < FX_GROUPS; g++) TipId(IDC_FXGRP_HOLD + g, L"Hold: this effect's hotkey turns it on only while you hold it, "
                                                                  L"then puts everything back when you let go.");
    TipId(IDC_MICTEST,   L"Record 5 seconds of what Discord hears (your mic with every effect), then play it back to you.");
    TipId(IDC_MICPLAY,   L"Play the last mic test again.");
    for (int b = 0; b < PAD_BANKS; b++) TipId(IDC_PADBANK0 + b, L"Soundboard pages: 8 pads each. The dot means the page has sounds. "
                                                                L"Pad hotkeys play the pad in that spot on whichever page is showing.");
    TipId(IDC_PADBANKKEY, L"A hotkey that flips to the next soundboard page (A > B > C > D > A). Right-click to clear it.");
    TipId(IDC_PADFX,      L"Pads and text to speech go through your voice effects first, as if you said them: "
                          L"a robot or demon soundboard. Off: they play clean.");
    TipId(IDC_TTSTEXT,    L"Type a line and press Enter (or Speak): Windows says it into Discord and your outputs.");
    TipId(IDC_TTSVOICE,   L"Which Windows voice speaks. More voices: Windows Settings > Time & language > Speech > Add voices.");
    TipId(IDC_TTSACCENT,  L"Read your words with an accent: a Windows voice from that country (installed for you if it's missing), "
                          L"its own pace, and some of its own words, mixed up every time. American and Canadian are stereotypical.");
    TipId(IDC_TTSMORE,    L"Voice settings: speed, pitch, room sound, pauses, natural sound, and a quick test.");
    TipId(IDC_TTSVOL,     L"Text-to-speech volume, % (100 = normal, up to 200). Also changes a line that's already speaking.");
    TipId(IDC_FONTSIZE,   L"How big the text is, in pixels (at 100% size).");
    TipId(IDC_LAYEDIT,    L"Drag any control or box to where you want it. Saved for the profile you're using.");
    TipId(IDC_LAYRESET,   L"Put every control and box back where it started.");
    TipId(IDC_STKLIST,    L"The pictures / GIFs on top. Pick one to change its size or opacity.");
    TipId(IDC_STKADD,     L"Add pictures or GIFs (pick several at once). Then drag them where you want them.");
    TipId(IDC_STKDEL,     L"Remove the picked picture.");
    TipId(IDC_STKSIZE,    L"Size of the picked picture (100% = its own size).");
    TipId(IDC_STKOPAC,    L"How see-through the picked picture is (100% = solid).");
    TipId(IDC_PICPLACE,   L"With Fit set to \"Place it yourself\": drag the background where you want it and scroll to resize it.");
    TipId(IDC_STKMOVE,    L"Drag pictures to move them, scroll over one to resize it, Delete removes it.");
    TipId(IDC_GIFFPS,     L"The most frames per second GIFs play at. Lower uses less CPU and memory.");
    TipId(IDC_GIFPAUSE,   L"Stop GIFs while you're in another window (saves CPU while gaming).");
    TipId(IDC_TTSSPEAK,   L"Say the text. It plays like a pad, at the soundboard volume.");
    TipId(IDC_CLIPAUTOTRIM, L"New clips start just before the first sound and end just after the last, so there's no dead air. "
                            L"The whole recording is kept: Reset in Trim brings it back.");
    TipId(IDC_CLIPFX,     L"Clips go through your voice effects when played, e.g. a robot-ified clip. Off: they play as recorded.");
    TipId(IDC_RANDLAG,    L"The stutter fires by itself now and then, with random loop lengths, so it sounds like really bad internet "
                          L"without you touching the key.");
    TipId(IDC_RANDSEC,    L"How often random lag happens, on average (in seconds).");
    TipId(IDC_REWINDKEY,  L"A hotkey that plays your last few seconds backwards, speeding up like a tape rewinding (set it up in the Rewind box). Right-click to clear it.");
    TipId(IDC_RWLEN,      L"How far back the rewind goes (300-3500 ms of what you just said).");
    TipId(IDC_RWTOP,      L"How fast it ends up spinning: 100% = normal speed backwards, 350% = the classic tape rewind.");
    TipId(IDC_RWRAMP,     L"How much of the rewind is spent speeding up. 0% = full speed straight away.");
    TipId(IDC_RWPITCH,    L"Make the rewind higher or lower, in semitones (on top of the speed-up).");
    TipId(IDC_REPEATKEY,  L"A hotkey that repeats the last word you said 3 times, DJ style: \"word-word-word\". Right-click to clear it.");
    TipId(IDC_PADSTOP,   L"Stop every pad and clip that's playing.");

    // Main
    TipId(IDC_MIC, L"The microphone Lag Effect listens to.");
    for (int k = 0; k < MAX_OUT; k++) {
        TipId(IDC_ROWLBL + k,  L"An output: a device Lag Effect plays to.");
        TipId(IDC_ROWDEV + k,  L"Where this output plays: VB-Cable (for Discord, OBS and games), your headphones or speakers.");
        TipId(IDC_ROWMODE + k, L"Off = nothing. Effect only = just the stutter. Everything = your voice plus the stutter (what others should hear). "
                               L"Apps only = just the Mixer channels you send to it, untouched (no mic, no effects).");
        TipId(IDC_ROWVOL + k,  L"Volume of this output. 100% = unchanged, up to 200%.");
        TipId(IDC_ROWDEL + k,  L"Remove this output.");
    }
    TipId(IDC_ADDOUT,  L"Add another output (up to 5), e.g. VB-Cable for Discord plus your headphones to hear yourself.");
    TipId(IDC_HEARON,   L"Pick your headphones' output to always hear the soundboard, clips and text to speech there, even if it's set to "
                        L"Off or Effect only, or the sounds go through your voice effects.");
    TipId(IDC_HEARLBL,  L"Pick your headphones' output to always hear the soundboard, clips and text to speech there, even if it's set to "
                        L"Off or Effect only, or the sounds go through your voice effects.");
    TipId(IDC_VBCABLE, L"Set up VB-Cable automatically: output 1 goes to VB-Cable, output 2 to your headphones.");
    TipId(IDC_LOOP,    L"How much of your last words gets repeated when you press the hotkey, in milliseconds.");
    TipId(IDC_SPEED,   L"How fast the loop plays through. 100% = normal; lower = slower and longer.");
    TipId(IDC_PITCH,   L"How high or low the loop sounds. 100% = normal; 200% = one octave up, 50% = one octave down.");
    TipId(IDC_FADE,    L"Fades the loop's edges to stop clicks where it repeats. 0 = sharp and choppy.");
    TipId(IDC_GATEON,  L"Mutes your mic between words so background noise doesn't get through. Fine-tune it on the Mic tab.");
    TipId(IDC_TALKON,  L"Keep your live voice going while the loop plays, so you can talk over the stutter.");
    TipId(IDC_TALKVOL, L"How loud your live voice is while the loop plays.");
    TipId(IDC_HOTKEY,  L"Click, then hold the key(s) you want (up to 3, e.g. Ctrl + F). Works in any app or game. Esc cancels.");
    TipId(IDC_HOLD,    L"The stutter plays while you hold the hotkey.");
    TipId(IDC_TOGGLE,  L"Press the hotkey once to start the stutter, again to stop it.");
    TipId(IDC_STATUS,  L"What Lag Effect is doing right now.");
    TipId(IDC_START,   L"Start or stop audio processing.");
    TipId(IDC_MUTEBTN, L"Mute or unmute your microphone instantly (outputs go silent, the effects keep their settings). "
                       L"You can set a Mute hotkey on the Settings tab.");
    TipId(IDC_TRAY,    L"Hide the window. Lag Effect keeps running in the system tray; click the tray icon to bring it back. "
                       L"Right-click the tray icon for quick on/off switches.");
    TipId(IDC_HELPBTN, L"How everything works, plus setup steps for Discord and OBS.");
    TipId(IDC_MUTEKEY, L"A hotkey that mutes / unmutes your mic from anywhere, even in a game. Right-click to clear it.");
    TipId(IDC_OSD,     L"Shows a short pop-up at the top of the screen (e.g. \"Pitch ON\", \"Mic muted\") when a hotkey "
                       L"switches something, so you know it worked. Doesn't show over exclusive-fullscreen games.");
    TipId(IDC_TOPMOST, L"Keep the Lag Effect window above other windows.");
    TipId(IDC_STARTWIN, L"Open Lag Effect when you sign in to Windows. Uses this copy's location, so tick it again if you move the app. "
                        L"Combine with \"Start audio && hide in tray when opened\" to have it ready in the background.");

    // Mic
    TipId(IDC_METER,    L"Mic level: your level after noise suppression. Green = the gate lets you through; the blue line is the gate threshold.\n"
                        L"Voice: how sure the AI is that you're talking (shown when noise suppression or the Voice gate is on); "
                        L"the blue line is the Voice setting.");
    TipId(IDC_NSON,     L"Turn AI noise suppression (RNNoise) on or off. It removes fans, keyboards, hum and room noise. Adds about 20 ms of delay.");
    TipId(IDC_RADIOPRESET, L"Which device you sound like. The knobs adjust the chosen preset; knobs it doesn't use are dimmed.");
    TipId(IDC_VOCSTYLE, L"Tune: auto-tune only. Tune + harmony: your tuned voice plus synth harmonies (the Voloco sound). "
                        L"Robot: a synth that talks with your voice. Choir: a full synth chord that sings with you.");
    TipId(IDC_VOCKEY,   L"The key of the song (its home note). Not sure? Try C with Major, or A with Minor.");
    TipId(IDC_SONGBTN,  L"Vocode to song: the music playing on your PC says your words. Talk or sing and you hear the song "
                        L"shaped by your voice; stay quiet and it's silent. Turns on Voice effects and the Vocoder's Song style. "
                        L"Click again to go back to the style you had.");
    TipId(IDC_SONGSRC,  L"Where the music comes from: one app (Spotify, a browser...), all PC sound except Lag Effect "
                        L"(so it never hears itself), or an audio file on your PC (MP3, WAV, FLAC; it loops). "
                        L"Recording one app needs Windows 11. Open the list to refresh it.");
    TipId(IDC_SONGSTATUS, L"Whether the song is reaching the vocoder.");
    TipId(IDC_VOCRANGE, L"How high your voice is. Auto works it out as you sing. "
                        L"Low / deep: for bass and baritone voices; hears notes down to 50 Hz, uses longer, smoother slices "
                        L"for tuning, and puts harmonies above you instead of below (adds ~15 ms delay). High: tenor, alto, soprano.");
    TipId(IDC_VOCSCALE, L"Which notes are allowed. Major = happy, Minor = darker, Pentatonic = safe for most songs, "
                        L"Chromatic = every note (just smooths your pitch).");
    TipId(IDC_GATEMODE, L"What opens the gate. Volume: when you're louder than Threshold. Voice: when the AI hears speech "
                        L"(ignores loud non-voice noise). Volume + voice: both.");

    // Voice FX
    TipId(IDC_FXON,         L"Turn all voice effects on or off. Order: Pitch > Gender > Formant > Harmonizer > Vocoder > Whisper > Growl > "
                            L"Ring mod > Distortion > Wah > Chorus > Wobble > Muffle > Echo > Ghost > Shimmer > Reverb > Radio > Glitch.\n"
                            L"Knobs: drag up/down or scroll (Shift = fine), double-click to reset. Hotkeys work from anywhere; "
                            L"right-click one (or press Backspace while setting it) to clear it.");
    TipId(IDC_FXKEY_MASTER, L"Set a hotkey that turns all voice effects on/off from anywhere. Right-click to clear it.");
    TipId(IDC_FXSUB0, L"Voice: Pitch, Formant (throat size) and Gender (one-knob voice change).");
    TipId(IDC_FXSUB1, L"Tune: the Vocoder (auto-tune, harmonies, robot, song), Harmonizer (extra voices) and Whisper.");
    TipId(IDC_FXSUB2, L"Monster: Growl (sub-octave rumble and rasp), Ring mod (sci-fi robot) and Distortion.");
    TipId(IDC_FXSUB3, L"Space: Reverb (a room), Shimmer (a rising, angelic reverb) and Echo.");
    TipId(IDC_FXSUB4, L"Motion: Ghost (backwards swells), Chorus / flanger and Wobble (tremolo, vibrato).");
    TipId(IDC_FXSUB5, L"Filter: Wah (opens as you get louder), Muffle (underwater, through a wall) and Radio / phone / megaphone.");
    TipId(IDC_FXSUB6, L"Fun: Glitch (a bad connection).");
    TipId(IDC_MICSUB0, L"Cleanup: AI noise suppression and the noise gate.");
    TipId(IDC_MICSUB1, L"Tone: mic level, low cut, leveler, de-esser, broadcast voice and a 5-band equalizer.");
    TipId(IDC_HARMMUTE,  L"Silences the extra voices but keeps the Harmonizer on and your own voice at full level. Click again to bring them back.");
    TipId(IDC_HARMSTYLE, L"Which extra voices sing along: an octave up or down, a chord, a fifth, a power chord or an angel choir.");
    TipId(IDC_BROADCAST, L"Radio-host sound: strong, even compression, a little presence and less mud, and the esses tamed. "
                         L"Every output also has a limiter, so loud moments never clip.");
    TipId(IDC_EQRESET,   L"Put the equalizer back to flat (all 0 dB).");
    TipId(IDC_FXCHAR, L"One-click voices built from the effects: Demon, Giant, Child, Alien, Ghost and more. Picking one turns off "
                      L"your other effects and sets the knobs; tweak them afterwards if you like.");
    TipId(IDC_ECHOSTYLE, L"Echo: clean repeats. Slapback: one quick repeat, the classic radio-DJ / rockabilly sound. "
                         L"Tape echo: dark, wobbly repeats. Canyon: long and far away.");
    TipId(IDC_DISTSTYLE, L"Overdrive: warm and rounded. Fuzz: harsh and buzzy. Bitcrush: 8-bit game voice. "
                         L"Broken mic: thin, clipped, and it cuts out now and then.");
    TipId(IDC_CHOSTYLE,  L"Chorus: thick and shimmery, like several of you. Flanger: a sweeping swoosh. "
                         L"Jet flanger: a stronger, slower sweep. Doubler: sounds like two takes at once.");
    TipId(IDC_MUFSTYLE,  L"Underwater: muffled, wobbly, with bubbles. Through a wall: heavy and boomy, like the next room. "
                         L"Under a blanket: softly muffled.");
    for (int g = 0; g < FX_GROUPS; g++) {
        static wchar_t on[FX_GROUPS][96], key[FX_GROUPS][128], rst[FX_GROUPS][96];
        wsprintfW(on[g],  L"Turn %s on or off.", gFxGroups[g].title);
        wsprintfW(key[g], L"Set a hotkey that turns %s on/off from anywhere (also turns Voice effects on). Right-click to clear it.", gFxGroups[g].title);
        wsprintfW(rst[g], L"Put all %s knobs back to their defaults.", gFxGroups[g].title);
        TipId(IDC_FXGRP_ON + g, on[g]);
        TipId(IDC_FXGRP_KEY + g, key[g]);
        TipId(IDC_FXGRP_RESET + g, rst[g]);
    }

    // Settings
    TipId(IDC_BUFFER,   L"Audio chunk size. Smaller = less delay; pick a bigger one if you hear crackling.");
    TipId(IDC_HIDESHARE, L"When you share your whole screen with sound, Discord records every app's audio, including what "
                         L"Lag Effect sends to VB-Cable, so people hear you twice. This locks Lag Effect's VB-Cable / VoiceMeeter "
                         L"outputs so screen shares can't record them. Discord still hears you through CABLE Output. "
                         L"Outputs to real speakers or headphones aren't locked: set those to Off or Effect only while streaming.");
    TipId(IDC_EXCL,     L"Takes over the mic and output 1 for the lowest delay. Other apps can't use them while it's on.");
    TipId(IDC_THEME,    L"Light, dark, or follow Windows.");
    TipId(IDC_COLORTHEME, L"The app's color: knobs, switches, tabs and a matching tint on the background. "
                          L"Classic is the original look. Custom (hex) lets you type any colour (pick another theme, then Custom again to change it).");
    TipId(IDC_AUTO,     L"When Lag Effect opens, start audio straight away and hide in the tray.");
    TipId(IDC_REPO,     L"The GitHub repo Lag Effect checks for new versions.");
    TipId(IDC_CHECKUPD, L"Check GitHub for a newer version now.");
    TipId(IDC_UPDSTART, L"Check for updates each time Lag Effect starts.");
    TipId(IDC_OPENSET,  L"Open the folder with your settings file (LagEffect.ini).");

    // Knobs
    for (int i = 0; i < KNOB_N; i++)
        for (const TipText& t : gKnobTips)
            if (!lstrcmpW(t.key, gKnobs[i].key)) {
                static wchar_t buf[KNOB_N][400];
                wsprintfW(buf[i], L"%s\nDrag up/down or scroll. Shift = fine steps. Double-click = reset.", t.text);
                Tip(GetDlgItem(gWnd, IDC_KNOB + i), buf[i]);
            }

    EnumChildWindows(gWnd, TipLabel, 0);
}

static void DrawOutLabel(DRAWITEMSTRUCT* d)     // "Out 1" with a thin level bar under it
{
    int k = (int)d->CtlID - IDC_ROWLBL;
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    wchar_t t[32]; OutName(k, t, 32);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, TXT_C);
    HGDIOBJ of = SelectObject(dc, gFont);
    RECT tr = { rc.left + 2, rc.top, rc.right, rc.bottom - 5 };
    DrawTextW(dc, t, -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_LEFT | DT_END_ELLIPSIS | DT_NOPREFIX);
    SelectObject(dc, of);
    float db = k < 8 ? gOutShow[k] : -80.0f;
    float f = (db + 60.0f) / 60.0f; if (f < 0) f = 0; if (f > 1) f = 1;
    RECT track = { rc.left + 2, rc.bottom - 4, rc.right - 4, rc.bottom - 1 };
    HBRUSH tb = CreateSolidBrush(gDark ? DK_TRACK : LT_TRACK); FillRect(dc, &track, tb); DeleteObject(tb);
    RECT lvl = track; lvl.right = track.left + (int)((track.right - track.left) * f);
    HBRUSH lb = CreateSolidBrush(db > -3.0f ? RGB(220, 70, 60) : UC(9, ACCENT)); FillRect(dc, &lvl, lb); DeleteObject(lb);
}

static const wchar_t* USERCOL_NAMES[USERCOL_N] = { L"Accent", L"Background", L"Panels", L"Borders", L"Text", L"Dim text",
                                                   L"Box titles", L"Knobs", L"Knob track", L"Meters", L"Tabs", L"Status bar" };
static void DrawSwatch(DRAWITEMSTRUCT* d)       // a colour box + its name; "theme" when not set
{
    int i = (int)d->CtlID - IDC_COLSW0;
    HDC dc = d->hDC; RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    const COLORREF nows[USERCOL_N] = { ACCENT, BgColor(), gDark ? DK_CTL : LT_CARD, gDark ? DK_SECTION : LT_BORDER, TXT_C,
                                       gDark ? DK_DIM : gLtDim, TITLE_C, KNOB_C, gDark ? DK_TRACK : LT_TRACK, METER_C, TAB_C, STATUS_C };
    COLORREF now = nows[Iclamp(i, 0, USERCOL_N - 1)];
    HBRUSH b = CreateSolidBrush(now); HPEN p = CreatePen(PS_SOLID, 1, gDark ? RGB(120, 120, 120) : RGB(150, 150, 150));
    HGDIOBJ ob = SelectObject(dc, b), op = SelectObject(dc, p);
    const int bw = (rc.bottom - rc.top) - 6;     // a square-ish swatch; your own colours have their name in bold
    RoundRect(dc, rc.left + 2, rc.top + 3, rc.left + 2 + bw, rc.bottom - 3, 8, 8);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(b); DeleteObject(p);
    const wchar_t* t = USERCOL_NAMES[i];
    SetBkMode(dc, TRANSPARENT); SetTextColor(dc, TXT_C);
    HGDIOBJ of = SelectObject(dc, gUserCol[i] == CLR_NONE ? gFont : gFontBold);
    RECT tr = { rc.left + bw + 8, rc.top, rc.right, rc.bottom };
    DrawTextW(dc, t, -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_LEFT | DT_END_ELLIPSIS);
    SelectObject(dc, of);
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) { RECT fr = rc; InflateRect(&fr, -1, -1); DrawFocusRect(dc, &fr); }
}

// Voice FX sub-tab: a pill, filled when selected, with how many of its effects are on.
static const wchar_t* MIC_SUB_NAMES[2] = { L"Cleanup", L"Tone" };
static const wchar_t* SET_SUB_NAMES[4] = { L"General", L"Look", L"Pictures", L"Features" };
static void DrawFxSub(DRAWITEMSTRUCT* d)        // Voice FX, Mic and Settings sub-tabs
{
    const bool set = (int)d->CtlID >= IDC_SETSUB0 && (int)d->CtlID <= IDC_SETSUB3;
    const bool mic = !set && (int)d->CtlID >= IDC_MICSUB0 && (int)d->CtlID <= IDC_MICSUB1;
    int t = (int)d->CtlID - (set ? IDC_SETSUB0 : mic ? IDC_MICSUB0 : IDC_FXSUB0);
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    bool active = t == (set ? gSetSub : mic ? gMicSub : gFxSub);
    int on = 0;
    if (!mic && !set) for (int g = 0; g < FX_GROUPS; g++) if (gFxGroups[g].sub == t && *gFxGroups[g].on && gFxOn) on++;
    HBRUSH b = CreateSolidBrush(active ? TAB_C : gDark ? DK_CTL : LT_CARD);
    HPEN   p = CreatePen(PS_SOLID, 1, active ? TAB_C : gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ ob = SelectObject(dc, b), op = SelectObject(dc, p);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 14, 14);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(b); DeleteObject(p);
    wchar_t text[32];
    const wchar_t* nm = set ? SET_SUB_NAMES[t] : mic ? MIC_SUB_NAMES[t] : FX_SUB_NAMES[t];
    if (on) wsprintfW(text, L"%s %d", nm, on); else lstrcpynW(text, nm, 32);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, active ? RGB(255, 255, 255) : TXT_C);
    HGDIOBJ of = SelectObject(dc, active ? gFontBold : gFont);
    DrawTextW(dc, text, -1, &rc, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(dc, of);
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) { RECT fr = rc; InflateRect(&fr, -3, -3); DrawFocusRect(dc, &fr); }
}

// Master switch at the top of the Voice FX page: a card with an on/off pill.
static void DrawFxSwitch(DRAWITEMSTRUCT* d)
{
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    FillRect(dc, &rc, BgBrush());
    const bool on = gFxOn;

    HBRUSH card = CreateSolidBrush(gDark ? DK_CTL : LT_CARD);
    HPEN   cpen = CreatePen(PS_SOLID, 1, on ? ACCENT : gDark ? DK_SECTION : LT_BORDER);
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
    SetTextColor(dc, TXT_C);
    RECT tr = { px + pw + 14, rc.top + 5, rc.right - 70, rc.top + 24 };
    DrawTextW(dc, L"Voice effects", -1, &tr, DT_SINGLELINE | DT_LEFT | DT_VCENTER);
    SelectObject(dc, gFont);
    SetTextColor(dc, gDark ? DK_DIM : RGB(105, 105, 105));
    RECT sr = { px + pw + 14, rc.top + 23, rc.right - 70, rc.bottom - 4 };
    DrawTextW(dc, L"On your live voice", -1, &sr,
              DT_SINGLELINE | DT_LEFT | DT_VCENTER | DT_END_ELLIPSIS);
    SelectObject(dc, gFontBold);
    SetTextColor(dc, on ? ACCENT : gDark ? DK_DIM : RGB(120, 120, 120));
    RECT st = { rc.right - 64, rc.top, rc.right - 16, rc.bottom };
    DrawTextW(dc, on ? L"ON" : L"OFF", -1, &st, DT_SINGLELINE | DT_RIGHT | DT_VCENTER);
    SelectObject(dc, of);

    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) {
        RECT fr = rc; InflateRect(&fr, -4, -4);
        SetTextColor(dc, TXT_C);
        DrawFocusRect(dc, &fr);
    }
}

static void SetFxOn(bool on)
{
    if (on && !gFeatFx) return;                 // (Voice FX is switched off in Settings > Features)
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
// ---- Mute mic ----
static void UpdateTrayTip();
static void SetMute(bool on)
{
    gMicMuted = on;
    SetDlgItemTextW(gWnd, IDC_MUTEBTN, on ? L"Unmute mic" : L"Mute mic");
    UpdateTrayTip();
    UpdateStatus(true);
}

// ---- on-screen pop-up when a hotkey switches something (so you know it worked mid-game) ----
static HWND  gOsd;
static HFONT gFontOsd;
static wchar_t gOsdText[64];
static bool  gOsdOn;
static int   gOsdTicks;                         // counts 30 ms steps while showing

static LRESULT CALLBACK OsdProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    if (m == WM_PAINT) {
        PAINTSTRUCT ps;
        HDC dc = BeginPaint(h, &ps);
        RECT rc; GetClientRect(h, &rc);
        COLORREF fill = gOsdOn ? ACCENT : (gDark ? RGB(60, 60, 60) : RGB(90, 90, 90));
        HBRUSH b = CreateSolidBrush(fill); FillRect(dc, &rc, b); DeleteObject(b);
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, gOsdOn && gDark ? RGB(20, 20, 20) : RGB(255, 255, 255));
        HGDIOBJ of = SelectObject(dc, gFontOsd);
        DrawTextW(dc, gOsdText, -1, &rc, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
        SelectObject(dc, of);
        EndPaint(h, &ps);
        return 0;
    }
    if (m == WM_NCHITTEST) return HTTRANSPARENT;   // clicks go straight through
    return DefWindowProcW(h, m, w, l);
}

static void HotkeyBeep(bool on);
static void ShowOsd(const wchar_t* text, bool on)
{
    if (gBeeps) HotkeyBeep(on);
    if (!gShowOsd) return;
    lstrcpynW(gOsdText, text, 64);
    gOsdOn = on;
    const int W = 280, H = 52;
    if (!gOsd) {
        gOsd = CreateWindowExW(WS_EX_TOPMOST | WS_EX_LAYERED | WS_EX_TRANSPARENT | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE,
                               L"LagOsd", L"", WS_POPUP, 0, 0, W, H, nullptr, nullptr, gInst, nullptr);
        if (!gOsd) return;
        SetWindowRgn(gOsd, CreateRoundRectRgn(0, 0, W + 1, H + 1, 18, 18), FALSE);
    }
    // top-centre of the screen you're on (the one with the game / focused window)
    HMONITOR mon = MonitorFromWindow(GetForegroundWindow(), MONITOR_DEFAULTTOPRIMARY);
    MONITORINFO mi = {}; mi.cbSize = sizeof(mi);
    GetMonitorInfoW(mon, &mi);
    int x = (mi.rcWork.left + mi.rcWork.right - W) / 2, y = mi.rcWork.top + 48;
    SetLayeredWindowAttributes(gOsd, 0, 235, LWA_ALPHA);
    SetWindowPos(gOsd, HWND_TOPMOST, x, y, W, H, SWP_NOACTIVATE | SWP_SHOWWINDOW);
    InvalidateRect(gOsd, nullptr, TRUE);
    gOsdTicks = 0;
    SetTimer(gWnd, TIMER_OSD, 30, nullptr);
}

static void OsdTick()                           // shows ~1.1 s, then fades out over 0.3 s
{
    if (!gOsd) { KillTimer(gWnd, TIMER_OSD); return; }
    gOsdTicks++;
    if (gOsdTicks > 36) {
        int a = 235 - (gOsdTicks - 36) * 24;
        if (a <= 0) { ShowWindow(gOsd, SW_HIDE); KillTimer(gWnd, TIMER_OSD); return; }
        SetLayeredWindowAttributes(gOsd, 0, (BYTE)a, LWA_ALPHA);
    }
}

static void ClipNow();
static void SetPadBank(int b);
static void PadKey(int i, bool pressed, bool released);
static bool ProfileLoad(int idx, bool osd);
static void HoldPress(int slot);
static void HoldRelease(int slot);
// ---- Mixer hotkeys: volume up / down (hold to keep going), mute, solo, duck, and a hold key per channel
static bool MixRepeat(int slot, bool down, bool pressed)   // now, then (still held) after 0.4 s every 0.09 s
{
    static DWORD next[KEY_SLOTS];
    const DWORD now = GetTickCount();
    if (pressed) { next[slot] = now + 400; return true; }
    if (down && (int)(now - next[slot]) >= 0) { next[slot] = now + 90; return true; }
    return false;
}
static void MixOsd(const wchar_t* who, const wchar_t* what, bool on)
{
    wchar_t t[64]; _snwprintf(t, 63, L"%s  %s", who, what); t[63] = 0;
    ShowOsd(t, on);
}
static void MixKey(int slot, bool down, bool pressed, bool released)
{
    const DWORD shown = 0; (void)shown;
    if (slot < SLOT_MIXOUT0) {
        const int c = (slot - SLOT_MIX0) / MIXA_N, a = (slot - SLOT_MIX0) % MIXA_N;
        if (gCh[c].type == CH_NONE) { if (a == MIXA_HOLD) gCh[c].held = false; return; }
        wchar_t who[64]; ChanLabel(c, who, 40);
        if (a == MIXA_HOLD) {                   // (its quiet state is worked out every poll: see MixHoldTick)
            if ((pressed || released) && gCh[c].holdTalk) MixOsd(who, down ? L"on (held)" : L"off", down);
            else if ((pressed || released)) MixOsd(who, down ? L"muted (held)" : L"back on", !down);
            return;
        }
        if (a == MIXA_UP || a == MIXA_DOWN) {
            if (!MixRepeat(slot, down, pressed)) return;
            int v = gCh[c].db10; if (v <= -600 && a == MIXA_UP) v = -610;
            FaderSet(IDC_CHVOL0 + c, v + (a == MIXA_UP ? 10 : -10) * gMixStep);
            wchar_t d[24]; DbText(gCh[c].db10, d); MixOsd(who, d, true);
            return;
        }
        if (!pressed) return;
        bool on = false;
        if (a == MIXA_MUTE) { on = gCh[c].mute = !gCh[c].mute; MixOsd(who, on ? L"muted" : L"unmuted", !on); }
        if (a == MIXA_SOLO) { on = gCh[c].solo = !gCh[c].solo; MixOsd(who, on ? L"solo" : L"solo off", on); }
        if (a == MIXA_DUCK) { on = gCh[c].duck = !gCh[c].duck; MixOsd(who, on ? L"ducks" : L"doesn't duck", on); }
        MixerRedraw();
        return;
    }
    const int k = (slot - SLOT_MIXOUT0) / MIXO_N, a = (slot - SLOT_MIXOUT0) % MIXO_N;
    if (k >= gRows) return;
    wchar_t who[40]; OutName(k, who, 32);
    if (a == MIXO_UP || a == MIXO_DOWN) {
        if (!MixRepeat(slot, down, pressed)) return;
        int v = FaderGet(IDC_OVOL0 + k); if (v <= -600 && a == MIXO_UP) v = -610;
        FaderSet(IDC_OVOL0 + k, v + (a == MIXO_UP ? 10 : -10) * gMixStep);
        wchar_t d[24]; DbText(FaderGet(IDC_OVOL0 + k), d); MixOsd(who, d, true);
        return;
    }
    if (!pressed) return;
    gOutMute[k] = !gOutMute[k];
    MixOsd(who, gOutMute[k] ? L"muted" : L"unmuted", !gOutMute[k]);
    MixerRedraw();
}
static void MixHoldTick()                       // (every poll) each channel's hold key: quiet or not
{
    for (int c = 0; c < CH_MAX; c++) {
        const int* k = gFxKeys[SLOT_MIX0 + c * MIXA_N + MIXA_HOLD];
        const bool has = k[0] || k[1] || k[2];
        const bool down = has && gFxKeyWasDown[SLOT_MIX0 + c * MIXA_N + MIXA_HOLD];
        const bool quiet = has && gCh[c].type != CH_NONE && (gCh[c].holdTalk ? !down : down);
        if (quiet != gCh[c].held) { gCh[c].held = quiet; InvalidateRect(GetDlgItem(gWnd, IDC_CHVOL0 + c), nullptr, FALSE); }
    }
}

static void PollFxKeys()
{
    BYTE cache[256] = {};
    for (int slot = 0; slot < KEY_SLOTS; slot++) {
        const bool off = ((slot < FX_KEY_SLOTS || slot == SLOT_TAPESTOP || slot == SLOT_DIVE) && !gFeatFx) ||
                         (((slot >= SLOT_PAD0 && slot < SLOT_PAD0 + PADS) || slot == SLOT_PADBANK) && !gFeatSound) ||
                         ((slot == SLOT_CLIPNOW || (slot >= SLOT_CLIP0 && slot < SLOT_CLIP0 + CLIPS)) && !gFeatClips) ||
                         ((slot == SLOT_REWIND || slot == SLOT_REPEAT) && !gFeatLag);
        if (off) { gFxKeyWasDown[slot] = false; if (slot == SLOT_DIVE) gDiveHeld = false; continue; }   // (its feature is off)
        bool down = !gCapturingKey && KeysDownCached(gFxKeys[slot], cache);
        bool pressed = down && !gFxKeyWasDown[slot], released = !down && gFxKeyWasDown[slot];
        gFxKeyWasDown[slot] = down;
        if (slot < FX_KEY_SLOTS && gFxHold[slot]) {   // hold-to-activate effect hotkeys
            if (pressed) HoldPress(slot); else if (released) HoldRelease(slot);
            continue;
        }
        if (slot >= SLOT_MIX0) { MixKey(slot, down, pressed, released); continue; }   // the Mixer's
        if (slot == SLOT_DIVE) { gDiveHeld = down; continue; }   // hold to bend
        if (slot == SLOT_PTT)  { gPttHeld = down; continue; }    // push-to-talk / push-to-mute
        if (slot >= SLOT_PAD0 && slot < SLOT_PAD0 + PADS) {      // pads: press (and release, for Hold mode)
            if (pressed || released) PadKey(PadSlot(slot - SLOT_PAD0), pressed, released);
            continue;
        }
        if (!pressed) continue;
        if (slot >= SLOT_PROF0)    { ProfileLoad(slot - SLOT_PROF0, true); continue; }
        if (slot == SLOT_TAPESTOP) { if (gRunning) gTapeReq = true; continue; }
        if (slot == SLOT_PROFNEXT) { if (gProfCount) ProfileLoad((gProfCur + 1) % gProfCount, true); continue; }
        if (slot == SLOT_REWIND)  { if (gRunning) gRewindReq = true; continue; }
        if (slot == SLOT_REPEAT)  { if (gRunning) gRepeatReq = true; continue; }
        if (slot == SLOT_PADBANK) {
            SetPadBank((gPadBank + 1) % PAD_BANKS);
            wchar_t m[48]; wsprintfW(m, L"Soundboard page %c", L'A' + gPadBank);
            ShowOsd(m, true);
            continue;
        }
        if (slot >= SLOT_CLIP0)   { gPads[CLIP0 + ClipSlot(slot - SLOT_CLIP0)].trigger = true; continue; }   // a clip on this page
        if (slot == SLOT_CLIPNOW) { ClipNow(); continue; }                                       // save the last N s
        if (slot >= SLOT_PAD0)    { gPads[PadSlot(slot - SLOT_PAD0)].trigger = true; continue; }  // pad on this page
        wchar_t msg[64];
        bool on;
        if (slot == SLOT_MUTE) {
            on = !gMicMuted;
            SetMute(on);
            lstrcpynW(msg, on ? L"Mic muted" : L"Mic on", 64);
        } else if (slot == 0) {
            on = !gFxOn;
            SetFxOn(on);
            wsprintfW(msg, L"Voice effects %s", on ? L"ON" : L"OFF");
        } else {
            int g = slot - 1;
            on = !(*gFxGroups[g].on && gFxOn);
            SetFxGroupOn(g, on);
            if (on && !gFxOn) SetFxOn(true);
            wsprintfW(msg, L"%s %s", gFxGroups[g].title, on ? L"ON" : L"OFF");
        }
        ShowOsd(msg, slot == SLOT_MUTE ? !on : on);
        UpdateStatus(true);
    }
    MixHoldTick();
}

// ---------- Mic tab ----------
static float gMeterShowDb = -90.0f, gMeterVadShow = 0.0f;

static void UpdateMeter()                       // every 50 ms: fast rise, smooth fall
{
    for (int k = 0; k < MAX_OUT && k < 8; k++) {   // output meters on the Main tab
        float pk = gOutPeak[k]; gOutPeak[k] = 0;
        float db = pk > 0.0001f ? 20.0f * log10f(pk) : -80.0f;
        float v = db > gOutShow[k] ? db : gOutShow[k] - 2.0f;
        if (v < -80.0f) v = -80.0f;
        const bool moved = (int)v != (int)gOutShow[k];   // (only redraw when it would look different)
        gOutShow[k] = v;
        if (moved && gPage == PAGE_MAIN && !gCompact) InvalidateRect(GetDlgItem(gWnd, IDC_ROWLBL + k), nullptr, FALSE);
    }
    float peak = gMeterPeak; gMeterPeak = 0;
    float db = peak > 0.0000316f ? 20.0f * log10f(peak) : -90.0f;
    gMeterShowDb = db > gMeterShowDb ? db : (gMeterShowDb - 2.5f > db ? gMeterShowDb - 2.5f : db);
    float v = gMeterVad;
    gMeterVadShow = v < 0 ? -1.0f : (v > gMeterVadShow ? v : gMeterVadShow * 0.8f + v * 0.2f);
    static int lastDb = -999, lastVad = -999, lastGate = -1;
    const int nowDb = (int)(gMeterShowDb * 2), nowVad = (int)(gMeterVadShow * 50), nowGate = gMeterGateOpen ? 1 : 0;
    if (gPage == PAGE_MIC && (nowDb != lastDb || nowVad != lastVad || nowGate != lastGate)) {
        lastDb = nowDb; lastVad = nowVad; lastGate = nowGate;
        InvalidateRect(GetDlgItem(gWnd, IDC_METER), nullptr, FALSE);
    }
}

static void DrawMeterTo(HDC dc, RECT rc)
{
    FillRect(dc, &rc, BgBrush());
    HBRUSH card = CreateSolidBrush(gDark ? DK_CTL : LT_CARD);
    HPEN   cpen = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ ob = SelectObject(dc, card), op = SelectObject(dc, cpen);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, 12, 12);
    SelectObject(dc, ob); SelectObject(dc, op);
    DeleteObject(card); DeleteObject(cpen);

    const float lo = -72.0f;
    const int x0 = rc.left + 96, x1 = rc.right - 120, bh = 12;
    const int by = rc.top + 11;                 // level bar row; the voice bar row sits under it
    auto X = [&](float db) { float t = (db - lo) / -lo; t = t < 0 ? 0 : t > 1 ? 1 : t; return x0 + (int)((x1 - x0) * t); };

    SetBkMode(dc, TRANSPARENT);
    HGDIOBJ of = SelectObject(dc, gFontBold);
    SetTextColor(dc, TXT_C);
    RECT lr = { rc.left + 14, by - 6, x0 - 8, by + bh + 6 };
    DrawTextW(dc, L"Mic level", -1, &lr, DT_SINGLELINE | DT_LEFT | DT_VCENTER);

    RECT track = { x0, by, x1, by + bh };
    HBRUSH tb = CreateSolidBrush(gDark ? DK_TRACK : LT_TRACK);
    FillRect(dc, &track, tb); DeleteObject(tb);

    bool gateOn = gGateMode != GATE_OFF, open = !gateOn || gMeterGateOpen;
    COLORREF fillc = !gRunning ? (gDark ? RGB(90, 90, 90) : RGB(180, 180, 180))
                   : open ? METER_C : (gDark ? RGB(110, 110, 110) : RGB(165, 165, 165));
    RECT lvl = { x0, by, X(gMeterShowDb), by + bh };
    HBRUSH fb = CreateSolidBrush(fillc); FillRect(dc, &lvl, fb); DeleteObject(fb);
    if (gMeterShowDb > -6.0f) {                 // hot zone
        RECT hot = { X(-6.0f), by, X(gMeterShowDb), by + bh };
        HBRUSH hb = CreateSolidBrush(RGB(235, 150, 40)); FillRect(dc, &hot, hb); DeleteObject(hb);
    }
    if (gateOn && (gGateMode == GATE_VOLUME || gGateMode == GATE_BOTH)) {   // threshold marker
        int tx = X((float)gGateThrDb);
        RECT m = { tx - 1, by - 4, tx + 1, by + bh + 4 };
        HBRUSH mb = CreateSolidBrush(ACCENT); FillRect(dc, &m, mb); DeleteObject(mb);
    }

    SelectObject(dc, gFont);
    SetTextColor(dc, gDark ? DK_DIM : RGB(105, 105, 105));
    if (gMeterVadShow >= 0) {                   // voice detection bar (when RNNoise is running)
        int vy = by + bh + 11;
        RECT vlab = { rc.left + 14, vy - 6, x0 - 8, vy + 11 };   // label to the left, like "Mic level"
        DrawTextW(dc, L"Voice", -1, &vlab, DT_SINGLELINE | DT_LEFT | DT_VCENTER);
        RECT vt = { x0, vy, x1, vy + 5 };
        HBRUSH vb = CreateSolidBrush(gDark ? DK_TRACK : LT_TRACK); FillRect(dc, &vt, vb); DeleteObject(vb);
        RECT vf = { x0, vy, x0 + (int)((x1 - x0) * (gMeterVadShow > 1 ? 1 : gMeterVadShow)), vy + 5 };
        HBRUSH vfb = CreateSolidBrush(RGB(160, 120, 240)); FillRect(dc, &vf, vfb); DeleteObject(vfb);
        if (gGateMode == GATE_VOICE || gGateMode == GATE_BOTH) {
            int tx = x0 + (int)((x1 - x0) * (gGateVoicePct / 100.0f));
            RECT m = { tx - 1, vy - 3, tx + 1, vy + 8 };
            HBRUSH mb = CreateSolidBrush(ACCENT); FillRect(dc, &m, mb); DeleteObject(mb);
        }
    }

    wchar_t t1[32], t2[32];
    if (!gRunning) { lstrcpynW(t1, L"--", 32); lstrcpynW(t2, L"Audio stopped", 32); }
    else {
        if (gMeterShowDb <= -89.0f) lstrcpynW(t1, L"silent", 32);
        else wsprintfW(t1, L"%d dB", (int)floorf(gMeterShowDb + 0.5f));
        lstrcpynW(t2, !gateOn ? L"Gate off" : open ? L"Gate open" : L"Gate closed", 32);
    }
    SelectObject(dc, gFontBold);
    SetTextColor(dc, TXT_C);
    RECT r1 = { x1 + 10, rc.top + 8, rc.right - 14, rc.top + 26 };
    DrawTextW(dc, t1, -1, &r1, DT_SINGLELINE | DT_RIGHT | DT_VCENTER);
    SelectObject(dc, gFont);
    SetTextColor(dc, open && gateOn && gRunning ? RGB(40, 170, 80) : gDark ? DK_DIM : RGB(105, 105, 105));
    RECT r2 = { x1 + 10, rc.top + 27, rc.right - 14, rc.top + 45 };
    DrawTextW(dc, t2, -1, &r2, DT_SINGLELINE | DT_RIGHT | DT_VCENTER);
    SelectObject(dc, of);
}

static void DrawMeter(DRAWITEMSTRUCT* d)        // double-buffered, it redraws 20 times a second
{
    RECT rc = d->rcItem;
    int w = rc.right - rc.left, h = rc.bottom - rc.top;
    HDC mem = CreateCompatibleDC(d->hDC);
    HBITMAP bmp = CreateCompatibleBitmap(d->hDC, w, h);
    HGDIOBJ old = SelectObject(mem, bmp);
    RECT local = { 0, 0, w, h };
    DrawMeterTo(mem, local);
    BitBlt(d->hDC, rc.left, rc.top, w, h, mem, 0, 0, SRCCOPY);
    SelectObject(mem, old); DeleteObject(bmp); DeleteDC(mem);
}

static void SetGateMode(int m)
{
    if (m != GATE_OFF) gGateLastMode = m;
    gGateMode = m;
    CheckDlgButton(gWnd, IDC_GATEON, m != GATE_OFF ? BST_CHECKED : BST_UNCHECKED);
    SendDlgItemMessageW(gWnd, IDC_GATEMODE, CB_SETCURSEL, m, 0);
    RedrawKnobs();
}

static void SetKnobVar(volatile int* var, int v)   // set a knob by the setting it controls
{
    for (int i = 0; i < KNOB_N; i++)
        if (gKnobs[i].var == var) { SetKnobValue(GetDlgItem(gWnd, IDC_KNOB + i), i, v); return; }
}

static void ApplyStyleKnobs(int g)              // a style's suggested knob values
{
    if (g == KG_ECHO)   { const EchoStyle& s = ECHO_STYLES[Iclamp(gEchoStyle, 0, ECHO_N - 1)]; SetKnobVar(&gEchoMs, s.ms); SetKnobVar(&gEchoFb, s.fb); SetKnobVar(&gEchoMix, s.mix); }
    if (g == KG_DIST)   { const DistStyle& s = DIST_STYLES[Iclamp(gDistStyle, 0, DIST_N - 1)]; SetKnobVar(&gDistDrive, s.drive); SetKnobVar(&gDistCrush, s.crush); SetKnobVar(&gDistMix, s.mix); }
    if (g == KG_CHORUS) { const ChoStyle& s = CHO_STYLES[Iclamp(gChoStyle, 0, CHO_N - 1)]; SetKnobVar(&gChoSpeed, s.speed); SetKnobVar(&gChoDepth, s.depth); SetKnobVar(&gChoMix, s.mix); }
    if (g == KG_MUFFLE) { const MufStyle& s = MUF_STYLES[Iclamp(gMufStyle, 0, MUF_N - 1)]; SetKnobVar(&gMufAmount, s.amount); SetKnobVar(&gMufWarble, s.warble); SetKnobVar(&gMufBubbles, s.bubbles); }
}

static void SetFxStyle(int g, int style)        // style dropdown changed (or set by a character)
{
    int id = g == KG_ECHO ? IDC_ECHOSTYLE : g == KG_DIST ? IDC_DISTSTYLE : g == KG_CHORUS ? IDC_CHOSTYLE : IDC_MUFSTYLE;
    volatile int* var = g == KG_ECHO ? &gEchoStyle : g == KG_DIST ? &gDistStyle : g == KG_CHORUS ? &gChoStyle : &gMufStyle;
    *var = style;
    SendDlgItemMessageW(gWnd, id, CB_SETCURSEL, style, 0);
    ApplyStyleKnobs(g);
    RedrawKnobs();
}

static void ResetFxGroup(int g)
{
    for (int i = 0; i < KNOB_N; i++)
        if (gKnobs[i].group == g) SetKnobValue(GetDlgItem(gWnd, IDC_KNOB + i), i, gKnobs[i].def);
    ApplyStyleKnobs(g);                         // effects with a style go back to that style's values
}

static void SetFxSub(int t)                     // show another Voice FX sub-tab
{
    t = Iclamp(t, 0, FX_SUBS - 1);
    if (t == gFxSub) return;
    gFxSub = t;
    Layout();
    for (int i = 0; i < FX_SUBS; i++) InvalidateRect(GetDlgItem(gWnd, IDC_FXSUB0 + i), nullptr, FALSE);
}

static void ShowOsd(const wchar_t* text, bool on);
// One-click voices, built from the effects. Each turns off every other effect first.
static void ApplyCharacter(int c)
{
    if (c <= 0 || c >= CHAR_N) return;
    for (int g = 0; g < FX_GROUPS; g++) SetFxGroupOn(g, false);
    auto use = [](int g) { ResetFxGroup(g); SetFxGroupOn(g, true); };
    switch (c) {
    case 1:  // Demon
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -8);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -2);
        use(KG_DIST);    SetFxStyle(KG_DIST, 0); SetKnobVar(&gDistDrive, 35); SetKnobVar(&gDistMix, 45);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 25); SetKnobVar(&gFxRevSize, 75);
        break;
    case 2:  // Giant
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -6);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -2);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 22); SetKnobVar(&gFxRevSize, 85); SetKnobVar(&gFxRevDamp, 60);
        break;
    case 3:  // Deeper voice
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -4);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, 2);
        break;
    case 4:  // Higher voice
        use(KG_PITCH);   SetKnobVar(&gFxSemi, 5);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -2);
        break;
    case 5:  // Child
        use(KG_PITCH);   SetKnobVar(&gFxSemi, 7);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -2);
        break;
    case 6:  // Chipmunk
        use(KG_PITCH);   SetKnobVar(&gFxSemi, 10);
        break;
    case 7:  // Alien
        use(KG_PITCH);   SetKnobVar(&gFxSemi, 2);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -5);
        use(KG_CHORUS);  SetFxStyle(KG_CHORUS, 1); SetKnobVar(&gChoSpeed, 55); SetKnobVar(&gChoDepth, 70);
        use(KG_WOBBLE);  SetKnobVar(&gWobSpeed, 7); SetKnobVar(&gWobTrem, 0); SetKnobVar(&gWobVib, 25);
        break;
    case 8:  // Ghost
        use(KG_GHOST);   SetKnobVar(&gRvsLenMs, 500); SetKnobVar(&gRvsMix, 70);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 35); SetKnobVar(&gFxRevSize, 90); SetKnobVar(&gFxRevDamp, 40);
        use(KG_WOBBLE);  SetKnobVar(&gWobSpeed, 4); SetKnobVar(&gWobTrem, 25); SetKnobVar(&gWobVib, 10);
        break;
    case 9:  // Underwater
        use(KG_MUFFLE);  SetFxStyle(KG_MUFFLE, 0);
        break;
    case 10: // Bad connection
        use(KG_GLITCH);  SetKnobVar(&gGlAmount, 45);
        break;
    case 11: // Robot announcer
        use(KG_RING);    SetKnobVar(&gRingHz, 50); SetKnobVar(&gRingMix, 60);
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -2);
        use(KG_ECHO);    SetFxStyle(KG_ECHO, 1);
        break;
    case 12: // Old man
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -2);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -1);
        use(KG_WOBBLE);  SetKnobVar(&gWobSpeed, 5); SetKnobVar(&gWobTrem, 15); SetKnobVar(&gWobVib, 30);
        use(KG_GROWL);   SetKnobVar(&gGrowlSub, 0); SetKnobVar(&gGrowlRasp, 35); SetKnobVar(&gGrowlGrit, 0);
        break;
    case 13: // Stadium announcer
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -1);
        use(KG_ECHO);    SetFxStyle(KG_ECHO, 3); SetKnobVar(&gEchoMix, 22);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 30); SetKnobVar(&gFxRevSize, 95);
        break;
    case 14: // Cave troll
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -7);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -4);
        use(KG_GROWL);   SetKnobVar(&gGrowlSub, 60); SetKnobVar(&gGrowlRasp, 30); SetKnobVar(&gGrowlGrit, 20);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 25); SetKnobVar(&gFxRevSize, 80); SetKnobVar(&gFxRevDamp, 70);
        break;
    case 15: // Space helmet
        use(KG_RADIO);   gRadioPreset = 4; SendDlgItemMessageW(gWnd, IDC_RADIOPRESET, CB_SETCURSEL, 4, 0);
                         { SetDlgItemTextW(gWnd, IDC_RADIODESC, RADIO_DESC[4]); FitOne(GetDlgItem(gWnd, IDC_RADIODESC)); }
        use(KG_CHORUS);  SetFxStyle(KG_CHORUS, 3);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 12); SetKnobVar(&gFxRevSize, 20);
        break;
    case 16: // Dark lord
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -5);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -1);
        use(KG_GROWL);   SetKnobVar(&gGrowlSub, 30); SetKnobVar(&gGrowlRasp, 0); SetKnobVar(&gGrowlGrit, 15);
        use(KG_DIST);    SetFxStyle(KG_DIST, 0); SetKnobVar(&gDistDrive, 20); SetKnobVar(&gDistMix, 25);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 15); SetKnobVar(&gFxRevSize, 40);
        break;
    case 17: // Radio DJ
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -1);
        use(KG_FORMANT); SetKnobVar(&gFormantShift, -1);
        use(KG_ECHO);    SetFxStyle(KG_ECHO, 1); SetKnobVar(&gEchoMix, 25);
        break;
    case 18: // Angel
        use(KG_HARM);    gHarmStyle = 7; SendDlgItemMessageW(gWnd, IDC_HARMSTYLE, CB_SETCURSEL, 7, 0); SetKnobVar(&gHarmLevel, 55);
        use(KG_SHIMMER); SetKnobVar(&gShimMix, 45); SetKnobVar(&gShimAmt, 60);
        break;
    case 19: // Monster
        use(KG_PITCH);   SetKnobVar(&gFxSemi, -5);
        use(KG_GROWL);   SetKnobVar(&gGrowlSub, 70); SetKnobVar(&gGrowlRasp, 50); SetKnobVar(&gGrowlGrit, 40);
        use(KG_DIST);    SetFxStyle(KG_DIST, 1); SetKnobVar(&gDistDrive, 40); SetKnobVar(&gDistMix, 40);
        break;
    case 20: // Whisperer
        use(KG_WHISPER); SetKnobVar(&gWhisperAmt, 100); SetKnobVar(&gWhisperAir, 50);
        use(KG_REVERB);  SetKnobVar(&gFxRevMix, 25); SetKnobVar(&gFxRevSize, 70);
        break;
    }
    SetFxOn(true);
    wchar_t msg[64]; wsprintfW(msg, L"Character: %s", CHARACTERS[c]);
    ShowOsd(msg, true);
    UpdateStatus(true);
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
    else if (gMicMuted) {
        wchar_t mk[120]; ComboName(gFxKeys[SLOT_MUTE], MAX_KEYS, mk, 120);
        if (mk[0]) wsprintfW(s, L"MUTED  -  press %s to unmute", mk); else lstrcpynW(s, L"MUTED  -  your mic is off", 160);
    }
    else {
        HotkeyName(key, 120);
        if (gFeatLag) wsprintfW(s, L"Live  -  %s %s to stutter", gToggleMode ? L"press" : L"hold", key);
        else lstrcpynW(s, L"Live", 160);
    }
    if (gRunning && gFxOn && !gMicMuted) {       // which voice effects are on
        wchar_t fx[120] = L"";
        for (int g = 0; g < FX_GROUPS; g++)
            if (*gFxGroups[g].on) { if (fx[0]) lstrcatW(fx, L", "); lstrcatW(fx, gFxGroups[g].title); }
        wchar_t add[160];
        wsprintfW(add, fx[0] ? L"   (Voice FX: %s)" : L"   (Voice FX on, none ticked)", fx);
        if (lstrlenW(s) + lstrlenW(add) < 199) lstrcatW(s, add);
    }
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

static void LayoutCompact(bool on)              // slim window: status, Start, Mute, effects, back to full
{
    const int ids[] = { IDC_STATUS, IDC_START, IDC_MUTEBTN, IDC_COMPACTFX, IDC_COMPACTFULL };
    const RECT pos[] = { { 8, 8, 544, 28 }, { 8, 42, 128, 34 }, { 142, 42, 128, 34 }, { 276, 42, 128, 34 }, { 410, 42, 142, 34 } };
    for (int i = 0; i < 5; i++) {
        HWND c = GetDlgItem(gWnd, ids[i]);
        if (on) { SetWindowPos(c, nullptr, SC(pos[i].left), SC(pos[i].top), SC(pos[i].right), SC(pos[i].bottom), SWP_NOZORDER | SWP_NOACTIVATE);
                  ShowWindow(c, ids[i] == IDC_COMPACTFX && !gFeatFx ? SW_HIDE : SW_SHOWNA); }   // (no Voice FX button with it off)
    }
    if (!on) {                                  // back to normal sizes (positions come from Layout)
        SetWindowPos(GetDlgItem(gWnd, IDC_STATUS), nullptr, 0, 0, SC(532), SC(30), SWP_NOMOVE | SWP_NOZORDER | SWP_NOACTIVATE);
        for (int i = 1; i < 3; i++) SetWindowPos(GetDlgItem(gWnd, ids[i]), nullptr, 0, 0, SC(127), SC(34), SWP_NOMOVE | SWP_NOZORDER | SWP_NOACTIVATE);
        ShowWindow(GetDlgItem(gWnd, IDC_COMPACTFX), SW_HIDE); ShowWindow(GetDlgItem(gWnd, IDC_COMPACTFULL), SW_HIDE);
    }
    for (int t = 0; t < TAB_COUNT; t++) ShowWindow(GetDlgItem(gWnd, IDC_TAB0 + t), on || !PageOn(t) ? SW_HIDE : SW_SHOWNA);   // (not a feature that's off)
    SetDlgItemTextW(gWnd, IDC_COMPACTFX, gFxOn ? L"Voice FX: on" : L"Voice FX: off");
}

// "Always hear sounds on" choices follow the output rows: Off, Out 1..Out n, Every output.
// (gHearListStale: an output was renamed or removed: the list is filled again)
static void FillHearList()
{
    HWND c = GetDlgItem(gWnd, IDC_HEARON);
    if (!c) return;
    static int shown = -1;
    if (shown == gRows && !gHearListStale && SendMessageW(c, CB_GETCOUNT, 0, 0) > 0) return;
    shown = gRows; gHearListStale = false;
    SendMessageW(c, CB_RESETCONTENT, 0, 0);
    SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"Off");
    for (int k = 0; k < gRows; k++) { wchar_t t[32]; OutName(k, t, 32); SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)t); }
    SendMessageW(c, CB_ADDSTRING, 0, (LPARAM)L"Every output");
    if (gHearOut > gRows && gHearOut <= MAX_OUT) gHearOut = 0;   // that output was removed
    SendMessageW(c, CB_SETCURSEL, gHearOut == MAX_OUT + 1 ? gRows + 1 : gHearOut, 0);
}

static void Layout()
{
    // Showing / hiding dozens of controls one by one flickers: freeze drawing, then paint once at the end.
    const bool freeze = IsWindowVisible(gWnd) != FALSE;
    if (freeze) SendMessageW(gWnd, WM_SETREDRAW, FALSE, 0);
    for (int i = 0; i < gPagedN; i++) {
        bool del;
        int k = RowOfId(GetDlgCtrlID(gPaged[i].h), &del);
        bool vis = gPaged[i].page == gPage && (k < 0 || (k < gRows && !(del && k == 0))) && (!gPaged[i].feat || FeatOn(gPaged[i].feat))
                && (gPaged[i].sub < 0 || gPaged[i].sub == (gPaged[i].page == PAGE_MIC ? gMicSub : gPaged[i].page == PAGE_SETTINGS ? gSetSub
                                                         : gPaged[i].page == PAGE_MIXER ? gMixSub : gFxSub));
        int  cid = GetDlgCtrlID(gPaged[i].h);
        bool songStyle = gVocStyle == VOC_SONG;    // Song style: "Music from" replaces key / scale / voice
        if (cid == IDC_VOCKEY || cid == IDC_VOCSCALE || cid == IDC_VOCRANGE) vis = vis && !songStyle;
        if (cid == IDC_SONGSRC || cid == IDC_SONGSTATUS) vis = vis && songStyle;
        if (cid == IDC_VOICEPROG) vis = vis && gVoiceInstalling;
        if (cid >= IDC_CHRT0 && cid < IDC_CHRT0 + CH_MAX * MAX_OUT) vis = vis && (cid - IDC_CHRT0) % MAX_OUT < gRows
                                                                          && gCh[(cid - IDC_CHRT0) / MAX_OUT].type != CH_NONE;
        {                                       // a Mixer channel: its strip when it plays something, else its Add box
            static const int chIds[] = { IDC_CHSRC0, IDC_CHDB0, IDC_CHVOL0, IDC_CHMETER0, IDC_CHMUTE0, IDC_CHSOLO0, IDC_CHDUCK0 };
            for (int base : chIds) if (cid >= base && cid < base + CH_MAX) vis = vis && gCh[cid - base].type != CH_NONE;
            if (cid >= IDC_CHADD0 && cid < IDC_CHADD0 + CH_MAX) vis = false;   // (one "+ Add channel" button instead)
            if (cid == IDC_MIXHINT) { bool any = false; for (int c = 0; c < CH_MAX; c++) if (gCh[c].type != CH_NONE) any = true; vis = vis && !any; }
            if (cid >= IDC_MIXKEY0 && cid < IDC_MIXKEY0 + (KEY_SLOTS - SLOT_MIX0)) {   // hotkeys: channels in use, outputs there
                const int sl = SLOT_MIX0 + cid - IDC_MIXKEY0;
                vis = vis && (sl < SLOT_MIXOUT0 ? gCh[(sl - SLOT_MIX0) / MIXA_N].type != CH_NONE : (sl - SLOT_MIXOUT0) / MIXO_N < gRows);
            }
            if (cid >= IDC_MIXKROW0 && cid < IDC_MIXKROW0 + CH_MAX + MAX_OUT) {
                const int r = cid - IDC_MIXKROW0;
                vis = vis && (r < CH_MAX ? gCh[r].type != CH_NONE : r - CH_MAX < gRows);
            }
            if (cid >= IDC_MIXHOLDMODE0 && cid < IDC_MIXHOLDMODE0 + CH_MAX) vis = vis && gCh[cid - IDC_MIXHOLDMODE0].type != CH_NONE;
        }
        for (int k = gRows; k < MAX_OUT; k++)
            if (cid == IDC_OLBL0 + k || cid == IDC_OMUTE0 + k || cid == IDC_OVOL0 + k || cid == IDC_OMETER0 + k ||
                cid == IDC_ODEV0 + k || cid == IDC_ODB0 + k || cid == IDC_OLIM0 + k) vis = false;
        if (gCompact && (cid == IDC_STATUS || cid == IDC_START || cid == IDC_MUTEBTN)) vis = true;
        else if (gCompact) vis = false;
        ShowWindow(gPaged[i].h, vis ? SW_SHOWNA : SW_HIDE);
    }

    int by = ROW_Y0 + ROW_H * gRows + 6;
    FillHearList();
    MixerOutNames();
    EnableWindow(GetDlgItem(gWnd, IDC_ADDOUT), gRows < MAX_OUT);
    gSections[gDevSectionIdx].h = by + 28 + 14 - gSections[gDevSectionIdx].y;

    int d = RowsDelta();
    PlaceAll();                                 // everything below the output list slides down with it

    DWORD style = (DWORD)GetWindowLongW(gWnd, GWL_STYLE);
    // every page shares the window size, so switching never jumps; plus however much bigger you made it
    RECT r = gCompact ? RECT{ 0, 0, SC(CLIENT_W), SC(COMPACT_H) }
                      : RECT{ 0, 0, Imax(SC(CLIENT_W), MixerNeedW()) + gExtraW, SC(BASE_H + d) + gExtraH };
    AdjustWindowRect(&r, style, FALSE);
    if (!IsZoomed(gWnd)) {
        gOwnSize = true;
        SetWindowPos(gWnd, nullptr, 0, 0, r.right - r.left, r.bottom - r.top, SWP_NOMOVE | SWP_NOZORDER | SWP_NOACTIVATE);
        gOwnSize = false;
    }
    PlaceAll(); MixerPlace(); PlaceTabs();      // (centred for the final width)
    LayoutCompact(gCompact);
    if (freeze) SendMessageW(gWnd, WM_SETREDRAW, TRUE, 0);
    RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_FRAME | RDW_INVALIDATE | RDW_ALLCHILDREN | (freeze ? RDW_UPDATENOW : 0));
    EdFollow();
}

// ---- resizing: the UI size (Settings) scales everything; the window itself sizes freely
static void Rescale(int ns)
{
    ns = Iclamp(ns, 80, 250);
    if (!gWnd || ns == gUiScale) return;
    if (gRenEdit) ChanRenameDone(true);
    SendMessageW(gWnd, WM_SETREDRAW, FALSE, 0);
    for (int i = 0; i < gDesignN; i++) {
        Design& d = gDesign[i];
        if (!d.s0) {                            // the first time: remember its size at the scale it was built at
            RECT r; GetWindowRect(d.h, &r);
            d.s0 = gUiScale; d.x0 = d.x; d.y0 = d.y; d.w0 = d.w; d.ht0 = d.ht;
            d.hh0 = r.bottom - r.top; d.ww0 = r.right - r.left;
            if (d.ud) { RECT u; GetWindowRect(d.ud, &u); d.udx0 = d.udx; d.udy0 = d.udy; d.udw0 = u.right - u.left; d.udh0 = u.bottom - u.top; }
        }
        const int s0 = d.s0;
        auto S = [&](int v) { return MulDiv(v, ns, s0); };
        d.x = S(d.x0); d.y = S(d.y0); d.w = S(d.w0); d.ht = S(d.ht0);
        const int ww = d.ud ? S(d.ww0) : d.w, hh = d.combo ? d.ht : S(d.hh0);
        SetWindowPos(d.h, nullptr, d.x, d.y, ww, hh, SWP_NOZORDER | SWP_NOACTIVATE | SWP_NOCOPYBITS);
        if (d.ud) {
            d.udx = S(d.udx0); d.udy = S(d.udy0);
            SetWindowPos(d.ud, nullptr, d.x + d.udx, d.y + d.udy, S(d.udw0), S(d.udh0), SWP_NOZORDER | SWP_NOACTIVATE | SWP_NOCOPYBITS);
        }
    }
    gUiScale = ns;
    gExtraW = gExtraH = 0;                      // (a new size: the window fits it snugly again)
    ApplyFont();                                // the fonts at the new size; every label re-measured
    SendDlgItemMessageW(gWnd, IDC_COLORTHEME, CB_SETITEMHEIGHT, (WPARAM)-1, SC(20));
    SendDlgItemMessageW(gWnd, IDC_COLORTHEME, CB_SETITEMHEIGHT, 0, SC(20));
    SendMessageW(gWnd, WM_SETREDRAW, TRUE, 0);
    Layout();                                   // places everything and sizes the window to match
    if (PicActive()) PictureRebuild();
    RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_FRAME | RDW_INVALIDATE | RDW_ALLCHILDREN);
}

static void SetPage(int page);
static void PageCheck()                         // (the open page's feature was switched off: back to Main)
{
    if (!PageOn(gPage)) { const int was = gPage; gPage = -1; SetPage(PAGE_MAIN); if (gPage < 0) gPage = was; }
}
static void SetPage(int page)
{
    if (page < 0 || page >= TAB_COUNT || page == gPage || !PageOn(page)) return;
    HWND focus = GetFocus();
    gPage = page;
    Layout();
    if (!focus || !IsWindowVisible(focus)) SetFocus(GetDlgItem(gWnd, IDC_TAB0 + page));
}

static int ModeToSel(int m) { return m; }
static int SelToMode(int i) { return i; }
static void SetRowMode(int k, int mode)
{
    gRowMode[k] = mode;
    SendDlgItemMessageW(gWnd, IDC_ROWMODE + k, CB_SETCURSEL, ModeToSel(mode), 0);
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
        lstrcpynW(gOutName[j], gOutName[j + 1], 32); gOutW[j] = gOutW[j + 1]; gOutMute[j] = gOutMute[j + 1];
    }
    gOutName[gRows - 1][0] = 0; gOutW[gRows - 1] = 0; gOutMute[gRows - 1] = false;
    gHearListStale = true;
    gRows--;
    Layout();
    RestartIfRunning();
}

// ======================= updater =======================
// Looks at https://api.github.com/repos/<user>/<repo>/releases/latest, compares the tag with
// APP_VERSION, downloads the attached .exe next to this one, swaps them and restarts.

struct UpdateJob {
    bool manual, ok, newer;
    wchar_t error[300], tag[64], url[1024], notes[1800];
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

// ---- natural voices: NaturalVoiceSAPIAdapter (gexgd0419, MIT licence) ----
// Windows 11's realistic "Natural" Narrator voices, and Edge's online neural voices, aren't open to other apps.
// This free add-on makes them normal Windows voices. Lag Effect downloads its latest release from GitHub,
// unpacks it to %LOCALAPPDATA%\LagEffect\NaturalVoiceSAPIAdapter (it must stay there once installed) and opens
// its installer; when that's closed, the voice list is read again.
struct NvsaJob { wchar_t dir[MAX_PATH], installer[MAX_PATH], error[300]; bool ok; };
static bool gNvsaBusy = false;
static bool NvsaFind(const wchar_t* dir, wchar_t* out, int depth)   // Installer.exe, up to 3 folders down
{
    wchar_t pat[MAX_PATH]; wsprintfW(pat, L"%s\\*", dir);
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd);
    if (h == INVALID_HANDLE_VALUE) return false;
    bool found = false;
    do {
        if (fd.cFileName[0] == L'.') continue;
        wchar_t full[MAX_PATH]; wsprintfW(full, L"%s\\%s", dir, fd.cFileName);
        if (!(fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) && !lstrcmpiW(fd.cFileName, L"Installer.exe")) { lstrcpynW(out, full, MAX_PATH); found = true; }
        else if ((fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) && depth > 0) found = NvsaFind(full, out, depth - 1);
    } while (!found && FindNextFileW(h, &fd));
    FindClose(h);
    return found;
}
static DWORD WINAPI NvsaThread(LPVOID arg)
{
    NvsaJob* j = (NvsaJob*)arg;
    wchar_t base[MAX_PATH] = L"";
    GetEnvironmentVariableW(L"LOCALAPPDATA", base, MAX_PATH);
    wsprintfW(j->dir, L"%s\\LagEffect", base); CreateDirectoryW(j->dir, nullptr);
    wsprintfW(j->dir, L"%s\\LagEffect\\NaturalVoiceSAPIAdapter", base);
    if (NvsaFind(j->dir, j->installer, 3)) { j->ok = true; }   // already downloaded: just open its installer
    else {
        DWORD len = 0;
        char* json = HttpGet(L"https://api.github.com/repos/gexgd0419/NaturalVoiceSAPIAdapter/releases/latest", &len, j->error, 300);
        char url[1024] = "", pick[1024] = "";
        if (json) {
            const char* p = json;
            // The release has NaturalVoiceSAPIAdapter_<ver>_x86_x64.zip (what PCs need), an ARM64 zip, and
            // debug_symbols.zip (no programs in it). Take the x86_x64 one; failing that any adapter zip that isn't ARM.
            auto has = [](const char* t, const char* w) {
                for (; *t; t++) { int k = 0; while (w[k] && t[k] && ((t[k] | 32) == (w[k] | 32))) k++; if (!w[k]) return true; }
                return false;
            };
            int best = -1;
            while (JsonString(json, "browser_download_url", &p, url, 1024)) {
                int n = lstrlenA(url);
                if (n < 5 || lstrcmpiA(url + n - 4, ".zip") || has(url, "debug") || !has(url, "NaturalVoiceSAPIAdapter")) continue;
                int score = has(url, "x86_x64") ? 3 : !has(url, "arm") ? 2 : 1;
                if (score > best) { best = score; lstrcpynA(pick, url, 1024); }
            }
            MemFree(json);
            if (!pick[0]) lstrcpynW(j->error, L"Its latest release has no .zip to download.", 300);
        }
        char* zip = nullptr; DWORD zlen = 0;
        if (pick[0]) { wchar_t wu[1024]; Widen(pick, wu, 1024); zip = HttpGet(wu, &zlen, j->error, 300); }
        if (zip) {
            wchar_t tmp[MAX_PATH], zpath[MAX_PATH]; GetTempPathW(MAX_PATH, tmp); wsprintfW(zpath, L"%sNaturalVoiceSAPIAdapter.zip", tmp);
            HANDLE f = CreateFileW(zpath, GENERIC_WRITE, 0, nullptr, CREATE_ALWAYS, 0, nullptr);
            DWORD w = 0; bool wrote = f != INVALID_HANDLE_VALUE && WriteFile(f, zip, zlen, &w, nullptr) && w == zlen;
            if (f != INVALID_HANDLE_VALUE) CloseHandle(f);
            MemFree(zip);
            if (!wrote) lstrcpynW(j->error, L"Couldn't save the download.", 300);
            else {                              // unpack with Windows' own PowerShell
                CreateDirectoryW(j->dir, nullptr);
                wchar_t cmd[2048];
                wsprintfW(cmd, L"powershell.exe -NoProfile -NonInteractive -ExecutionPolicy Bypass -Command \"Expand-Archive -LiteralPath '%s' -DestinationPath '%s' -Force\"", zpath, j->dir);
                STARTUPINFOW si = { sizeof(si) }; si.dwFlags = STARTF_USESHOWWINDOW; si.wShowWindow = SW_HIDE;
                PROCESS_INFORMATION pi = {};
                if (CreateProcessW(nullptr, cmd, nullptr, nullptr, FALSE, CREATE_NO_WINDOW, nullptr, nullptr, &si, &pi)) {
                    WaitForSingleObject(pi.hProcess, 120000); CloseHandle(pi.hProcess); CloseHandle(pi.hThread);
                }
                DeleteFileW(zpath);
                if (NvsaFind(j->dir, j->installer, 3)) j->ok = true;
                else lstrcpynW(j->error, L"Unpacked it, but couldn't find its Installer.exe.", 300);
            }
        }
    }
    if (!PostMessageW(gWnd, WM_NVSA_READY, 0, (LPARAM)j)) HeapFree(GetProcessHeap(), 0, j);
    return 0;
}
static void NvsaStart()
{
    if (gNvsaBusy) return;
    NvsaJob* j = (NvsaJob*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(NvsaJob));
    if (!j) return;
    HANDLE t = CreateThread(nullptr, 0, NvsaThread, j, 0, nullptr);
    if (!t) { HeapFree(GetProcessHeap(), 0, j); return; }
    CloseHandle(t);
    gNvsaBusy = true;
    SetDlgItemTextW(gWnd, IDC_TTSSPEAK, L"Downloading..."); FitOne(GetDlgItem(gWnd, IDC_TTSSPEAK));
}
static DWORD WINAPI NvsaWaitThread(LPVOID arg)
{
    HANDLE proc = (HANDLE)arg;
    WaitForSingleObject(proc, INFINITE); CloseHandle(proc);
    PostMessageW(gWnd, WM_NVSA_DONE, 0, 0);
    return 0;
}
static void OnNvsaReady(NvsaJob* j)
{
    SetDlgItemTextW(gWnd, IDC_TTSSPEAK, L"Speak"); FitOne(GetDlgItem(gWnd, IDC_TTSSPEAK));
    if (!j->ok) {
        gNvsaBusy = false;
        wchar_t m[600]; wsprintfW(m, L"Couldn't get the natural voices add-on: %s\n\nYou can download it yourself from its GitHub page (Releases). Open it?", j->error);
        if (MessageBoxW(gWnd, m, L"Lag Effect - Natural voices", MB_YESNO | MB_ICONWARNING) == IDYES)
            ShellExecuteW(nullptr, L"open", L"https://github.com/gexgd0419/NaturalVoiceSAPIAdapter/releases", nullptr, nullptr, SW_SHOWNORMAL);
        HeapFree(GetProcessHeap(), 0, j);
        return;
    }
    MessageBoxW(gWnd, L"Its installer opens next. In it:\n\n"
                      L"1. Click Install for 64-bit (and 32-bit too, if offered). Windows asks for permission.\n"
                      L"2. Turn on the voices you want: \"Narrator\" (Windows 11's natural voices; add more in Settings > "
                      L"Accessibility > Narrator > Add natural voices) and/or \"Edge online\" (many more, needs internet).\n"
                      L"3. Close the installer. Lag Effect then finds the new voices by itself.\n\n"
                      L"NaturalVoiceSAPIAdapter is a free, open-source project by gexgd0419 (MIT licence).",
                L"Lag Effect - Natural voices", MB_ICONINFORMATION);
    SHELLEXECUTEINFOW se = {}; se.cbSize = sizeof(se); se.fMask = SEE_MASK_NOCLOSEPROCESS; se.hwnd = gWnd;
    se.lpVerb = L"open"; se.lpFile = j->installer; se.nShow = SW_SHOWNORMAL;
    wchar_t dir[MAX_PATH]; lstrcpynW(dir, j->installer, MAX_PATH); if (wchar_t* sl = wcsrchr(dir, L'\\')) *sl = 0; se.lpDirectory = dir;
    HeapFree(GetProcessHeap(), 0, j);
    HANDLE t = nullptr;
    if (ShellExecuteExW(&se) && se.hProcess && (t = CreateThread(nullptr, 0, NvsaWaitThread, se.hProcess, 0, nullptr)) != nullptr) {
        CloseHandle(t);
        SetDlgItemTextW(gWnd, IDC_TTSSPEAK, L"Setting up..."); FitOne(GetDlgItem(gWnd, IDC_TTSSPEAK));
    } else { if (se.hProcess) CloseHandle(se.hProcess); gNvsaBusy = false; }
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
        // Read the recent releases (newest first) and take the first that's a Lag Effect version (v1.2.3).
        wsprintfW(api, L"https://api.github.com/repos/%s/releases?per_page=30", repo);
        DWORD len = 0;
        char* json = HttpGet(api, &len, job->error, 300);
        if (json) {
            char tag[64] = "", notes[1700] = "", url[1024] = "";
            bool found = false;
            char* at = strstr(json, "\"tag_name\"");
            while (at && !found) {
                char* next = strstr(at + 10, "\"tag_name\"");   // this release runs up to the next one's tag
                char keep = 0; if (next) { keep = *next; *next = 0; }
                const char* p = at;
                char t[64] = "";
                JsonString(at, "tag_name", &p, t, 64);
                const bool mixTag = _strnicmp(t, "mixward-", 8) == 0;
                if (!mixTag && (t[0] == 'v' || t[0] == 'V' || (t[0] >= '0' && t[0] <= '9'))) {   // (skip any "mixward-" test releases)
                    found = true;
                    lstrcpynA(tag, mixTag ? t + 8 : t, 64);   // (just the version: "v1.0.0")
                    p = at;
                    const char* want = "/LagEffect.exe"; const int wl = lstrlenA(want);
                    while (JsonString(at, "browser_download_url", &p, url, 1024)) {   // our exe (else any .exe)
                        int n = lstrlenA(url);
                        if (n > wl && lstrcmpiA(url + n - wl, want) == 0) break;
                        url[0] = 0;
                    }
                    if (!url[0]) {
                        p = at;
                        while (JsonString(at, "browser_download_url", &p, url, 1024)) {
                            int n = lstrlenA(url);
                            if (n > 4 && lstrcmpiA(url + n - 4, ".exe") == 0) break;
                            url[0] = 0;
                        }
                    }
                    p = at;
                    if (!JsonString(at, "body", &p, notes, 1700)) notes[0] = 0;
                }
                if (next) *next = keep;
                at = next;
            }
            MemFree(json);
            Widen(tag, job->tag, 64);
            Widen(notes, job->notes, 1800);
            Widen(url, job->url, 1024);
            if (!found)       lstrcpynW(job->error, L"No Lag Effect release found yet.", 300);
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
    // What's new, made readable: no markdown symbols, bullets as dots. (Built with lstrcat: wsprintf stops at 1024 characters.)
    wchar_t nice[1800]; int o = 0;
    for (const wchar_t* q = job->notes; *q && o < 1790; ) {
        const bool lineStart = q == job->notes || q[-1] == L'\n';
        if (lineStart && *q == L'#') { while (*q == L'#' || *q == L' ') q++; continue; }
        if (lineStart && (*q == L'-' || *q == L'*') && q[1] == L' ') { nice[o++] = 0x2022; q++; continue; }
        if (*q == L'*' && q[1] == L'*') { q += 2; continue; }
        if (*q == L'\r') { q++; continue; }
        nice[o++] = *q++;
    }
    nice[o] = 0;
    wchar_t msg[2400];
    wsprintfW(msg, L"Version %s is available (you have %s).\n\n", job->tag, APP_VERSION);
    lstrcatW(msg, nice);
    lstrcatW(msg, nice[0] ? L"\n\nUpdate now? Lag Effect will restart." : L"Update now? Lag Effect will restart.");
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
        L"Main has the outputs, effect and hotkey. Mic cleans up your microphone. Voice FX has 12 effects for your live voice "
        L"on four sub-tabs, plus one-click Characters. Settings has latency, theme and updates. Ctrl+Tab switches between them.\n\n"
        L"MIC\n"
        L"The meter shows your mic level (green = the gate lets it through). Noise suppression (AI) removes "
        L"background noise. The noise gate mutes you between words: open it on Volume (set Threshold just above "
        L"the meter's level when you're quiet), on Voice (AI speech detection) or both. Low cut removes rumble, "
        L"Leveler evens out your volume.\n\n"
        L"VOICE FX\n"
        L"Flip the switch at the top, then tick the effects you want. Drag a knob up or down, scroll it, "
        L"or use the arrow keys (hold Shift for fine steps). Double-click a knob to reset it.\n"
        L"Hotkeys: click \"Set hotkey\" next to the switch, Pitch or Reverb and press a key or combo. "
        L"They work from anywhere, even in a game. Right-click a hotkey button (or press Backspace while setting it) to clear it.\n"
        L"Pitch: semitones + fine cents. Grain: longer = smoother, shorter = less delay.\n"
        L"Reverb: Mix = how much room, Size = how big, Damping = darker tail, Pre-delay = gap before the echo.\n"
        L"Vocoder: auto-tune to a key and scale, plus synth harmonies, Robot or Choir voices. Pick the key of the song; "
        L"Vocode to song: click it and the music playing on your PC (one app, all PC sound, or an audio file) says your words. "
        L"Retune 0 ms gives the hard auto-tune sound. Deep voice? Set Voice to Low / deep (Auto usually picks it for you).\n"
        L"Radio: sound like a walkie-talkie, phone call, megaphone, old radio, space radio, drive-thru, 8-bit or the next room. "
        L"Drive = distortion, Static = background noise, Squelch = start/stop sounds.\n"
        L"Formant: throat size without changing pitch (with Pitch, a different person instead of sped up). "
        L"Echo, Ghost (backwards reverb swells), Distortion (overdrive, fuzz, 8-bit), Chorus / flanger, Wobble (tremolo, vibrato), "
        L"Muffle (underwater, through a wall) and Glitch (a bad connection). Effects run in the order shown at the bottom.\n"
        L"Character: pick Demon, Giant, Child, Alien, Ghost and more to set everything up in one click.\n\n"
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
        L"4. On the Mic tab, turn on Noise suppression (AI) and/or the noise gate to keep background noise out.\n\n"
        L"OBS\n"
        L"With VB-Cable: add Audio Input Capture = \"CABLE Output\".\n"
        L"Sharing your whole screen in Discord? Tick Settings > Hide from screen share, or people hear you twice.\n"
        L"Without VB-Cable: add Application Audio Capture and pick LagEffect.exe.\n\n"
        L"MORE LAG AND TRICKS\n"
        L"Main tab: lag presets and beat repeat (loop synced to a tempo). Voice FX > Fun: Rewind, Repeat word, Tape stop and "
        L"Pitch dive hotkeys. Bottom of Voice FX: Character (save your own with \"Save my current voice\"), Surprise me, "
        L"and hold the A/B button to hear yourself without effects.\n\n"
        L"LOOK (Settings > Look)\n"
        L"Theme and colour presets, your own colour for the accent, background, panels, borders and text, a background "
        L"picture (with how much it fades into the theme), the font, window size and opacity.\n\n"
        L"MORE\n"
        L"Mic tab: push-to-talk / push-to-mute. Outputs: \"Clean voice\" sends your voice without effects (e.g. to OBS). "
        L"Settings: status overlay, hotkey beeps, UI size, compact window (Ctrl+M), export / import, and a profile can "
        L"switch on by itself while a game runs. The tray menu switches profiles, characters and soundboard pages.\n\n"
        L"PROFILES (Settings tab)\n"
        L"Save how you sound as a named profile (Gaming, Streaming, Trolling...) and switch by picking it or with its hotkey. "
        L"Effect hotkeys can be Hold: the effect is on only while you hold the key.\n\n"
        L"MIC TEST (Mic tab)\n"
        L"Record 5 s and hear exactly what Discord hears.\n\n"
        L"LAG EXTRAS (Main tab)\n"
        L"Random lag fires the stutter by itself now and then. Rewind plays your last 2 seconds backwards like a tape. "
        L"Repeat word plays the last word you said 3 times. (Change the 2 s / 3 times in the settings file: rewind_ms, repeat_word_times.)\n\n"
        L"SOUNDBOARD\n"
        L"Drop sound files onto the 8 pads (or click Load), set hotkeys, and play them into Discord. "
        L"They play on every output that isn't Off; Mute mic doesn't touch them. Pages A-D give you 32 pads (a hotkey flips pages). "
        L"Tick \"Play through my voice effects\" for a robot or demon soundboard. Text to speech: type a line, press Enter.\n\n"
        L"SOUNDBOARD OPTIONS\n"
        L"Each pad's ... button: play mode (one-shot, loop, hold-to-play, toggle), speed, pitch, fade in/out, name, colour, "
        L"and Record from my mic. Below the pads: one sound at a time, lower my voice while a pad plays, load a folder.\n\n"
        L"CLIPS (INSTANT REPLAY)\n"
        L"Lag Effect keeps the last few seconds of your voice, PC sound or just Discord (pick in Record) in memory. Press Clip it (or its hotkey) "
        L"to save them as a clip. Trim lets you listen back privately, cut the start and end, and undo. "
        L"Clips are saved as WAV files in %APPDATA%\\LagEffect\\Clips.\n\n"
        L"SHORTCUTS\n"
        L"Ctrl+1-6 jumps to a tab. Right-click the tray icon for quick switches (mute, voice effects, vocode to song, "
        L"noise suppression, gate). Settings has a Mute hotkey, hotkey pop-ups, Always on top and Start with Windows.\n\n"
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
    wchar_t k[100];
    ComboName(gFxKeys[slot], MAX_KEYS, k, 100);
    if (!k[0]) lstrcpynW(k, slot >= SLOT_MIX0 ? L"Set" : L"Set hotkey", 100);
    const wchar_t* pre = slot == SLOT_REWIND ? L"Rewind: " : slot == SLOT_REPEAT ? L"Repeat word: "
                       : slot == SLOT_PADBANK ? L"Next page: " : slot == SLOT_PROFNEXT ? L"Next profile: "
                       : slot >= SLOT_PROF0 ? L"This profile: " : slot == SLOT_TAPESTOP ? L"Tape stop: "
                       : slot == SLOT_DIVE ? L"Pitch dive (hold): " : slot == SLOT_PTT ? L"Key: " : L"";
    wsprintfW(buf, L"%s%s", pre, k);
}

static int FxKeyButtonId(int slot)
{
    if (slot >= SLOT_MIX0) return IDC_MIXKEY0 + (slot - SLOT_MIX0);
    if (slot >= SLOT_PROF0)    return slot - SLOT_PROF0 == gProfSel ? IDC_PROFKEY : 0;   // the selected profile's button
    if (slot == SLOT_TAPESTOP) return IDC_TAPEKEY;
    if (slot == SLOT_PTT)      return IDC_PTTKEY;
    if (slot == SLOT_DIVE)     return IDC_DIVEKEY;
    if (slot == SLOT_PROFNEXT) return IDC_PROFNEXTKEY;
    if (slot == SLOT_REWIND)  return IDC_REWINDKEY;
    if (slot == SLOT_REPEAT)  return IDC_REPEATKEY;
    if (slot == SLOT_PADBANK) return IDC_PADBANKKEY;
    if (slot >= SLOT_CLIP0)   return IDC_CLIPKEY + slot - SLOT_CLIP0;
    if (slot == SLOT_CLIPNOW) return IDC_CLIPNOWKEY;
    if (slot >= SLOT_PAD0) return IDC_PADKEY + slot - SLOT_PAD0;
    return slot == SLOT_MUTE ? IDC_MUTEKEY : slot == 0 ? IDC_FXKEY_MASTER : IDC_FXGRP_KEY + slot - 1;
}

static void ShowCaptureTarget()
{
    wchar_t name[120];
    if (gCapButton == IDC_HOTKEY) HotkeyName(name, 120);
    else {
        int slot = 0;
        for (int k = 0; k < KEY_SLOTS; k++) if (FxKeyButtonId(k) == gCapButton) slot = k;
        FxKeyButtonText(slot, name, 120);
    }
    SetDlgItemTextW(gWnd, gCapButton, name);
    FitOne(GetDlgItem(gWnd, gCapButton));
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

static bool gCheckConflict = false;
static void CheckHotkeyConflict(volatile int* target);
static void EndKeyCapture()
{
    gCapturingKey = false;
    KillTimer(gWnd, TIMER_KEY);
    if (gCheckConflict) { gCheckConflict = false; CheckHotkeyConflict(gCapTarget); }
    ShowCaptureTarget();
    for (int slot = 0; slot < KEY_SLOTS; slot++) gFxKeyWasDown[slot] = KeysDown(gFxKeys[slot]);   // no instant toggle
    UpdateStatus(true);
}

static void ClearFxKey(int slot)
{
    if (gCapturingKey) EndKeyCapture();
    for (int i = 0; i < MAX_KEYS; i++) gFxKeys[slot][i] = 0;
    wchar_t name[120]; FxKeyButtonText(slot, name, 120);
    SetDlgItemTextW(gWnd, FxKeyButtonId(slot), name);
    FitOne(GetDlgItem(gWnd, FxKeyButtonId(slot)));
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
    if (gCapKeyCount) gCheckConflict = true;    // checked once the picker has closed
    EndKeyCapture();
}

// ======================= remote control (Streamer.bot & co.) =======================
// A small WebSocket server on 127.0.0.1, only while Settings > Features > Remote control is on. Commands are JSON,
// e.g. {"do":"lag","ms":2000}; every command gets a reply, and changes (mute, lag, profile...) are sent as events.
// ---- remote control: the protocol bits (no Windows calls, so they're tested on their own) ----
static void Sha1(const unsigned char* data, size_t len, unsigned char out[20])   // for the WebSocket handshake
{
    unsigned h[5] = { 0x67452301u, 0xEFCDAB89u, 0x98BADCFEu, 0x10325476u, 0xC3D2E1F0u };
    const unsigned long long bits = (unsigned long long)len * 8;
    size_t total = ((len + 8) / 64 + 1) * 64;
    for (size_t off = 0; off < total; off += 64) {
        unsigned char blk[64];
        for (int i = 0; i < 64; i++) {
            size_t k = off + i;
            unsigned char b = k < len ? data[k] : k == len ? 0x80 : 0;
            if (k >= total - 8) b = (unsigned char)(bits >> (8 * (total - 1 - k)));
            blk[i] = b;
        }
        unsigned w[80];
        for (int i = 0; i < 16; i++) w[i] = (unsigned)blk[i * 4] << 24 | (unsigned)blk[i * 4 + 1] << 16 | (unsigned)blk[i * 4 + 2] << 8 | blk[i * 4 + 3];
        for (int i = 16; i < 80; i++) { unsigned x = w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]; w[i] = x << 1 | x >> 31; }
        unsigned a = h[0], b = h[1], c = h[2], d = h[3], e = h[4];
        for (int i = 0; i < 80; i++) {
            unsigned f, k;
            if (i < 20)      { f = (b & c) | (~b & d);          k = 0x5A827999u; }
            else if (i < 40) { f = b ^ c ^ d;                   k = 0x6ED9EBA1u; }
            else if (i < 60) { f = (b & c) | (b & d) | (c & d); k = 0x8F1BBCDCu; }
            else             { f = b ^ c ^ d;                   k = 0xCA62C1D6u; }
            unsigned t = (a << 5 | a >> 27) + f + e + k + w[i];
            e = d; d = c; c = b << 30 | b >> 2; b = a; a = t;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e;
    }
    for (int i = 0; i < 20; i++) out[i] = (unsigned char)(h[i / 4] >> (24 - 8 * (i % 4)));
}
static void Base64(const unsigned char* in, int n, char* out)
{
    static const char T[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    int o = 0;
    for (int i = 0; i < n; i += 3) {
        unsigned v = (unsigned)in[i] << 16 | (i + 1 < n ? (unsigned)in[i + 1] << 8 : 0) | (i + 2 < n ? in[i + 2] : 0);
        out[o++] = T[v >> 18 & 63]; out[o++] = T[v >> 12 & 63];
        out[o++] = i + 1 < n ? T[v >> 6 & 63] : '=';
        out[o++] = i + 2 < n ? T[v & 63] : '=';
    }
    out[o] = 0;
}
static bool WsHeader(const char* req, const char* name, char* out, int cap)   // an HTTP header's value (case ignored)
{
    const int nl = (int)strlen(name);
    for (const char* p = req; *p; ) {
        const char* eol = strstr(p, "\r\n");
        if (!eol) break;
        if (eol - p > nl && _strnicmp(p, name, nl) == 0 && p[nl] == ':') {
            const char* v = p + nl + 1; while (*v == ' ' || *v == '\t') v++;
            int n = (int)(eol - v); while (n > 0 && (v[n - 1] == ' ' || v[n - 1] == '\t')) n--;
            if (n >= cap) n = cap - 1;
            memcpy(out, v, n); out[n] = 0;
            return true;
        }
        p = eol + 2;
    }
    return false;
}
// The handshake reply for a request (the whole header, ending "\r\n\r\n"). Returns false: refuse it.
// Web pages are refused (a browser always says which site it's from), so a website can't control the app.
static bool WsAccept(const char* req, char* reply, int cap)
{
    char key[128], origin[256], up[64];
    if (!WsHeader(req, "Upgrade", up, 64) || _stricmp(up, "websocket") != 0) return false;
    if (!WsHeader(req, "Sec-WebSocket-Key", key, 100)) return false;
    if (WsHeader(req, "Origin", origin, 256) &&
        (_strnicmp(origin, "http", 4) == 0 || _strnicmp(origin, "null", 4) == 0 || _strnicmp(origin, "file", 4) == 0)) return false;
    char cat[200]; snprintf(cat, sizeof(cat), "%s258EAFA5-E914-47DA-95CA-C5AB0DC85B11", key);
    unsigned char dg[20]; Sha1((const unsigned char*)cat, strlen(cat), dg);
    char acc[40]; Base64(dg, 20, acc);
    snprintf(reply, cap, "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: %s\r\n\r\n", acc);
    return true;
}
// One frame from a client: returns the bytes it used (0: not all here yet, -1: broken / too big).
// Clients must mask their frames; the payload is unmasked into out (cap bytes at most).
static int WsParse(const unsigned char* b, int n, int* op, bool* fin, unsigned char* out, int cap, int* plen)
{
    if (n < 2) return 0;
    *fin = (b[0] & 0x80) != 0; *op = b[0] & 0x0F;
    const bool masked = (b[1] & 0x80) != 0;
    unsigned long long len = b[1] & 0x7F;
    int at = 2;
    if (len == 126) { if (n < 4) return 0; len = (unsigned)b[2] << 8 | b[3]; at = 4; }
    else if (len == 127) {
        if (n < 10) return 0;
        len = 0; for (int i = 0; i < 8; i++) len = len << 8 | b[2 + i];
        at = 10;
    }
    if (!masked || len > (unsigned long long)cap) return -1;
    if (n < at + 4 + (int)len) return 0;
    const unsigned char* m = b + at; at += 4;
    for (int i = 0; i < (int)len; i++) out[i] = b[at + i] ^ m[i & 3];
    *plen = (int)len;
    return at + (int)len;
}
static int WsFrame(int op, const char* data, int len, unsigned char* out)   // a server frame (not masked); out: len + 10
{
    int at = 0;
    out[at++] = (unsigned char)(0x80 | op);
    if (len < 126) out[at++] = (unsigned char)len;
    else if (len < 65536) { out[at++] = 126; out[at++] = (unsigned char)(len >> 8); out[at++] = (unsigned char)len; }
    else { out[at++] = 127; for (int i = 7; i >= 0; i--) out[at++] = i < 4 ? (unsigned char)(len >> (8 * i)) : 0; }
    memcpy(out + at, data, len);
    return at + len;
}
// Reading a message: {"do":"lag","ms":2000,"on":true,"name":"Robot"}
static bool JsonNum(const char* json, const char* key, double* v)
{
    char pat[64]; snprintf(pat, sizeof(pat), "\"%s\"", key);
    const char* p = strstr(json, pat);
    if (!p) return false;
    p += strlen(pat);
    while (*p == ' ' || *p == ':' || *p == '\t') p++;
    if (*p == '"') p++;                         // ("2000" works too)
    char* e = nullptr; double d = strtod(p, &e);
    if (e == p) return false;
    *v = d; return true;
}
static int JsonOnOff(const char* json, const char* key)   // 1 on, 0 off, 2 toggle, -1 not given
{
    char pat[64]; snprintf(pat, sizeof(pat), "\"%s\"", key);
    const char* p = strstr(json, pat);
    if (!p) return -1;
    p += strlen(pat);
    while (*p == ' ' || *p == ':' || *p == '\t' || *p == '"') p++;
    if (!_strnicmp(p, "true", 4) || !_strnicmp(p, "on", 2) || *p == '1') return 1;
    if (!_strnicmp(p, "false", 5) || !_strnicmp(p, "off", 3) || *p == '0') return 0;
    if (!_strnicmp(p, "toggle", 6)) return 2;
    return -1;
}
static void JsonEsc(const char* in, char* out, int cap)   // a string's inside, for a reply
{
    int o = 0;
    for (; *in && o < cap - 7; in++) {
        unsigned char ch = (unsigned char)*in;
        if (ch == '"' || ch == '\\') { out[o++] = '\\'; out[o++] = (char)ch; }
        else if (ch < 0x20) o += snprintf(out + o, cap - o, "\\u%04x", ch);
        else out[o++] = (char)ch;
    }
    out[o] = 0;
}

// ---- remote control: the server (a background thread, only while it's switched on) ----
// Off: no thread, no port open, networking not even started. On: listens on 127.0.0.1 (this PC only).
#define WS_MAX 8
struct WsConn { SOCKET s; int id; bool ws; int inN; unsigned char in[70000]; char msg[65536]; int msgN; };
static WsConn*   gWsConn[WS_MAX];
static HANDLE    gWsThread = nullptr;
static volatile LONG gWsStopNow = 0;
static CRITICAL_SECTION gWsLock;
static bool      gWsLockInit = false, gWsNetUp = false;
struct WsOut { int id; char* msg; };
static WsOut     gWsQ[128]; static int gWsQN = 0;  // replies / events waiting to go out (id -1: everyone)
static int       gWsAuthed[32], gWsAuthedN = 0; // connections that gave the password
static int       gWsCount = 0;                  // connected now (window thread's count)
static int       gWsState = 0;                  // 0 off, 1 listening, 2 the port is in use

static void WsQueue(int id, const char* utf8)   // (any thread) send to one connection, or -1: all of them
{
    if (!gWsLockInit || !gWsThread) return;
    const int n = (int)strlen(utf8);
    char* c = (char*)HeapAlloc(GetProcessHeap(), 0, n + 1);
    if (!c) return;
    memcpy(c, utf8, n + 1);
    EnterCriticalSection(&gWsLock);
    if (gWsQN < 128) gWsQ[gWsQN++] = { id, c }; else HeapFree(GetProcessHeap(), 0, c);
    LeaveCriticalSection(&gWsLock);
}
static void WsSendAll(SOCKET s, const unsigned char* d, int n)
{
    while (n > 0) { int k = send(s, (const char*)d, n, 0); if (k <= 0) return; d += k; n -= k; }
}
static void WsClose(int i)
{
    if (!gWsConn[i]) return;
    closesocket(gWsConn[i]->s);
    if (gWsConn[i]->ws) PostMessageW(gWnd, WM_WS_CONN, (WPARAM)gWsConn[i]->id, 0);   // (only ones that had connected)
    HeapFree(GetProcessHeap(), 0, gWsConn[i]);
    gWsConn[i] = nullptr;
}
static DWORD WINAPI WsThread(LPVOID arg)
{
    const int port = (int)(INT_PTR)arg;
    SOCKET ls = INVALID_SOCKET;
    int nextId = 1;
    DWORD lastTry = 0;
    while (!gWsStopNow) {
        if (ls == INVALID_SOCKET && GetTickCount() - lastTry > 3000) {   // (the port may be in use: tried again now and then)
            lastTry = GetTickCount();
            ls = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
            if (ls != INVALID_SOCKET) {
                BOOL ex = TRUE; setsockopt(ls, SOL_SOCKET, SO_EXCLUSIVEADDRUSE, (const char*)&ex, sizeof(ex));
                sockaddr_in a = {}; a.sin_family = AF_INET; a.sin_port = htons((u_short)port); a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
                if (bind(ls, (sockaddr*)&a, sizeof(a)) != 0 || listen(ls, 4) != 0) { closesocket(ls); ls = INVALID_SOCKET; }
            }
            PostMessageW(gWnd, WM_WS_STATE, ls != INVALID_SOCKET ? 1 : 2, 0);
        }
        fd_set rd; FD_ZERO(&rd);
        if (ls != INVALID_SOCKET) FD_SET(ls, &rd);
        for (int i = 0; i < WS_MAX; i++) if (gWsConn[i]) FD_SET(gWsConn[i]->s, &rd);
        timeval tv = { 0, 20000 };              // 20 ms: replies go out quickly
        if (rd.fd_count) select(0, &rd, nullptr, nullptr, &tv); else Sleep(20);
        if (ls != INVALID_SOCKET && FD_ISSET(ls, &rd)) {
            SOCKET c = accept(ls, nullptr, nullptr);
            if (c != INVALID_SOCKET) {
                int slot = -1; for (int i = 0; i < WS_MAX; i++) if (!gWsConn[i]) { slot = i; break; }
                WsConn* w = slot >= 0 ? (WsConn*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(WsConn)) : nullptr;
                if (!w) closesocket(c);
                else { BOOL nd = TRUE; setsockopt(c, IPPROTO_TCP, TCP_NODELAY, (const char*)&nd, sizeof(nd)); w->s = c; w->id = nextId++; gWsConn[slot] = w; }
            }
        }
        for (int i = 0; i < WS_MAX; i++) {
            WsConn* w = gWsConn[i];
            if (!w || !FD_ISSET(w->s, &rd)) continue;
            int k = recv(w->s, (char*)w->in + w->inN, (int)sizeof(w->in) - 1 - w->inN, 0);
            if (k <= 0) { WsClose(i); continue; }
            w->inN += k; w->in[w->inN] = 0;
            if (!w->ws) {                       // the handshake first
                if (!strstr((char*)w->in, "\r\n\r\n")) { if (w->inN > 8000) WsClose(i); continue; }
                char reply[400];
                if (!WsAccept((char*)w->in, reply, 400)) {
                    const char* no = "HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\nConnection: close\r\n\r\n";
                    WsSendAll(w->s, (const unsigned char*)no, (int)strlen(no));
                    WsClose(i); continue;
                }
                WsSendAll(w->s, (const unsigned char*)reply, (int)strlen(reply));
                w->ws = true; w->inN = 0;
                PostMessageW(gWnd, WM_WS_CONN, (WPARAM)w->id, 1);
                continue;
            }
            bool dead = false;
            for (;;) {                          // every whole frame that's arrived
                int op = 0, len = 0; bool fin = false;
                static unsigned char pay[65536];
                int used = WsParse(w->in, w->inN, &op, &fin, pay, 65535, &len);
                if (used == 0) break;
                if (used < 0) { dead = true; break; }
                memmove(w->in, w->in + used, w->inN - used); w->inN -= used;
                if (op == 8) { unsigned char f[16]; WsSendAll(w->s, f, WsFrame(8, "", 0, f)); dead = true; break; }   // close
                if (op == 9) { static unsigned char f[65546]; WsSendAll(w->s, f, WsFrame(10, (const char*)pay, len, f)); continue; }   // ping
                if (op != 0 && op != 1) continue;   // (pong, binary: ignored)
                if (op == 1) w->msgN = 0;
                if (w->msgN + len >= (int)sizeof(w->msg)) { dead = true; break; }
                memcpy(w->msg + w->msgN, pay, len); w->msgN += len;
                if (fin) {                      // a whole message: the window runs it
                    char* m = (char*)HeapAlloc(GetProcessHeap(), 0, w->msgN + 1);
                    if (m) { memcpy(m, w->msg, w->msgN); m[w->msgN] = 0; if (!PostMessageW(gWnd, WM_WS_MSG, (WPARAM)w->id, (LPARAM)m)) HeapFree(GetProcessHeap(), 0, m); }
                    w->msgN = 0;
                }
            }
            if (dead) WsClose(i);
        }
        EnterCriticalSection(&gWsLock);         // replies and events
        WsOut q[128]; const int qn = gWsQN; memcpy(q, gWsQ, sizeof(WsOut) * qn); gWsQN = 0;
        LeaveCriticalSection(&gWsLock);
        for (int j = 0; j < qn; j++) {
            const int n = (int)strlen(q[j].msg);
            unsigned char* f = (unsigned char*)HeapAlloc(GetProcessHeap(), 0, n + 16);
            if (f) {
                const int fl = WsFrame(1, q[j].msg, n, f);
                for (int i = 0; i < WS_MAX; i++)
                    if (gWsConn[i] && gWsConn[i]->ws && (q[j].id < 0 || q[j].id == gWsConn[i]->id)) WsSendAll(gWsConn[i]->s, f, fl);
                HeapFree(GetProcessHeap(), 0, f);
            }
            HeapFree(GetProcessHeap(), 0, q[j].msg);
        }
    }
    for (int i = 0; i < WS_MAX; i++) if (gWsConn[i]) { closesocket(gWsConn[i]->s); HeapFree(GetProcessHeap(), 0, gWsConn[i]); gWsConn[i] = nullptr; }
    if (ls != INVALID_SOCKET) closesocket(ls);
    return 0;
}
static void WsStop()                            // closes the port and every connection, and ends the thread
{
    if (gWsThread) {
        gWsStopNow = 1;
        WaitForSingleObject(gWsThread, 3000);
        CloseHandle(gWsThread); gWsThread = nullptr;
    }
    if (gWsLockInit) {
        EnterCriticalSection(&gWsLock);
        for (int j = 0; j < gWsQN; j++) HeapFree(GetProcessHeap(), 0, gWsQ[j].msg);
        gWsQN = 0;
        LeaveCriticalSection(&gWsLock);
    }
    if (gWsNetUp) { WSACleanup(); gWsNetUp = false; }
    gWsAuthedN = 0; gWsCount = 0; gWsState = 0;
}
static void WsStart()                           // (only when it's switched on in Settings)
{
    WsStop();
    if (!gWsOn) return;
    if (!gWsLockInit) { InitializeCriticalSection(&gWsLock); gWsLockInit = true; }
    WSADATA wd;
    if (WSAStartup(MAKEWORD(2, 2), &wd) != 0) return;
    gWsNetUp = true;
    gWsStopNow = 0;
    gWsThread = CreateThread(nullptr, 0, WsThread, (LPVOID)(INT_PTR)Iclamp(gWsPort, 1024, 65535), 0, nullptr);
}

// ---- remote control: running a command (the window's thread) ----
static bool WsAuthed(int id)
{
    if (!gWsPass[0]) return true;
    for (int i = 0; i < gWsAuthedN; i++) if (gWsAuthed[i] == id) return true;
    return false;
}
static void WsReply(int id, const char* what, const char* err)
{
    char r[400];
    if (err) { char e[300]; JsonEsc(err, e, 300); snprintf(r, sizeof(r), "{\"ok\":false,\"do\":\"%s\",\"error\":\"%s\"}", what, e); }
    else snprintf(r, sizeof(r), "{\"ok\":true,\"do\":\"%s\"}", what);
    WsQueue(id, r);
}
static void WsStatusJson(char* out, int cap)
{
    char prof[200] = "", pe[300];
    if (gProfCur >= 0 && gProfCur < gProfCount) WideCharToMultiByte(CP_UTF8, 0, gProfNames[gProfCur], -1, prof, 200, nullptr, nullptr);
    JsonEsc(prof, pe, 300);
    snprintf(out, cap, "{\"event\":\"status\",\"version\":\"%ls\",\"running\":%s,\"muted\":%s,\"lagging\":%s,\"fx\":%s,\"profile\":\"%s\","
                       "\"features\":{\"lag\":%s,\"voicefx\":%s,\"soundboard\":%s,\"clips\":%s}}",
             APP_VERSION, gRunning ? "true" : "false", gMicMuted ? "true" : "false", gLooping ? "true" : "false",
             gFxOn ? "true" : "false", pe, gFeatLag ? "true" : "false", gFeatFx ? "true" : "false",
             gFeatSound ? "true" : "false", gFeatClips ? "true" : "false");
}
static bool WsBool(const char* m, const char* key, bool now, bool* out)   // on/off/toggle; missing = toggle
{
    const int v = JsonOnOff(m, key);
    *out = v == 1 ? true : v == 0 ? false : !now;
    return true;
}
static int WsFindChannel(const char* m)         // "n": 1-8, or "name": its name on the Mixer (or app / input)
{
    double n;
    if (JsonNum(m, "n", &n)) { int c = (int)n - 1; return c >= 0 && c < CH_MAX && gCh[c].type != CH_NONE ? c : -1; }
    char nm[200]; const char* p = m;
    if (!JsonString(m, "name", &p, nm, 200)) return -1;
    wchar_t w[200]; MultiByteToWideChar(CP_UTF8, 0, nm, -1, w, 200);
    for (int c = 0; c < CH_MAX; c++) {
        if (gCh[c].type == CH_NONE) continue;
        wchar_t l[64]; ChanLabel(c, l, 64);
        if (!lstrcmpiW(l, w) || !lstrcmpiW(gCh[c].src, w)) return c;
    }
    return -1;
}
static int WsFindOutput(const char* m)          // "n": 1-5, or "name": its name ("Out 2" or yours)
{
    double n;
    if (JsonNum(m, "n", &n)) { int k = (int)n - 1; return k >= 0 && k < gRows ? k : -1; }
    char nm[200]; const char* p = m;
    if (!JsonString(m, "name", &p, nm, 200)) return -1;
    wchar_t w[200]; MultiByteToWideChar(CP_UTF8, 0, nm, -1, w, 200);
    for (int k = 0; k < gRows; k++) { wchar_t l[32]; OutName(k, l, 32); if (!lstrcmpiW(l, w)) return k; }
    return -1;
}
static void WsExec(int id, const char* m)
{
    char what[40] = ""; const char* p = m;
    if (!JsonString(m, "do", &p, what, 40)) { WsReply(id, "", "Send JSON like {\"do\":\"lag\",\"ms\":2000}."); return; }
    for (char* q = what; *q; q++) *q = (char)tolower((unsigned char)*q);
    if (!strcmp(what, "auth")) {
        char pw[100] = ""; const char* pp = m; JsonString(m, "password", &pp, pw, 100);
        wchar_t w[100]; MultiByteToWideChar(CP_UTF8, 0, pw, -1, w, 100);
        if (gWsPass[0] && lstrcmpW(w, gWsPass)) { WsReply(id, what, "Wrong password."); return; }
        if (!WsAuthed(id) && gWsAuthedN < 32) gWsAuthed[gWsAuthedN++] = id;
        WsReply(id, what, nullptr); return;
    }
    if (!WsAuthed(id)) { WsReply(id, what, "Send {\"do\":\"auth\",\"password\":\"...\"} first."); return; }
    const char* offLag = "The lag effect is off (Settings > Features).";
    const char* offFx = "Voice FX is off (Settings > Features).";
    const char* offSb = "The soundboard is off (Settings > Features).";
    const char* offCl = "Clips are off (Settings > Features).";
    double v; bool b;
    if (!strcmp(what, "ping")) { char r[120]; snprintf(r, sizeof(r), "{\"ok\":true,\"do\":\"ping\",\"version\":\"%ls\"}", APP_VERSION); WsQueue(id, r); return; }
    if (!strcmp(what, "status")) { char r[700]; WsStatusJson(r, 700); WsQueue(id, r); return; }
    if (!strcmp(what, "start")) { if (!gWantRunning) StartAudio(false); UpdateUi(); WsReply(id, what, nullptr); return; }
    if (!strcmp(what, "stop"))  { if (gWantRunning) StopAudio(); UpdateUi(); WsReply(id, what, nullptr); return; }
    if (!strcmp(what, "mute"))  { WsBool(m, "on", gMicMuted, &b); SetMute(b); UpdateUi(); WsReply(id, what, nullptr); return; }
    if (!strcmp(what, "unmute")) { SetMute(false); UpdateUi(); WsReply(id, what, nullptr); return; }
    if (!strcmp(what, "lag")) {                 // stutter for "ms" (default 1.5 s); {"on":false} stops it
        if (!gFeatLag) { WsReply(id, what, offLag); return; }
        if (JsonOnOff(m, "on") == 0) gWsLagUntil = GetTickCount();
        else { int ms = JsonNum(m, "ms", &v) ? (int)v : 1500; gWsLagUntil = GetTickCount() + (DWORD)Iclamp(ms, 50, 30000); }
        WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "rewind") || !strcmp(what, "repeat")) {
        if (!gFeatLag) { WsReply(id, what, offLag); return; }
        if (what[1] == 'e' && what[2] == 'w') gRewindReq = true; else gRepeatReq = true;
        WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "fx")) {
        if (!gFeatFx) { WsReply(id, what, offFx); return; }
        WsBool(m, "on", gFxOn, &b); SetFxOn(b); UpdateStatus(true); WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "character") || !strcmp(what, "profile")) {   // by name: reuses the command-line control
        if (what[0] == 'c' && !gFeatFx) { WsReply(id, what, offFx); return; }
        char nm[200] = ""; const char* np = m;
        if (!JsonString(m, "name", &np, nm, 200)) { WsReply(id, what, "Give its \"name\"."); return; }
        wchar_t cmd[300], w[200]; MultiByteToWideChar(CP_UTF8, 0, nm, -1, w, 200);
        for (wchar_t* q = w; *q; q++) if (*q == L'"') *q = L'\'';
        swprintf(cmd, 300, L"x /%hs \"%ls\"", what, w);
        const bool was = gCmdLine; gCmdLine = true; ExecCommandLine(cmd); gCmdLine = was;
        WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "nextprofile")) {
        if (gProfCount) { int k = (gProfCur + 1) % gProfCount; ProfileLoad(k, true); ProfilesFill(gProfNames[k]); }
        WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "tts") || !strcmp(what, "say")) {   // {"do":"tts","text":"hello","accent":"Scottish"}
        if (!gFeatSound) { WsReply(id, what, offSb); return; }
        static char txt[1800]; const char* tp = m;
        if (!JsonString(m, "text", &tp, txt, 1800)) { WsReply(id, what, "Give the \"text\"."); return; }
        wchar_t w[600]; MultiByteToWideChar(CP_UTF8, 0, txt, -1, w, 600);
        char ac[64] = ""; const char* ap = m; const int keep = gTtsAccent;
        if (JsonString(m, "accent", &ap, ac, 64)) {
            wchar_t wa[64]; MultiByteToWideChar(CP_UTF8, 0, ac, -1, wa, 64);
            for (int i = 0; i < TTS_ACCENT_N; i++) if (!lstrcmpiW(TTS_ACCENTS[i].name, wa)) gTtsAccent = i;
        }
        if (gTtsBusy) { gTtsAccent = keep; WsReply(id, what, "Still speaking the last one."); return; }
        TtsSpeakText(w);
        gTtsAccent = keep;
        WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "pad") || !strcmp(what, "sound")) {
        if (!gFeatSound) { WsReply(id, what, offSb); return; }
        int k = JsonNum(m, "n", &v) ? (int)v - 1 : -1;
        if (k < 0 || k >= PAD_N) { WsReply(id, what, "Give its number \"n\" (1-32)."); return; }
        PadKey(k, true, false); WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "stopsounds")) { for (int k = 0; k < SB_N; k++) gPads[k].stop = true; WsReply(id, what, nullptr); return; }
    if (!strcmp(what, "clip")) {                // save the last few seconds
        if (!gFeatClips) { WsReply(id, what, offCl); return; }
        ClipNow(); WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "playclip")) {
        if (!gFeatClips) { WsReply(id, what, offCl); return; }
        int k = JsonNum(m, "n", &v) ? (int)v - 1 : -1;
        if (k < 0 || k >= CLIP_N || !gClips[k].base) { WsReply(id, what, "No clip with that number \"n\"."); return; }
        gPads[CLIP0 + k].trigger = true; WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "channel")) {             // {"do":"channel","name":"Spotify","db":-12,"mute":true,"solo":false,"duck":true}
        const int c = WsFindChannel(m);
        if (c < 0) { WsReply(id, what, "No Mixer channel with that \"n\" or \"name\"."); return; }
        if (JsonNum(m, "db", &v)) FaderSet(IDC_CHVOL0 + c, (int)lround(v * 10));
        if (JsonOnOff(m, "mute") >= 0) { WsBool(m, "mute", gCh[c].mute, &b); gCh[c].mute = b; }
        if (JsonOnOff(m, "solo") >= 0) { WsBool(m, "solo", gCh[c].solo, &b); gCh[c].solo = b; }
        if (JsonOnOff(m, "duck") >= 0) { WsBool(m, "duck", gCh[c].duck, &b); gCh[c].duck = b; }
        MixerRedraw(); WsReply(id, what, nullptr); return;
    }
    if (!strcmp(what, "output")) {              // {"do":"output","n":2,"mute":true,"volume":80}
        const int k = WsFindOutput(m);
        if (k < 0) { WsReply(id, what, "No output with that \"n\" or \"name\"."); return; }
        if (JsonNum(m, "volume", &v)) { gRowVol[k] = Iclamp((int)lround(v), 0, 200); SendDlgItemMessageW(gWnd, SPIN_UD(IDC_ROWVOL + k), UDM_SETPOS32, 0, gRowVol[k]); }
        if (JsonOnOff(m, "mute") >= 0) { WsBool(m, "mute", gOutMute[k], &b); gOutMute[k] = b; }
        MixerRedraw(); WsReply(id, what, nullptr); return;
    }
    WsReply(id, what, "Unknown command. Try ping, status, mute, lag, fx, character, profile, tts, pad, clip, channel or output.");
}
static void WsEvents()                          // (50 ms, while anything is connected) tell them what changed
{
    if (!gWsThread || !gWsCount) return;
    static int lastMute = -1, lastLag = -1, lastFx = -1, lastProf = -2, lastRun = -1;
    char r[300];
    if ((int)gMicMuted != lastMute) { if (lastMute >= 0) { snprintf(r, sizeof(r), "{\"event\":\"mute\",\"on\":%s}", gMicMuted ? "true" : "false"); WsQueue(-1, r); } lastMute = gMicMuted; }
    if ((int)gLooping != lastLag)   { if (lastLag >= 0)  { snprintf(r, sizeof(r), "{\"event\":\"lag\",\"on\":%s}", gLooping ? "true" : "false"); WsQueue(-1, r); } lastLag = gLooping; }
    if ((int)gFxOn != lastFx)       { if (lastFx >= 0)   { snprintf(r, sizeof(r), "{\"event\":\"fx\",\"on\":%s}", gFxOn ? "true" : "false"); WsQueue(-1, r); } lastFx = gFxOn; }
    if ((int)gRunning != lastRun)   { if (lastRun >= 0)  { snprintf(r, sizeof(r), "{\"event\":\"running\",\"on\":%s}", gRunning ? "true" : "false"); WsQueue(-1, r); } lastRun = gRunning; }
    if (gProfCur != lastProf) {
        if (lastProf != -2 && gProfCur >= 0 && gProfCur < gProfCount) {
            char n[200], e[300]; WideCharToMultiByte(CP_UTF8, 0, gProfNames[gProfCur], -1, n, 200, nullptr, nullptr); JsonEsc(n, e, 300);
            snprintf(r, sizeof(r), "{\"event\":\"profile\",\"name\":\"%s\"}", e); WsQueue(-1, r);
        }
        lastProf = gProfCur;
    }
}
static void WsStatusText()                      // Settings: what it's doing
{
    wchar_t t[200];
    if (!gWsOn) lstrcpynW(t, L"Off: nothing can connect.", 200);
    else if (gWsState == 2) wsprintfW(t, L"Port %d is in use by another app: pick another one.", gWsPort);
    else if (gWsState == 1) wsprintfW(t, L"On: ws://127.0.0.1:%d  \x00B7  %d connected", gWsPort, gWsCount);
    else lstrcpynW(t, L"Starting...", 200);
    SetDlgItemTextW(gWnd, IDC_WSSTATUS, t);
}
static void WsHelp()                            // Settings: how to set up Streamer.bot (and copy the C# to paste)
{
    wchar_t code[1200];
    swprintf(code, 1200,
        L"// Lag Effect remote control. In Streamer.bot: Servers/Clients > Websocket Clients > Add,\r\n"
        L"// Endpoint ws://127.0.0.1:%d, then use this in an action's C# (\"Execute C# Code\"):\r\n"
        L"using System;\r\n"
        L"public class CPHInline\r\n{\r\n    public bool Execute()\r\n    {\r\n"
        L"        // the 0 is the connection's number in Websocket Clients (the first one is 0)\r\n"
        L"%ls"
        L"        CPH.WebsocketSend(\"{\\\"do\\\":\\\"lag\\\",\\\"ms\\\":2000}\", 0);\r\n"
        L"        return true;\r\n    }\r\n}\r\n",
        Iclamp(gWsPort, 1024, 65535),
        gWsPass[0] ? L"        CPH.WebsocketSend(\"{\\\"do\\\":\\\"auth\\\",\\\"password\\\":\\\"YOUR PASSWORD\\\"}\", 0);   // (once per connection)\r\n" : L"");
    if (OpenClipboard(gWnd)) {
        EmptyClipboard();
        const size_t n = (wcslen(code) + 1) * sizeof(wchar_t);
        HGLOBAL g = GlobalAlloc(GMEM_MOVEABLE, n);
        if (g) { memcpy(GlobalLock(g), code, n); GlobalUnlock(g); if (!SetClipboardData(CF_UNICODETEXT, g)) GlobalFree(g); }
        CloseClipboard();
    }
    MessageBoxW(gWnd, L"Copied. In Streamer.bot, paste it into an action's \"Execute C# Code\" sub-action, change the message "
                      L"between the quotes to the command you want, then Compile and Save.\n\n\"How to use...\" has every step and command.",
                L"Lag Effect - remote control", MB_OK | MB_ICONINFORMATION);
}
static void WsGuide()                           // Settings: the walkthrough, and how messages are written
{
    wchar_t t[4500];
    swprintf(t, 4500,
        L"USING LAG EFFECT WITH STREAMER.BOT\n\n"
        L"1. Here: tick \"Let apps on this PC control Lag Effect\". The line under it says ws://127.0.0.1:%d.\n\n"
        L"2. In Streamer.bot: Servers/Clients > Websocket Clients > right-click > Add.\n"
        L"    Name: Lag Effect.   Endpoint: ws://127.0.0.1:%d.   Tick Auto Connect and Auto Reconnect.\n"
        L"    OK, then right-click it > Connect. Here it now says \"1 connected\".\n\n"
        L"3. Actions tab > right-click > Add an action (e.g. \"Lag chat\"), and give it a trigger,\n"
        L"    like a channel point reward or a chat command.\n\n"
        L"4. In the action: right-click Sub-Actions > Core > C# > Execute C# Code. Here press \"Copy C# code\"\n"
        L"    and paste it in. Change the message to the command you want (below), then Compile and Save.\n"
        L"    The 0 in WebsocketSend is the connection's number in Websocket Clients (the first is 0).\n\n"
        L"5. Run the action (right-click > Test Trigger). Lag Effect does it.\n\n"
        L"MESSAGES\n"
        L"Each one is JSON: {\"do\":\"command\", then any options}. Inside C#, put a \\ before every \" in the message, e.g.\n"
        L"    CPH.WebsocketSend(\"{\\\"do\\\":\\\"lag\\\",\\\"ms\\\":2000}\", 0);\n\n"
        L"    {\"do\":\"lag\",\"ms\":2000}   stutter for 2 seconds  (needs the Lag effect on)\n"
        L"    {\"do\":\"mute\",\"on\":true}   mute; false = unmute, \"toggle\" = switch\n"
        L"    {\"do\":\"fx\",\"on\":\"toggle\"}   Voice FX on / off  (needs Voice FX on)\n"
        L"    {\"do\":\"character\",\"name\":\"Robot\"}   a Voice FX character\n"
        L"    {\"do\":\"profile\",\"name\":\"Gaming\"}   or {\"do\":\"nextprofile\"}\n"
        L"    {\"do\":\"tts\",\"text\":\"hello chat\",\"accent\":\"Scottish\"}   speak  (needs the Soundboard on)\n"
        L"    {\"do\":\"pad\",\"n\":3}   play soundboard pad 3;  {\"do\":\"stopsounds\"}\n"
        L"    {\"do\":\"clip\"}   save the last few seconds;  {\"do\":\"playclip\",\"n\":1}  (needs Clips on)\n"
        L"    {\"do\":\"channel\",\"name\":\"Spotify\",\"db\":-12,\"mute\":false,\"solo\":false,\"duck\":true}   a Mixer channel\n"
        L"    {\"do\":\"output\",\"n\":2,\"mute\":true,\"volume\":80}   an output (or \"name\": what you called it)\n"
        L"    {\"do\":\"start\"}  {\"do\":\"stop\"}  {\"do\":\"status\"}  {\"do\":\"ping\"}\n\n"
        L"REPLIES AND EVENTS\n"
        L"Every message gets a reply: {\"ok\":true,...} or {\"ok\":false,\"error\":\"why\"}. Lag Effect also tells Streamer.bot\n"
        L"when things change: {\"event\":\"mute\",\"on\":true}, {\"event\":\"lag\",...}, {\"event\":\"fx\",...},\n"
        L"{\"event\":\"profile\",\"name\":...}, {\"event\":\"running\",...}. Use them with the trigger\n"
        L"Core > Websocket > Client > Websocket Client Message (the text is in %%message%%).\n\n"
        L"PASSWORD\n"
        L"If you set one, send {\"do\":\"auth\",\"password\":\"...\"} first after connecting (\"Copy C# code\" includes it).\n\n"
        L"Only apps on this PC can connect, never websites. Untick the box above to switch it all off.",
        Iclamp(gWsPort, 1024, 65535), Iclamp(gWsPort, 1024, 65535));
    MessageBoxW(gWnd, t, L"Lag Effect - Streamer.bot", MB_OK | MB_ICONINFORMATION);
}

// ======================= start with Windows =======================
// HKCU\...\Run\LagEffect = "this exe". Uses this copy's location (re-tick it after moving the app).
static const wchar_t* RUN_KEY = L"Software\\Microsoft\\Windows\\CurrentVersion\\Run";
static bool StartWithWindows()
{
    wchar_t v[MAX_PATH + 8]; DWORD sz = sizeof(v);
    return RegGetValueW(HKEY_CURRENT_USER, RUN_KEY, L"LagEffect", RRF_RT_REG_SZ, nullptr, v, &sz) == ERROR_SUCCESS;
}
static void SetStartWithWindows(bool on)
{
    HKEY k;
    if (RegOpenKeyExW(HKEY_CURRENT_USER, RUN_KEY, 0, KEY_SET_VALUE, &k) != ERROR_SUCCESS) return;
    if (on) {
        wchar_t exe[MAX_PATH], v[MAX_PATH + 8];
        GetModuleFileNameW(nullptr, exe, MAX_PATH);
        wsprintfW(v, L"\"%s\"", exe);
        RegSetValueExW(k, L"LagEffect", 0, REG_SZ, (const BYTE*)v, (lstrlenW(v) + 1) * sizeof(wchar_t));
    } else {
        RegDeleteValueW(k, L"LagEffect");
    }
    RegCloseKey(k);
}

static void StartWithWindowsFollow()            // (on start) it pointed at an older copy of Lag Effect: point it at this one
{
    wchar_t v[MAX_PATH + 8]; DWORD sz = sizeof(v);
    if (RegGetValueW(HKEY_CURRENT_USER, RUN_KEY, L"LagEffect", RRF_RT_REG_SZ, nullptr, v, &sz) != ERROR_SUCCESS) return;
    wchar_t* p = v; if (*p == L'"') p++;
    wchar_t* q = wcschr(p, L'"'); if (q) *q = 0;
    wchar_t exe[MAX_PATH]; GetModuleFileNameW(nullptr, exe, MAX_PATH);
    if (!lstrcmpiW(p, exe)) return;
    WIN32_FILE_ATTRIBUTE_DATA a = {}, b = {};
    const bool otherThere = GetFileAttributesExW(p, GetFileExInfoStandard, &a) != 0;
    if (!GetFileAttributesExW(exe, GetFileExInfoStandard, &b)) return;
    // the other one is gone, or older than this one: start this one with Windows instead (a newer one is left alone)
    if (!otherThere || CompareFileTime(&a.ftLastWriteTime, &b.ftLastWriteTime) < 0) SetStartWithWindows(true);
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
    lstrcpynW(nid.szTip, gMicMuted ? L"Lag Effect - mic muted" : L"Lag Effect", 128);
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

static bool SongModeOn();
static void UpdateTrayTip()                     // tray tooltip says when you're muted
{
    if (!gInTray) return;
    NOTIFYICONDATAW nid = {};
    nid.cbSize = sizeof(nid);
    nid.hWnd = gWnd;
    nid.uID = 1;
    nid.uFlags = NIF_TIP;
    lstrcpynW(nid.szTip, gMicMuted ? L"Lag Effect - mic muted" : L"Lag Effect", 128);
    Shell_NotifyIconW(NIM_MODIFY, &nid);
}

static void TrayMenu()
{
    POINT p; GetCursorPos(&p);
    HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING, ID_TRAY_OPEN, L"Open");
    AppendMenuW(m, MF_STRING, ID_TRAY_RUN, gWantRunning ? L"Stop audio" : L"Start audio");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(m, MF_STRING | (gMicMuted ? MF_CHECKED : 0), ID_TRAY_MUTE, L"Mute mic");
    if (gFeatFx) {
        AppendMenuW(m, MF_STRING | (gFxOn ? MF_CHECKED : 0), ID_TRAY_FX, L"Voice effects");
        AppendMenuW(m, MF_STRING | (SongModeOn() ? MF_CHECKED : 0), ID_TRAY_SONG, L"Vocode to song");
    }
    AppendMenuW(m, MF_STRING | (gNsOn ? MF_CHECKED : 0), ID_TRAY_NS, L"Noise suppression");
    AppendMenuW(m, MF_STRING | (gGateMode != GATE_OFF ? MF_CHECKED : 0), ID_TRAY_GATE, L"Noise gate");
    AppendMenuW(m, MF_SEPARATOR, 0, nullptr);
    HMENU prof = CreatePopupMenu(), chr = CreatePopupMenu(), page = CreatePopupMenu();
    for (int i = 0; i < gProfCount; i++) AppendMenuW(prof, MF_STRING | (i == gProfCur ? MF_CHECKED : 0), 1200 + i, gProfNames[i]);
    if (!gProfCount) AppendMenuW(prof, MF_STRING | MF_GRAYED, 0, L"(save one on the Settings tab)");
    for (int i = 1; i < CHAR_N; i++) AppendMenuW(chr, MF_STRING, 1220 + i, CHARACTERS[i]);
    for (int i = 0; i < PAD_BANKS; i++) { wchar_t t[16]; wsprintfW(t, L"Page %c", L'A' + i); AppendMenuW(page, MF_STRING | (i == gPadBank ? MF_CHECKED : 0), 1260 + i, t); }
    AppendMenuW(m, MF_POPUP, (UINT_PTR)prof, L"Profile");
    if (gFeatFx) AppendMenuW(m, MF_POPUP, (UINT_PTR)chr, L"Character"); else DestroyMenu(chr);
    if (gFeatSound) AppendMenuW(m, MF_POPUP, (UINT_PTR)page, L"Soundboard page"); else DestroyMenu(page);
    AppendMenuW(m, MF_STRING | (gOverlayOn ? MF_CHECKED : 0), 1270, L"Status overlay");
    AppendMenuW(m, MF_STRING | (gCompact ? MF_CHECKED : 0), 1271, L"Compact window");
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
    const wchar_t* modeNames[] = { L"Off", L"Effect only", L"Everything", L"Clean voice", L"Apps only" };

    // Tabs (always visible). Drawn by DrawTab().
    gBuildPage = -1;
    {
        const wchar_t* tabNames[TAB_COUNT] = { L"Main", L"Mic", L"Voice FX", L"Soundboard", L"Clips", L"Settings", L"Mixer" };
        for (int slot = 0; slot < TAB_SHOWN; slot++) {   // (PlaceTabs sets where: only the ones in use show)
            const int t = TAB_ORDER[slot];
            Ctl(L"BUTTON", tabNames[t], BS_OWNERDRAW | WS_TABSTOP, 14 + slot * 76, 10, 74, 32, IDC_TAB0 + t);
            gDesign[gDesignN - 1].free = true;
        }
    }

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
        Ctl(L"STATIC", lbl, SS_OWNERDRAW | SS_NOTIFY, 28, y, 50, 24, IDC_ROWLBL + k);   // name + a little level meter
        HWND dev = Ctl(L"COMBOBOX", L"", COMBO, 80, y, 234, 300, IDC_ROWDEV + k);
        SendMessageW(dev, CB_SETDROPPEDWIDTH, 420, 0);       // the open list shows full device names
        HWND mc = Ctl(L"COMBOBOX", L"", COMBO, 320, y, 106, 200, IDC_ROWMODE + k);
        for (const wchar_t* n : modeNames) SendMessageW(mc, CB_ADDSTRING, 0, (LPARAM)n);
        SendMessageW(mc, CB_SETCURSEL, ModeToSel(gRowMode[k]), 0);
        Spin(IDC_ROWVOL + k, 432, y, 68, 0, 200, gRowVol[k]);
        Ctl(L"BUTTON", L"×", WS_TABSTOP, 506, y, 24, 23, IDC_ROWDEL + k);
    }
    Ctl(L"BUTTON", L"+ Add output", WS_TABSTOP, 30, 170, 124, 28, IDC_ADDOUT);
    Ctl(L"BUTTON", L"Use VB-Cable", WS_TABSTOP, 162, 170, 124, 28, IDC_VBCABLE);
    gBuildFeat = FEAT_SOUND | FEAT_CLIPS;       // (the soundboard and clips: hearing them yourself)
    Ctl(L"STATIC", L"Always hear sounds on:", SS_NOTIFY, 298, 175, 132, 20, IDC_HEARLBL);
    Ctl(L"COMBOBOX", L"", COMBO, 432, 171, 102, 200, IDC_HEARON);
    gBuildFeat = 0;
    FillDevices();

    gRecordShift = true;                        // everything below on this page moves with the output list
    gBuildFeat = FEAT_LAG;                      // the stutter (Settings > Features > Lag effect)

    // Effect
    AddSection(14, 232, 532, 148, L"Effect");
    Ctl(L"STATIC", L"Loop length:", 0, 30, 255, 104, 20, -1);
    Spin(IDC_LOOP, 136, 252, 76, 10, 2000, gLoopMs);
    Ctl(L"STATIC", L"ms", 0, 218, 255, 40, 20, -1);
    Ctl(L"STATIC", L"Speed:", 0, 290, 255, 100, 20, -1);
    Spin(IDC_SPEED, 392, 252, 76, 10, 400, gSpeedPct);
    Ctl(L"STATIC", L"%", 0, 474, 255, 40, 20, -1);

    Ctl(L"STATIC", L"Pitch:", 0, 30, 285, 104, 20, -1);
    Spin(IDC_PITCH, 136, 282, 76, 25, 400, gPitchPct);
    Ctl(L"STATIC", L"%", 0, 218, 285, 40, 20, -1);
    Ctl(L"STATIC", L"Smoothing:", 0, 290, 285, 100, 20, -1);
    Spin(IDC_FADE, 392, 282, 76, 0, 50, gFadeMs);
    Ctl(L"STATIC", L"ms", 0, 474, 285, 40, 20, -1);

    Ctl(L"BUTTON", L"Keep talking during the effect", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 315, 250, 20, IDC_TALKON);
    CheckDlgButton(gWnd, IDC_TALKON, gTalkOver ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Voice level:", 0, 290, 315, 100, 20, -1);
    Spin(IDC_TALKVOL, 392, 312, 76, 0, 200, gTalkVolPct);
    Ctl(L"STATIC", L"%", 0, 474, 315, 40, 20, -1);

    wchar_t key[120]; HotkeyName(key, 120);     // the stutter hotkey
    Ctl(L"BUTTON", key, WS_TABSTOP, 30, 341, 260, 28, IDC_HOTKEY);
    Ctl(L"BUTTON", L"Hold", BS_AUTORADIOBUTTON | WS_GROUP | WS_TABSTOP, 310, 345, 80, 20, IDC_HOLD);
    Ctl(L"BUTTON", L"Toggle", BS_AUTORADIOBUTTON, 400, 345, 100, 20, IDC_TOGGLE);
    CheckRadioButton(gWnd, IDC_HOLD, IDC_TOGGLE, gToggleMode ? IDC_TOGGLE : IDC_HOLD);

    // Extras: random lag + presets, beat sync
    AddSection(14, 394, 532, 90, L"Lag extras");
    Ctl(L"BUTTON", L"Random lag, every ~", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 30, 416, 140, 20, IDC_RANDLAG);
    CheckDlgButton(gWnd, IDC_RANDLAG, gRandLagOn ? BST_CHECKED : BST_UNCHECKED);
    Spin(IDC_RANDSEC, 172, 413, 54, 2, 120, gRandLagSec);
    Ctl(L"STATIC", L"s", 0, 230, 416, 12, 20, -1);
    {
        HWND lp = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 290, 412, 240, 300, IDC_LAGPRESET);
        for (int i = 0; i < LAG_PRESET_N; i++) SendMessageW(lp, CB_ADDSTRING, 0, (LPARAM)LAG_PRESETS[i].name);
        SendMessageW(lp, CB_SETCURSEL, 0, 0);
    }
    Ctl(L"BUTTON", L"Sync the loop to", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 30, 450, 124, 20, IDC_BEATSYNC);
    CheckDlgButton(gWnd, IDC_BEATSYNC, gBeatSync ? BST_CHECKED : BST_UNCHECKED);
    Spin(IDC_BPM, 156, 447, 60, 40, 300, gBpm);
    Ctl(L"STATIC", L"BPM, every", 0, 222, 450, 66, 20, -1);
    {
        HWND bd = Ctl(L"COMBOBOX", L"", COMBO, 290, 446, 120, 200, IDC_BEATDIV);
        const wchar_t* divs[] = { L"1/4 note", L"1/8 note", L"1/16 note", L"1/32 note" };
        for (const wchar_t* n : divs) SendMessageW(bd, CB_ADDSTRING, 0, (LPARAM)n);
        SendMessageW(bd, CB_SETCURSEL, gBeatDiv, 0);
    }
    Ctl(L"STATIC", L"(beat repeat)", 0, 418, 450, 110, 20, IDC_HDR);

    // Status + buttons
    gBuildFeat = 0;
    gStatus = Ctl(L"STATIC", L"", SS_OWNERDRAW | SS_NOTIFY | WS_GROUP, 14, 498, 532, 30, IDC_STATUS);
    Ctl(L"BUTTON", L"Start", WS_TABSTOP, 14, 540, 127, 34, IDC_START);
    Ctl(L"BUTTON", L"Mute mic", WS_TABSTOP, 149, 540, 127, 34, IDC_MUTEBTN);
    Ctl(L"BUTTON", L"Hide to tray", WS_TABSTOP, 284, 540, 127, 34, IDC_TRAY);
    Ctl(L"BUTTON", L"Help && setup", WS_TABSTOP, 419, 540, 127, 34, IDC_HELPBTN);

    gRecordShift = false;

    // ---------------- Mic page ----------------
    // Live meter, then AI noise suppression, noise gate and voice quality sections.
    gBuildPage = PAGE_MIC;
    Ctl(L"STATIC", L"", SS_OWNERDRAW | SS_NOTIFY, 14, 56, 532, 52, IDC_METER);
    Ctl(L"BUTTON", L"Cleanup", BS_OWNERDRAW | WS_TABSTOP | WS_GROUP, 14, 116, 90, 28, IDC_MICSUB0);
    Ctl(L"BUTTON", L"Tone", BS_OWNERDRAW | WS_TABSTOP, 108, 116, 90, 28, IDC_MICSUB1);
    {
        const int MIC_Y0 = 160, MIC_STEP = 146, MIC_H = 126;
        int y = MIC_Y0;                         // noise suppression
        gBuildSub = 0;
        AddSection(14, y, 532, MIC_H, L"Noise suppression (AI)");
        for (int i = 0; i < KNOB_N; i++)
            if (gKnobs[i].group == KG_NS) Ctl(L"LagKnob", L"", WS_TABSTOP | WS_GROUP, 26, y + 14, KNOB_W, KNOB_H, IDC_KNOB + i);
        Ctl(L"STATIC", L"Removes background noise like fans, keyboards, hum and room echo, "
                       L"and keeps your voice. Uses RNNoise. Adds about 20 ms of delay.", 0, 134, y + 24, 284, 74, IDC_HDR);
        Ctl(L"BUTTON", L"On", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 430, y + 16, 100, 20, IDC_NSON);
        CheckDlgButton(gWnd, IDC_NSON, gNsOn ? BST_CHECKED : BST_UNCHECKED);

        y += MIC_STEP;                          // noise gate
        AddSection(14, y, 532, MIC_H, L"Noise gate");
        int col = 0;
        for (int i = 0; i < KNOB_N; i++) {
            if (gKnobs[i].group != KG_GATE) continue;
            Ctl(L"LagKnob", L"", WS_TABSTOP | (col == 0 ? WS_GROUP : 0), 22 + col * 80, y + 14, 80, KNOB_H, IDC_KNOB + i);
            col++;
        }
        Ctl(L"STATIC", L"Opens on:", 0, 430, y + 16, 100, 18, IDC_HDR);
        HWND gm = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 428, y + 36, 104, 200, IDC_GATEMODE);
        const wchar_t* gateNames[] = { L"Off", L"Volume", L"Voice", L"Volume + voice" };
        for (const wchar_t* n : gateNames) SendMessageW(gm, CB_ADDSTRING, 0, (LPARAM)n);
        SendMessageW(gm, CB_SETCURSEL, gGateMode, 0);
        SendMessageW(gm, CB_SETDROPPEDWIDTH, 130, 0);
        Ctl(L"STATIC", L"Hover any knob for help.", 0, 430, y + 70, 104, 36, IDC_HDR);

        y += MIC_STEP;                          // push-to-talk (Cleanup sub-tab)
        AddSection(14, y, 532, 92, L"Push-to-talk");
        {
            HWND pm = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 30, y + 22, 160, 200, IDC_PTTMODE);
            const wchar_t* ptt[] = { L"Off (mic always on)", L"Push-to-talk", L"Push-to-mute" };
            for (const wchar_t* n : ptt) SendMessageW(pm, CB_ADDSTRING, 0, (LPARAM)n);
            SendMessageW(pm, CB_SETCURSEL, gPttMode, 0);
            wchar_t kn[120]; FxKeyButtonText(SLOT_PTT, kn, 120);
            Ctl(L"BUTTON", kn, WS_TABSTOP, 198, y + 20, 160, 28, IDC_PTTKEY);
            Ctl(L"STATIC", L"Push-to-talk: your mic only goes through while the key is held. Push-to-mute: held = muted.",
                0, 30, y + 56, 500, 30, IDC_HDR);
        }

        y = MIC_Y0;                             // voice quality (Tone sub-tab)
        gBuildSub = 1;
        AddSection(14, y, 532, MIC_H, L"Voice quality");
        col = 0;
        for (int i = 0; i < KNOB_N; i++) {
            if (gKnobs[i].group != KG_TONE) continue;
            Ctl(L"LagKnob", L"", WS_TABSTOP | (col == 0 ? WS_GROUP : 0), 26 + col * 98, y + 14, KNOB_W, KNOB_H, IDC_KNOB + i);
            col++;
        }
        Ctl(L"BUTTON", L"Broadcast voice", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 430, y + 16, 110, 20, IDC_BROADCAST);
        CheckDlgButton(gWnd, IDC_BROADCAST, gBroadcast ? BST_CHECKED : BST_UNCHECKED);
        Ctl(L"STATIC", L"Tight, clear radio-host sound.", 0, 432, y + 40, 104, 40, IDC_HDR);

        y += MIC_STEP;                          // 5-band EQ
        AddSection(14, y, 532, MIC_H, L"Equalizer");
        col = 0;
        for (int i = 0; i < KNOB_N; i++) {
            if (gKnobs[i].group != KG_EQ) continue;
            Ctl(L"LagKnob", L"", WS_TABSTOP | (col == 0 ? WS_GROUP : 0), 22 + col * 80, y + 14, 80, KNOB_H, IDC_KNOB + i);
            col++;
        }
        Ctl(L"BUTTON", L"Flat", WS_TABSTOP | WS_GROUP, 430, y + 16, 100, 26, IDC_EQRESET);
        Ctl(L"STATIC", L"Bass 100 Hz, low mid 400, mid 1.2k, presence 3.5k, treble 8k.", 0, 432, y + 50, 104, 60, IDC_HDR);
        gBuildSub = -1;
    }
    gBuildSub = -1;
    Ctl(L"BUTTON", L"\x25CF  Record 5 s", WS_TABSTOP | WS_GROUP, 14, 556, 128, 30, IDC_MICTEST);
    Ctl(L"BUTTON", L"\x25B6  Play again", WS_TABSTOP, 148, 556, 110, 30, IDC_MICPLAY);
    EnableWindow(GetDlgItem(gWnd, IDC_MICPLAY), FALSE);
    Ctl(L"STATIC", L"Mic test: talk for 5 seconds, then hear exactly what Discord hears (with all your effects), "
                   L"on your speakers or headphones.", 0, 268, 556, 278, 32, IDC_HDR);

    // ---------------- Voice FX page ----------------
    // Master switch, then one section per effect: knobs on the left, on/off + reset on the right.
    // Sections stack downward (FX_SEC_STEP apart); there's room below for more effects.
    gBuildPage = PAGE_FX;
    Ctl(L"BUTTON", L"Voice effects", BS_OWNERDRAW | WS_TABSTOP, 14, 52, 290, 44, IDC_FXON);
    Ctl(L"BUTTON", L"Vocode to song", BS_OWNERDRAW | WS_TABSTOP, 310, 52, 116, 44, IDC_SONGBTN);
    {
        wchar_t kn[120]; FxKeyButtonText(0, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 432, 52, 114, 28, IDC_FXKEY_MASTER);
        Ctl(L"BUTTON", L"Hold to use", BS_AUTOCHECKBOX | WS_TABSTOP, 436, 83, 110, 18, IDC_FXHOLD);
        CheckDlgButton(gWnd, IDC_FXHOLD, gFxHold[0] ? BST_CHECKED : BST_UNCHECKED);
    }
    // sub-tabs (three effects each) and the Characters menu
    for (int t = 0; t < FX_SUBS; t++)
        Ctl(L"BUTTON", FX_SUB_NAMES[t], BS_OWNERDRAW | WS_TABSTOP | (t == 0 ? WS_GROUP : 0), 14 + t * 76, 104, 72, 28, IDC_FXSUB0 + t);
    Ctl(L"STATIC", L"Character:", 0, 16, 514, 66, 18, -1);
    {
        HWND ch = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 84, 510, 160, 500, IDC_FXCHAR);
        SendMessageW(ch, CB_SETDROPPEDWIDTH, 200, 0);
        MyCharsScan();
        FillCharCombo();
    }

    Ctl(L"BUTTON", L"Surprise me", WS_TABSTOP, 252, 509, 104, 26, IDC_SURPRISE);
    Ctl(L"BUTTON", L"Hold: hear without effects", WS_TABSTOP, 362, 509, 184, 26, IDC_ABTEST);
    SetWindowSubclass(GetDlgItem(gWnd, IDC_ABTEST), AbButtonProc, 1, 0);
    {                                           // Fun sub-tab: hotkey tricks (work without Voice effects on)
        gBuildSub = 6;
        int y = 144 + 120;
        AddSection(14, y, 532, 110, L"Hotkey tricks");
        wchar_t kn[120];
        FxKeyButtonText(SLOT_REWIND, kn, 120);   Ctl(L"BUTTON", kn, WS_TABSTOP | WS_GROUP, 26, y + 14, 250, 28, IDC_REWINDKEY);
        FxKeyButtonText(SLOT_REPEAT, kn, 120);   Ctl(L"BUTTON", kn, WS_TABSTOP, 282, y + 14, 250, 28, IDC_REPEATKEY);
        FxKeyButtonText(SLOT_TAPESTOP, kn, 120); Ctl(L"BUTTON", kn, WS_TABSTOP, 26, y + 46, 250, 28, IDC_TAPEKEY);
        FxKeyButtonText(SLOT_DIVE, kn, 120);     Ctl(L"BUTTON", kn, WS_TABSTOP, 282, y + 46, 186, 28, IDC_DIVEKEY);
        HWND dv = Ctl(L"COMBOBOX", L"", COMBO, 472, y + 48, 60, 300, IDC_DIVESEMIS);
        static const int diveOpts[] = { -12, -7, -5, 5, 7, 12 };
        int sel = 0;
        for (int i = 0; i < 6; i++) {
            wchar_t t[16]; wsprintfW(t, L"%s%d st", diveOpts[i] > 0 ? L"+" : L"", diveOpts[i]);   // wsprintf has no %+d
            SendMessageW(dv, CB_ADDSTRING, 0, (LPARAM)t);
            if (diveOpts[i] == gDiveSemis) sel = i;
        }
        SendMessageW(dv, CB_SETCURSEL, sel, 0);
        Ctl(L"STATIC", L"These work any time audio is running, even with Voice effects off. Right-click a button to clear its hotkey.",
            0, 28, y + 80, 500, 28, IDC_HDR);
        y += 120;                               // Rewind: how it sounds
        AddSection(14, y, 532, 110, L"Rewind");
        Ctl(L"STATIC", L"Length:", 0, 30, y + 25, 60, 20, -1);
        Spin(IDC_RWLEN, 92, y + 22, 76, 300, 3500, gRewindMs);
        Ctl(L"STATIC", L"ms", 0, 172, y + 25, 30, 20, -1);
        Ctl(L"STATIC", L"Top speed:", 0, 230, y + 25, 76, 20, -1);
        Spin(IDC_RWTOP, 308, y + 22, 70, 100, 800, gRewindTop);
        Ctl(L"STATIC", L"%", 0, 382, y + 25, 20, 20, -1);
        Ctl(L"STATIC", L"Speed-up:", 0, 30, y + 57, 60, 20, -1);
        Spin(IDC_RWRAMP, 92, y + 54, 76, 0, 100, gRewindRamp);
        Ctl(L"STATIC", L"% of it", 0, 172, y + 57, 54, 20, -1);
        Ctl(L"STATIC", L"Pitch:", 0, 230, y + 57, 76, 20, -1);
        Spin(IDC_RWPITCH, 308, y + 54, 70, -12, 12, gRewindPitch);
        Ctl(L"STATIC", L"semitones", 0, 382, y + 57, 80, 20, -1);
        Ctl(L"STATIC", L"How far back, how fast it spins, how soon it gets there, and how high.", 0, 30, y + 86, 500, 18, IDC_HDR);
        gBuildSub = -1;
    }
    const int FX_SEC_Y0 = 144, FX_SEC_STEP = 120, FX_SEC_H = 110, FX_KNOB_H = 96;
    for (int g = 0; g < FX_GROUPS; g++) {
        int y = FX_SEC_Y0 + FX_SEC_STEP * gFxGroups[g].slot;
        gBuildSub = gFxGroups[g].sub;
        AddSection(14, y, 532, FX_SEC_H, gFxGroups[g].title);
        int kx = 26, kstep = 98, kw = KNOB_W;
        if (g == KG_VOCODER) {                  // dropdowns on the left, narrower knobs after them
            // three dropdowns stacked: style, key + scale, voice range (hover each for help)
            HWND st = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 26, y + 10, 152, 300, IDC_VOCSTYLE);
            const wchar_t* styleNames[VOC_STYLES] = { L"Tune", L"Tune + harmony", L"Robot", L"Choir", L"Song (vocode music)" };
            for (const wchar_t* n : styleNames) SendMessageW(st, CB_ADDSTRING, 0, (LPARAM)n);
            SendMessageW(st, CB_SETCURSEL, gVocStyle, 0);
            HWND ky = Ctl(L"COMBOBOX", L"", COMBO, 26, y + 40, 56, 300, IDC_VOCKEY);
            const wchar_t* keyNames[12] = { L"C", L"C#", L"D", L"D#", L"E", L"F", L"F#", L"G", L"G#", L"A", L"A#", L"B" };
            for (const wchar_t* n : keyNames) SendMessageW(ky, CB_ADDSTRING, 0, (LPARAM)n);
            SendMessageW(ky, CB_SETCURSEL, gVocKey, 0);
            HWND sc = Ctl(L"COMBOBOX", L"", COMBO, 86, y + 40, 92, 300, IDC_VOCSCALE);
            const wchar_t* scaleNames[VOC_SCALES] = { L"Chromatic", L"Major", L"Minor", L"Major pentatonic", L"Minor pentatonic", L"Blues" };
            for (const wchar_t* n : scaleNames) SendMessageW(sc, CB_ADDSTRING, 0, (LPARAM)n);
            SendMessageW(sc, CB_SETCURSEL, gVocScale, 0);
            SendMessageW(sc, CB_SETDROPPEDWIDTH, 140, 0);
            HWND vr = Ctl(L"COMBOBOX", L"", COMBO, 26, y + 70, 152, 300, IDC_VOCRANGE);
            const wchar_t* rangeNames[3] = { L"Voice: Auto", L"Voice: High", L"Voice: Low / deep" };
            for (const wchar_t* n : rangeNames) SendMessageW(vr, CB_ADDSTRING, 0, (LPARAM)n);
            SendMessageW(vr, CB_SETCURSEL, gVocRange, 0);
            HWND ss = Ctl(L"COMBOBOX", L"", COMBO, 26, y + 40, 152, 300, IDC_SONGSRC);   // Song style only
            SendMessageW(ss, CB_SETDROPPEDWIDTH, 220, 0);
            FillSongSources();
            Ctl(L"STATIC", L"", 0, 28, y + 68, 150, 34, IDC_SONGSTATUS);
            if (gSongUseFile && gSongFile[0]) LoadSongFile(gSongFile, true);   // reload last time's song, quietly
            kx = 186; kstep = 80; kw = 80;
        } else if (g == KG_RADIO) {             // preset dropdown + a line about it
            Ctl(L"STATIC", L"Preset", 0, 28, y + 10, 150, 16, IDC_HDR);
            HWND rp = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 26, y + 27, 152, 300, IDC_RADIOPRESET);
            for (int i = 0; i < RADIO_N; i++) SendMessageW(rp, CB_ADDSTRING, 0, (LPARAM)RADIO_PRESETS[i].name);
            SendMessageW(rp, CB_SETCURSEL, gRadioPreset, 0);
            Ctl(L"STATIC", RADIO_DESC[Iclamp(gRadioPreset, 0, RADIO_N - 1)], 0, 28, y + 56, 152, 48, IDC_RADIODESC);
            kx = 186; kstep = 80; kw = 80;
        } else if (g == KG_ECHO || g == KG_DIST || g == KG_CHORUS || g == KG_MUFFLE) {   // style dropdown
            int id = g == KG_ECHO ? IDC_ECHOSTYLE : g == KG_DIST ? IDC_DISTSTYLE : g == KG_CHORUS ? IDC_CHOSTYLE : IDC_MUFSTYLE;
            Ctl(L"STATIC", L"Style", 0, 28, y + 10, 150, 16, IDC_HDR);
            HWND sc = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 26, y + 27, 152, 300, id);
            int n = 0, cur = 0;
            const wchar_t* names[8];
            if (g == KG_ECHO)   { n = ECHO_N; cur = gEchoStyle; for (int i = 0; i < n; i++) names[i] = ECHO_STYLES[i].name; }
            if (g == KG_DIST)   { n = DIST_N; cur = gDistStyle; for (int i = 0; i < n; i++) names[i] = DIST_STYLES[i].name; }
            if (g == KG_CHORUS) { n = CHO_N;  cur = gChoStyle;  for (int i = 0; i < n; i++) names[i] = CHO_STYLES[i].name; }
            if (g == KG_MUFFLE) { n = MUF_N;  cur = gMufStyle;  for (int i = 0; i < n; i++) names[i] = MUF_STYLES[i].name; }
            for (int i = 0; i < n; i++) SendMessageW(sc, CB_ADDSTRING, 0, (LPARAM)names[i]);
            SendMessageW(sc, CB_SETCURSEL, Iclamp(cur, 0, n - 1), 0);
            Ctl(L"STATIC", g == KG_ECHO   ? L"Picking a style sets the knobs to suit it."
                         : g == KG_DIST   ? L"Crush = fewer bits and a lower sample rate (8-bit)."
                         : g == KG_CHORUS ? L"Flanger = the swooshing jet sound."
                         :                  L"Bubbles only make sense underwater.",
                0, 28, y + 56, 152, 48, IDC_HDR);
            kx = 186; kstep = 80; kw = 80;
        } else if (g == KG_HARM) {              // which extra voices
            Ctl(L"STATIC", L"Voices", 0, 28, y + 10, 150, 16, IDC_HDR);
            HWND hs = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 26, y + 27, 152, 300, IDC_HARMSTYLE);
            for (int i = 0; i < HARM_N; i++) SendMessageW(hs, CB_ADDSTRING, 0, (LPARAM)HARM_STYLES[i].name);
            SendMessageW(hs, CB_SETCURSEL, Iclamp(gHarmStyle, 0, HARM_N - 1), 0);
            Ctl(L"BUTTON", HarmMuteText(), WS_TABSTOP, 26, y + 56, 152, 26, IDC_HARMMUTE);
            Ctl(L"STATIC", L"They follow your pitch.", 0, 28, y + 86, 152, 18, IDC_HDR);
            kx = 186; kstep = 80; kw = 80;
        } else if (g == KG_GENDER || g == KG_RING || g == KG_WHISPER) {   // two knobs + a note
            const wchar_t* note = g == KG_GENDER ? L"One-knob voice change: below 0 = deeper, more masculine; above 0 = higher, "
                                                   L"more feminine. Moves pitch and throat size together."
                                : g == KG_RING   ? L"Multiplies your voice by a tone. 30-60 Hz = the classic sci-fi robot / Dalek; "
                                                   L"higher = metallic and bell-like."
                                :                  L"Turns your voice into a breathy whisper, even when you talk normally. "
                                                   L"Air brightens the breath.";
            Ctl(L"STATIC", note, 0, 226, y + 14, 194, 86, IDC_HDR);
        } else if (g == KG_FORMANT) {
            Ctl(L"STATIC", L"How big your throat sounds, without changing pitch. Below 0 = bigger, deeper, "
                           L"older; above 0 = smaller, younger. Add Pitch to sound like someone else.",
                0, 226, y + 14, 194, 86, IDC_HDR);
        }
        int col = 0;
        for (int i = 0; i < KNOB_N; i++) {
            if (gKnobs[i].group != g) continue;
            Ctl(L"LagKnob", L"", WS_TABSTOP | (col == 0 ? WS_GROUP : 0), kx + col * kstep, y + 8, kw, FX_KNOB_H, IDC_KNOB + i);
            col++;
        }
        Ctl(L"BUTTON", L"On", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 430, y + 12, 46, 20, IDC_FXGRP_ON + g);
        CheckDlgButton(gWnd, IDC_FXGRP_ON + g, *gFxGroups[g].on ? BST_CHECKED : BST_UNCHECKED);
        Ctl(L"BUTTON", L"Hold", BS_AUTOCHECKBOX | WS_TABSTOP, 478, y + 12, 56, 20, IDC_FXGRP_HOLD + g);
        CheckDlgButton(gWnd, IDC_FXGRP_HOLD + g, gFxHold[1 + g] ? BST_CHECKED : BST_UNCHECKED);
        wchar_t kn[120]; FxKeyButtonText(1 + g, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 428, y + 38, 104, 26, IDC_FXGRP_KEY + g);
        Ctl(L"BUTTON", L"Reset", WS_TABSTOP, 428, y + 70, 104, 26, IDC_FXGRP_RESET + g);
    }
    gBuildSub = -1;

    // ---------------- Soundboard page ----------------
    // Pages A-D of 8 pads each, text to speech, and playback options.
    gBuildPage = PAGE_SOUND;
    Ctl(L"STATIC", L"Page:", 0, 16, 63, 40, 20, -1);
    for (int b2 = 0; b2 < PAD_BANKS; b2++)
        Ctl(L"BUTTON", L"", BS_OWNERDRAW | WS_TABSTOP | (b2 == 0 ? WS_GROUP : 0), 58 + b2 * 48, 58, 44, 28, IDC_PADBANK0 + b2);
    {
        wchar_t kn[120]; FxKeyButtonText(SLOT_PADBANK, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP | WS_GROUP, 290, 58, 256, 28, IDC_PADBANKKEY);
    }
    AddSection(14, 98, 532, 326, L"Pads");
    Ctl(L"STATIC", L"Sound", 0, 30, 112, 120, 16, IDC_HDR);
    Ctl(L"STATIC", L"Volume %", 0, 212, 112, 70, 16, IDC_HDR);
    Ctl(L"STATIC", L"Hotkey", 0, 292, 112, 110, 16, IDC_HDR);
    for (int i = 0; i < PADS; i++) {
        int y = 130 + i * 36;
        Ctl(L"BUTTON", L"", BS_OWNERDRAW | WS_TABSTOP, 30, y, 174, 30, IDC_PADPLAY + i);
        Spin(IDC_PADVOL + i, 212, y + 3, 70, 0, 200, gPads[PadSlot(i)].vol);
        wchar_t kn[120]; FxKeyButtonText(SLOT_PAD0 + i, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 290, y + 1, 110, 28, IDC_PADKEY + i);
        Ctl(L"BUTTON", L"\x22EF", WS_TABSTOP, 406, y + 1, 28, 28, IDC_PADMORE + i);
        Ctl(L"BUTTON", L"Load...", WS_TABSTOP, 440, y + 1, 58, 28, IDC_PADLOAD + i);
        Ctl(L"BUTTON", L"\x00D7", WS_TABSTOP, 504, y + 1, 26, 28, IDC_PADCLR + i);
    }
    for (int i = 0; i < PAD_N; i++)
        if (gPadFile[i][0]) PadLoad(i, gPadFile[i], true);   // reload last time's sounds (every page), quietly
    AddSection(14, 436, 532, 60, L"Text to speech");
    {
        HWND te = Ctl(L"EDIT", L"", WS_TABSTOP | ES_AUTOHSCROLL, 30, 457, 116, 24, IDC_TTSTEXT, WS_EX_CLIENTEDGE);
        Spin(IDC_TTSVOL, 150, 457, 56, 0, 200, gTtsVol);
        SendMessageW(te, EM_SETCUEBANNER, TRUE, (LPARAM)L"Type, then Enter");
        SendMessageW(te, EM_LIMITTEXT, 500, 0);
        HWND ta = Ctl(L"COMBOBOX", L"", COMBO, 212, 457, 104, 400, IDC_TTSACCENT);
        for (int i = 0; i < TTS_ACCENT_N; i++) SendMessageW(ta, CB_ADDSTRING, 0, (LPARAM)TTS_ACCENTS[i].name);
        gTtsAccent = Iclamp(gTtsAccent, 0, TTS_ACCENT_N - 1);
        SendMessageW(ta, CB_SETCURSEL, gTtsAccent, 0);
        SendMessageW(ta, CB_SETDROPPEDWIDTH, SC(180), 0);
        HWND tv = Ctl(L"COMBOBOX", L"", COMBO, 322, 457, 104, 300, IDC_TTSVOICE);
        SendMessageW(tv, CB_SETDROPPEDWIDTH, 280, 0);
        SendMessageW(tv, CB_ADDSTRING, 0, (LPARAM)L"Default voice");   // the rest arrive from the background list
        if (gTtsVoice[0]) SendMessageW(tv, CB_ADDSTRING, 0, (LPARAM)gTtsVoice);
        SendMessageW(tv, CB_SETCURSEL, gTtsVoice[0] ? 1 : 0, 0);
        { HANDLE t = CreateThread(nullptr, 0, TtsListThread, nullptr, 0, nullptr); if (t) CloseHandle(t); }
        Ctl(L"BUTTON", L"Speak", WS_TABSTOP, 432, 455, 68, 28, IDC_TTSSPEAK);
        Ctl(L"BUTTON", L"\x22EF", WS_TABSTOP, 504, 455, 26, 28, IDC_TTSMORE);   // voice settings
        Ctl(L"STATIC", L"", SS_OWNERDRAW, 30, 486, 500, 6, IDC_VOICEPROG);   // voice install progress (only while installing)
    }
    AddSection(14, 508, 532, 76, L"Playback");
    Ctl(L"STATIC", L"Volume:", 0, 30, 529, 56, 20, -1);
    Spin(IDC_PADMASTER, 88, 526, 64, 0, 200, gPadMaster);
    Ctl(L"STATIC", L"%", 0, 158, 529, 16, 20, -1);
    Ctl(L"BUTTON", L"Play through my voice effects", BS_AUTOCHECKBOX | WS_TABSTOP, 186, 529, 220, 20, IDC_PADFX);
    CheckDlgButton(gWnd, IDC_PADFX, gPadsFx ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Stop all", WS_TABSTOP, 424, 524, 106, 26, IDC_PADSTOP);
    Ctl(L"BUTTON", L"One sound at a time", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 557, 150, 20, IDC_PADCHOKE);
    CheckDlgButton(gWnd, IDC_PADCHOKE, gPadChoke ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Lower my voice while a pad plays", BS_AUTOCHECKBOX | WS_TABSTOP, 186, 557, 230, 20, IDC_PADDUCK);
    CheckDlgButton(gWnd, IDC_PADDUCK, gPadDuck ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Load folder...", WS_TABSTOP, 424, 553, 106, 26, IDC_PADFOLDER);

    // ---------------- Clips page ----------------
    gBuildPage = PAGE_CLIPS;
    AddSection(14, 60, 532, 184, L"Instant replay");
    Ctl(L"BUTTON", L"Clip it", WS_TABSTOP, 30, 82, 100, 30, IDC_CLIPNOW);
    {
        wchar_t kn[120]; FxKeyButtonText(SLOT_CLIPNOW, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 138, 83, 128, 28, IDC_CLIPNOWKEY);
    }
    Ctl(L"STATIC", L"Last", 0, 282, 89, 30, 20, -1);
    Spin(IDC_RECSECS, 314, 86, 60, 3, REC_MAX_S, gRecSeconds);
    Ctl(L"STATIC", L"seconds", 0, 380, 89, 56, 20, -1);
    Ctl(L"BUTTON", L"Stop clips", WS_TABSTOP, 446, 83, 84, 28, IDC_CLIPSTOP);
    Ctl(L"STATIC", L"Record:", 0, 30, 126, 52, 20, -1);
    {
        HWND rs = Ctl(L"COMBOBOX", L"", COMBO, 84, 122, 170, 200, IDC_RECSRC);
        int sel = 0;
        for (int k = 0; k < REC_N; k++) {
            SendMessageW(rs, CB_ADDSTRING, 0, (LPARAM)kRecNames[k]);
            if (kRecOrder[k] == gRecSource) sel = k;
        }
        SendMessageW(rs, CB_SETCURSEL, sel, 0);
    }
    Ctl(L"STATIC", L"Volume:", 0, 266, 126, 52, 20, -1);
    Spin(IDC_CLIPMASTER, 320, 123, 64, 0, 200, gClipMaster);
    Ctl(L"STATIC", L"%", 0, 390, 126, 16, 20, -1);
    Ctl(L"BUTTON", L"History...", WS_TABSTOP, 424, 121, 106, 28, IDC_CLIPHIST);
    Ctl(L"STATIC", L"", 0, 30, 156, 500, 34, IDC_RECSTATUS);
    Ctl(L"BUTTON", L"Cut silence off new clips", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 30, 196, 190, 20, IDC_CLIPAUTOTRIM);
    CheckDlgButton(gWnd, IDC_CLIPAUTOTRIM, gClipAutoTrim ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Play clips through my voice effects", BS_AUTOCHECKBOX | WS_TABSTOP, 236, 196, 260, 20, IDC_CLIPFX);
    CheckDlgButton(gWnd, IDC_CLIPFX, gClipsFx ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Also save my voice and the other sound separately", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 218, 330, 20, IDC_CLIPSEP);
    CheckDlgButton(gWnd, IDC_CLIPSEP, gClipSeparate ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"When full, replace the oldest", BS_AUTOCHECKBOX | WS_TABSTOP, 362, 218, 178, 20, IDC_CLIPREPLACE);
    CheckDlgButton(gWnd, IDC_CLIPREPLACE, gClipReplace ? BST_CHECKED : BST_UNCHECKED);
    AddSection(14, 254, 532, 330, L"Clips");
    Ctl(L"STATIC", L"Clip", 0, 30, 270, 120, 16, IDC_HDR);
    Ctl(L"STATIC", L"Volume %", 0, 212, 270, 70, 16, IDC_HDR);
    Ctl(L"STATIC", L"Page:", 0, 300, 270, 40, 16, IDC_HDR);
    for (int b2 = 0; b2 < CLIP_BANKS; b2++)
        Ctl(L"BUTTON", L"", BS_OWNERDRAW | WS_TABSTOP | (b2 == 0 ? WS_GROUP : 0), 342 + b2 * 47, 264, 43, 24, IDC_CLIPBANK0 + b2);
    for (int i = 0; i < CLIPS; i++) {
        int y = 292 + i * 36;
        Ctl(L"BUTTON", L"", BS_OWNERDRAW | WS_TABSTOP | WS_GROUP, 30, y, 174, 30, IDC_CLIPPLAY + i);
        Spin(IDC_CLIPVOL + i, 212, y + 3, 70, 0, 200, gPads[CLIP0 + ClipSlot(i)].vol);
        wchar_t kn[120]; FxKeyButtonText(SLOT_CLIP0 + i, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 290, y + 1, 110, 28, IDC_CLIPKEY + i);
        Ctl(L"BUTTON", L"\x22EF", WS_TABSTOP, 406, y + 1, 28, 28, IDC_CLIPMORE + i);
        Ctl(L"BUTTON", L"Trim...", WS_TABSTOP, 440, y + 1, 58, 28, IDC_CLIPTRIM + i);
        Ctl(L"BUTTON", L"\x00D7", WS_TABSTOP, 504, y + 1, 26, 28, IDC_CLIPCLR + i);
    }
    for (int c = 0; c < CLIP_N; c++)
        if (gPadFile[CLIP0 + c][0]) PadLoad(CLIP0 + c, gPadFile[CLIP0 + c], true);   // last time's clips (every page), quietly

    // ---------------- Settings page ----------------
    gBuildPage = PAGE_SETTINGS;

    Ctl(L"BUTTON", L"General", BS_OWNERDRAW | WS_TABSTOP | WS_GROUP, 14, 52, 90, 26, IDC_SETSUB0);
    Ctl(L"BUTTON", L"Look", BS_OWNERDRAW | WS_TABSTOP, 108, 52, 90, 26, IDC_SETSUB1);
    Ctl(L"BUTTON", L"Pictures", BS_OWNERDRAW | WS_TABSTOP, 202, 52, 90, 26, IDC_SETSUB2);
    Ctl(L"BUTTON", L"Features", BS_OWNERDRAW | WS_TABSTOP, 296, 52, 90, 26, IDC_SETSUB3);
    gBuildSub = 0;
    AddSection(14, 88, 532, 108, L"Profiles");
    Ctl(L"STATIC", L"Profile:", 0, 30, 110, 56, 20, -1);
    {
        HWND pc = Ctl(L"COMBOBOX", L"", CBS_DROPDOWN | CBS_AUTOHSCROLL | WS_VSCROLL | WS_TABSTOP | WS_GROUP, 88, 106, 214, 300, IDC_PROFILE);
        SendMessageW(pc, CB_LIMITTEXT, 40, 0);
        COMBOBOXINFO ci = {}; ci.cbSize = sizeof(ci);
        if (GetComboBoxInfo(pc, &ci) && ci.hwndItem) SendMessageW(ci.hwndItem, EM_SETCUEBANNER, TRUE, (LPARAM)L"Name, e.g. Gaming");
    }
    Ctl(L"BUTTON", L"Save", WS_TABSTOP, 310, 105, 106, 26, IDC_PROFSAVE);
    Ctl(L"BUTTON", L"Delete", WS_TABSTOP, 424, 105, 106, 26, IDC_PROFDEL);
    Ctl(L"BUTTON", L"", WS_TABSTOP, 30, 136, 248, 26, IDC_PROFKEY);
    {
        wchar_t kn[120]; FxKeyButtonText(SLOT_PROFNEXT, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 284, 136, 246, 26, IDC_PROFNEXTKEY);
    }
    Ctl(L"BUTTON", L"Use for an app...", WS_TABSTOP, 30, 166, 140, 24, IDC_PROFAUTO);
    Ctl(L"STATIC", L"", 0, 178, 170, 352, 18, IDC_PROFAUTOINFO);
    {
        wchar_t cur[64]; GetPrivateProfileStringW(L"settings", L"profile_current", L"", cur, 64, gIni);
        ProfilesScan();
        ProfileAppsLoad();
        for (int i = 0; i < gProfCount; i++) if (!lstrcmpiW(gProfNames[i], cur)) gProfCur = i;
        ProfilesFill(gProfCur >= 0 ? gProfNames[gProfCur] : nullptr);
        ProfileAutoInfo();
    }

    AddSection(14, 210, 532, 52, L"Latency");
    Ctl(L"STATIC", L"Buffer:", 0, 30, 231, 90, 20, -1);
    HWND buf = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 124, 227, 168, 200, IDC_BUFFER);
    const wchar_t* bufNames[] = { L"32 (fastest)", L"64", L"128 (default)", L"256", L"512 (safest)" };
    for (const wchar_t* n : bufNames) SendMessageW(buf, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(buf, CB_SETCURSEL, gBufIdx, 0);
    Ctl(L"BUTTON", L"Exclusive mode", BS_AUTOCHECKBOX | WS_TABSTOP, 310, 230, 220, 20, IDC_EXCL);
    CheckDlgButton(gWnd, IDC_EXCL, gExclusive ? BST_CHECKED : BST_UNCHECKED);

    AddSection(14, 276, 532, 108, L"App");
    Ctl(L"BUTTON", L"Start audio && hide in tray when opened", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 298, 270, 20, IDC_AUTO);
    CheckDlgButton(gWnd, IDC_AUTO, gAutoStart ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Export...", WS_TABSTOP, 330, 294, 96, 26, IDC_EXPORT);
    Ctl(L"BUTTON", L"Import...", WS_TABSTOP, 434, 294, 96, 26, IDC_IMPORT);
    Ctl(L"STATIC", L"Updates:", 0, 30, 329, 60, 20, -1);
    HWND repo = Ctl(L"EDIT", gUpdateRepo, WS_TABSTOP | ES_AUTOHSCROLL, 94, 326, 200, 24, IDC_REPO, WS_EX_CLIENTEDGE);
    SendMessageW(repo, EM_SETCUEBANNER, TRUE, (LPARAM)L"github-user/repo");
    if (gFramedN < MAX_FRAMED) gFramed[gFramedN++] = { repo, nullptr };
    Ctl(L"BUTTON", L"Check now", WS_TABSTOP, 302, 325, 100, 26, IDC_CHECKUPD);
    Ctl(L"BUTTON", L"On startup", BS_AUTOCHECKBOX | WS_TABSTOP, 412, 328, 118, 20, IDC_UPDSTART);
    CheckDlgButton(gWnd, IDC_UPDSTART, gUpdateOnStart ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Lag Effect " APP_VERSION L"  \x00B7  settings are in %APPDATA%\\LagEffect", SS_NOTIFY, 30, 360, 400, 18, IDC_VERSION);
    Ctl(L"BUTTON", L"Open folder", WS_TABSTOP, 446, 356, 84, 24, IDC_OPENSET);

    AddSection(14, 398, 532, 70, L"Screen share");
    Ctl(L"BUTTON", L"Hide from screen share", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 418, 300, 20, IDC_HIDESHARE);
    CheckDlgButton(gWnd, IDC_HIDESHARE, gHideShare ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Stops screen shares picking up your voice twice (hover for more).", 0, 30, 442, 500, 18, IDC_HDR);

    AddSection(14, 482, 532, 104, L"Shortcuts & window");      // painted text: a single & shows as &
    Ctl(L"STATIC", L"Mute hotkey:", 0, 30, 503, 90, 20, -1);
    {
        wchar_t kn[120]; FxKeyButtonText(SLOT_MUTE, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 122, 499, 124, 26, IDC_MUTEKEY);
    }
    Ctl(L"BUTTON", L"Pop-up on hotkeys", BS_AUTOCHECKBOX | WS_TABSTOP, 262, 503, 140, 20, IDC_OSD);
    CheckDlgButton(gWnd, IDC_OSD, gShowOsd ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Beep on hotkeys", BS_AUTOCHECKBOX | WS_TABSTOP, 408, 503, 126, 20, IDC_BEEPS);
    CheckDlgButton(gWnd, IDC_BEEPS, gBeeps ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Always on top", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 531, 200, 20, IDC_TOPMOST);
    CheckDlgButton(gWnd, IDC_TOPMOST, gTopMost ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Start with Windows", BS_AUTOCHECKBOX | WS_TABSTOP, 262, 531, 270, 20, IDC_STARTWIN);
    CheckDlgButton(gWnd, IDC_STARTWIN, StartWithWindows() ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Status overlay (over games)", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 557, 220, 20, IDC_OVERLAY);
    CheckDlgButton(gWnd, IDC_OVERLAY, gOverlayOn ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"BUTTON", L"Compact window (Ctrl+M)", WS_TABSTOP, 262, 554, 268, 26, IDC_COMPACT);

    // ---- Features ----
    gBuildSub = 3;
    AddSection(14, 88, 532, 300, L"Features");
    Ctl(L"STATIC", L"Turn on only what you use. A feature that's off is hidden and doesn't run at all, so it costs nothing.",
        0, 30, 110, 500, 36, IDC_HDR);
    {
        struct { int id; const wchar_t* name; const wchar_t* what; bool on; } f[] = {
            { IDC_FEATLAG,   L"Lag effect", L"Hold a hotkey to stutter your voice. Its settings are on the Main tab.", gFeatLag },
            { IDC_FEATFX,    L"Voice FX", L"Effects for your live voice, characters and Vocode to song. Adds a tab.", gFeatFx },
            { IDC_FEATSOUND, L"Soundboard", L"Sounds on hotkeys, and text to speech. Adds a tab.", gFeatSound },
            { IDC_FEATCLIPS, L"Clips", L"Keeps the last few seconds so you can save them as a clip. Adds a tab.", gFeatClips },
        };
        for (int i = 0; i < 4; i++) {
            const int y = 156 + i * 56;
            Ctl(L"BUTTON", f[i].name, BS_AUTOCHECKBOX | WS_TABSTOP | (i == 0 ? WS_GROUP : 0), 30, y, 160, 20, f[i].id);
            CheckDlgButton(gWnd, f[i].id, f[i].on ? BST_CHECKED : BST_UNCHECKED);
            Ctl(L"STATIC", f[i].what, 0, 50, y + 22, 480, 18, IDC_HDR);
        }
    }
    AddSection(14, 402, 532, 132, L"Remote control (Streamer.bot)");
    Ctl(L"BUTTON", L"Let apps on this PC control Lag Effect (like Streamer.bot)", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 30, 424, 420, 20, IDC_WSON);
    CheckDlgButton(gWnd, IDC_WSON, gWsOn ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Port:", 0, 30, 456, 40, 20, -1);
    Spin(IDC_WSPORT, 72, 453, 86, 1024, 65535, gWsPort);
    Ctl(L"STATIC", L"Password (optional):", 0, 176, 456, 130, 20, -1);
    Ctl(L"EDIT", gWsPass, ES_AUTOHSCROLL | WS_TABSTOP, 308, 453, 120, 23, IDC_WSPASS);
    SendDlgItemMessageW(gWnd, IDC_WSPASS, EM_LIMITTEXT, 60, 0);
    Ctl(L"STATIC", L"", SS_NOPREFIX | SS_ENDELLIPSIS, 30, 492, 250, 20, IDC_WSSTATUS);
    Ctl(L"BUTTON", L"How to use...", WS_TABSTOP, 288, 486, 118, 28, IDC_WSGUIDE);
    Ctl(L"BUTTON", L"Copy C# code", WS_TABSTOP, 412, 486, 118, 28, IDC_WSHELP);

    // ---- Look ----
    gBuildSub = 1;
    AddSection(14, 88, 532, 96, L"Theme");
    Ctl(L"STATIC", L"Theme:", 0, 30, 111, 50, 20, -1);
    HWND th = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 82, 107, 92, 200, IDC_THEME);
    const wchar_t* themeNames[] = { L"System", L"Light", L"Dark" };
    for (const wchar_t* n : themeNames) SendMessageW(th, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(th, CB_SETCURSEL, gThemeMode, 0);
    Ctl(L"STATIC", L"Color:", 0, 184, 111, 44, 20, -1);
    HWND ct = Ctl(L"COMBOBOX", L"", COMBO | CBS_OWNERDRAWFIXED | CBS_HASSTRINGS, 228, 107, 134, 400, IDC_COLORTHEME);
    for (int i = 0; i < COLOR_THEME_N; i++) SendMessageW(ct, CB_ADDSTRING, 0, (LPARAM)COLOR_THEMES[i].name);
    SendMessageW(ct, CB_SETCURSEL, gColorTheme, 0);
    Ctl(L"STATIC", L"Size:", 0, 372, 111, 36, 20, -1);
    {
        HWND us = Ctl(L"COMBOBOX", L"", COMBO, 410, 107, 120, 200, IDC_UISCALE);
        static const int scales[] = { 100, 125, 150, 175, 200 };
        int sel = 0;
        for (int i = 0; i < 5; i++) { wchar_t t[16]; wsprintfW(t, L"%d%%", scales[i]); SendMessageW(us, CB_ADDSTRING, 0, (LPARAM)t); if (scales[i] == gUiScale) sel = i; }
        SendMessageW(us, CB_SETCURSEL, sel, 0);
    }
    Ctl(L"STATIC", L"Font:", 0, 30, 147, 44, 20, -1);
    {
        HWND fc = Ctl(L"COMBOBOX", L"", COMBO | CBS_SORT, 76, 143, 160, 300, IDC_FONT);
        SendMessageW(fc, CB_ADDSTRING, 0, (LPARAM)gFontName);   // every installed font is added when you open the list
        SendMessageW(fc, CB_SETCURSEL, 0, 0);
        Ctl(L"STATIC", L"Text size:", 0, 246, 147, 64, 20, -1);
        HWND fs = Ctl(L"COMBOBOX", L"", COMBO, 312, 143, 58, 300, IDC_FONTSIZE);
        for (int px = 11; px <= 18; px++) { wchar_t t[8]; wsprintfW(t, L"%d", px); SendMessageW(fs, CB_ADDSTRING, 0, (LPARAM)t); }
        SendMessageW(fs, CB_SETCURSEL, Iclamp(gFontPx, 11, 18) - 11, 0);
    }
    Ctl(L"STATIC", L"Opacity:", 0, 380, 147, 58, 20, -1);
    Spin(IDC_OPACITY, 440, 144, 60, 40, 100, gOpacity);
    Ctl(L"STATIC", L"%", 0, 504, 147, 16, 20, -1);

    AddSection(14, 198, 532, 148, L"Your colours");
    for (int i = 0; i < USERCOL_N; i++)
        Ctl(L"BUTTON", L"", BS_OWNERDRAW | WS_TABSTOP | (i == 0 ? WS_GROUP : 0), 30 + (i % 4) * 126, 218 + (i / 4) * 32, 120, 28, IDC_COLSW0 + i);
    Ctl(L"STATIC", L"Click: change it. Right-click: theme's colour.", 0, 30, 318, 390, 18, IDC_HDR);
    Ctl(L"BUTTON", L"Reset all", WS_TABSTOP, 430, 314, 100, 26, IDC_COLRESET);

    AddSection(14, 360, 532, 84, L"Layout");
    Ctl(L"BUTTON", L"Move things around...", WS_TABSTOP | WS_GROUP, 30, 382, 180, 28, IDC_LAYEDIT);
    Ctl(L"BUTTON", L"Put everything back", WS_TABSTOP, 218, 382, 160, 28, IDC_LAYRESET);
    Ctl(L"STATIC", L"Saved per profile: each one can have its own layout.", 0, 30, 418, 500, 18, IDC_HDR);
    gBuildSub = -1;

    // ---- Pictures ----
    gBuildSub = 2;
    AddSection(14, 88, 532, 106, L"Background picture");
    Ctl(L"BUTTON", L"Choose a picture or GIF...", WS_TABSTOP | WS_GROUP, 30, 110, 176, 28, IDC_PICCHOOSE);
    Ctl(L"BUTTON", L"Remove", WS_TABSTOP, 212, 110, 80, 28, IDC_PICREMOVE);
    Ctl(L"STATIC", L"", 0, 300, 116, 230, 18, IDC_PICINFO);
    Ctl(L"STATIC", L"Fit:", 0, 30, 150, 30, 20, -1);
    {
        HWND pf = Ctl(L"COMBOBOX", L"", COMBO, 62, 146, 150, 200, IDC_PICFIT);
        const wchar_t* fits[] = { L"Fill (crop)", L"Stretch", L"Centre", L"Tile", L"Place it yourself" };
        for (const wchar_t* n : fits) SendMessageW(pf, CB_ADDSTRING, 0, (LPARAM)n);
        SendMessageW(pf, CB_SETCURSEL, gPicFit, 0);
    }
    Ctl(L"STATIC", L"Fade:", 0, 226, 150, 40, 20, -1);
    Spin(IDC_PICDIM, 268, 147, 60, 0, 95, gPicDim);
    Ctl(L"STATIC", L"%", 0, 332, 150, 16, 20, -1);
    Ctl(L"BUTTON", L"Move && resize...", WS_TABSTOP, 352, 145, 178, 28, IDC_PICPLACE);

    AddSection(14, 208, 532, 120, L"Pictures on top");
    Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 30, 230, 226, 300, IDC_STKLIST);
    Ctl(L"BUTTON", L"Add pictures or GIFs...", WS_TABSTOP, 264, 229, 170, 28, IDC_STKADD);
    Ctl(L"BUTTON", L"Remove", WS_TABSTOP, 440, 229, 90, 28, IDC_STKDEL);
    Ctl(L"STATIC", L"Size:", 0, 30, 268, 36, 20, -1);
    Spin(IDC_STKSIZE, 68, 265, 64, 5, 400, 100);
    Ctl(L"STATIC", L"%", 0, 136, 268, 16, 20, -1);
    Ctl(L"STATIC", L"Opacity:", 0, 164, 268, 58, 20, -1);
    Spin(IDC_STKOPAC, 224, 265, 64, 5, 100, 100);
    Ctl(L"STATIC", L"%", 0, 292, 268, 16, 20, -1);
    Ctl(L"BUTTON", L"Move && resize...", WS_TABSTOP, 360, 263, 170, 28, IDC_STKMOVE);
    Ctl(L"STATIC", L"Up to 8, shown on every page and not faded.", 0, 30, 302, 500, 18, IDC_HDR);

    AddSection(14, 342, 532, 84, L"GIFs");
    Ctl(L"STATIC", L"Frame-rate limit:", 0, 30, 364, 110, 20, -1);
    {
        HWND gf = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 142, 360, 110, 200, IDC_GIFFPS);
        const wchar_t* fpsN[] = { L"10 fps", L"15 fps", L"24 fps", L"30 fps", L"60 fps", L"No limit" };
        static const int fpsV[] = { 10, 15, 24, 30, 60, 0 };
        int sel = 3;
        for (int i = 0; i < 6; i++) { SendMessageW(gf, CB_ADDSTRING, 0, (LPARAM)fpsN[i]); if (fpsV[i] == gGifFps) sel = i; }
        SendMessageW(gf, CB_SETCURSEL, sel, 0);
    }
    Ctl(L"BUTTON", L"Pause while another window is in front", BS_AUTOCHECKBOX | WS_TABSTOP, 266, 364, 264, 20, IDC_GIFPAUSE);
    CheckDlgButton(gWnd, IDC_GIFPAUSE, gGifPauseBg ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Lower = less CPU and memory (GIFs keep their speed).", 0, 30, 396, 500, 18, IDC_HDR);
    gBuildSub = -1;


    // ---------------- Mixer page ----------------
    // Strips, like a mixing desk: per channel its source, a dB fader with a stereo meter, Mute / Solo / Duck,
    // and the outputs it goes to. Below, one strip per output.
    gBuildPage = PAGE_MIXER;
    gSecChan = gSectionN;
    gBuildSub = 0;                              // (the strips: Mixer sub-view 0; its hotkeys are sub-view 1)
    AddSection(14, 54, 532, 330, L"Channels");
    gBuildSub = -1;
    Ctl(L"BUTTON", L"Hotkeys", WS_TABSTOP, 152, 62, 110, 26, IDC_MIXKEYSBTN);
    gBuildSub = 0;
    Ctl(L"BUTTON", L"+ Add channel", WS_TABSTOP, 30, 62, 116, 26, IDC_CHADDBTN);
    gMixHint   = Ctl(L"STATIC", L"No channels yet. Click \"+ Add channel\" to bring in an app (Spotify, a game, a browser...), "
                                L"another input, or what an output device plays.", SS_CENTER, 30, 160, 500, 40, IDC_MIXHINT);
    gDuckLbl   = Ctl(L"STATIC", L"Duck by", SS_RIGHT, 292, 67, 50, 18, 0);
    Spin(IDC_DUCKDB, 344, 64, 52, 3, 30, gDuckDb);
    gDuckDbLbl = Ctl(L"STATIC", L"dB", 0, 400, 67, 22, 18, 0);
    Ctl(L"BUTTON", L"Restart audio", WS_TABSTOP, 434, 62, 104, 26, IDC_RESTARTAUD);
    gBuildSub = 0;
    for (int c = 0; c < CH_MAX; c++) {
        const int x = 21 + c * 65;
        wchar_t db[24]; DbText(gCh[c].db10, db);
        Ctl(L"BUTTON", L"", BS_OWNERDRAW | WS_TABSTOP | (c == 0 ? WS_GROUP : 0), x + 1, 96, 60, 26, IDC_CHSRC0 + c);
        Ctl(L"STATIC", db, SS_CENTER | SS_NOPREFIX, x, 123, 62, 16, IDC_CHDB0 + c);
        Ctl(L"LagFader", L"", WS_TABSTOP, x + 10, 141, 22, 150, IDC_CHVOL0 + c);
        Ctl(L"STATIC", L"", SS_OWNERDRAW, x + 36, 143, 12, 146, IDC_CHMETER0 + c);
        Ctl(L"BUTTON", L"M", BS_OWNERDRAW | WS_TABSTOP, x + 4, 297, 26, 20, IDC_CHMUTE0 + c);
        Ctl(L"BUTTON", L"S", BS_OWNERDRAW | WS_TABSTOP, x + 32, 297, 26, 20, IDC_CHSOLO0 + c);
        Ctl(L"BUTTON", L"Duck", BS_OWNERDRAW | WS_TABSTOP, x + 4, 320, 54, 20, IDC_CHDUCK0 + c);
        for (int k = 0; k < MAX_OUT; k++) {
            wchar_t n[4]; wsprintfW(n, L"%d", k + 1);
            Ctl(L"BUTTON", n, BS_OWNERDRAW | WS_TABSTOP, x + 4 + k * 11, 344, 10, 18, IDC_CHRT0 + c * MAX_OUT + k);
        }
        Ctl(L"BUTTON", L"", BS_OWNERDRAW | WS_TABSTOP, x + 4, 96, 54, 268, IDC_CHADD0 + c);
    }

    gSecOut = gSectionN;
    gBuildSub = 0;
    AddSection(14, 400, 532, 184, L"Outputs");
    for (int k = 0; k < MAX_OUT; k++) {
        const int x = 21 + k * 105;
        wchar_t n[16]; wsprintfW(n, L"Out %d", k + 1);
        Ctl(L"LagFader", L"", WS_TABSTOP | (k == 0 ? WS_GROUP : 0), x + 4, 420, 20, 150, IDC_OVOL0 + k);
        Ctl(L"STATIC", L"", SS_OWNERDRAW, x + 27, 422, 8, 146, IDC_OMETER0 + k);
        Ctl(L"BUTTON", n, BS_OWNERDRAW | WS_TABSTOP, x + 40, 420, 56, 18, IDC_OLBL0 + k);
        Ctl(L"STATIC", L"", SS_NOPREFIX | SS_ENDELLIPSIS, x + 40, 439, 56, 18, IDC_ODEV0 + k);
        Ctl(L"STATIC", L"", SS_NOPREFIX, x + 40, 458, 56, 18, IDC_ODB0 + k);
        Ctl(L"STATIC", L"", SS_OWNERDRAW, x + 40, 522, 56, 16, IDC_OLIM0 + k);
        Ctl(L"BUTTON", L"M", BS_OWNERDRAW | WS_TABSTOP, x + 40, 546, 56, 22, IDC_OMUTE0 + k);
    }
    // the Mixer's hotkeys (sub-view 1): a row per channel in use and per output; MixerPlace lays it out
    gBuildSub = 1;
    gSecKeys = gSectionN;
    AddSection(14, 54, 532, 530, L"Mixer hotkeys");
    {
        static const wchar_t* cols[7] = { L"", L"Volume +", L"Volume \x2212", L"Mute", L"Solo", L"Duck", L"Hold" };
        for (int i = 1; i < 7; i++) Ctl(L"STATIC", cols[i], SS_CENTER, 30 + i * 60, 100, 58, 18, IDC_MIXKCOL0 + i);
        Ctl(L"STATIC", L"Hold does", SS_CENTER, 470, 100, 60, 18, IDC_MIXKCOL0);
        for (int r = 0; r < CH_MAX + MAX_OUT; r++) Ctl(L"STATIC", L"", SS_NOPREFIX | SS_ENDELLIPSIS, 30, 124 + r * 28, 88, 20, IDC_MIXKROW0 + r);
        for (int sl = SLOT_MIX0; sl < KEY_SLOTS; sl++) {
            wchar_t t[120]; FxKeyButtonText(sl, t, 120);
            Ctl(L"BUTTON", t, WS_TABSTOP, 30, 124, 58, 24, FxKeyButtonId(sl));
        }
        for (int c = 0; c < CH_MAX; c++) Ctl(L"BUTTON", gCh[c].holdTalk ? L"Talk" : L"Mute", BS_OWNERDRAW | WS_TABSTOP, 470, 124, 58, 24, IDC_MIXHOLDMODE0 + c);
        Ctl(L"STATIC", L"Volume keys change it by", 0, 30, 540, 160, 20, IDC_MIXKEYHDR);
        Spin(IDC_MIXSTEP, 196, 537, 56, 1, 10, gMixStep);
        Ctl(L"STATIC", L"dB a press (hold to keep going)", 0, 258, 540, 200, 20, IDC_MIXSTEPDB);
    }
    gBuildSub = -1;
    gBuildPage = -1;
    AppScanStart();                             // (icons and the apps list arrive from the background)
    for (int i = 0; i < gDesignN; i++)          // the Mixer's strips are placed by MixerPlace, not the layout
        if (gDesign[i].page == PAGE_MIXER) gDesign[i].free = true;
    for (int c = 0; c < CH_MAX; c++) FaderLabel(IDC_CHVOL0 + c);
    for (int k = 0; k < MAX_OUT; k++) FaderLabel(IDC_OVOL0 + k);

    // compact mode's own buttons (shown only in compact mode)
    gBuildPage = -1;
    ShowWindow(Ctl(L"BUTTON", L"Voice FX", WS_TABSTOP, 276, 42, 128, 34, IDC_COMPACTFX), SW_HIDE);
    ShowWindow(Ctl(L"BUTTON", L"Full window", WS_TABSTOP, 410, 42, 142, 34, IDC_COMPACTFULL), SW_HIDE);

    gBuildPage = -1;
    {                                           // the "+ Add output" row sits just under the output list
        static const int follow[] = { IDC_ADDOUT, IDC_VBCABLE, IDC_HEARLBL, IDC_HEARON };
        for (int id : follow) { HWND c = GetDlgItem(gWnd, id); for (int i = 0; i < gDesignN; i++) if (gDesign[i].h == c) gDesign[i].shifted = true; }
    }
    AssignSections();
    EnumChildWindows(gWnd, BufLabelAttach, 0);  // labels paint off-screen (no flicker over pictures)
    LayoutLoad(gIni, false);                    // where you moved things to
    gUiReady = true;
    AddTips();
    FitText();
    Layout();
}

// Color dropdown: a swatch of each theme's accent next to its name.
static void DrawColorItem(DRAWITEMSTRUCT* d)
{
    if (d->itemID == (UINT)-1) return;
    HDC dc = d->hDC;
    RECT rc = d->rcItem;
    bool sel = (d->itemState & ODS_SELECTED) && !(d->itemState & ODS_COMBOBOXEDIT);
    COLORREF bg = sel ? (gDark ? Mix(DK_CTL, ACCENT, 0.35f) : GetSysColor(COLOR_HIGHLIGHT)) : (gDark ? DK_CTL : GetSysColor(COLOR_WINDOW));
    COLORREF fg = sel && !gDark ? GetSysColor(COLOR_HIGHLIGHTTEXT) : (gDark ? DK_TEXT : GetSysColor(COLOR_WINDOWTEXT));
    HBRUSH b = CreateSolidBrush(bg); FillRect(dc, &rc, b); DeleteObject(b);
    int i = Iclamp((int)d->itemID, 0, COLOR_THEME_N - 1);
    COLORREF sw = gDark ? COLOR_THEMES[i].dark : COLOR_THEMES[i].light;
    int cy = (rc.top + rc.bottom) / 2;
    HBRUSH sb = CreateSolidBrush(sw);
    HPEN   sp = CreatePen(PS_SOLID, 1, gDark ? Mix(sw, RGB(255, 255, 255), 0.3f) : Mix(sw, RGB(0, 0, 0), 0.2f));
    HGDIOBJ ob = SelectObject(dc, sb), op = SelectObject(dc, sp);
    Ellipse(dc, rc.left + 6, cy - 6, rc.left + 18, cy + 6);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(sb); DeleteObject(sp);
    HGDIOBJ of = SelectObject(dc, gFont);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, fg);
    RECT tr = rc; tr.left += 26;
    DrawTextW(dc, COLOR_THEMES[i].name, -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_LEFT);
    SelectObject(dc, of);
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT) && !(d->itemState & ODS_COMBOBOXEDIT)) DrawFocusRect(dc, &rc);
}

// Colours for static text, buttons and text boxes (main window and the trim editor).
static LRESULT CtlColor(HWND h, UINT m, WPARAM w, LPARAM l)
{
    HDC dc = (HDC)w;
    int  cid    = GetDlgCtrlID((HWND)l);
    bool header = h == gWnd ? (cid == IDC_HDR || cid == IDC_RADIODESC || cid == IDC_SONGSTATUS || cid == IDC_RECSTATUS || cid == IDC_FXORDER)
                            : cid == IDT_HINT;  // dim helper text
    bool field  = m == WM_CTLCOLOREDIT || m == WM_CTLCOLORLISTBOX;
    if (gBrPicture && !field && h == gWnd) {    // background picture: text sits on the picture, lined up with it
        POINT pt = { 0, 0 }; MapWindowPoints((HWND)l, gWnd, &pt, 1);
        SetBrushOrgEx(dc, -pt.x, -pt.y, nullptr);
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, header ? (gDark ? DK_DIM : gLtDim) : TXT_C);
        return (LRESULT)gBrPicture;
    }
    if (!gDark) {
        if (field) return DefWindowProcW(h, m, w, l);   // text boxes and lists keep Windows' white
        SetTextColor(dc, header ? gLtDim : gUserCol[4] != CLR_NONE ? gLtText : GetSysColor(COLOR_WINDOWTEXT));
        SetBkColor(dc, gLtBg);
        return (LRESULT)gBrLightBg;
    }
    SetTextColor(dc, header ? DK_DIM : DK_TEXT);
    SetBkColor(dc, field ? DK_CTL : DK_BG);
    return (LRESULT)(field ? gBrDarkCtl : gBrDarkBg);
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
    SetTextColor(dc, active ? (TXT_C) : (gDark ? DK_DIM : RGB(105, 105, 105)));
    RECT tr = rc; tr.bottom -= 3;
    for (int lvl = 1; lvl <= 3; lvl++) {        // (seven tabs are narrower: a long name in a wide font gets a smaller size)
        SIZE sz; GetTextExtentPoint32W(dc, text, lstrlenW(text), &sz);
        if (sz.cx <= tr.right - tr.left - 6) break;
        SelectObject(dc, FitFont(lvl));
    }
    DrawTextW(dc, text, -1, &tr, DT_SINGLELINE | DT_CENTER | DT_VCENTER);
    SelectObject(dc, of);
    if (active) {
        HBRUSH ab = CreateSolidBrush(TAB_C);
        RECT bar = { rc.left + 14, rc.bottom - 3, rc.right - 14, rc.bottom };
        FillRect(dc, &bar, ab);
        DeleteObject(ab);
    }
    if ((d->itemState & ODS_FOCUS) && !(d->itemState & ODS_NOFOCUSRECT)) {
        RECT fr = rc; InflateRect(&fr, -4, -4);
        SetTextColor(dc, TXT_C);
        DrawFocusRect(dc, &fr);
    }
}

static void PaintWindow(HDC dc)
{
    int d = RowsDelta();
    SetBkMode(dc, gBrPicture ? TRANSPARENT : OPAQUE);
    HGDIOBJ oldFont = SelectObject(dc, gFontBold);
    HPEN border = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ oldPen = SelectObject(dc, border), oldBr = SelectObject(dc, GetStockObject(NULL_BRUSH));

    {                                           // line under the tabs
        HPEN sep = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : LT_BORDER);
        HGDIOBJ op = SelectObject(dc, sep);
        if (!gCompact) { MoveToEx(dc, gOrgX + SC(14), SC(42), nullptr); LineTo(dc, gOrgX + SC(CLIENT_W - 14), SC(42)); }
        SelectObject(dc, op);
        DeleteObject(sep);
    }

    for (int i = 0; i < gSectionN; i++) {       // rounded section frames with their title in the top edge
        Section& s = gSections[i];
        if (s.page >= 0 && s.page != gPage) continue;
        if (s.sub >= 0 && s.sub != (s.page == PAGE_MIC ? gMicSub : s.page == PAGE_SETTINGS ? gSetSub : s.page == PAGE_MIXER ? gMixSub : gFxSub)) continue;
        if (gCompact) continue;
        if (s.feat && !FeatOn(s.feat)) continue;   // (a feature that's off: not shown)
        int y = SC(s.y + s.oy + (s.shifts ? d : 0)), sx = SC(s.x + s.ox) + (i == gSecChan || i == gSecOut || i == gSecKeys ? 0 : gOrgX);
        RoundRect(dc, sx, y, sx + SC(s.w), y + SC(s.h), 12, 12);
        SIZE sz; GetTextExtentPoint32W(dc, s.title, lstrlenW(s.title), &sz);
        RECT tr = { sx + 10, y - sz.cy / 2, sx + 18 + sz.cx, y + sz.cy / 2 + 1 };
        FillRect(dc, &tr, BgBrush());
        SetBkColor(dc, BgColor());
        SetTextColor(dc, TITLE_C);
        TextOutW(dc, sx + 14, y - sz.cy / 2, s.title, lstrlenW(s.title));
    }
    MixerPaintStrips(dc);

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
    bool loop = gLooping || (gRunning && gMicMuted), live = gRunning;   // red while looping or muted
    COLORREF fill = loop ? (gDark ? RGB(92, 30, 34) : RGB(253, 224, 224)) : STATUS_C;
    COLORREF text = loop ? (gDark ? RGB(255, 125, 125) : RGB(185, 20, 20)) : (TXT_C);
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
    if (code == STN_CLICKED && (id == 0xFFFF || id == IDC_HDR || id == IDC_METER || id == IDC_STATUS ||
                                (id >= IDC_ROWLBL && id < IDC_ROWLBL + MAX_OUT))) {
        SetFocus(gWnd);                         // clicking text = clicking empty space
        return;
    }
    if (id >= IDC_ROWDEV && id < IDC_ROWDEV + MAX_OUT) {
        if (code == CBN_SELCHANGE) RestartIfRunning();
        return;
    }
    if (id >= IDC_ROWMODE && id < IDC_ROWMODE + MAX_OUT) {
        if (code == CBN_SELCHANGE) gRowMode[id - IDC_ROWMODE] = SelToMode((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0));
        return;
    }
    if (id >= IDC_PADPLAY && id < IDC_PADPLAY + PADS) {
        if (code == BN_CLICKED) {
            int i = PadSlot(id - IDC_PADPLAY);
            if (gPadRec && gPadRecSlot == i) gPadRec = false;          // stop recording (finished in the tick)
            else if (gPads[i].data) PadKey(i, true, false); else PadBrowse(i);
        }
        return;
    }
    if (id >= IDC_PADLOAD && id < IDC_PADLOAD + PADS) { if (code == BN_CLICKED) PadBrowse(PadSlot(id - IDC_PADLOAD)); return; }
    if (id >= IDC_PADCLR && id < IDC_PADCLR + PADS)   { if (code == BN_CLICKED) PadClear(PadSlot(id - IDC_PADCLR)); return; }
    if (id >= IDC_PADKEY && id < IDC_PADKEY + PADS) {
        if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_PAD0 + id - IDC_PADKEY], id);
        return;
    }
    if ((id >= IDC_PADVOL && id < IDC_PADVOL + PADS) || (id >= IDC_CLIPVOL && id < IDC_CLIPVOL + CLIPS) ||
        id == IDC_PADMASTER || id == IDC_CLIPMASTER) {
        if (!gUiReady) return;
        volatile int* var = id == IDC_PADMASTER ? &gPadMaster : id == IDC_CLIPMASTER ? &gClipMaster
                          : id >= IDC_CLIPVOL ? &gPads[CLIP0 + ClipSlot(id - IDC_CLIPVOL)].vol : &gPads[PadSlot(id - IDC_PADVOL)].vol;
        BOOL ok = FALSE;
        int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok) *var = Iclamp(v, 0, 200);
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)*var, FALSE);
        return;
    }
    if (id >= IDC_PADBANK0 && id < IDC_PADBANK0 + PAD_BANKS) { if (code == BN_CLICKED) SetPadBank(id - IDC_PADBANK0); return; }
    if (id == IDC_PADBANKKEY) { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_PADBANK], id); return; }
    if (id == IDC_REWINDKEY)  { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_REWIND], id); return; }
    if (id == IDC_REPEATKEY)  { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_REPEAT], id); return; }
    if (id == IDC_RANDLAG)    { gRandLagOn = Checked(id); return; }
    if (id == IDC_WSON) {                       // remote control: on = the server starts; off = it's closed completely
        if (code != BN_CLICKED) return;
        gWsOn = Checked(id);
        if (gWsOn) WsStart(); else WsStop();
        WsStatusText(); SaveSettings();
        return;
    }
    if (id == IDC_WSPORT) {
        if (!gUiReady) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_KILLFOCUS) {             // (applied when you leave the box, not on every keypress)
            if (ok && v >= 1024 && v <= 65535 && v != gWsPort) { gWsPort = v; if (gWsOn) WsStart(); WsStatusText(); SaveSettings(); }
            SetDlgItemInt(gWnd, id, (UINT)gWsPort, FALSE);
        }
        return;
    }
    if (id == IDC_WSPASS) {
        if (code == EN_CHANGE && gUiReady) { GetDlgItemTextW(gWnd, id, gWsPass, 64); gWsAuthedN = 0; }   // (everyone signs in again)
        if (code == EN_KILLFOCUS) SaveSettings();
        return;
    }
    if (id == IDC_WSHELP)  { if (code == BN_CLICKED) WsHelp(); return; }
    if (id == IDC_WSGUIDE) { if (code == BN_CLICKED) WsGuide(); return; }
    if (id >= IDC_FEATLAG && id <= IDC_FEATCLIPS) {   // Settings > Features
        if (code != BN_CLICKED) return;
        const bool on = Checked(id);
        if (id == IDC_FEATLAG)   gFeatLag = on;
        if (id == IDC_FEATFX)    { gFeatFx = on; if (!on && gFxOn) SetFxOn(false); }   // (off: the effects stop too)
        if (id == IDC_FEATSOUND) { gFeatSound = on; if (!on) for (int i = 0; i < PADS; i++) gPads[i].stop = true; }
        if (id == IDC_FEATCLIPS) { gFeatClips = on; if (!on) for (int i = 0; i < CLIP_N; i++) gPads[CLIP0 + i].stop = true; }
        Layout();
        RedrawWindow(gWnd, nullptr, nullptr, RDW_INVALIDATE | RDW_ALLCHILDREN);
        UpdateStatus();
        SaveSettings();
        return;
    }
    if (id == IDC_RANDSEC) {
        if (!gUiReady) return;
        BOOL ok = FALSE;
        int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok && v >= 2) gRandLagSec = Iclamp(v, 2, 120);
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gRandLagSec, FALSE);
        return;
    }
    if (id == IDC_PADFX)       { gPadsFx = Checked(id); return; }
    if (id == IDC_TAPEKEY)     { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_TAPESTOP], id); return; }
    if (id == IDC_DIVEKEY)     { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_DIVE], id); return; }
    if (id == IDC_DIVESEMIS)   {
        static const int diveOpts[] = { -12, -7, -5, 5, 7, 12 };
        if (code == CBN_SELCHANGE) gDiveSemis = diveOpts[Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, 5)];
        return;
    }
    if (id == IDC_BEATSYNC)    { gBeatSync = Checked(id); return; }
    if (id == IDC_BEATDIV)     { if (code == CBN_SELCHANGE) gBeatDiv = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, 3); return; }
    if (id == IDC_BPM) {
        if (!gUiReady) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok && v >= 40) gBpm = Iclamp(v, 40, 300);
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gBpm, FALSE);
        return;
    }
    if (id == IDC_LAGPRESET) {
        if (code == CBN_SELCHANGE) {
            int i = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
            if (i > 0 && i < LAG_PRESET_N) {
                const LagPreset& p = LAG_PRESETS[i];
                gLoopMs = p.loopMs; gSpeedPct = p.speed; gPitchPct = p.pitch; gFadeMs = p.fade;
                if (p.randSec) { gRandLagOn = true; gRandLagSec = p.randSec; }
                gBeatSync = false;
                RefreshSoundUI();
                wchar_t m[64]; wsprintfW(m, L"Lag: %s", p.name); ShowOsd(m, true);
            }
            SendDlgItemMessageW(gWnd, id, CB_SETCURSEL, 0, 0);
        }
        return;
    }
    if (id == IDC_SURPRISE)    { if (code == BN_CLICKED) SurpriseMe(); return; }
    if (id == IDC_FXHOLD)      { if (gHoldActive[0]) HoldRelease(0); gFxHold[0] = Checked(id); return; }
    if (id == IDC_MICTEST)     {
        if (code == BN_CLICKED) { if (gPrevRunning && gPrevData == gTestBuf) PrevStop(); else if (!gTestRec) MicTestStart(); }
        return;
    }
    if (id == IDC_MICPLAY)     { if (code == BN_CLICKED && gTestLen) PrevPlay(gTestBuf, 0, gTestLen, 1.0f); return; }
    if (id == IDC_PROFSAVE)    { if (code == BN_CLICKED) ProfileSaveClicked(); return; }
    if (id == IDC_PROFDEL)     { if (code == BN_CLICKED) ProfileDeleteClicked(); return; }
    if (id == IDC_PROFKEY)     { if (code == BN_CLICKED && gProfSel >= 0) BeginKeyCapture(gFxKeys[SLOT_PROF0 + gProfSel], id); return; }
    if (id == IDC_PROFNEXTKEY) { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_PROFNEXT], id); return; }
    if (id == IDC_PROFILE) {
        if (code == CBN_SELCHANGE) {            // picking a profile switches to it
            int i = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
            if (i >= 0 && i < gProfCount) { ProfileLoad(i, false); ProfilesFill(gProfNames[i]); ProfileAutoInfo(); }
        } else if (code == CBN_EDITCHANGE) {    // typing a new name: nothing selected yet
            wchar_t t[64]; GetDlgItemTextW(gWnd, id, t, 64);
            gProfSel = -1;
            for (int i = 0; i < gProfCount; i++) if (!lstrcmpiW(gProfNames[i], t)) gProfSel = i;
            wchar_t kn[120];
            if (gProfSel >= 0) FxKeyButtonText(SLOT_PROF0 + gProfSel, kn, 120); else lstrcpynW(kn, L"This profile: (save it first)", 120);
            SetDlgItemTextW(gWnd, IDC_PROFKEY, kn); FitOne(GetDlgItem(gWnd, IDC_PROFKEY));
            EnableWindow(GetDlgItem(gWnd, IDC_PROFKEY), gProfSel >= 0);
            EnableWindow(GetDlgItem(gWnd, IDC_PROFDEL), gProfSel >= 0);
        }
        return;
    }
    if (id == IDC_CLIPFX)      { gClipsFx = Checked(id); return; }
    if (id == IDC_CLIPAUTOTRIM){ gClipAutoTrim = Checked(id); return; }
    if (id == IDC_TTSSPEAK)    { if (code == BN_CLICKED) TtsSpeak(); return; }
    if (id == IDC_TTSMORE) { if (code == BN_CLICKED) TtsSettingsOpen(); return; }
    if (id == IDC_TTSVOL) {
        if (!gUiReady) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok) { gTtsVol = Iclamp(v, 0, 200); gPads[TTS_SLOT].vol = gTtsVol; }   // (changes what's speaking now too)
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gTtsVol, FALSE);
        return;
    }
    if (id == IDC_TTSACCENT) {
        if (code == CBN_SELCHANGE) {
            TtsEnsureListed();
            gTtsAccent = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, TTS_ACCENT_N - 1);
            const TtsAccent& a = TTS_ACCENTS[gTtsAccent];
            int v = TtsVoiceFor(gTtsAccent);
            if (v >= 0) {                       // show which voice will speak
                SendDlgItemMessageW(gWnd, IDC_TTSVOICE, CB_SETCURSEL, v + 1, 0);
                lstrcpynW(gTtsVoice, gTtsNames[v], 128);
            } else if (gTtsAccent > 0 && !gVoiceInstalling) {
                wchar_t m[600];
                wsprintfW(m, L"The %s accent needs Windows' %s voice, and it isn't installed yet.\n\n"
                             L"Download and install it now? Windows will ask for permission, then it downloads in the "
                             L"background (usually a minute or two). Until then the accent's words are used with your current voice.",
                          a.name, a.voiceName);
                if (MessageBoxW(gWnd, m, L"Lag Effect - Text to speech", MB_YESNO | MB_ICONQUESTION) == IDYES) TtsInstallVoice(gTtsAccent);
            }
        }
        return;
    }
    if (id == IDC_TTSVOICE) {
        if (code == CBN_DROPDOWN) TtsEnsureListed();
        if (code == CBN_SELCHANGE && (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0) == gTtsCount + 1) {
            TtsFillVoices();                    // (put the selection back)
            if (gNvsaBusy) return;
            if (MessageBoxW(gWnd, L"Get realistic voices? Lag Effect downloads the free NaturalVoiceSAPIAdapter from GitHub and opens "
                                  L"its installer, which makes Windows 11's natural Narrator voices and Edge's online neural voices "
                                  L"usable here. Download and set it up now?",
                            L"Lag Effect - Natural voices", MB_YESNO | MB_ICONQUESTION) == IDYES) NvsaStart();
            return;
        }
        if (code == CBN_SELCHANGE) {
            TtsEnsureListed();
            int sel = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
            lstrcpynW(gTtsVoice, sel > 0 && sel - 1 < gTtsCount ? gTtsNames[sel - 1] : L"", 128);
        }
        return;
    }
    if (id == IDC_PADSTOP) { if (code == BN_CLICKED) for (int i = 0; i < SB_N; i++) gPads[i].stop = true; return; }
    if (id >= IDC_CLIPPLAY && id < IDC_CLIPPLAY + CLIPS) {
        if (code == BN_CLICKED) { int c = ClipSlot(id - IDC_CLIPPLAY); if (gClips[c].base) gPads[CLIP0 + c].trigger = true; else ClipBrowse(c); }
        return;
    }
    if (id >= IDC_CLIPTRIM && id < IDC_CLIPTRIM + CLIPS) {
        if (code == BN_CLICKED) { int c = ClipSlot(id - IDC_CLIPTRIM); if (gClips[c].base) OpenTrim(c); else ClipBrowse(c); }
        return;
    }
    if (id >= IDC_CLIPCLR && id < IDC_CLIPCLR + CLIPS) { if (code == BN_CLICKED) { int c = ClipSlot(id - IDC_CLIPCLR); ClipClear(c); gClipPinned[c] = false; ClipShiftUp(c); } return; }
    if (id >= IDC_CLIPMORE && id < IDC_CLIPMORE + CLIPS) { if (code == BN_CLICKED) ClipMenu(ClipSlot(id - IDC_CLIPMORE), GetDlgItem(gWnd, id)); return; }
    if (id >= IDC_PADMORE && id < IDC_PADMORE + PADS)    { if (code == BN_CLICKED) PadMenu(PadSlot(id - IDC_PADMORE), GetDlgItem(gWnd, id)); return; }
    if (id >= IDC_CLIPBANK0 && id < IDC_CLIPBANK0 + CLIP_BANKS) { if (code == BN_CLICKED) SetClipBank(id - IDC_CLIPBANK0); return; }
    if (id == IDC_CLIPHIST)    { if (code == BN_CLICKED) ClipHistory(GetDlgItem(gWnd, id)); return; }
    if (id == IDC_PADFOLDER)   { if (code == BN_CLICKED) PadLoadFolder(); return; }
    if (id >= IDC_SETSUB0 && id <= IDC_SETSUB3) {
        if (code == BN_CLICKED && gSetSub != id - IDC_SETSUB0) {
            gSetSub = id - IDC_SETSUB0; Layout();
            for (int k = IDC_SETSUB0; k <= IDC_SETSUB3; k++) InvalidateRect(GetDlgItem(gWnd, k), nullptr, FALSE);
        }
        return;
    }
    if (id >= IDC_COLSW0 && id < IDC_COLSW0 + USERCOL_N) {
        if (code == BN_CLICKED) {
            int i = id - IDC_COLSW0;
            const COLORREF nows[USERCOL_N] = { ACCENT, BgColor(), gDark ? DK_CTL : LT_CARD, gDark ? DK_SECTION : LT_BORDER, TXT_C,
                                               gDark ? DK_DIM : gLtDim, TITLE_C, KNOB_C, gDark ? DK_TRACK : LT_TRACK, METER_C, TAB_C, STATUS_C };
            wchar_t title[64]; wsprintfW(title, L"Colour: %s", USERCOL_NAMES[i]);
            COLORREF c;
            if (HexColorPick(title, nows[i], &c)) { gUserCol[i] = c; ApplyTheme(); }
        }
        return;
    }
    if (id == IDC_COLRESET) { if (code == BN_CLICKED) { for (int i = 0; i < USERCOL_N; i++) gUserCol[i] = CLR_NONE; ApplyTheme(); } return; }
    if (id == IDC_FONT && code == CBN_DROPDOWN) {
        static bool filled = false;
        if (!filled) { filled = true; HCURSOR old = SetCursor(LoadCursor(nullptr, IDC_WAIT)); FontsFill(GetDlgItem(gWnd, id)); SetCursor(old); }
        return;
    }
    if (id == IDC_FONT) {
        if (code == CBN_SELCHANGE) {
            int i = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
            wchar_t n[40]; SendDlgItemMessageW(gWnd, id, CB_GETLBTEXT, i, (LPARAM)n);
            lstrcpynW(gFontName, n, 40); ApplyFont(); RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_ALLCHILDREN);
        }
        return;
    }
    if (id == IDC_OPACITY) {
        if (!gUiReady) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok && v >= 40) { gOpacity = Iclamp(v, 40, 100); ApplyOpacity(); }
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gOpacity, FALSE);
        return;
    }
    if (id == IDC_PICCHOOSE) {
        if (code == BN_CLICKED) {
            wchar_t path[MAX_PATH] = L"";
            OPENFILENAMEW o = {};
            o.lStructSize = sizeof(o); o.hwndOwner = gWnd; o.lpstrFile = path; o.nMaxFile = MAX_PATH;
            o.lpstrFilter = L"Pictures and GIFs (PNG, JPG, BMP, GIF)\0*.png;*.jpg;*.jpeg;*.bmp;*.gif\0All files\0*.*\0";
            o.lpstrTitle = L"Pick a background picture or GIF"; o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
            if (GetOpenFileNameW(&o)) {
                HCURSOR old = SetCursor(LoadCursor(nullptr, IDC_WAIT));
                if (PictureLoad(path)) { lstrcpynW(gPicPath, path, MAX_PATH); ApplyTheme(); }
                else { PictureLoad(gPicPath); MessageBoxW(gWnd, L"Couldn't open that picture. PNG, JPG, BMP and GIF work.", L"Lag Effect", MB_ICONWARNING); }
                SetCursor(old);
            }
            PictureInfo();
        }
        return;
    }
    if (id == IDC_PICREMOVE) { if (code == BN_CLICKED) { gPicPath[0] = 0; PictureLoad(gPicPath); ApplyTheme(); PictureInfo(); } return; }
    if (id == IDC_PICFIT) {
        if (code == CBN_SELCHANGE) {
            int was = gPicFit;
            gPicFit = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, 4);
            if (gPicFit == 4 && was != 4 && gBase.gp) {   // start small, in the middle, then let you place it
                int big = Imax(gBase.w0, gBase.h0);
                gPicSize = Iclamp(big > 0 ? 24000 / big : 100, 5, 400);
                gPicX = (CLIENT_W - gBase.w0 * gPicSize / 100) / 2; gPicY = 180;
            }
            ApplyTheme(); PictureInfo();
            if (gPicFit == 4 && was != 4 && gBase.gp) EdBegin(ED_PICS);
        }
        return;
    }
    if (id == IDC_PICPLACE) { if (code == BN_CLICKED && gBase.gp && gPicFit == 4) EdBegin(ED_PICS); return; }
    if (id == IDC_FONTSIZE) {
        if (code == CBN_SELCHANGE) {
            gFontPx = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0) + 11, 11, 18);
            ApplyFont(); RedrawWindow(gWnd, nullptr, nullptr, RDW_ERASE | RDW_INVALIDATE | RDW_ALLCHILDREN);
        }
        return;
    }
    if (id == IDC_LAYEDIT)  { if (code == BN_CLICKED) EdBegin(ED_LAYOUT); return; }
    if (id == IDC_LAYRESET) {
        if (code == BN_CLICKED && MessageBoxW(gWnd, L"Put everything back where it started (for this profile)?", L"Lag Effect - Layout",
                                              MB_YESNO | MB_ICONQUESTION) == IDYES) {
            LayoutReset(); EdReplace(); LayoutSaveNow();
        }
        return;
    }
    if (id == IDC_STKMOVE)  {
        if (code == BN_CLICKED) {
            if (!gStkN && !(gBase.gp && gPicFit == 4))
                MessageBoxW(gWnd, L"Add a picture or GIF first (or set the background to \"Place it yourself\").", L"Lag Effect - Pictures", MB_ICONINFORMATION);
            else EdBegin(ED_PICS);
        }
        return;
    }
    if (id == IDC_STKLIST)  { if (code == CBN_SELCHANGE) { gStkSel = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0); PicUiRefresh(); } return; }
    if (id == IDC_STKADD) {
        if (code == BN_CLICKED) {
            if (gStkN >= STK_MAX) { MessageBoxW(gWnd, L"That's the most (8). Remove one to add another.", L"Lag Effect - Pictures", MB_ICONINFORMATION); return; }
            static wchar_t files[16384];
            files[0] = 0;
            OPENFILENAMEW o = {};
            o.lStructSize = sizeof(o); o.hwndOwner = gWnd; o.lpstrFile = files; o.nMaxFile = 16384;
            o.lpstrFilter = L"Pictures and GIFs (PNG, GIF, JPG, BMP)\0*.png;*.gif;*.jpg;*.jpeg;*.bmp\0All files\0*.*\0";
            o.lpstrTitle = L"Add pictures or GIFs (you can pick several)";
            o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY | OFN_ALLOWMULTISELECT | OFN_EXPLORER;
            if (!GetOpenFileNameW(&o)) return;
            int added = 0, failed = 0;
            const wchar_t* dir = files; const wchar_t* f = files + lstrlenW(files) + 1;
            HCURSOR old = SetCursor(LoadCursor(nullptr, IDC_WAIT));
            if (!*f) { if (StkAdd(files)) added++; else failed++; }   // one file: the full path
            for (; *f && gStkN < STK_MAX; f += lstrlenW(f) + 1) {
                wchar_t path[MAX_PATH]; wsprintfW(path, L"%s\\%s", dir, f);
                if (StkAdd(path)) added++; else failed++;
            }
            SetCursor(old);
            if (added) { gStkSel = gStkN - 1; PictureRebuild(); PicRedraw(nullptr); StkSaveAll(); }
            PicUiRefresh();
            if (failed) MessageBoxW(gWnd, L"Some files couldn't be opened (PNG, GIF, JPG and BMP work), or there wasn't room for them.", L"Lag Effect - Pictures", MB_ICONWARNING);
            else if (added) EdBegin(ED_PICS);    // straight to placing them
        }
        return;
    }
    if (id == IDC_STKDEL) {
        if (code == BN_CLICKED && gStkSel >= 0 && gStkSel < gStkN) {
            RECT r; StkRect(gStk[gStkSel], &r);
            StkRemove(gStkSel); PictureRebuild(); PicRedraw(nullptr); StkSaveAll(); PicUiRefresh();
        }
        return;
    }
    if (id == IDC_STKSIZE || id == IDC_STKOPAC) {
        if (!gUiReady || gPicUiBusy || gStkSel < 0 || gStkSel >= gStkN) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        Sticker& st = gStk[gStkSel];
        if (code == EN_CHANGE && ok && v >= 5) {
            RECT before; StkRect(st, &before);
            if (id == IDC_STKSIZE) { st.size = Iclamp(v, 5, 400); st.stale = true; SetTimer(gWnd, TIMER_STKSIZE, 300, nullptr); }
            else st.opacity = Iclamp(v, 5, 100);
            StkRefresh(&before);
        } else if (code == EN_KILLFOCUS) { SetDlgItemInt(gWnd, id, (UINT)(id == IDC_STKSIZE ? st.size : st.opacity), FALSE); StkSaveAll(); }
        return;
    }
    if (id == IDC_GIFFPS) {
        if (code == CBN_SELCHANGE) {
            static const int fpsV[] = { 10, 15, 24, 30, 60, 0 };
            gGifFps = fpsV[Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, 5)];
            PictureRebuild(); PicRedraw(nullptr);  // frames are decoded again (in the background) for the new limit
        }
        return;
    }
    if (id == IDC_GIFPAUSE) { gGifPauseBg = Checked(id); return; }
    if (id == IDC_PICDIM) {
        if (!gUiReady) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok) { gPicDim = Iclamp(v, 0, 95); if (PicActive()) ApplyTheme(); }
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gPicDim, FALSE);
        return;
    }
    if (id == IDC_PTTMODE)     { if (code == CBN_SELCHANGE) gPttMode = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, 2); return; }
    if (id == IDC_PTTKEY)      { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_PTT], id); return; }
    if (id == IDC_OVERLAY)     { gOverlayOn = Checked(id); OverlayUpdate(); return; }
    if (id == IDC_BEEPS)       { gBeeps = Checked(id); if (gBeeps) HotkeyBeep(true); return; }
    if (id == IDC_EXPORT)      { if (code == BN_CLICKED) ExportSettings(); return; }
    if (id == IDC_IMPORT)      { if (code == BN_CLICKED) ImportSettings(); return; }
    if (id == IDC_COMPACT || id == IDC_COMPACTFULL) { if (code == BN_CLICKED) SetCompact(id == IDC_COMPACT); return; }
    if (id == IDC_COMPACTFX)   { if (code == BN_CLICKED) { SetFxOn(!gFxOn); SetDlgItemTextW(gWnd, id, gFxOn ? L"Voice FX: on" : L"Voice FX: off"); UpdateStatus(true); } return; }
    if (id == IDC_PROFAUTO)    { if (code == BN_CLICKED) ProfileAutoClicked(); return; }
    if (id == IDC_UISCALE) {
        if (code == CBN_SELCHANGE) {
            static const int scales[] = { 100, 125, 150, 175, 200 };
            int v = scales[Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, 4)];
            if (v != gUiScale) Rescale(v);   // (straight away: no restart needed now)
        }
        return;
    }
    if (id == IDC_PADCHOKE)    { gPadChoke = Checked(id); return; }
    if (id == IDC_PADDUCK)     { gPadDuck = Checked(id); return; }
    if (id == IDC_HEARON) {
        if (code == CBN_SELCHANGE) {
            int i = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
            gHearOut = i <= 0 ? 0 : i > gRows ? MAX_OUT + 1 : i;
        }
        return;
    }
    if (id == IDC_CLIPSEP)     { gClipSeparate = Checked(id); return; }
    if (id == IDC_CLIPREPLACE) { gClipReplace = Checked(id); return; }
    if (id >= IDC_CLIPKEY && id < IDC_CLIPKEY + CLIPS) {
        if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_CLIP0 + id - IDC_CLIPKEY], id);
        return;
    }
    if (id == IDC_CLIPNOWKEY) { if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_CLIPNOW], id); return; }
    if (id == IDC_CLIPNOW)    { if (code == BN_CLICKED) ClipNow(); return; }
    if (id == IDC_CLIPSTOP)   { if (code == BN_CLICKED) for (int i = CLIP0; i < CLIP0 + CLIP_N; i++) gPads[i].stop = true; return; }
    if (id == IDC_CLIPFOLDER) {
        if (code == BN_CLICKED) { ClipFolder(); ShellExecuteW(nullptr, L"open", gClipDir, nullptr, nullptr, SW_SHOWNORMAL); }
        return;
    }
    if (id == IDC_RECSRC) {
        if (code == CBN_SELCHANGE) {
            gRecSource = kRecOrder[Iclamp((int)SendDlgItemMessageW(gWnd, IDC_RECSRC, CB_GETCURSEL, 0, 0), 0, REC_N - 1)];
            RecRestart();
            ClipTick();
        }
        return;
    }
    if (id == IDC_RECSECS) {
        if (!gUiReady) return;
        BOOL ok = FALSE;
        int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok && v >= 3) { gRecSeconds = Iclamp(v, 3, REC_MAX_S); ClipTick(); }
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gRecSeconds, FALSE);
        return;
    }
    if (id >= IDC_CHSRC0 && id < IDC_CHSRC0 + CH_MAX) {   // its name: the menu (what it plays, rename, colour)
        if (code == BN_CLICKED) ChanMenu(id - IDC_CHSRC0, GetDlgItem(gWnd, id));
        return;
    }
    if (id >= IDC_CHADD0 && id < IDC_CHADD0 + CH_MAX) {
        if (code == BN_CLICKED) ChanMenu(id - IDC_CHADD0, GetDlgItem(gWnd, id));
        return;
    }
    if (id == IDC_MIXKEYSBTN) {                 // the Mixer: its strips <-> its hotkeys
        if (code != BN_CLICKED) return;
        if (gCapturingKey) EndKeyCapture();
        gMixSub = !gMixSub;
        SetWindowTextW(GetDlgItem(gWnd, id), gMixSub ? L"Back to mixer" : L"Hotkeys");
        Layout(); MixerRedraw();
        return;
    }
    if (id >= IDC_MIXKEY0 && id < IDC_MIXKEY0 + (KEY_SLOTS - SLOT_MIX0)) {
        if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_MIX0 + id - IDC_MIXKEY0], id);
        return;
    }
    if (id >= IDC_MIXHOLDMODE0 && id < IDC_MIXHOLDMODE0 + CH_MAX) {   // its hold key: mutes it / push-to-talk
        if (code != BN_CLICKED) return;
        const int c = id - IDC_MIXHOLDMODE0;
        gCh[c].holdTalk = !gCh[c].holdTalk;
        SetWindowTextW(GetDlgItem(gWnd, id), gCh[c].holdTalk ? L"Talk" : L"Mute");
        InvalidateRect(GetDlgItem(gWnd, id), nullptr, FALSE);
        return;
    }
    if (id == IDC_MIXSTEP) {
        if (!gUiReady) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok && v >= 1) gMixStep = Iclamp(v, 1, 10);
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gMixStep, FALSE);
        return;
    }
    if (id == IDC_CHADDBTN) {                   // a new channel: the first free one, then pick what it plays
        if (code == BN_CLICKED) for (int c = 0; c < CH_MAX; c++) if (gCh[c].type == CH_NONE) { ChanMenu(c, GetDlgItem(gWnd, id)); break; }
        return;
    }
    if (id >= IDC_OLBL0 && id < IDC_OLBL0 + MAX_OUT) {   // an output's name: rename it
        if (code == BN_CLICKED) ChanRename(CH_MAX + id - IDC_OLBL0);
        return;
    }
    if (id >= IDC_CHMUTE0 && id < IDC_CHMUTE0 + CH_MAX) {
        if (code == BN_CLICKED) { gCh[id - IDC_CHMUTE0].mute = !gCh[id - IDC_CHMUTE0].mute; MixerRedraw(); }
        return;
    }
    if (id >= IDC_CHSOLO0 && id < IDC_CHSOLO0 + CH_MAX) {
        if (code == BN_CLICKED) { gCh[id - IDC_CHSOLO0].solo = !gCh[id - IDC_CHSOLO0].solo; MixerRedraw(); }
        return;
    }
    if (id >= IDC_CHDUCK0 && id < IDC_CHDUCK0 + CH_MAX) {
        if (code == BN_CLICKED) { gCh[id - IDC_CHDUCK0].duck = !gCh[id - IDC_CHDUCK0].duck; InvalidateRect(GetDlgItem(gWnd, id), nullptr, FALSE); }
        return;
    }
    if (id >= IDC_CHRT0 && id < IDC_CHRT0 + CH_MAX * MAX_OUT) {
        if (code == BN_CLICKED) {
            int c = (id - IDC_CHRT0) / MAX_OUT, k = (id - IDC_CHRT0) % MAX_OUT;
            gCh[c].routes ^= 1u << k;
            InvalidateRect(GetDlgItem(gWnd, id), nullptr, FALSE);
        }
        return;
    }
    if (id >= IDC_OMUTE0 && id < IDC_OMUTE0 + MAX_OUT) {
        if (code == BN_CLICKED) {
            const int k = id - IDC_OMUTE0;
            gOutMute[k] = !gOutMute[k];
            InvalidateRect(GetDlgItem(gWnd, id), nullptr, FALSE); InvalidateRect(GetDlgItem(gWnd, IDC_OVOL0 + k), nullptr, FALSE);
        }
        return;
    }
    if (id == IDC_DUCKDB) {
        if (!gUiReady) return;
        BOOL ok = FALSE; int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok && v >= 3) gDuckDb = Iclamp(v, 3, 30);
        else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)gDuckDb, FALSE);
        return;
    }
    if (id == IDC_RESTARTAUD) {                 // close and reopen every device (after plugging things in / out)
        if (code == BN_CLICKED) {
            HCURSOR old = SetCursor(LoadCursor(nullptr, IDC_WAIT));
            if (gWantRunning) StopAudio();
            StartAudio(false);
            UpdateUi();
            SetCursor(old);
        }
        return;
    }
    if (id >= IDC_ROWVOL && id < IDC_ROWVOL + MAX_OUT) {
        if (!gUiReady) return;
        int k = id - IDC_ROWVOL;
        BOOL ok = FALSE;
        int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
        if (code == EN_CHANGE && ok) { gRowVol[k] = Iclamp(v, 0, 200); InvalidateRect(GetDlgItem(gWnd, IDC_OVOL0 + k), nullptr, FALSE); FaderLabel(IDC_OVOL0 + k); }
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
    if (id >= IDC_FXGRP_HOLD && id < IDC_FXGRP_HOLD + FX_GROUPS) {
        int g = id - IDC_FXGRP_HOLD;
        if (gHoldActive[1 + g]) HoldRelease(1 + g);
        gFxHold[1 + g] = Checked(id);
        return;
    }
    if (id >= IDC_FXGRP_RESET && id < IDC_FXGRP_RESET + FX_GROUPS) {
        if (code == BN_CLICKED) ResetFxGroup(id - IDC_FXGRP_RESET);
        return;
    }

    if (id >= 1200 && id < 1200 + PROF_MAX) { ProfileLoad(id - 1200, true); ProfilesFill(gProfNames[id - 1200]); ProfileAutoInfo(); return; }
    if (id > 1220 && id < 1220 + CHAR_N)    { ApplyCharacter(id - 1220); return; }
    if (id >= 1260 && id < 1260 + PAD_BANKS) { SetPadBank(id - 1260); return; }
    switch (id) {
    case IDC_LOOP: case IDC_SPEED: case IDC_PITCH: case IDC_FADE: case IDC_TALKVOL:
    case IDC_RWLEN: case IDC_RWTOP: case IDC_RWRAMP: case IDC_RWPITCH:
        if (!gUiReady) break;
        for (Range& r : gRanges) {
            if (r.id != id) continue;
            BOOL ok = FALSE;
            int v = (int)GetDlgItemInt(gWnd, id, &ok, TRUE);
            if (code == EN_CHANGE && ok) *r.var = Iclamp(v, r.lo, r.hi);
            else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)*r.var, TRUE);
        }
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
    case IDC_GATEON:   SetGateMode(Checked(IDC_GATEON) ? gGateLastMode : GATE_OFF); break;
    case IDC_GATEMODE:
        if (code == CBN_SELCHANGE) SetGateMode((int)SendDlgItemMessageW(gWnd, IDC_GATEMODE, CB_GETCURSEL, 0, 0));
        break;
    case IDC_NSON:     gNsOn = Checked(IDC_NSON); RedrawKnobs(); break;
    case IDC_FXSUB0: case IDC_FXSUB1: case IDC_FXSUB2: case IDC_FXSUB3: case IDC_FXSUB4: case IDC_FXSUB5: case IDC_FXSUB6:
        if (code == BN_CLICKED) SetFxSub(id - IDC_FXSUB0);
        break;
    case IDC_MICSUB0: case IDC_MICSUB1:
        if (code == BN_CLICKED && gMicSub != id - IDC_MICSUB0) {
            gMicSub = id - IDC_MICSUB0;
            Layout();
            InvalidateRect(GetDlgItem(gWnd, IDC_MICSUB0), nullptr, FALSE); InvalidateRect(GetDlgItem(gWnd, IDC_MICSUB1), nullptr, FALSE);
        }
        break;
    case IDC_HARMMUTE:
        if (code == BN_CLICKED) {
            gHarmMute = !gHarmMute;
            SetDlgItemTextW(gWnd, id, HarmMuteText());
            FitOne(GetDlgItem(gWnd, id));
            UpdateStatus(true);
        }
        break;
    case IDC_HARMSTYLE:
        if (code == CBN_SELCHANGE) gHarmStyle = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, HARM_N - 1);
        break;
    case IDC_BROADCAST: gBroadcast = Checked(IDC_BROADCAST); break;
    case IDC_EQRESET:
        if (code == BN_CLICKED) for (int i = 0; i < KNOB_N; i++) if (gKnobs[i].group == KG_EQ) SetKnobValue(GetDlgItem(gWnd, IDC_KNOB + i), i, 0);
        break;
    case IDC_FXCHAR:
        if (code == CBN_SELCHANGE) {
            OnCharacterPicked((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0));   // back to "Pick a voice..." after
        }
        break;
    case IDC_ECHOSTYLE: case IDC_DISTSTYLE: case IDC_CHOSTYLE: case IDC_MUFSTYLE:
        if (code == CBN_SELCHANGE) {
            int g = id == IDC_ECHOSTYLE ? KG_ECHO : id == IDC_DISTSTYLE ? KG_DIST : id == IDC_CHOSTYLE ? KG_CHORUS : KG_MUFFLE;
            SetFxStyle(g, (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0));
        }
        break;
    case IDC_RADIOPRESET:
        if (code == CBN_SELCHANGE) {
            gRadioPreset = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, RADIO_N - 1);
            { SetDlgItemTextW(gWnd, IDC_RADIODESC, RADIO_DESC[gRadioPreset]); FitOne(GetDlgItem(gWnd, IDC_RADIODESC)); }
            RedrawKnobs();                      // dims knobs the preset doesn't use
        }
        break;
    case IDC_SONGBTN:
        if (code == BN_CLICKED) SetSongMode(!SongModeOn());
        break;
    case IDC_SONGSRC:
        if (code == CBN_DROPDOWN) FillSongSources();              // refresh: which apps are playing now
        else if (code == CBN_SELCHANGE) {
            int sel = (int)SendDlgItemMessageW(gWnd, IDC_SONGSRC, CB_GETCURSEL, 0, 0);
            int idx = (int)SendDlgItemMessageW(gWnd, IDC_SONGSRC, CB_GETITEMDATA, sel, 0);
            if (idx == SONGSRC_BROWSE) { BrowseSongFile(); break; }
            if (idx == SONGSRC_FILE) {
                if (gFileData) gSongUseFile = true; else LoadSongFile(gSongFile);
            } else {
                gSongUseFile = false;
                lstrcpynW(gSongApp, idx > 0 && idx <= gSongListN ? gSongList[idx - 1] : L"", 64);
            }
            UpdateSongCapture();
        }
        break;
    case IDC_VOCSTYLE: case IDC_VOCKEY: case IDC_VOCSCALE: case IDC_VOCRANGE:
        if (code == CBN_SELCHANGE) {
            int v = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
            if (id == IDC_VOCSTYLE) { if (gVocStyle != VOC_SONG && v == VOC_SONG) gPrevVocStyle = gVocStyle; VocSetStyle(v); SongStyleChanged(); }
            else if (id == IDC_VOCKEY) gVocKey = v;
            else if (id == IDC_VOCSCALE) gVocScale = v; else gVocRange = Iclamp(v, 0, 2);
            RedrawKnobs();                      // Synth dims in the Tune style
        }
        break;
    case IDC_OPENSET:
        if (code == BN_CLICKED) {
            SaveSettings();                     // so the file is there and up to date
            wchar_t args[MAX_PATH + 16];
            wsprintfW(args, L"/select,\"%s\"", gIni);
            ShellExecuteW(nullptr, L"open", L"explorer.exe", args, nullptr, SW_SHOWNORMAL);
        }
        break;
    case IDC_TAB3: case IDC_TAB4: case IDC_TAB5: case IDC_TAB6:
        if (code == BN_CLICKED) SetPage(id - IDC_TAB0);
        break;
    case IDC_TALKON:   gTalkOver = Checked(IDC_TALKON); break;
    case IDC_UPDSTART: gUpdateOnStart = Checked(IDC_UPDSTART); break;
    case IDC_CHECKUPD: if (code == BN_CLICKED) StartUpdateCheck(true); break;
    case IDC_HOLD:
    case IDC_TOGGLE:   gToggleMode = Checked(IDC_TOGGLE); UpdateStatus(true); break;
    case IDC_HOTKEY:   if (code == BN_CLICKED) BeginKeyCapture(gHotkeys, IDC_HOTKEY); break;
    case IDC_FXKEY_MASTER:
        if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[0], IDC_FXKEY_MASTER);
        break;
    case IDC_COLORTHEME:
        if (code == CBN_SELCHANGE) {
            int was = gColorTheme;
            gColorTheme = Iclamp((int)SendDlgItemMessageW(gWnd, IDC_COLORTHEME, CB_GETCURSEL, 0, 0), 0, COLOR_THEME_N - 1);
            if (gColorTheme == COLOR_THEME_N - 1) {   // Custom: type its colour
                COLORREF c;
                if (HexColorPick(L"Custom theme colour", gCustomAccent, &c)) gCustomAccent = c;
                else if (was != COLOR_THEME_N - 1) { gColorTheme = was; SendDlgItemMessageW(gWnd, IDC_COLORTHEME, CB_SETCURSEL, was, 0); }
            }
            ApplyTheme();                       // live preview
        }
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
    case IDC_HIDESHARE: gHideShare = Checked(IDC_HIDESHARE); RestartIfRunning(); break;
    case IDC_MUTEBTN:  if (code == BN_CLICKED) SetMute(!gMicMuted); break;
    case ID_TRAY_MUTE: SetMute(!gMicMuted); break;
    case IDC_MUTEKEY:  if (code == BN_CLICKED) BeginKeyCapture(gFxKeys[SLOT_MUTE], IDC_MUTEKEY); break;
    case IDC_OSD:      gShowOsd = Checked(IDC_OSD); if (gShowOsd) ShowOsd(L"Pop-ups are on", true); break;
    case IDC_TOPMOST:
        gTopMost = Checked(IDC_TOPMOST);
        SetWindowPos(gWnd, gTopMost ? HWND_TOPMOST : HWND_NOTOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
        break;
    case IDC_STARTWIN: SetStartWithWindows(Checked(IDC_STARTWIN)); break;
    case ID_TRAY_FX:   SetFxOn(!gFxOn); UpdateStatus(true); break;
    case ID_TRAY_SONG: SetSongMode(!SongModeOn()); break;
    case ID_TRAY_NS:
        gNsOn = !gNsOn;
        CheckDlgButton(gWnd, IDC_NSON, gNsOn ? BST_CHECKED : BST_UNCHECKED);
        RedrawKnobs();
        break;
    case ID_TRAY_GATE: SetGateMode(gGateMode != GATE_OFF ? GATE_OFF : gGateLastMode); break;
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
    case 1270: gOverlayOn = !gOverlayOn; CheckDlgButton(gWnd, IDC_OVERLAY, gOverlayOn ? BST_CHECKED : BST_UNCHECKED); OverlayUpdate(); break;
    case 1271: SetCompact(!gCompact); break;
    case ID_TRAY_EXIT: PostMessageW(gWnd, WM_CLOSE, 0, 0); break;
    }
}

// Owner-drawn controls are drawn off-screen and copied in one go, so nothing flickers when the picture behind
// them changes (e.g. a GIF background). The meter buffers itself; dropdown items aren't on the window background.
static bool DrawItemDispatch(WPARAM w, DRAWITEMSTRUCT* d)
{
    if (w >= IDC_CHMUTE0 && w < IDC_CHMUTE0 + CH_MAX) { DrawToggle(d, gCh[w - IDC_CHMUTE0].mute, true); return true; }
    if (w >= IDC_CHSOLO0 && w < IDC_CHSOLO0 + CH_MAX) { DrawToggleC(d, gCh[w - IDC_CHSOLO0].solo, SOLO_C, RGB(27, 27, 27)); return true; }
    if (w >= IDC_CHDUCK0 && w < IDC_CHDUCK0 + CH_MAX) { DrawToggleC(d, gCh[w - IDC_CHDUCK0].duck, ACCENT, RGB(255, 255, 255)); return true; }
    if (w >= IDC_CHSRC0 && w < IDC_CHSRC0 + CH_MAX)   { DrawChanSrc(d, (int)(w - IDC_CHSRC0)); return true; }
    if (w >= IDC_CHADD0 && w < IDC_CHADD0 + CH_MAX)   { DrawChanAdd(d); return true; }
    if (w >= IDC_OLIM0 && w < IDC_OLIM0 + MAX_OUT)    { DrawLimit(d, gLimShow[w - IDC_OLIM0] > 0); return true; }
    if (w >= IDC_MIXHOLDMODE0 && w < IDC_MIXHOLDMODE0 + CH_MAX) { DrawToggleC(d, gCh[w - IDC_MIXHOLDMODE0].holdTalk != 0, ACCENT, RGB(255, 255, 255)); return true; }
    if (w >= IDC_OLBL0 && w < IDC_OLBL0 + MAX_OUT) {   // an output's name (click: rename it)
        HDC dc = d->hDC; RECT rc = d->rcItem;
        FillRect(dc, &rc, BgBrush());
        wchar_t t[32]; OutName((int)(w - IDC_OLBL0), t, 32);
        SetBkMode(dc, TRANSPARENT); SetTextColor(dc, TXT_C);
        HGDIOBJ of = SelectObject(dc, gFontBold);
        DrawTextW(dc, t, -1, &rc, DT_SINGLELINE | DT_VCENTER | DT_LEFT | DT_END_ELLIPSIS | DT_NOPREFIX);
        SelectObject(dc, of);
        if (d->itemState & ODS_FOCUS) { RECT f = rc; DrawFocusRect(dc, &f); }
        return true;
    }
    if (w >= IDC_CHRT0 && w < IDC_CHRT0 + CH_MAX * MAX_OUT) {
        int c = (int)(w - IDC_CHRT0) / MAX_OUT, k = (int)(w - IDC_CHRT0) % MAX_OUT;
        DrawToggle(d, (gCh[c].routes >> k) & 1, false); return true;
    }
    if (w >= IDC_OMUTE0 && w < IDC_OMUTE0 + MAX_OUT) { DrawToggle(d, gOutMute[w - IDC_OMUTE0], true); return true; }
    if (w >= IDC_CHMETER0 && w < IDC_CHMETER0 + CH_MAX) {
        int c = (int)(w - IDC_CHMETER0);
        DrawVMeter2(d, gChShownL[c], gChShownR[c], gChA[c].live, gChHoldL[c], gChHoldR[c], GetTickCount() - gChClipT[c] < 2000 && gChClipT[c]);
        return true;
    }
    if (w >= IDC_OMETER0 && w < IDC_OMETER0 + MAX_OUT) {
        int k = (int)(w - IDC_OMETER0);
        DrawVMeter2(d, gOutShown[k], -1.0f, gRunning, gOutHold[k], 0, GetTickCount() - gOutClipT[k] < 2000 && gOutClipT[k]);
        return true;
    }
    if ((d)->hwndItem == gStatus) { DrawStatus(d); return true; }
    if (w == IDC_VOICEPROG) { DrawVoiceProgress(d); return true; }
    if (w >= IDC_TAB0 && w < IDC_TAB0 + TAB_COUNT) { DrawTab(d); return true; }
    if (w == IDC_FXON) { DrawFxSwitch(d); return true; }
    if (w == IDC_SONGBTN) { DrawSongButton(d); return true; }
    if ((w >= IDC_FXSUB0 && w < IDC_FXSUB0 + FX_SUBS) || w == IDC_MICSUB0 || w == IDC_MICSUB1 || (w >= IDC_SETSUB0 && w <= IDC_SETSUB3)) {
        DrawFxSub(d); return true;
    }
    if (w >= IDC_COLSW0 && w < IDC_COLSW0 + USERCOL_N) { DrawSwatch(d); return true; }
    if (w >= IDC_PADBANK0 && w < IDC_PADBANK0 + PAD_BANKS) { DrawPadBank(d); return true; }
    if (w >= IDC_CLIPBANK0 && w < IDC_CLIPBANK0 + CLIP_BANKS) { DrawClipBank(d); return true; }
    if (w >= IDC_ROWLBL && w < IDC_ROWLBL + MAX_OUT) { DrawOutLabel(d); return true; }
    if ((w >= IDC_PADPLAY && w < IDC_PADPLAY + PADS) || (w >= IDC_CLIPPLAY && w < IDC_CLIPPLAY + CLIPS)) {
        DrawPadButton(d); return true;
    }
    if (w == IDC_METER) { DrawMeter(d); return true; }
    if (w == IDC_COLORTHEME) { DrawColorItem(d); return true; }
    return false;
}

// ---- hitch log: anything that keeps the window busy for over 25 ms goes in LagEffect-hitches.txt next to the
// exe (or in %TEMP%), so a stutter can be traced to what caused it. At most 400 lines a run.
static int gHitchN = 0;
static void HitchLog(UINT m, WPARAM w, int ms)
{
    if (gHitchN >= 400) return;
    static wchar_t path[MAX_PATH] = L"";
    HANDLE f = INVALID_HANDLE_VALUE;
    if (!path[0]) {                             // (only when LagEffect-hitches.txt is next to the exe: put an empty one there)
        GetModuleFileNameW(nullptr, path, MAX_PATH);
        wchar_t* b = wcsrchr(path, L'\\'); if (b) lstrcpyW(b + 1, L"LagEffect-hitches.txt");
        f = CreateFileW(path, FILE_APPEND_DATA, FILE_SHARE_READ, nullptr, OPEN_EXISTING, 0, nullptr);
        if (f == INVALID_HANDLE_VALUE) { gHitchN = 400; return; }   // not asked for: never log
        else {
            static const char head[] = "---- Lag Effect " "1.32.1" " started ----\r\n"; DWORD wr;
            WriteFile(f, head, sizeof(head) - 1, &wr, nullptr);
        }
    }
    if (f == INVALID_HANDLE_VALUE) f = CreateFileW(path, FILE_APPEND_DATA, FILE_SHARE_READ, nullptr, OPEN_EXISTING, 0, nullptr);
    if (f == INVALID_HANDLE_VALUE) return;
    SYSTEMTIME st; GetLocalTime(&st);
    char line[200];
    wsprintfA(line, "%02d:%02d:%02d.%03d  msg 0x%04X  w %u  %d ms%s  page %d  pic %d  opacity %d\r\n",
              st.wHour, st.wMinute, st.wSecond, st.wMilliseconds, m, (unsigned)w, ms, gMoving ? "  (while moving)" : "",
              gPage, PicActive() ? 1 : 0, gOpacity);
    DWORD wr; WriteFile(f, line, lstrlenA(line), &wr, nullptr);
    CloseHandle(f);
    gHitchN++;
}
static LRESULT CALLBACK WndProcInner(HWND h, UINT m, WPARAM w, LPARAM l);
static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    // (menus, message boxes and dragging run their own loops inside these: their length is just you)
    if (m == WM_SYSCOMMAND || m == WM_NCLBUTTONDOWN || m == WM_NCLBUTTONDBLCLK || m == WM_COMMAND || m == WM_CONTEXTMENU ||
        m == WM_NCRBUTTONDOWN || m == WM_NCRBUTTONUP || m == WM_TRAY || m == WM_CREATE || m == WM_CLOSE || m == WM_DESTROY)
        return WndProcInner(h, m, w, l);
    LARGE_INTEGER a, b, fq; QueryPerformanceCounter(&a);
    LRESULT r = WndProcInner(h, m, w, l);
    QueryPerformanceCounter(&b); QueryPerformanceFrequency(&fq);
    const int ms = (int)((b.QuadPart - a.QuadPart) * 1000 / fq.QuadPart);
    if (ms > 25) HitchLog(m, w, ms);
    return r;
}
static LRESULT CALLBACK WndProcInner(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_CREATE:
        gWnd = h;
        CreateUI();
        DragAcceptFiles(h, TRUE);                // drop audio files onto soundboard pads
        ApplyTheme();
        StartWithWindowsFollow();
        if (gWsOn) WsStart();                   // remote control (only if you switched it on)
        WsStatusText();
        // Keeps retrying quietly if the devices are still busy (e.g. the old version is closing).
        if ((gAutoStart || gResumeAudio) && !StartAudio(true)) SetTimer(h, TIMER_RECONNECT, 1000, nullptr);
        UpdateUi();
        if (gCompact) Layout();
        ExecCommandLine(GetCommandLineW());     // switches given on the first start (only if allowed)
        PictureLoad(gPicPath);
        StkLoadAll();
        if (PicActive()) { PictureRebuild(); InvalidateRect(h, nullptr, TRUE); }
        PictureInfo();
        ApplyOpacity();
        SetTimer(h, TIMER_STATUS, 50, nullptr);
        SetTimer(h, TIMER_CLEANUP, 1000, nullptr);
        SetTimer(h, TIMER_FXKEYS, 20, nullptr);
        return 0;
    case WM_TIMER:
        if (w == TIMER_STATUS) {
            if (gMoving) return 0;              // you're dragging the window: meters and checks wait (no stutter)
            SongTick(); PadTick();
            UpdateStatus(); UpdateMeter(); MixerMeterTick(); WsEvents();
            static int chTick = 0;
            if (++chTick >= 40) {               // every 2 s
                chTick = 0; ChanTick();
                if (gPage == PAGE_MIXER) AppScanStart();
                if (gRunning && !gStopping) {   // outputs that dropped out (unplugged, cable reinstalled...): try again,
                    const DWORD now = GetTickCount();   // less and less often (4 s .. 30 s) while they keep failing
                    for (int k = 1; k < gRows; k++) {
                        if (gExtraRunning[k] || (int)(now - gOutNextTry[k]) < 0) continue;
                        if (StartExtraOutput(k)) gOutWait[k] = 0;
                        else { gOutWait[k] = gOutWait[k] ? Imin((int)gOutWait[k] * 2, 30000) : 4000; gOutNextTry[k] = now + gOutWait[k]; }
                    }
                }
            }
        }
        else if (w == TIMER_KEY) PollKeyCapture();
        else if (w == TIMER_CLEANUP) { if (!gMoving) { CleanupOldExe(); VoiceProgressTick(); } }
        else if (w == TIMER_FXKEYS) PollFxKeys();
        else if (w == TIMER_OSD) OsdTick();
        else if (w == TIMER_PICANIM) { if (!gMoving) PicAnimTick(); }   // (a GIF background pauses while you drag)
        else if (w == TIMER_STKSIZE) {          // a picture was resized: decode it again at its new size (sharp, fast)
            KillTimer(h, TIMER_STKSIZE);
            bool any = false;
            for (int i = 0; i < gStkN; i++) if (gStk[i].stale) { StkEnsureDecoded(gStk[i]); any = true; }
            if (gBase.gp && gPicFit == 4) { PictureRebuild(); PicRedraw(nullptr); }
            else if (any) StkRefresh(nullptr);
            PicAnimTimer();
        }
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
    case WM_PIC_DECODED:
        OnPicDecoded((PicJob*)l);
        return 0;
    case WM_OUTPUT_LOST: {                      // an extra output's device went away: close it; the timer reopens it
        const int k = (int)w;
        if (k > 0 && k < MAX_OUT && gExtraRunning[k]) {
            ringOn[k] = false; gExtraRunning[k] = false;
            ma_device_uninit(&gExtraDev[k]);
            gOutWait[k] = 0; gOutNextTry[k] = GetTickCount() + 2000;
        }
        return 0;
    }
    case WM_RENAME_DONE:
        ChanRenameDone(w != 0);
        return 0;
    case WM_WS_MSG:                             // remote control: run a command
        if (gWsThread) WsExec((int)w, (const char*)l);
        HeapFree(GetProcessHeap(), 0, (void*)l);
        return 0;
    case WM_WS_CONN:
        if (l) gWsCount++;
        else {
            gWsCount = Imax(0, gWsCount - 1);
            for (int i = 0; i < gWsAuthedN; i++) if (gWsAuthed[i] == (int)w) { gWsAuthed[i] = gWsAuthed[--gWsAuthedN]; break; }
        }
        if (l && gWsThread) { char r[700]; WsStatusJson(r, 700); WsQueue((int)w, r); }   // (a newcomer gets the state)
        WsStatusText();
        return 0;
    case WM_WS_STATE:
        if (gWsThread) { gWsState = (int)w; WsStatusText(); }
        return 0;
    case WM_APPS_SCANNED: {                     // the background scan: the apps list, icons, and apps that just opened
        AppScan* sc = (AppScan*)l;
        gAppCache = *sc; gAppCacheOk = true;
        for (int c = 0; c < CH_MAX; c++) {
            if (gCh[c].type != CH_APP || lstrcmpiW(sc->want[c], gCh[c].src)) continue;   // (changed meanwhile)
            if (sc->path[c][0] && lstrcmpiW(gChIconSrc[c], gCh[c].src)) ChanIconFromPath(c, sc->path[c]);
            if (gRunning && !gStopping && sc->pid[c] && (gChLost[c] || !gChRun[c])) ChanStartPid(c, sc->pid[c]);
        }
        HeapFree(GetProcessHeap(), 0, sc);
        return 0;
    }
    case WM_NVSA_READY:
        OnNvsaReady((NvsaJob*)l);
        return 0;
    case WM_NVSA_DONE: {
        gNvsaBusy = false;
        SetDlgItemTextW(gWnd, IDC_TTSSPEAK, L"Speak"); FitOne(GetDlgItem(gWnd, IDC_TTSSPEAK));
        TtsListVoices(); TtsFillVoices();
        if (gTtsAccent > 0) { int v = TtsVoiceFor(gTtsAccent); if (v >= 0) { lstrcpynW(gTtsVoice, gTtsNames[v], 128); TtsFillVoices(); } }
        int nat = 0; for (int i = 0; i < gTtsCount; i++) if (TtsIsNatural(gTtsNames[i])) nat++;
        wchar_t m[400];
        if (nat) wsprintfW(m, L"Found %d natural voice%s. They're at the top of the voice list, and accents use them first.", nat, nat == 1 ? L"" : L"s");
        else lstrcpynW(m, L"No natural voices showed up yet. If you installed the add-on and turned voices on, restart Lag Effect. "
                          L"(Narrator's natural voices also need adding in Settings > Accessibility > Narrator.)", 400);
        MessageBoxW(gWnd, m, L"Lag Effect - Natural voices", MB_ICONINFORMATION);
        return 0;
    }
    case WM_VOICES_LISTED:
        if (!gTtsListed) {
            TtsAdopt(*(VoiceList*)l);
            if (gTtsAccent > 0) { int v = TtsVoiceFor(gTtsAccent); if (v >= 0) lstrcpynW(gTtsVoice, gTtsNames[v], 128); }   // show the accent's voice
            TtsFillVoices();
        }
        HeapFree(GetProcessHeap(), 0, (void*)l);
        return 0;
    case WM_VOICE_INSTALLED:
        OnVoiceInstalled((DWORD)w, (int)l);
        return 0;
    case WM_DROPFILES:
        OnDropFiles((HDROP)w);
        return 0;
    case WM_SIZE:                               // the picture is sized to the window
        if (PicActive() && w != SIZE_MINIMIZED) { PictureRebuild(); InvalidateRect(h, nullptr, TRUE); }
        EdFollow();
        if (w != SIZE_MINIMIZED && gUiReady) {  // free sizing: centre the page, the Mixer fills the width / height
            static bool busy = false;
            if (!busy) {
                busy = true;
                if (!gOwnSize && !IsZoomed(h) && !gCompact) {   // remember how much bigger than needed you made it
                    RECT c; GetClientRect(h, &c);
                    gExtraW = Imax(0, (int)c.right - Imax(SC(CLIENT_W), MixerNeedW()));
                    gExtraH = Imax(0, (int)c.bottom - SC(DesignH()));
                }
                PlaceAll(); MixerPlace(); PlaceTabs();
                InvalidateRect(h, nullptr, FALSE);
                busy = false;
            }
        }
        break;
    case WM_ENTERSIZEMOVE: gMoving = true; break;
    case WM_EXITSIZEMOVE:  gMoving = false; break;
    case WM_GETMINMAXINFO: {                    // never smaller than the layout needs
        MINMAXINFO* mm = (MINMAXINFO*)l;
        RECT r = { 0, 0, Imax(SC(CLIENT_W), MixerNeedW()), SC(gWnd ? DesignH() : BASE_H) };
        AdjustWindowRect(&r, (DWORD)GetWindowLongW(h, GWL_STYLE), FALSE);
        mm->ptMinTrackSize.x = r.right - r.left; mm->ptMinTrackSize.y = r.bottom - r.top;
        return 0;
    }
    case WM_MOUSEWHEEL: {                       // the wheel goes to the fader under the mouse
        POINT pt = { (short)LOWORD(l), (short)HIWORD(l) };
        HWND t = WindowFromPoint(pt);
        if (t && t != h && IsChild(h, t)) {
            wchar_t cls[16]; GetClassNameW(t, cls, 16);
            if (!lstrcmpW(cls, L"LagFader")) return SendMessageW(t, m, w, l);
        }
        break;
    }
    case WM_MOVE:
        EdFollow();                             // the move-things-around layer stays over the window
        break;
    case WM_COPYDATA: {                         // command-line control from another LagEffect.exe (if allowed)
        const COPYDATASTRUCT* cd = (const COPYDATASTRUCT*)l;
        if (cd && cd->dwData == 0x4C414731 && cd->cbData >= sizeof(wchar_t)) {
            static wchar_t cmd[2048];
            lstrcpynW(cmd, (const wchar_t*)cd->lpData, (int)Min<DWORD>(2048, cd->cbData / sizeof(wchar_t)));
            ExecCommandLine(cmd);
        }
        return TRUE;
    }
    case WM_TTS_DONE:
        OnTtsDone((TtsJob*)l);
        return 0;
    case WM_SHOW_ME:                            // someone opened Lag Effect again: show this one
        FromTray();
        return 0;
    case WM_SONGFILE_LOADED:
        OnSongFileLoaded((SongFileJob*)l);
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
    case WM_DRAWITEM: {
        DRAWITEMSTRUCT* d = (DRAWITEMSTRUCT*)l;
        const RECT rc = d->rcItem; const int bw = rc.right - rc.left, bh = rc.bottom - rc.top;
        const bool buffer = w != IDC_METER && d->CtlType != ODT_COMBOBOX && d->CtlType != ODT_LISTBOX && bw > 0 && bh > 0;
        HDC real = d->hDC, mem = nullptr;
        OffScreen* os = buffer ? new OffScreen(real, bw, bh) : nullptr;
        if (os && os->dc) { mem = os->dc; SetViewportOrgEx(mem, -rc.left, -rc.top, nullptr); d->hDC = mem; }
        if (gBrPicture) {                       // the picture behind owner-drawn controls lines up with the window
            POINT pt = { 0, 0 }; MapWindowPoints(d->hwndItem, gWnd, &pt, 1);
            SetBrushOrgEx(d->hDC, -pt.x - (mem ? rc.left : 0), -pt.y - (mem ? rc.top : 0), nullptr);
        }
        bool done = DrawItemDispatch(w, d);
        if (mem) {
            BitBlt(real, rc.left, rc.top, bw, bh, mem, rc.left, rc.top, SRCCOPY);
            d->hDC = real;
        }
        delete os;
        if (done) return TRUE;
        break;
    }
    case WM_SETCURSOR:                          // a strip's right edge: the resize arrows
        if ((HWND)w == h && LOWORD(l) == HTCLIENT) {
            POINT p; GetCursorPos(&p); ScreenToClient(h, &p);
            if (gEdgeDrag >= 0 || MixerEdgeAt(p.x, p.y) >= 0) { SetCursor(LoadCursor(nullptr, IDC_SIZEWE)); return TRUE; }
        }
        break;
    case WM_LBUTTONDOWN: {                      // click on empty space: leave the text/number box you were in
        SetFocus(h);
        const int x = (short)LOWORD(l), y = (short)HIWORD(l), e = MixerEdgeAt(x, y);
        if (e >= 0) {
            if (e == gEdgeLast && GetTickCount() - gEdgeLastT < GetDoubleClickTime()) {   // double-click: normal width
                gEdgeLast = -1; MixerEdgeSet(e, 0); return 0;
            }
            gEdgeLast = e; gEdgeLastT = GetTickCount();
            gEdgeDrag = e; gEdgeX0 = x; gEdgeW0 = e < CH_MAX ? ChW(e) : OutW(e - CH_MAX);
            SetCapture(h);
        }
        return 0;
    }
    case WM_MOUSEMOVE:
        if (gEdgeDrag >= 0 && GetCapture() == h) MixerEdgeSet(gEdgeDrag, gEdgeW0 + UNSC((short)LOWORD(l) - gEdgeX0));
        break;
    case WM_LBUTTONUP:
        if (gEdgeDrag >= 0) { gEdgeDrag = -1; ReleaseCapture(); }
        break;
    case WM_CAPTURECHANGED:
        gEdgeDrag = -1;
        break;
    case WM_CONTEXTMENU: {                      // right-click a Voice FX hotkey button to clear it
        int id = GetDlgCtrlID((HWND)w);
        if (id == IDC_FXKEY_MASTER) { ClearFxKey(0); return 0; }
        if (id >= IDC_FXGRP_KEY && id < IDC_FXGRP_KEY + FX_GROUPS) { ClearFxKey(1 + id - IDC_FXGRP_KEY); return 0; }
        if (id == IDC_MUTEKEY) { ClearFxKey(SLOT_MUTE); return 0; }
        if (id >= IDC_PADKEY && id < IDC_PADKEY + PADS) { ClearFxKey(SLOT_PAD0 + id - IDC_PADKEY); return 0; }
        if (id >= IDC_PADPLAY && id < IDC_PADPLAY + PADS) { gPads[PadSlot(id - IDC_PADPLAY)].stop = true; return 0; }   // right-click: stop
        if (id == IDC_REWINDKEY)  { ClearFxKey(SLOT_REWIND); return 0; }
        if (id == IDC_PROFNEXTKEY) { ClearFxKey(SLOT_PROFNEXT); return 0; }
        if (id == IDC_PTTKEY)      { ClearFxKey(SLOT_PTT); return 0; }
        if (id >= IDC_MIXKEY0 && id < IDC_MIXKEY0 + (KEY_SLOTS - SLOT_MIX0)) { ClearFxKey(SLOT_MIX0 + id - IDC_MIXKEY0); return 0; }
        if (id >= IDC_COLSW0 && id < IDC_COLSW0 + USERCOL_N) { gUserCol[id - IDC_COLSW0] = CLR_NONE; ApplyTheme(); return 0; }
        if (id == IDC_VERSION) {                // hidden: command-line control for Stream Deck / scripts
            HMENU mm = CreatePopupMenu();
            AppendMenuW(mm, MF_STRING | (gCmdLine ? MF_CHECKED : 0), 1, L"Allow command-line control (Stream Deck, scripts)");
            AppendMenuW(mm, MF_STRING, 2, L"How to use it...");
            POINT pt; GetCursorPos(&pt);
            int cmd = TrackPopupMenu(mm, TPM_RETURNCMD | TPM_NONOTIFY, pt.x, pt.y, 0, gWnd, nullptr);
            DestroyMenu(mm);
            if (cmd == 1) gCmdLine = !gCmdLine;
            if (cmd == 2) MessageBoxW(gWnd,
                L"With this on, running LagEffect.exe with these switches controls the running copy:\n\n"
                L"/mute  /unmute  /togglemute\n/fx on | off | toggle\n/profile \"Name\"   /nextprofile\n/character \"Demon\"\n"
                L"/pad 1-32   /clip 1-32   /clipnow   /stopall\n/rewind   /repeat   /tapestop\n/start   /stop   /page A-D\n\n"
                L"Example for a Stream Deck \"Open\" action:\n\"C:\\...\\LagEffect.exe\" /profile \"Gaming\"",
                L"Lag Effect - Command-line control", MB_ICONINFORMATION);
            return 0;
        }
        if (id == IDC_TAPEKEY)     { ClearFxKey(SLOT_TAPESTOP); return 0; }
        if (id == IDC_DIVEKEY)     { ClearFxKey(SLOT_DIVE); return 0; }
        if (id == IDC_PROFKEY && gProfSel >= 0) { ClearFxKey(SLOT_PROF0 + gProfSel); return 0; }
        if (id == IDC_REPEATKEY)  { ClearFxKey(SLOT_REPEAT); return 0; }
        if (id == IDC_PADBANKKEY) { ClearFxKey(SLOT_PADBANK); return 0; }
        if (id >= IDC_CLIPKEY && id < IDC_CLIPKEY + CLIPS) { ClearFxKey(SLOT_CLIP0 + id - IDC_CLIPKEY); return 0; }
        if (id == IDC_CLIPNOWKEY) { ClearFxKey(SLOT_CLIPNOW); return 0; }
        if (id >= IDC_CLIPPLAY && id < IDC_CLIPPLAY + CLIPS) { gPads[CLIP0 + ClipSlot(id - IDC_CLIPPLAY)].stop = true; return 0; }
        break;
    }
    case WM_MEASUREITEM:
        if (w == IDC_COLORTHEME) { ((MEASUREITEMSTRUCT*)l)->itemHeight = SC(20); return TRUE; }
        break;
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
    case WM_ERASEBKGND:
        return 1;                               // WM_PAINT fills the background (no erase-then-draw flash)
    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC dc = BeginPaint(h, &ps);
        RECT rc; GetClientRect(h, &rc);
        HDC mem = CreateCompatibleDC(dc);
        HBITMAP bmp = CreateCompatibleBitmap(dc, rc.right, rc.bottom);
        HGDIOBJ ob = SelectObject(mem, bmp);
        FillRect(mem, &rc, BgBrush());
        PaintWindow(mem);
        BitBlt(dc, ps.rcPaint.left, ps.rcPaint.top, ps.rcPaint.right - ps.rcPaint.left, ps.rcPaint.bottom - ps.rcPaint.top,
               mem, ps.rcPaint.left, ps.rcPaint.top, SRCCOPY);
        SelectObject(mem, ob); DeleteObject(bmp); DeleteDC(mem);
        EndPaint(h, &ps);
        return 0;
    }
    case WM_CTLCOLORSTATIC: case WM_CTLCOLORBTN: case WM_CTLCOLOREDIT: case WM_CTLCOLORLISTBOX:
        return CtlColor(h, m, w, l);
    case WM_CLOSE: {
        WINDOWPLACEMENT wp = {}; wp.length = sizeof(wp);   // remember where the window was
        if (GetWindowPlacement(h, &wp)) {
            SaveInt(L"win_x", wp.rcNormalPosition.left);
            SaveInt(L"win_y", wp.rcNormalPosition.top);
        }
        if (!gNoSaveOnExit) SaveSettings();     // (after Import, the imported file is kept as it is)
        WsStop();
        StopAudio();
        RemoveTray();
        DestroyWindow(h);
        return 0;
    }
    case WM_QUERYENDSESSION:                    // Windows is restarting / shutting down: save now (no WM_CLOSE comes)
        if (!gNoSaveOnExit) {
            WINDOWPLACEMENT wp = {}; wp.length = sizeof(wp);
            if (GetWindowPlacement(h, &wp)) { SaveInt(L"win_x", wp.rcNormalPosition.left); SaveInt(L"win_y", wp.rcNormalPosition.top); }
            SaveSettings();
        }
        return TRUE;
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
    icc.dwICC = ICC_STANDARD_CLASSES | ICC_UPDOWN_CLASS | ICC_BAR_CLASSES;   // BAR = tooltips
    InitCommonControlsEx(&icc);

    bool justUpdated = wcsstr(GetCommandLineW(), L"--updated") != nullptr;
    gResumeAudio = justUpdated && wcsstr(GetCommandLineW(), L"--resume") != nullptr;

    // One copy at a time: a second launch brings the running one to the front instead of fighting it
    // for the mic. After an update, wait for the old version to finish closing.
    HANDLE single = CreateMutexW(nullptr, TRUE, L"LagEffect.SingleInstance");
    if (single && GetLastError() == ERROR_ALREADY_EXISTS) {
        if (justUpdated) WaitForSingleObject(single, 5000);
        else {
            HWND other = FindWindowW(L"LagEffectWnd", nullptr);
            const wchar_t* cl = GetCommandLineW();
            bool hasArgs = false;                   // "/mute", "/profile X"...: hand them to the running copy
            { int ac = 0; LPWSTR* av = CommandLineToArgvW(cl, &ac); if (av) { for (int i = 1; i < ac; i++) if (av[i][0] == L'/') hasArgs = true; LocalFree(av); } }
            if (other && hasArgs) {
                COPYDATASTRUCT cd = { 0x4C414731, (DWORD)((lstrlenW(cl) + 1) * sizeof(wchar_t)), (PVOID)cl };
                SendMessageW(other, WM_COPYDATA, 0, (LPARAM)&cd);
            } else if (other) {
                DWORD pid = 0; GetWindowThreadProcessId(other, &pid);
                AllowSetForegroundWindow(pid);
                PostMessageW(other, WM_SHOW_ME, 0, 0);
            }
            return 0;
        }
    }

    LoadSettings();
    LoadThemeApis();
    gNs = rnnoise_create(nullptr);              // built-in model; created once, used by the audio thread
    gCtxOk = ma_context_init(nullptr, 0, nullptr, &gCtx) == MA_SUCCESS;
    if (gCtxOk) ma_context_get_devices(&gCtx, &gPlayDevs, &gPlayCount, &gCapDevs, &gCapCount);

    gFont     = CreateFontW(-SC(gFontPx), 0, 0, 0, FW_NORMAL,   0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, gFontName);
    gFontBold = CreateFontW(-SC(gFontPx), 0, 0, 0, FW_SEMIBOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, gFontName);
    gFontOsd  = CreateFontW(-20, 0, 0, 0, FW_SEMIBOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
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

    WNDCLASSW oc = {};                                   // hotkey pop-up
    oc.lpfnWndProc   = OsdProc;
    oc.hInstance     = hi;
    oc.hCursor       = LoadCursorW(nullptr, IDC_ARROW);
    oc.lpszClassName = L"LagOsd";
    RegisterClassW(&oc);

    WNDCLASSW tc = {};                                   // clip trim editor + its waveform
    tc.lpfnWndProc   = TrimProc;
    tc.hInstance     = hi;
    tc.hIcon         = gIcon;
    tc.hCursor       = LoadCursorW(nullptr, IDC_ARROW);
    tc.lpszClassName = L"LagTrim";
    RegisterClassW(&tc);
    tc.lpfnWndProc   = WaveProc;
    tc.hIcon         = nullptr;
    tc.lpszClassName = L"LagWave";
    RegisterClassW(&tc);
    {                                           // the Mixer's faders
        WNDCLASSW fc = {};
        fc.style = CS_DBLCLKS | CS_HREDRAW | CS_VREDRAW; fc.lpfnWndProc = FaderProc; fc.hInstance = hi;
        fc.hCursor = LoadCursorW(nullptr, IDC_HAND); fc.lpszClassName = L"LagFader";
        RegisterClassW(&fc);
    }

    gRecVoice.buf = (short*)HeapAlloc(GetProcessHeap(), 0, REC_LEN * sizeof(short));   // instant replay buffers
    gRecPc.buf    = (short*)HeapAlloc(GetProcessHeap(), 0, REC_LEN * sizeof(short));
    ClipFolder();

    DWORD style = WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_MAXIMIZEBOX | WS_THICKFRAME | WS_CLIPCHILDREN;
    RECT r = { 0, 0, SC(CLIENT_W), SC(BASE_H) };
    AdjustWindowRect(&r, style, FALSE);
    int wx = CW_USEDEFAULT, wy = CW_USEDEFAULT;          // reopen where it was, if that's still on a screen
    if (gWinX != INT_MIN && gWinY != INT_MIN) {
        POINT probe = { gWinX + 60, gWinY + 15 };        // a point on the title bar
        if (MonitorFromPoint(probe, MONITOR_DEFAULTTONULL)) { wx = gWinX; wy = gWinY; }
    }
    HWND h = CreateWindowExW(0, wc.lpszClassName, L"Lag Effect " APP_VERSION, style, wx, wy,
                             r.right - r.left, r.bottom - r.top, nullptr, nullptr, hi, nullptr);
    if (!h) return 1;
    if (gTopMost) SetWindowPos(h, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);

    if (!gCtxOk) MessageBoxW(h, L"Couldn't start the Windows audio system.", L"Lag Effect", MB_ICONERROR);
    if (gAutoStart && !justUpdated) ToTray();
    else { ShowWindow(h, show); UpdateWindow(h); }

    if (justUpdated)
        MessageBoxW(h, L"Lag Effect was updated to version " APP_VERSION L".", L"Lag Effect", MB_ICONINFORMATION);
    else if (gUpdateOnStart && gUpdateRepo[0])
        StartUpdateCheck(false);

    MSG msg;
    SendMessageW(h, WM_CHANGEUISTATE, MAKEWPARAM(UIS_SET, UISF_HIDEFOCUS), 0);   // (no focus boxes until you use the keyboard)
    auto setKbdNav = [&](bool on) {
        gKbdNav = on;
        SendMessageW(h, WM_CHANGEUISTATE, MAKEWPARAM(on ? UIS_CLEAR : UIS_SET, UISF_HIDEFOCUS), 0);
        RedrawWindow(h, nullptr, nullptr, RDW_INVALIDATE | RDW_ALLCHILDREN);
    };
    while (GetMessageW(&msg, nullptr, 0, 0) > 0) {
        if (gKbdNav && (msg.message == WM_LBUTTONDOWN || msg.message == WM_RBUTTONDOWN) && (msg.hwnd == h || IsChild(h, msg.hwnd)))
            setKbdNav(false);
        else if (!gKbdNav && msg.message == WM_KEYDOWN && (msg.hwnd == h || IsChild(h, msg.hwnd)) &&
                 (msg.wParam == VK_TAB || msg.wParam == VK_LEFT || msg.wParam == VK_RIGHT || msg.wParam == VK_UP || msg.wParam == VK_DOWN))
            setKbdNav(true);
        if (msg.message == WM_KEYDOWN && msg.wParam == VK_TAB && (GetKeyState(VK_CONTROL) & 0x8000) &&
            (msg.hwnd == h || IsChild(h, msg.hwnd))) {
            { int slot = 0; for (int i = 0; i < TAB_SHOWN; i++) if (TAB_ORDER[i] == gPage) slot = i;   // Ctrl+Tab: next page
              for (int n = 1; n < TAB_SHOWN; n++) { const int pg = TAB_ORDER[(slot + n) % TAB_SHOWN]; if (PageOn(pg)) { SetPage(pg); break; } } }
            continue;
        }
        if (msg.message == WM_KEYDOWN && msg.wParam >= '1' && msg.wParam < '1' + TAB_COUNT &&
            (GetKeyState(VK_CONTROL) & 0x8000) && (msg.hwnd == h || IsChild(h, msg.hwnd))) {
            SetPage((int)(msg.wParam - '1'));   // Ctrl+1..6: jump to a tab
            continue;
        }
        if (TrimKey(&msg)) continue;
        if (msg.message == WM_KEYDOWN && msg.wParam == 'M' && (GetKeyState(VK_CONTROL) & 0x8000) && (msg.hwnd == h || IsChild(h, msg.hwnd))) {
            SetCompact(!gCompact);              // Ctrl+M: compact window
            continue;
        }
        if (msg.message == WM_KEYDOWN && msg.wParam == VK_RETURN && GetParent(msg.hwnd) == GetDlgItem(h, IDC_PROFILE)) {
            ProfileSaveClicked();               // Enter in the profile name box saves it
            continue;
        }
        if (msg.message == WM_KEYDOWN && msg.wParam == VK_RETURN && msg.hwnd == GetDlgItem(h, IDC_TTSTEXT)) {
            TtsSpeak();                         // Enter in the text-to-speech box speaks it
            continue;
        }
        if (gTrimWnd && IsDialogMessageW(gTrimWnd, &msg)) continue;
        if (!IsDialogMessageW(h, &msg)) {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
    }
    if (gCtxOk) ma_context_uninit(&gCtx);
    DeleteObject(gFont);
    DeleteObject(gFontBold);
    DeleteObject(gFontOsd);
    if (single) CloseHandle(single);
    return 0;
}
