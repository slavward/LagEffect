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

#define APP_VERSION L"1.11.1"
#define DEFAULT_UPDATE_REPO L"slavward/LagEffect"

#define UNICODE
#define _UNICODE
#define NOMINMAX
#define MINIAUDIO_IMPLEMENTATION
#include "miniaudio.h"
#include "rnnoise/include/rnnoise.h"           // AI noise suppression (BSD licence, see rnnoise/COPYING)

#include <windows.h>
#include <commctrl.h>
#include <shellapi.h>
#include <winhttp.h>
#include <mmdeviceapi.h>                        // listing apps that play sound (Vocode to song)
#include <audiopolicy.h>
#include <tlhelp32.h>                           // process names without opening the process (browsers' audio helpers)
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
#pragma comment(lib, "ole32.lib")
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
static volatile int   gTalkVolPct = 100;
#define MAX_KEYS 3                             // hotkey can be a combination of up to 3 keys
static volatile int   gHotkeys[MAX_KEYS] = { VK_F8, 0, 0 };
static volatile bool  gToggleMode = false, gTalkOver = false;
static volatile bool  gCapturingKey = false, gLooping = false;
static volatile int   gRowMode[MAX_OUT] = { MODE_ALL, MODE_EFFECT, MODE_EFFECT, MODE_EFFECT, MODE_EFFECT };
static volatile int   gRowVol[MAX_OUT]  = { 100, 100, 100, 100, 100 };

static float  hist[HIST], frozen[HIST], hann[MAXGRAIN];
static size_t wpos = 0, frozenLen = 1;
static bool   looping = false, prevDown = false, toggled = false;
static double loopPos = 0, grainStart[2];
static int    grainAge[2], grainLen = 2;
static float  gateEnv = 0, gateGain = 1;
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
static volatile bool     ringOn[MAX_OUT];

static inline double WrapPos(double p, double len)
{
    while (p >= len) p -= len;
    while (p < 0) p += len;
    return p;
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

static inline float SongRead()                  // audio thread
{
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

static float VocodeBands(VocState& v, float mod, float car)   // channel vocoder: car shaped by mod
{
    float voc = 0;
    for (int b = 0; b < VOC_BANDS; b++) {
        float m = BqRun(v.modBp[b][1], BqRun(v.modBp[b][0], mod));
        float c = BqRun(v.carBp[b][1], BqRun(v.carBp[b][0], car));
        float am = m < 0 ? -m : m, ac = c < 0 ? -c : c;
        v.modEnv[b] += (am - v.modEnv[b]) * (am > v.modEnv[b] ? 0.007f : 0.0014f);   // ~3 ms attack, ~15 ms release
        v.carEnv[b] += (ac - v.carEnv[b]) * 0.0014f;
        voc += c * v.modEnv[b] / (v.carEnv[b] + 0.0005f);         // carrier flattened, voice's shape applied
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
        float voc = VocodeBands(v, x, song) * SONG_GAIN;
        voc += BqRun(v.sibHp[1], BqRun(v.sibHp[0], x)) * 0.5f;   // keep "s" and "t" sounds clear
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

static void FxReset()                          // audio thread only
{
    PsReset(gPsFx); PsReset(gPsTune); VocReset(); RadioReset();
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
    const bool   fxVoc   = gFxOn && gFxVocOn;
    if (fxVoc) VocBlock();
    const bool   fxRadio = gFxOn && gFxRadioOn;
    if (fxRadio) RadioBlock();
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

    for (ma_uint32 f = 0; f < frames; f++) {
        float s = in ? in[f] * boost : 0.0f;
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

        if (lvAmt > 0) {                        // leveler: gentle compressor above -30 dBFS + make-up gain
            float pw = s * s;
            lvEnv += (pw - lvEnv) * (pw > lvEnv ? 0.0042f : 0.0001f);   // ~5 ms attack, ~200 ms release
            float lvl = 10.0f * log10f(lvEnv + 1e-12f);
            float gdb = (lvl > -30.0f ? (-30.0f - lvl) * (1.0f - 1.0f / lvRatio) : 0.0f) + lvMakeupDb;
            s *= powf(10.0f, gdb / 20.0f);
        }

        if (fxPitch) s = PitchShift(gPsFx, s, psRatio, psGrain, psMix);
        if (fxVoc)   s = Vocoder(s);
        if (fxRev)   s = Reverb(s, rvSize, rvDamp, rvMix, rvPre);
        if (fxRadio) s = Radio(s);                  // last: you're heard *through* the device

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
        }

        float o = Limit(0, RowSignal(mode[0], effect, everything) * vol[0]);
        out[f * 2] = o;
        out[f * 2 + 1] = o;

        for (int k = 1; k < MAX_OUT; k++) {
            if (!on[k] || (w[k] - r[k]) >= RING_SIZE) continue;
            ring[k][w[k] & (RING_SIZE - 1)] = Limit(k, RowSignal(mode[k], effect, everything) * vol[k]);
            w[k]++;
        }
    }
    MemoryBarrier();
    for (int k = 1; k < MAX_OUT; k++) if (on[k]) ringW[k] = w[k];
    if (blockPeak > gMeterPeak) gMeterPeak = blockPeak;
    gMeterVad = nsStage ? nsVad : -1.0f;
    gMeterGateOpen = gateHold > 0;
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
    IDC_THEME, IDC_REPO, IDC_CHECKUPD, IDC_UPDSTART, IDC_HDR, IDC_TAB0, IDC_TAB1, IDC_TAB2, IDC_TAB3,   // tabs must stay consecutive
    IDC_FXON, IDC_FXKEY_MASTER, IDC_METER, IDC_GATEMODE, IDC_NSON, IDC_OPENSET, IDC_VOCSTYLE, IDC_VOCKEY, IDC_VOCSCALE, IDC_VOCRANGE, IDC_HIDESHARE, IDC_COLORTHEME, IDC_SONGBTN, IDC_SONGSRC, IDC_SONGSTATUS, IDC_RADIOPRESET, IDC_RADIODESC,
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
static ma_device gSongDev;                        // loopback capture of the music (Vocode to song)
static bool      gSongRunning = false;
static volatile bool gSongLost = false, gSongRetryNow = false;
static bool gCtxOk = false, gRunning = false, gWantRunning = false, gStopping = false;
static bool gExtraRunning[MAX_OUT];
static ma_device_info *gPlayDevs = nullptr, *gCapDevs = nullptr; static ma_uint32 gPlayCount = 0, gCapCount = 0;
static int  gRows = 1, gBufIdx = 2;
static bool gExclusive = false, gAutoStart = false, gInTray = false, gUiReady = false;
static bool gHideShare = false;                 // lock virtual-cable outputs so screen shares can't record them
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
};

// Voice FX page: one group (section) per effect, each with an on/off box and a row of knobs.
struct FxGroup { const wchar_t* title; volatile bool* on; const wchar_t* key; bool def; const wchar_t* hotkeyKey; };
static FxGroup gFxGroups[] = {
    { L"Pitch",  &gFxPitchOn, L"fx_pitch_on",  true, L"fx_pitch_hotkey"  },
    { L"Reverb", &gFxRevOn,   L"fx_reverb_on", true, L"fx_reverb_hotkey" },
    { L"Vocoder", &gFxVocOn,  L"fx_vocoder_on", true, L"fx_vocoder_hotkey" },
    { L"Radio",   &gFxRadioOn, L"fx_radio_on",  true, L"fx_radio_hotkey" },
};
#define FX_GROUPS ((int)(sizeof(gFxGroups) / sizeof(gFxGroups[0])))

// Optional hotkeys that switch Voice FX on/off: slot 0 = the whole page, slot 1+g = effect group g.
// Each is a combination of up to MAX_KEYS keys (0 = unused). Polled by the window (TIMER_FXKEYS).
#define FX_KEY_SLOTS (1 + FX_GROUPS)
static int  gFxKeys[FX_KEY_SLOTS][MAX_KEYS];
static bool gFxKeyWasDown[FX_KEY_SLOTS];

// Knob groups: 0..FX_GROUPS-1 are the Voice FX effects; the rest live on the Mic tab.
enum { KG_PITCH = 0, KG_REVERB = 1, KG_VOCODER = 2, KG_RADIO = 3, KG_NS = 4, KG_GATE = 5, KG_TONE = 6 };
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
    { L"Strength",  L"%",   0,   100, 100, &gNsStrength,    L"ns_strength",       KG_NS,   false, nullptr },
    { L"Threshold", L" dB", -90, -10, -50, &gGateThrDb,     L"gate_threshold_db", KG_GATE, false, nullptr },
    { L"Voice",     L"%",   10,  99,  60,  &gGateVoicePct,  L"gate_voice_pct",    KG_GATE, false, nullptr },
    { L"Hold",      L" ms", 0,   1000, 150, &gGateHoldMs,   L"gate_hold_ms",      KG_GATE, false, nullptr },
    { L"Release",   L" ms", 10,  1000, 80, &gGateReleaseMs, L"gate_release_ms",   KG_GATE, false, nullptr },
    { L"Range",     L" dB", 0,   80,  80,  &gGateRangeDb,   L"gate_range_db",     KG_GATE, false, nullptr },
    { L"Mic boost", L" dB", -12, 24,  0,   &gMicBoostDb,    L"mic_boost_db",      KG_TONE, true, nullptr  },
    { L"Low cut",   L" Hz", 0,   300, 80,  &gLowCutHz,      L"low_cut_hz",        KG_TONE, false, L"Off" },
    { L"Leveler",   L"%",   0,   100, 0,   &gLevelerPct,    L"leveler",           KG_TONE, false, L"Off" },
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
static HBRUSH gBrDarkBg, gBrDarkCtl, gBrLightBg;
static HWND   gTip;                             // hover-help tooltip window (see AddTips)

// ---- color themes ----
// Each theme has an accent (knobs, switches, tabs, checkboxes) in a bright version for dark mode and a
// deeper one for light mode, plus how strongly it tints the backgrounds. Add a row to add a theme.
struct ColorTheme { const wchar_t* name; COLORREF dark, light; float tint; };
static const ColorTheme COLOR_THEMES[] = {
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
};
#define COLOR_THEME_N ((int)(sizeof(COLOR_THEMES) / sizeof(COLOR_THEMES[0])))
static int gColorTheme = 0;

// The palette in use (set by ApplyPalette). The old constant names now point at these.
static COLORREF gDkBg, gDkCtl, gDkBorder, gDkSection, gDkText = RGB(235, 235, 235), gDkDim = RGB(160, 160, 160);
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
    if (gBrDarkBg)  DeleteObject(gBrDarkBg);
    if (gBrDarkCtl) DeleteObject(gBrDarkCtl);
    if (gBrLightBg) DeleteObject(gBrLightBg);
    gBrDarkBg  = CreateSolidBrush(gDkBg);
    gBrDarkCtl = CreateSolidBrush(gDkCtl);
    gBrLightBg = CreateSolidBrush(gLtBg);
}

static COLORREF BgColor()  { return gDark ? DK_BG : gLtBg; }
static HBRUSH   BgBrush()  { return gDark ? gBrDarkBg : gBrLightBg; }

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

static void ApplyTheme()
{
    gDark = gThemeMode == THEME_DARK || (gThemeMode == THEME_SYSTEM && SystemUsesDark());
    ApplyPalette();
    if (pDwmSetWindowAttribute) {
        BOOL d = gDark;
        if (FAILED(pDwmSetWindowAttribute(gWnd, 20, &d, sizeof(d))))    // DWMWA_USE_IMMERSIVE_DARK_MODE
            pDwmSetWindowAttribute(gWnd, 19, &d, sizeof(d));            // older Windows 10 builds
        // Windows 11: title bar matches the window, thin border in the accent (Classic keeps Windows' own)
        bool tinted = COLOR_THEMES[Iclamp(gColorTheme, 0, COLOR_THEME_N - 1)].tint > 0;
        COLORREF cap = tinted ? BgColor() : 0xFFFFFFFF, brd = tinted ? ACCENT : 0xFFFFFFFF;   // 0xFFFFFFFF = default
        pDwmSetWindowAttribute(gWnd, 35, &cap, sizeof(cap));          // DWMWA_CAPTION_COLOR
        pDwmSetWindowAttribute(gWnd, 34, &brd, sizeof(brd));          // DWMWA_BORDER_COLOR
    }
    if (pSetPreferredAppMode) {                 // dark tray menu
        pSetPreferredAppMode(gDark ? 2 : 3);
        if (pFlushMenuThemes) pFlushMenuThemes();
    }
    EnumChildWindows(gWnd, ThemeChild, 0);
    if (gTip) SetTheme(gTip, gDark ? L"DarkMode_Explorer" : nullptr, nullptr);
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
static wchar_t gSongApp[64] = L"";               // Vocode to song: app to take music from ("" = all PC sound)
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
    gAutoStart     = INI_INT(L"autostart", 0) != 0;
    gThemeMode     = Iclamp(INI_INT(L"theme", THEME_SYSTEM), 0, 2);
    gColorTheme    = Iclamp(INI_INT(L"color_theme", 0), 0, COLOR_THEME_N - 1);
    gUpdateOnStart = INI_INT(L"update_on_start", 1) != 0;

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
    // Mic tab. Settings from 1.5 and older: gate=1/0 and gate_db=50 (meaning -50 dB).
    gNsOn         = INI_INT(L"ns_on", 0) != 0;
    gVocStyle     = Iclamp(INI_INT(L"voc_style", VOC_HARMONY), 0, VOC_STYLES - 1);
    gVocKey       = Iclamp(INI_INT(L"voc_key", 0), 0, 11);
    gVocScale     = Iclamp(INI_INT(L"voc_scale", 1), 0, VOC_SCALES - 1);
    gVocRange     = Iclamp(INI_INT(L"voc_range", VR_AUTO), 0, 2);
    GetPrivateProfileStringW(L"settings", L"voc_song_app", L"", gSongApp, 64, gIni);
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
    SaveInt(L"gate", gGateMode != GATE_OFF); SaveInt(L"talkover", gTalkOver);
    SaveInt(L"gate_mode", gGateMode); SaveInt(L"gate_last_mode", gGateLastMode); SaveInt(L"ns_on", gNsOn);
    SaveInt(L"voc_style", gVocStyle); SaveInt(L"voc_key", gVocKey); SaveInt(L"voc_scale", gVocScale); SaveInt(L"voc_range", gVocRange);
    WritePrivateProfileStringW(L"settings", L"voc_song_app", gSongApp, gIni);
    SaveInt(L"radio_preset", gRadioPreset);
    SaveInt(L"buffer", gBufIdx); SaveInt(L"exclusive", gExclusive); SaveInt(L"hide_from_share", gHideShare); SaveInt(L"autostart", gAutoStart);
    SaveInt(L"theme", gThemeMode); SaveInt(L"color_theme", gColorTheme); SaveInt(L"update_on_start", gUpdateOnStart);
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
    for (int k = 0; k < MAX_OUT; k++) ringOn[k] = false;
    if (gRunning) { ma_device_uninit(&gDev); gRunning = false; }
    for (int k = 0; k < MAX_OUT; k++)
        if (gExtraRunning[k]) { ma_device_uninit(&gExtraDev[k]); gExtraRunning[k] = false; }
    if (gSongRunning) { ma_device_uninit(&gSongDev); gSongRunning = false; }
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
#define ROW_Y0    134
#define ROW_H     30
#define TAB_COUNT 4
enum { PAGE_MAIN = 0, PAGE_MIC = 1, PAGE_FX = 2, PAGE_SETTINGS = 3 };

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
    case KG_TONE: return true;
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

    HBRUSH body = CreateSolidBrush(gDark ? DK_KNOB : LT_CARD);
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
    if (k.offText && *k.var == k.lo) lstrcpynW(txt, k.offText, 32);
    else wsprintfW(txt, k.bipolar && *k.var > 0 ? L"+%d%s" : L"%d%s", *k.var, k.unit);
    SelectObject(dc, gFontBold);
    SetTextColor(dc, on ? (gDark ? DK_TEXT : RGB(30, 30, 30)) : (gDark ? DK_DIM : RGB(130, 130, 130)));
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
    SendMessageW(c, CB_SETCURSEL, sel, 0);
}

static void SongNotify(const ma_device_notification* n)
{
    if (n->type == ma_device_notification_type_stopped && !gStopping) gSongLost = true;   // e.g. the app closed
}

static bool SongStartDevice(DWORD pid, bool exclude)
{
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

static bool SongModeOn() { return gFxOn && gFxVocOn && gVocStyle == VOC_SONG; }

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
    default: lstrcpynW(t, gRunning ? L"Turn on to vocode music" : L"Press Start on the Main tab", 96); break;
    }
    wchar_t cur[96];
    GetDlgItemTextW(gWnd, IDC_SONGSTATUS, cur, 96);
    if (lstrcmpW(cur, t)) SetDlgItemTextW(gWnd, IDC_SONGSTATUS, t);
}

// Starts / stops / re-targets the music capture to match the settings.
static void UpdateSongCapture()
{
    bool want = gRunning && SongModeOn();
    if (gSongRunning && (!want || gSongLost || lstrcmpiW(gSongActiveApp, gSongApp))) {
        ma_device_uninit(&gSongDev);
        gSongRunning = false;
    }
    if (!want) { gSongState = 0; UpdateSongStatusText(); return; }
    if (gSongRunning) { UpdateSongStatusText(); return; }

    lstrcpynW(gSongActiveApp, gSongApp, 64);
    if (gSongApp[0]) {                           // one app
        AudioApp apps[32];
        int n = ListAudioApps(apps, 32);
        DWORD pid = 0;
        for (int i = 0; i < n; i++) if (!lstrcmpiW(apps[i].name, gSongApp)) pid = apps[i].pid;
        if (!pid)                               gSongState = 4;   // not playing yet: the timer tries again
        else if (SongStartDevice(pid, false))   gSongState = 1;
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

static void SetSongMode(bool on)
{
    if (on) {
        if (gVocStyle != VOC_SONG) gPrevVocStyle = gVocStyle;
        gVocStyle = VOC_SONG;
        if (!gFxVocOn) SetFxGroupOn(KG_VOCODER, true);
        if (!gFxOn) SetFxOn(true);
    } else if (gVocStyle == VOC_SONG) {
        gVocStyle = gPrevVocStyle;
    }
    SendDlgItemMessageW(gWnd, IDC_VOCSTYLE, CB_SETCURSEL, gVocStyle, 0);
    SongStyleChanged();
    UpdateStatus(true);
}

static void SongTick()                          // every 50 ms
{
    static bool lastWant = false, lastOn = false;
    static DWORD lastTry = 0, lastHeard = 0;
    bool on = SongModeOn(), want = on && gRunning;
    if (on != lastOn) { lastOn = on; InvalidateRect(GetDlgItem(gWnd, IDC_SONGBTN), nullptr, FALSE); }
    DWORD now = GetTickCount();
    if (want != lastWant || (!want && gSongRunning) ||
        (want && (!gSongRunning || gSongLost) && (gSongRetryNow || now - lastTry > 1500))) {
        lastWant = want; lastTry = now; gSongRetryNow = false;
        UpdateSongCapture();
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
    COLORREF txt = on ? (gDark ? RGB(20, 20, 20) : RGB(255, 255, 255)) : (gDark ? DK_TEXT : RGB(30, 30, 30));
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
    Tip(GetDlgItem(gWnd, SPIN_UD(id)), text);
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
    TipId(IDC_TAB0 + PAGE_SETTINGS, L"Latency, theme, updates and where settings are saved.");

    // Main
    TipId(IDC_MIC, L"The microphone Lag Effect listens to.");
    for (int k = 0; k < MAX_OUT; k++) {
        TipId(IDC_ROWLBL + k,  L"An output: a device Lag Effect plays to.");
        TipId(IDC_ROWDEV + k,  L"Where this output plays: VB-Cable (for Discord, OBS and games), your headphones or speakers.");
        TipId(IDC_ROWMODE + k, L"Off = nothing. Effect only = just the stutter. Everything = your voice plus the stutter (what others should hear).");
        TipId(IDC_ROWVOL + k,  L"Volume of this output. 100% = unchanged, up to 200%.");
        TipId(IDC_ROWDEL + k,  L"Remove this output.");
    }
    TipId(IDC_ADDOUT,  L"Add another output (up to 5), e.g. VB-Cable for Discord plus your headphones to hear yourself.");
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
    TipId(IDC_TRAY,    L"Hide the window. Lag Effect keeps running in the system tray; click the tray icon to bring it back.");
    TipId(IDC_HELPBTN, L"How everything works, plus setup steps for Discord and OBS.");

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
    TipId(IDC_SONGSRC,  L"Where the music comes from: one app (Spotify, a browser...) or all PC sound except Lag Effect "
                        L"(so it never hears itself). Recording one app needs Windows 11. Open the list to refresh it.");
    TipId(IDC_SONGSTATUS, L"Whether the song is reaching the vocoder.");
    TipId(IDC_VOCRANGE, L"How high your voice is. Auto works it out as you sing. "
                        L"Low / deep: for bass and baritone voices; hears notes down to 50 Hz, uses longer, smoother slices "
                        L"for tuning, and puts harmonies above you instead of below (adds ~15 ms delay). High: tenor, alto, soprano.");
    TipId(IDC_VOCSCALE, L"Which notes are allowed. Major = happy, Minor = darker, Pentatonic = safe for most songs, "
                        L"Chromatic = every note (just smooths your pitch).");
    TipId(IDC_GATEMODE, L"What opens the gate. Volume: when you're louder than Threshold. Voice: when the AI hears speech "
                        L"(ignores loud non-voice noise). Volume + voice: both.");

    // Voice FX
    TipId(IDC_FXON,         L"Turn all voice effects on or off. Order: Pitch, Vocoder, Reverb, then Radio last, "
                            L"so you're heard through the device.\n"
                            L"Knobs: drag up/down or scroll (Shift = fine), double-click to reset. Hotkeys work from anywhere; "
                            L"right-click one (or press Backspace while setting it) to clear it.");
    TipId(IDC_FXKEY_MASTER, L"Set a hotkey that turns all voice effects on/off from anywhere. Right-click to clear it.");
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
                          L"Classic is the original look. Works with light and dark.");
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
    SetTextColor(dc, gDark ? DK_TEXT : RGB(30, 30, 30));
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

// ---------- Mic tab ----------
static float gMeterShowDb = -90.0f, gMeterVadShow = 0.0f;

static void UpdateMeter()                       // every 50 ms: fast rise, smooth fall
{
    float peak = gMeterPeak; gMeterPeak = 0;
    float db = peak > 0.0000316f ? 20.0f * log10f(peak) : -90.0f;
    gMeterShowDb = db > gMeterShowDb ? db : (gMeterShowDb - 2.5f > db ? gMeterShowDb - 2.5f : db);
    float v = gMeterVad;
    gMeterVadShow = v < 0 ? -1.0f : (v > gMeterVadShow ? v : gMeterVadShow * 0.8f + v * 0.2f);
    if (gPage == PAGE_MIC) InvalidateRect(GetDlgItem(gWnd, IDC_METER), nullptr, FALSE);
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
    SetTextColor(dc, gDark ? DK_TEXT : RGB(30, 30, 30));
    RECT lr = { rc.left + 14, by - 6, x0 - 8, by + bh + 6 };
    DrawTextW(dc, L"Mic level", -1, &lr, DT_SINGLELINE | DT_LEFT | DT_VCENTER);

    RECT track = { x0, by, x1, by + bh };
    HBRUSH tb = CreateSolidBrush(gDark ? DK_TRACK : LT_TRACK);
    FillRect(dc, &track, tb); DeleteObject(tb);

    bool gateOn = gGateMode != GATE_OFF, open = !gateOn || gMeterGateOpen;
    COLORREF fillc = !gRunning ? (gDark ? RGB(90, 90, 90) : RGB(180, 180, 180))
                   : open ? RGB(40, 190, 90) : (gDark ? RGB(110, 110, 110) : RGB(165, 165, 165));
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
    SetTextColor(dc, gDark ? DK_TEXT : RGB(30, 30, 30));
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
        int  cid = GetDlgCtrlID(gPaged[i].h);
        bool songStyle = gVocStyle == VOC_SONG;    // Song style: "Music from" replaces key / scale / voice
        if (cid == IDC_VOCKEY || cid == IDC_VOCSCALE || cid == IDC_VOCRANGE) vis = vis && !songStyle;
        if (cid == IDC_SONGSRC || cid == IDC_SONGSTATUS) vis = vis && songStyle;
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
        L"Main has the outputs, effect and hotkey. Mic cleans up your microphone. Voice FX adds pitch, reverb, "
        L"the vocoder (auto-tune + harmonies) and radio effects to your live voice. Settings has latency, theme and updates. Ctrl+Tab switches between them.\n\n"
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
        L"Vocode to song: click it and the music playing on your PC (one app or all PC sound) says your words. "
        L"Retune 0 ms gives the hard auto-tune sound. Deep voice? Set Voice to Low / deep (Auto usually picks it for you).\n"
        L"Radio: sound like a walkie-talkie, phone call, megaphone, old radio, space radio, drive-thru, 8-bit or the next room. "
        L"Drive = distortion, Static = background noise, Squelch = start/stop sounds.\n\n"
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
    Ctl(L"BUTTON", L"Mic",      BS_OWNERDRAW | WS_TABSTOP, 118, 10, 100, 32, IDC_TAB0 + PAGE_MIC);
    Ctl(L"BUTTON", L"Voice FX", BS_OWNERDRAW | WS_TABSTOP, 222, 10, 100, 32, IDC_TAB0 + PAGE_FX);
    Ctl(L"BUTTON", L"Settings", BS_OWNERDRAW | WS_TABSTOP, 326, 10, 100, 32, IDC_TAB0 + PAGE_SETTINGS);

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
    CheckDlgButton(gWnd, IDC_GATEON, gGateMode != GATE_OFF ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Threshold, AI noise suppression and more are on the Mic tab.", 0, 136, 328, 390, 18, IDC_HDR);

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
    gStatus = Ctl(L"STATIC", L"", SS_OWNERDRAW | SS_NOTIFY | WS_GROUP, 14, 504, 532, 30, IDC_STATUS);
    Ctl(L"BUTTON", L"Start", WS_TABSTOP, 14, 544, 172, 34, IDC_START);
    Ctl(L"BUTTON", L"Minimize to tray", WS_TABSTOP, 194, 544, 172, 34, IDC_TRAY);
    Ctl(L"BUTTON", L"Help / Discord && OBS", WS_TABSTOP, 374, 544, 172, 34, IDC_HELPBTN);

    gRecordShift = false;

    // ---------------- Mic page ----------------
    // Live meter, then AI noise suppression, noise gate and voice quality sections.
    gBuildPage = PAGE_MIC;
    Ctl(L"STATIC", L"", SS_OWNERDRAW | SS_NOTIFY, 14, 56, 532, 52, IDC_METER);
    {
        const int MIC_Y0 = 130, MIC_STEP = 146, MIC_H = 126;
        int y = MIC_Y0;                         // noise suppression
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

        y += MIC_STEP;                          // voice quality
        AddSection(14, y, 532, MIC_H, L"Voice quality");
        col = 0;
        for (int i = 0; i < KNOB_N; i++) {
            if (gKnobs[i].group != KG_TONE) continue;
            Ctl(L"LagKnob", L"", WS_TABSTOP | (col == 0 ? WS_GROUP : 0), 26 + col * 98, y + 14, KNOB_W, KNOB_H, IDC_KNOB + i);
            col++;
        }
        Ctl(L"STATIC", L"Every output also has a limiter, so loud moments never clip or distort.", 0, 330, y + 30, 196, 54, IDC_HDR);
    }

    // ---------------- Voice FX page ----------------
    // Master switch, then one section per effect: knobs on the left, on/off + reset on the right.
    // Sections stack downward (FX_SEC_STEP apart); there's room below for more effects.
    gBuildPage = PAGE_FX;
    Ctl(L"BUTTON", L"Voice effects", BS_OWNERDRAW | WS_TABSTOP, 14, 52, 290, 44, IDC_FXON);
    Ctl(L"BUTTON", L"Vocode to song", BS_OWNERDRAW | WS_TABSTOP, 310, 52, 116, 44, IDC_SONGBTN);
    {
        wchar_t kn[120]; FxKeyButtonText(0, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 432, 59, 114, 30, IDC_FXKEY_MASTER);
    }
    const int FX_SEC_Y0 = 110, FX_SEC_STEP = 120, FX_SEC_H = 110, FX_KNOB_H = 96;
    for (int g = 0; g < FX_GROUPS; g++) {
        int y = FX_SEC_Y0 + FX_SEC_STEP * g;
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
            kx = 186; kstep = 80; kw = 80;
        } else if (g == KG_RADIO) {             // preset dropdown + a line about it
            Ctl(L"STATIC", L"Preset", 0, 28, y + 10, 150, 16, IDC_HDR);
            HWND rp = Ctl(L"COMBOBOX", L"", COMBO | WS_GROUP, 26, y + 27, 152, 300, IDC_RADIOPRESET);
            for (int i = 0; i < RADIO_N; i++) SendMessageW(rp, CB_ADDSTRING, 0, (LPARAM)RADIO_PRESETS[i].name);
            SendMessageW(rp, CB_SETCURSEL, gRadioPreset, 0);
            Ctl(L"STATIC", RADIO_DESC[Iclamp(gRadioPreset, 0, RADIO_N - 1)], 0, 28, y + 56, 152, 48, IDC_RADIODESC);
            kx = 186; kstep = 80; kw = 80;
        }
        int col = 0;
        for (int i = 0; i < KNOB_N; i++) {
            if (gKnobs[i].group != g) continue;
            Ctl(L"LagKnob", L"", WS_TABSTOP | (col == 0 ? WS_GROUP : 0), kx + col * kstep, y + 8, kw, FX_KNOB_H, IDC_KNOB + i);
            col++;
        }
        Ctl(L"BUTTON", L"On", BS_AUTOCHECKBOX | WS_TABSTOP | WS_GROUP, 430, y + 12, 100, 20, IDC_FXGRP_ON + g);
        CheckDlgButton(gWnd, IDC_FXGRP_ON + g, *gFxGroups[g].on ? BST_CHECKED : BST_UNCHECKED);
        wchar_t kn[120]; FxKeyButtonText(1 + g, kn, 120);
        Ctl(L"BUTTON", kn, WS_TABSTOP, 428, y + 38, 104, 26, IDC_FXGRP_KEY + g);
        Ctl(L"BUTTON", L"Reset", WS_TABSTOP, 428, y + 70, 104, 26, IDC_FXGRP_RESET + g);
    }

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

    AddSection(14, 167, 532, 134, L"App");
    Ctl(L"STATIC", L"Theme:", 0, 30, 196, 60, 20, -1);
    HWND th = Ctl(L"COMBOBOX", L"", COMBO, 94, 192, 110, 200, IDC_THEME);
    const wchar_t* themeNames[] = { L"System", L"Light", L"Dark" };
    for (const wchar_t* n : themeNames) SendMessageW(th, CB_ADDSTRING, 0, (LPARAM)n);
    SendMessageW(th, CB_SETCURSEL, gThemeMode, 0);
    Ctl(L"STATIC", L"Color:", 0, 222, 196, 50, 20, -1);
    HWND ct = Ctl(L"COMBOBOX", L"", COMBO | CBS_OWNERDRAWFIXED | CBS_HASSTRINGS, 274, 192, 140, 400, IDC_COLORTHEME);
    for (int i = 0; i < COLOR_THEME_N; i++) SendMessageW(ct, CB_ADDSTRING, 0, (LPARAM)COLOR_THEMES[i].name);
    SendMessageW(ct, CB_SETCURSEL, gColorTheme, 0);

    Ctl(L"BUTTON", L"Start audio && hide in tray when opened", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 230, 300, 20, IDC_AUTO);
    CheckDlgButton(gWnd, IDC_AUTO, gAutoStart ? BST_CHECKED : BST_UNCHECKED);

    Ctl(L"STATIC", L"Updates:", 0, 30, 264, 60, 20, -1);
    HWND repo = Ctl(L"EDIT", gUpdateRepo, WS_TABSTOP | ES_AUTOHSCROLL, 94, 261, 200, 24, IDC_REPO, WS_EX_CLIENTEDGE);
    SendMessageW(repo, EM_SETCUEBANNER, TRUE, (LPARAM)L"github-user/repo");
    if (gFramedN < 24) gFramed[gFramedN++] = { repo, nullptr };
    Ctl(L"BUTTON", L"Check now", WS_TABSTOP, 302, 260, 100, 26, IDC_CHECKUPD);
    Ctl(L"BUTTON", L"On startup", BS_AUTOCHECKBOX | WS_TABSTOP, 412, 263, 118, 20, IDC_UPDSTART);
    CheckDlgButton(gWnd, IDC_UPDSTART, gUpdateOnStart ? BST_CHECKED : BST_UNCHECKED);

    Ctl(L"STATIC", L"Lag Effect " APP_VERSION, 0, 30, 317, 300, 18, IDC_HDR);
    Ctl(L"STATIC", L"Settings are saved in %APPDATA%\\LagEffect, shared by every copy and version.", 0, 30, 337, 410, 18, IDC_HDR);
    Ctl(L"BUTTON", L"Open folder", WS_TABSTOP, 446, 332, 84, 26, IDC_OPENSET);

    AddSection(14, 378, 532, 92, L"Screen share");
    Ctl(L"BUTTON", L"Hide from screen share", BS_AUTOCHECKBOX | WS_TABSTOP, 30, 402, 300, 20, IDC_HIDESHARE);
    CheckDlgButton(gWnd, IDC_HIDESHARE, gHideShare ? BST_CHECKED : BST_UNCHECKED);
    Ctl(L"STATIC", L"Stops Discord screen shares from picking up your voice a second time. Locks the VB-Cable "
                   L"output to Lag Effect; your mic and speakers stay free for other apps.", 0, 30, 426, 500, 36, IDC_HDR);

    gBuildPage = -1;
    gUiReady = true;
    AddTips();
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
    HPEN border = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : LT_BORDER);
    HGDIOBJ oldPen = SelectObject(dc, border), oldBr = SelectObject(dc, GetStockObject(NULL_BRUSH));

    {                                           // line under the tabs
        HPEN sep = CreatePen(PS_SOLID, 1, gDark ? DK_SECTION : LT_BORDER);
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
    COLORREF fill = loop ? (gDark ? RGB(92, 30, 34) : RGB(253, 224, 224)) : (gDark ? DK_CTL : LT_STATUS);
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
    case IDC_LOOP: case IDC_SPEED: case IDC_PITCH: case IDC_FADE: case IDC_TALKVOL:
        if (!gUiReady) break;
        for (Range& r : gRanges) {
            if (r.id != id) continue;
            BOOL ok = FALSE;
            int v = (int)GetDlgItemInt(gWnd, id, &ok, FALSE);
            if (code == EN_CHANGE && ok) *r.var = Iclamp(v, r.lo, r.hi);
            else if (code == EN_KILLFOCUS) SetDlgItemInt(gWnd, id, (UINT)*r.var, FALSE);
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
    case IDC_RADIOPRESET:
        if (code == CBN_SELCHANGE) {
            gRadioPreset = Iclamp((int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0), 0, RADIO_N - 1);
            SetDlgItemTextW(gWnd, IDC_RADIODESC, RADIO_DESC[gRadioPreset]);
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
            lstrcpynW(gSongApp, idx > 0 && idx <= gSongListN ? gSongList[idx - 1] : L"", 64);
            UpdateSongCapture();
        }
        break;
    case IDC_VOCSTYLE: case IDC_VOCKEY: case IDC_VOCSCALE: case IDC_VOCRANGE:
        if (code == CBN_SELCHANGE) {
            int v = (int)SendDlgItemMessageW(gWnd, id, CB_GETCURSEL, 0, 0);
            if (id == IDC_VOCSTYLE) { if (gVocStyle != VOC_SONG && v == VOC_SONG) gPrevVocStyle = gVocStyle; gVocStyle = v; SongStyleChanged(); }
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
    case IDC_TAB3:
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
            gColorTheme = Iclamp((int)SendDlgItemMessageW(gWnd, IDC_COLORTHEME, CB_GETCURSEL, 0, 0), 0, COLOR_THEME_N - 1);
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
        if (w == TIMER_STATUS) { UpdateStatus(); UpdateMeter(); SongTick(); }
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
        if (w == IDC_SONGBTN) { DrawSongButton((DRAWITEMSTRUCT*)l); return TRUE; }
        if (w == IDC_METER) { DrawMeter((DRAWITEMSTRUCT*)l); return TRUE; }
        if (w == IDC_COLORTHEME) { DrawColorItem((DRAWITEMSTRUCT*)l); return TRUE; }
        break;
    case WM_LBUTTONDOWN:                        // click on empty space: leave the text/number box you were in
        SetFocus(h);
        return 0;
    case WM_CONTEXTMENU: {                      // right-click a Voice FX hotkey button to clear it
        int id = GetDlgCtrlID((HWND)w);
        if (id == IDC_FXKEY_MASTER) { ClearFxKey(0); return 0; }
        if (id >= IDC_FXGRP_KEY && id < IDC_FXGRP_KEY + FX_GROUPS) { ClearFxKey(1 + id - IDC_FXGRP_KEY); return 0; }
        break;
    }
    case WM_MEASUREITEM:
        if (w == IDC_COLORTHEME) { ((MEASUREITEMSTRUCT*)l)->itemHeight = 20; return TRUE; }
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
        int  cid    = GetDlgCtrlID((HWND)l);
        bool header = cid == IDC_HDR || cid == IDC_RADIODESC || cid == IDC_SONGSTATUS;   // dim helper text
        bool field  = m == WM_CTLCOLOREDIT || m == WM_CTLCOLORLISTBOX;
        if (!gDark) {
            if (field) break;                   // text boxes and lists keep Windows' white
            SetTextColor(dc, header ? RGB(110, 110, 110) : GetSysColor(COLOR_WINDOWTEXT));
            SetBkColor(dc, gLtBg);
            return (LRESULT)gBrLightBg;
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
    icc.dwICC = ICC_STANDARD_CLASSES | ICC_UPDOWN_CLASS | ICC_BAR_CLASSES;   // BAR = tooltips
    InitCommonControlsEx(&icc);

    bool justUpdated = wcsstr(GetCommandLineW(), L"--updated") != nullptr;
    gResumeAudio = justUpdated && wcsstr(GetCommandLineW(), L"--resume") != nullptr;

    LoadSettings();
    LoadThemeApis();
    gNs = rnnoise_create(nullptr);              // built-in model; created once, used by the audio thread
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
