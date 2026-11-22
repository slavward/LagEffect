// Noise suppression's two models (1.60.0): Classic (RNNoise 0.1.1) and New (RNNoise 0.2, every name prefixed rn2_),
// through the real mic code: both take hiss out between "words" and keep the voice; New really is a different model;
// switching while it runs is clean.
#include "stubs.h"
#include AUDIO
#include <cstdio>
#include <cmath>
#include <vector>
#define R 48000
static float outb[960], mic[480];
static long pos = 0; static unsigned rs = 777;
static int fails = 0;
static void check(const char* what, bool ok) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
static float rnd() { rs = rs * 1664525u + 1013904223u; return ((int)(rs >> 8) - (1 << 23)) / (float)(1 << 23); }
static std::vector<float> rec;
static void run(int blocks)                     // a "voice" (180 Hz and harmonics) for 0.5 s, then 0.5 s of hiss only
{
    for (int b = 0; b < blocks; b++) {
        for (int j = 0; j < 480; j++, pos++) {
            const bool talk = (pos / (R / 2)) % 2 == 0;
            float v = 0.03f * rnd();
            if (talk) for (int k = 1; k <= 6; k++) v += 0.12f / k * sinf(2 * M_PI * 180 * k * pos / R);
            mic[j] = v;
        }
        AudioCallback(nullptr, outb, mic, 480);
        for (int j = 0; j < 480; j++) rec.push_back(outb[2 * j]);
    }
}
static double rmsDb(size_t a, size_t n) { double e = 0; for (size_t i = a; i < a + n; i++) e += rec[i] * rec[i]; return 10 * log10(e / n + 1e-20); }
static double gz(size_t a, size_t n, double f)
{
    double c = 2 * cos(2 * M_PI * f / R), s1 = 0, s2 = 0;
    for (size_t i = a; i < a + n; i++) { const double s = rec[i] + c * s1 - s2; s2 = s1; s1 = s; }
    return sqrt(s1 * s1 + s2 * s2 - c * s1 * s2) * 2 / n;
}
struct M { double hiss, voice; };
static M measure()                              // last 2 s: hiss level between words, the voice's 180 Hz
{
    rec.clear(); run(400);
    double h = 0, v = 0;
    for (int k = 2; k < 4; k++) {               // (rec starts on a whole second: talk for half of each, then hiss)
        const size_t s0 = (size_t)R * k;
        h += rmsDb(s0 + R / 2 + R / 10, R / 4) / 2; v += gz(s0 + R / 10, R / 4, 180) / 2;
    }
    return { h, v };
}
int main()
{
    MicReset(); gMicMuted = false; gGateMode = GATE_OFF; gLowCutHz = 0; gFxOn = false;
    gRowMode[0] = MODE_ALL; gRowVol[0] = 100;
    gNs = rnnoise_create(nullptr);
    run((int)((R - pos % R) / 480));            // (line up on a whole second)
    printf("Noise suppression models (1.60.0)\n");
    gNsOn = false; const M off = measure();
    gNsOn = true; gNsModel = 0; run(200); const M c = measure();
    std::vector<float> classic = rec;
    gNs2.store(rn2_rnnoise_create(nullptr)); gNsModel = 1; run(200); const M n = measure();
    printf("  hiss between words: off %.1f dB, Classic %.1f dB, New %.1f dB; voice 180 Hz: off %.3f, Classic %.3f, New %.3f\n",
           off.hiss, c.hiss, n.hiss, off.voice, c.voice, n.voice);
    check("Classic takes the hiss down (> 15 dB)", off.hiss - c.hiss > 15);
    check("New takes the hiss down (> 15 dB)", off.hiss - n.hiss > 15);
    check("both keep the voice (> half)", c.voice > off.voice * 0.5 && n.voice > off.voice * 0.5);
    double d = 0; for (size_t i = 0; i < rec.size() && i < classic.size(); i++) d += fabs(rec[i] - classic[i]);
    check("New is a different model from Classic", d / rec.size() > 1e-4);
    bool fin = true;
    for (int k = 0; k < 40; k++) { gNsModel = k & 1; rec.clear(); run(3); for (float v : rec) if (!std::isfinite(v) || fabsf(v) > 1.5f) fin = false; }
    check("switching back and forth while it runs: no NaN, no blow-up", fin);
    gNsModel = 0;
    printf(fails ? "noise: %d FAILED\n" : "noise: all passed\n", fails);
    return fails ? 1 : 0;
}
