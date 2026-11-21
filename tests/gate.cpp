// The Mixer channel gate (1.54.0), through the real audio code: a talker (0.4 s of tone at -20 dBFS, then hiss at -50 dBFS).
#include "stubs.h"
#include AUDIO
#include <cstdio>
#define R 48000
static float outb[256], mic[128], pkt[480 * 2]; static unsigned n = 0; static long gb = 0;
static int fails = 0;
static float src(unsigned i)
{
    static unsigned s = 1; s = s * 1664525u + 1013904223u;
    const unsigned p = i % (R * 16 / 10);
    return p < R * 4 / 10 ? 0.1f * sinf(2 * M_PI * 300 * i / R) : ((int)(s >> 9) - (1 << 22)) / (float)(1 << 22) * 0.0032f;
}
static float lvl[64];                           // level (dB) per 25 ms over one 1.6 s cycle
static void run(double secs, bool measure)
{
    const int blocks = (int)(secs * R / 128); double e[64] = {}; int cnt[64] = {};
    for (int b = 0; b < blocks; b++, gb++) {
        while ((double)n < (gb + 1) * 128.0 + 1500) { for (int i = 0; i < 480; i++) { const float v = src(n + i); pkt[2 * i] = v; pkt[2 * i + 1] = v; } ChanPush(0, pkt, 480, 2); n += 480; }
        AudioCallback(nullptr, outb, mic, 128);
        if (measure) for (int j = 0; j < 128; j++) { const unsigned t = (unsigned)((gb * 128 + j) % (R * 16 / 10)); const int w = t / (R * 25 / 1000); if (w < 64) { e[w] += outb[2 * j] * outb[2 * j]; cnt[w]++; } }
    }
    if (measure) for (int w = 0; w < 64; w++) lvl[w] = cnt[w] ? (float)(10 * log10(e[w] / cnt[w] + 1e-20)) : -999;
}
static void check(const char* what, bool ok) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
int main()
{
    MicReset(); gNsOn = false; gGateMode = GATE_OFF; gLowCutHz = 0; gFxOn = false; gMicMuted = true; gRowMode[0] = MODE_OFF; gRowVol[0] = 100;
    gCh[0].type = CH_APP; gCh[0].db10 = 0; gCh[0].routes = 1; gChA[0].live = true;
    // tone window 8, hiss: +50 ms = window 18, +600 ms = 40, +1100 ms = 60
    gCh[0].gate = 0; run(3.2, false); run(3.2, true);
    const float tone0 = lvl[8], hiss0 = lvl[60];
    printf("off: tone %.1f dB, hiss %.1f dB\n", tone0, hiss0);
    check("off: hiss passes", hiss0 > -60);
    gCh[0].gate = 30; gCh[0].gateHold = 250; gCh[0].gateRange = 80; run(3.2, false); run(3.2, true);
    printf("opens above -40 dB: tone %.1f, hiss +50 ms %.1f, +600 ms %.1f, +1100 ms %.1f dB\n", lvl[8], lvl[18], lvl[40], lvl[60]);
    check("tone passes unchanged", fabsf(lvl[8] - tone0) < 0.2f);
    check("still open during the hold", lvl[18] > hiss0 - 1);
    check("shut after it (below -75 dB)", lvl[40] < -75);
    check("silent later (range 80 = silent)", lvl[60] < -100);
    gCh[0].gateHold = 1000; run(3.2, false); run(3.2, true);
    printf("hold 1000 ms: +600 ms %.1f dB\n", lvl[40]);
    check("a longer hold keeps it open", lvl[40] > hiss0 - 1);
    gCh[0].gateHold = 250; gCh[0].gateRange = 20; run(3.2, false); run(3.2, true);
    printf("range 20 dB: +1100 ms %.1f dB\n", lvl[60]);
    check("shut = 20 dB down", fabsf(lvl[60] - (hiss0 - 20)) < 1.0f);
    gCh[0].gateRange = 80; gCh[0].gate = 10; run(3.2, false); run(3.2, true);
    printf("opens above -60 dB (under the hiss): +1100 ms %.1f dB\n", lvl[60]);
    check("hiss louder than the threshold keeps it open", fabsf(lvl[60] - hiss0) < 0.5f);
    gCh[0].gate = 25; run(3.2, false); gCh[0].gate = 0; run(1.0, false); run(3.2, true);
    check("switched off: fully open again", fabsf(lvl[60] - hiss0) < 0.5f);
    printf(fails ? "gate: %d FAILED\n" : "gate: all ok\n", fails);
    return fails ? 1 : 0;
}
