// Extra outputs (2 and up) never running dry: the real ExtraOutputCallback, fed the way Windows feeds the main audio
// (480 frames every 10 ms, in blocks of our buffer size), played by a device with its own clock, timing jitter,
// and sometimes much bigger requests than its stated period.
#include "stubs.h"
#include AUDIO
#include EXT
#include <cstdio>
#include <random>
static int fails = 0;
static float out[16384];
// buf: our block size; per: the device's stated period; jitMs: timing wobble; drift: its clock vs ours; bigN / big: every bigN-th
// request is big frames instead (0 = never). Returns the dry-outs per minute over 10 minutes.
static void sim(unsigned buf, unsigned per, double jitMs, double drift, unsigned bigN, unsigned big, unsigned long dry[10])
{
    const int k = 1;
    ringW[k] = ringR[k] = 0; gExtPrimed[k] = false; gExtFill[k] = 0; gExtAcc[k] = 0; gExtBoost[k] = 0; gExtMaxReq[k] = 0;
    gMainBurst = 480; gDropArmed = true;
    std::mt19937 rng(1); std::normal_distribution<double> J(0, jitMs / 1000.0);
    ma_device d = {}; d.pUserData = (void*)(intptr_t)k; d.playback.internalPeriodSizeInFrames = per;
    long nMain = 0; double tMain = 0, tExt = 0, extT = 0; long call = 0;
    for (int minute = 0; minute < 10; minute++) {
        const unsigned before = gDropDryK[k].load();
        while (tMain < (minute + 1) * 60.0) {
            if (tMain <= tExt) {                // Windows hands the main audio 480 frames; it runs them in blocks of buf
                for (unsigned left = 480; left; ) {
                    const unsigned b = left < buf ? left : buf; gMainFrames = b;
                    for (unsigned f = 0; f < b; f++) { const unsigned i = (ringW[k] & (RING_FRAMES - 1)) * 2; ring[k][i] = ring[k][i + 1] = 0.1f; ringW[k]++; }
                    left -= b;
                }
                nMain++; tMain = nMain * 0.010 + fabs(J(rng)) * 0.3;
            } else {
                const unsigned req = bigN && ++call % bigN == 0 ? big : per;
                ExtraOutputCallback(&d, out, nullptr, req);
                extT += req / (48000.0 * (1 + drift)); tExt = extT + fabs(J(rng));
            }
        }
        dry[minute] = gDropDryK[k].load() - before;
    }
}
static void check(const char* what, unsigned buf, unsigned per, double jit, double drift, unsigned bigN, unsigned big, unsigned maxFirst, unsigned maxAfter)
{
    unsigned long dry[10]; sim(buf, per, jit, drift, bigN, big, dry);
    unsigned long after = 0; for (int m = 1; m < 10; m++) after += dry[m];
    const bool ok = dry[0] <= maxFirst && after <= maxAfter;
    printf("  %s %-52s dry: first minute %lu, then %lu (reserve +%.1f ms)\n", ok ? "ok  " : "FAIL", what, dry[0], after, gExtBoost[1] * 1000.0 / 48000);
    if (!ok) fails++;
}
int main()
{
    check("steady device, buffer 256, period 256", 256, 256, 2, 0, 0, 0, 0, 0);
    check("steady device, period 480, 3 ms jitter", 256, 480, 3, 0, 0, 0, 0, 0);
    check("buffer 64, period 480, 4 ms jitter", 64, 480, 4, 0, 0, 0, 0, 0);
    check("clock 200 ppm fast", 256, 256, 2, 0.0002, 0, 0, 0, 0);
    check("clock 200 ppm slow, 5 ms jitter", 256, 480, 5, -0.0002, 0, 0, 0, 0);
    check("every 8th request 1440 frames (VB-Cable style)", 256, 256, 2, 0, 8, 1440, 2, 0);
    check("every 20th request 3072 frames", 256, 128, 2, 0, 20, 3072, 2, 0);
    printf(fails ? "outputs: %d FAILED\n" : "outputs: all ok\n", fails);
    return fails ? 1 : 0;
}
