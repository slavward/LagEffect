// Same sound as before? Runs your mic (through the gate modes, leveler, noise suppression, Mic boost), a Mixer channel and the vocoder
// through the real audio code with default settings, and prints a hash of every sample that came out.
// run.sh builds this twice, against this commit's LagEffect.cpp and against main's, and the hashes must match:
// a new feature that's off must not change a single sample. (Only long-standing settings are used here, so main builds too.)
#include "stubs.h"
#include AUDIO
#include <cstdio>
#include <cstdint>
#define R 48000
static float outb[1024], mic[1024], pkt[480 * 2];
static long pos = 0; static unsigned rs = 12345, n = 0; static long gb = 0;
static uint64_t h = 1469598103934665603ull;
static float rnd() { rs = rs * 1664525u + 1013904223u; return ((rs >> 8) & 0xFFFF) / 32768.0f - 1.0f; }
static void hashBlock(int samples) { for (int j = 0; j < samples; j++) { uint32_t u; memcpy(&u, &outb[j], 4); h = (h ^ u) * 1099511628211ull; } }
static void feed(int blocks, int kind)          // 0 room noise, 1 speech-like bursts
{
    for (int b = 0; b < blocks; b++) {
        for (int j = 0; j < 480; j++, pos++) {
            float v = 0.0008f * rnd();
            if (kind == 1) v += ((pos / 12000) % 2 ? 0.25f : 0.02f) * sinf(2 * M_PI * 180 * pos / R) + 0.05f * sinf(2 * M_PI * 2500 * pos / R);
            mic[j] = v;
        }
        AudioCallback(nullptr, outb, mic, 480);
        hashBlock(960);
    }
}
static float chSrc(unsigned i)                  // a Mixer channel: a tone, then hiss, repeated
{
    static unsigned s = 1; s = s * 1664525u + 1013904223u;
    const unsigned p = i % (R * 16 / 10);
    return p < R * 4 / 10 ? 0.1f * sinf(2 * M_PI * 300 * i / R) : ((int)(s >> 9) - (1 << 22)) / (float)(1 << 22) * 0.0032f;
}
int main()
{
    MicReset(); gMicMuted = false; gNsOn = false; gLowCutHz = 80; gFeatFx = true; gFxOn = false;
    gRowMode[0] = MODE_ALL; gRowVol[0] = 100;
    gGateMode = GATE_VOLUME; gGateThrDb = -40; feed(60, 1); feed(30, 0);
    gLevelerPct = 60; feed(80, 1);
    gNsOn = true; gGateMode = GATE_BOTH; feed(80, 1); gNsOn = false;
    gGateMode = GATE_OFF; gLevelerPct = 0; gMicBoostDb = 6; feed(40, 1); gMicBoostDb = 0;
    printf("mic %016llx\n", (unsigned long long)h);
    // a Mixer channel (an app) on output 1, with the mic muted: EQ / compressor / gate all at their defaults (off)
    h = 1469598103934665603ull; gMicMuted = true; gRowMode[0] = MODE_OFF;
    gCh[0].type = CH_APP; gCh[0].db10 = 0; gCh[0].routes = 1; gChA[0].live = true;
    const int blocks = 20 * R / 128;
    for (int b = 0; b < blocks; b++, gb++) {
        while ((double)n < (gb + 1) * 128.0 + 1500) { for (int i = 0; i < 480; i++) { const float v = chSrc(n + i); pkt[2 * i] = v; pkt[2 * i + 1] = v; } ChanPush(0, pkt, 480, 2); n += 480; }
        AudioCallback(nullptr, outb, mic, 128);
        hashBlock(256);
    }
    printf("channel %016llx\n", (unsigned long long)h);
    // the vocoder (the heaviest effect): Tune + harmony, Robot, Choir, Tune, through the band filters and the pitch tracker
    h = 1469598103934665603ull;
    gCh[0].type = CH_NONE; gChA[0].live = false; gMicMuted = false; gRowMode[0] = MODE_ALL;
    gFxOn = true; gFxPitchOn = false; gFxRevOn = false; gFxVocOn = true;
    gVocKey = 0; gVocScale = 1; gVocRetuneMs = 15; gVocSynth = 60; gVocMix = 100;
    const int styles[4] = { VOC_HARMONY, VOC_ROBOT, VOC_CHOIR, VOC_TUNE };
    for (int st : styles) { gVocStyle = st; feed(60, 1); feed(20, 0); }
    printf("vocoder %016llx\n", (unsigned long long)h);
}
