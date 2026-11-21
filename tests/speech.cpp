// Mic > Speech (1.57.0), the audio side, through the real audio code: the clock, what the speech recognizer
// hears, bleeped outputs (delay, bleeps where words / the key say), your voice muted for the TTS voice.
#include "stubs.h"
#include AUDIO
#include <cstdio>
#include <climits>
#include <vector>
#define R 48000
#define BLK 480
static float outb[BLK * 2], mic[BLK]; static long pos = 0;
static int fails = 0;
static void check(const char* what, bool ok) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
static std::vector<float> rec;
typedef float (*Src)(long);
static float silence(long) { return 0.0f; }
static float tone300(long n) { return 0.2f * (float)sin(2 * M_PI * 300 * n / R); }
static long gClickAt = -1;
static float click(long n) { return n >= gClickAt && n < gClickAt + 48 ? 0.8f : 0.0f; }
static void run(int blocks, Src src)
{
    for (int b = 0; b < blocks; b++) {
        for (int j = 0; j < BLK; j++) mic[j] = src(pos + j);
        pos += BLK;
        AudioCallback(nullptr, outb, mic, BLK);
        for (int j = 0; j < BLK; j++) rec.push_back(outb[2 * j]);
    }
}
static double goertzel(const std::vector<float>& x, size_t a, size_t n, double hz, double rate = R)
{
    const double w = 2 * M_PI * hz / rate, c = 2 * cos(w); double s1 = 0, s2 = 0;
    for (size_t i = a; i < a + n && i < x.size(); i++) { const double s0 = x[i] + c * s1 - s2; s2 = s1; s1 = s0; }
    return sqrt(s1 * s1 + s2 * s2 - c * s1 * s2) / (n / 2.0);
}
int main()
{
    MicReset(); gMicMuted = false; gNsOn = false; gGateMode = GATE_OFF; gLowCutHz = 0;
    gRowMode[0] = MODE_ALL; gRowVol[0] = 100;
    gFeatSpeech = true;                         // (Settings > Features > Speech)
    run(20, silence);
    printf("The clock\n");
    const long long t0 = gAudT.load(); run(10, silence);
    check("counts frames", gAudT.load() - t0 == 10 * BLK);

    printf("What the speech recognizer hears\n");
    gSpFeed = true; gSpStartReq = true;
    const long startPos = pos;                  // the clock and pos move together from here
    const long long clockAtStart = gAudT.load();
    run(100, tone300);                          // 1 s of a 300 Hz tone
    const unsigned base = gSpBaseW.load(), got = gSpW.load() - base;
    printf("  %u samples for 1 s\n", got);
    check("16 kHz", got >= 15990 && got <= 16010);
    std::vector<float> sp(got); for (unsigned i = 0; i < got; i++) sp[i] = gSpRing[(base + i) & (SP_RING - 1)] / 32768.0f;
    const double lvl = goertzel(sp, 2000, 8000, 300, 16000);
    printf("  300 Hz at %.3f (sang 0.2)\n", lvl);
    check("your voice, at the right pitch and level", lvl > 0.17 && lvl < 0.21);
    check("its clock starts where feeding started", gSpT0.load() == clockAtStart);
    gClickAt = pos + 2000; const long long clickClock = clockAtStart + (gClickAt - startPos);
    run(20, click);
    {
        const unsigned w = gSpW.load(); int at = -1; float pk = 0;
        for (unsigned i = base; i < w; i++) { const float v = gSpRing[i & (SP_RING - 1)]; if (v > pk) { pk = v; at = (int)(i - base); } }
        const long long heardAt = gSpT0.load() + 3LL * at;
        printf("  a click at clock %lld is speech sample %d = clock %lld\n", clickClock, at, heardAt);
        check("a sound's place in speech samples maps back to the clock (within 1 ms)", llabs(heardAt - clickClock) < 48 + 48);
    }
    gSpRead.store(gSpW.load());                 // (as if the recognizer took it all)

    printf("Bleep\n");
    gBlOuts = 1; gBlDelayF = R / 2; gBlSound = 0; gBlOn = true;
    rec.clear(); const long long onClock = gAudT.load(); run(100, tone300);
    {
        int first = -1; for (size_t i = 0; i < rec.size(); i++) if (fabs(rec[i]) > 0.02f) { first = (int)i; break; }
        printf("  your voice comes out %.0f ms later\n", first * 1000.0 / R);
        check("bleeped outputs run behind by the delay (0.5 s)", first >= R / 2 - 10 && first < R / 2 + 60);
    }
    // a "word" at clock C .. C + 0.1 s: bleeped when it comes out
    const long long C = gAudT.load() + 4800;
    BlAdd(C, C + 4800);
    rec.clear(); const long long recClock = gAudT.load(); run(100, tone300);
    {
        const size_t a = (size_t)(C + R / 2 - recClock), n = 4800;   // where the word comes out in rec
        const double bleep = goertzel(rec, a + 480, n - 960, 1000), voice = goertzel(rec, a + 480, n - 960, 300);
        const double before = goertzel(rec, a - 9600, 4800, 300), after = goertzel(rec, a + n + 4800, 4800, 300);
        printf("  during the word: 1 kHz %.3f, voice %.3f; before %.3f, after %.3f\n", bleep, voice, before, after);
        check("the word is a bleep", bleep > 0.18 && voice < 0.01);
        check("only the word: before and after it's your voice", before > 0.17 && after > 0.17);
    }
    gBlSound = 1;
    { const long long c2 = gAudT.load() + 4800; BlAdd(c2, c2 + 4800);
      rec.clear(); const long long rc2 = gAudT.load(); run(100, tone300);
      const size_t a = (size_t)(c2 + R / 2 - rc2);
      double e = 0; for (size_t i = a + 480; i < a + 4320; i++) e += rec[i] * rec[i];
      check("silence instead of a bleep", sqrt(e / 3840) < 0.005); }
    gBlSound = 0;
    {   // the key: from a little before it was pressed until it's let go
        const long long press = gAudT.load(); const unsigned slot = BlAdd(press - 9600, LLONG_MAX);
        rec.clear(); const long long rc3 = gAudT.load(); run(30, tone300);
        gBlR[slot].b.store(gAudT.load() + 2400);   // let go (+50 ms)
        const long long rel = gAudT.load() + 2400;
        run(100, tone300);
        const size_t a = (size_t)(press - 9600 + R / 2 - rc3), b = (size_t)(rel + R / 2 - rc3);
        check("the key bleeps from before it was pressed until let go", goertzel(rec, a + 480, b - a - 960, 300) < 0.01 &&
              goertzel(rec, b + 960, 4800, 300) > 0.17);
    }
    gBlOn = false; run(60, tone300);
    rec.clear(); run(20, tone300);
    check("off: no delay again", goertzel(rec, 0, 4800, 300) > 0.17);

    printf("Talk through a TTS voice\n");
    const unsigned w0 = gSpW.load();
    gSpMuteVoice = true; run(20, tone300); rec.clear(); run(50, tone300);
    double e = 0; for (float v : rec) e += v * v;
    check("your voice is muted on the outputs", sqrt(e / rec.size()) < 0.001);
    std::vector<float> sp2; for (unsigned i = w0 + 4000; i < gSpW.load(); i++) sp2.push_back(gSpRing[i & (SP_RING - 1)] / 32768.0f);
    check("the recognizer still hears you", goertzel(sp2, 0, 8000, 300, 16000) > 0.17);
    gSpMuteVoice = false; run(20, tone300); rec.clear(); run(20, tone300);
    check("back again when it's off", goertzel(rec, 0, 4800, 300) > 0.17);
    gFeatSpeech = false; gBlOuts = 1; gBlOn = true; gSpMuteVoice = true; run(20, tone300); rec.clear(); run(20, tone300);
    check("with Speech off in Features: no delay, no muting", goertzel(rec, 0, 4800, 300) > 0.17);
    printf(fails ? "%d FAILED\n" : "all ok\n", fails);
    return fails ? 1 : 0;
}
