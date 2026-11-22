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
    // 1.59.0: more sounds. bleepAt: a 0.1 s "word" C2 .. C2 + 4800, then where it comes out in rec
    auto bleepAt = [&](Src src, long long len = 4800, int blocks = 100) -> size_t {
        const long long c2 = gAudT.load() + 4800; BlAdd(c2, c2 + len);
        rec.clear(); const long long rc = gAudT.load(); run(blocks, src);
        return (size_t)(c2 + R / 2 - rc);
    };
    printf("Bleep sounds (1.59.0)\n");
    gBlHz = 500;
    { const size_t a = bleepAt(tone300);
      check("the beep's pitch can be changed (500 Hz)", goertzel(rec, a + 480, 3840, 500) > 0.18 && goertzel(rec, a + 480, 3840, 1000) < 0.01); }
    gBlHz = 1000; gBlVolPc = 50;
    { const size_t a = bleepAt(tone300); const double v = goertzel(rec, a + 480, 3840, 1000);
      printf("  at 50%%: %.3f\n", v); check("its volume (50%: half)", v > 0.09 && v < 0.13); }
    gBlVolPc = 100;
    gBlSound = BLS_STATIC;
    { const size_t a = bleepAt(tone300); double e = 0; for (size_t i = a + 480; i < a + 4320; i++) e += rec[i] * rec[i];
      const double rms = sqrt(e / 3840), v = goertzel(rec, a + 480, 3840, 300);
      printf("  static: rms %.3f, voice %.3f\n", rms, v); check("static: noise, no voice", rms > 0.03 && v < 0.01); }
    gBlSound = BLS_MUFFLE;
    {   // a low and a high tone together: muffled keeps the low one, loses the high one
        auto lowhigh = [](long n) { return 0.15f * (float)sin(2 * M_PI * 150 * n / R) + 0.15f * (float)sin(2 * M_PI * 3000 * n / R); };
        const size_t a = bleepAt(lowhigh);
        const double lo = goertzel(rec, a + 960, 2880, 150), hi = goertzel(rec, a + 960, 2880, 3000), hiB = goertzel(rec, a + 7200, 2400, 3000);
        printf("  muffled: 150 Hz %.3f, 3 kHz %.4f (after the word %.3f)\n", lo, hi, hiB);
        check("muffled: the word is still there but dull", lo > 0.07 && hi < 0.01 && hiB > 0.13);
    }
    gBlSound = BLS_BACK;
    {   // a rising sweep (200 Hz -> 2 kHz over each 0.2 s) comes out falling
        auto sweep = [](long n) { const double ph = (double)(n % 9600) / R; return 0.2f * (float)sin(2 * M_PI * (200 * ph + 0.5 * (1800 / 0.2) * ph * ph)); };
        const long long c2 = gAudT.load() + 9600 - (long long)(pos % 9600);   // (starts with a sweep)
        BlAdd(c2, c2 + 9600);
        rec.clear(); const long long rc = gAudT.load(); run(100, sweep);
        const size_t a = (size_t)(c2 + R / 2 - rc);
        const double hiFirst = goertzel(rec, a + 480, 1920, 1800), loFirst = goertzel(rec, a + 480, 1920, 300);
        const double hiLast = goertzel(rec, a + 7200, 1920, 1800), loLast = goertzel(rec, a + 7200, 1920, 300);
        printf("  backwards: start 1.8k %.3f / 300 %.3f, end 1.8k %.3f / 300 %.3f\n", hiFirst, loFirst, hiLast, loLast);
        check("backwards: the word is played in reverse (high first)", hiFirst > 2 * loFirst && loLast > 2 * hiLast);
    }
    {   // the key held (end not known yet): reversed in 250 ms pieces, still not your voice forwards
        const long long press = gAudT.load(); const unsigned slot = BlAdd(press, LLONG_MAX);
        rec.clear(); const long long rc = gAudT.load(); run(60, tone300);
        gBlR[slot].b.store(gAudT.load()); run(60, tone300);
        const size_t a = (size_t)(press + R / 2 - rc);
        check("backwards with the key: plays (no gap, no click)", goertzel(rec, a + 2400, 9600, 300) > 0.15);
    }
    gBlSound = BLS_FILE;
    std::vector<float> c700(R * 3 / 10), c1500(R / 20);   // a 0.3 s 700 Hz and a 50 ms 1.5 kHz sound file
    for (size_t i = 0; i < c700.size(); i++) c700[i] = 0.3f * (float)sin(2 * M_PI * 700 * i / R);
    for (size_t i = 0; i < c1500.size(); i++) c1500[i] = 0.3f * (float)sin(2 * M_PI * 1500 * i / R);
    BlClip k700 = { c700.data(), (int)c700.size() }, k1500 = { c1500.data(), (int)c1500.size() };
    gBlClip[0] = &k700; gBlClip[1] = &k1500;
    gBlClipSel = 1; gBlFinish = true;
    { const size_t a = bleepAt(tone300);
      check("your sound file, looped while the word lasts", goertzel(rec, a + 480, 3840, 1500) > 0.25 && goertzel(rec, a + 480, 3840, 300) < 0.01); }
    gBlClipSel = 0;
    { const size_t a = bleepAt(tone300);
      const double during = goertzel(rec, a + 480, 3840, 700), after = goertzel(rec, a + 5280, 4800, 700), voice = goertzel(rec, a + 5280, 4800, 300);
      printf("  play to the end: 700 Hz during %.3f, after %.3f, voice after %.3f\n", during, after, voice);
      check("plays to its end over your voice after the word", during > 0.25 && after > 0.25 && voice > 0.17); }
    gBlFinish = false;
    { const size_t a = bleepAt(tone300);
      const double after = goertzel(rec, a + 5280, 4800, 700), voice = goertzel(rec, a + 5280, 4800, 300);
      check("or stops with the word", after < 0.01 && voice > 0.17); }
    gBlFinish = true; gBlClipSel = -1;
    {   int n7 = 0, n15 = 0;
        for (int i = 0; i < 12; i++) { const size_t a = bleepAt(tone300, 4800, 70);
            if (goertzel(rec, a + 480, 1920, 700) > 0.2) n7++; if (goertzel(rec, a + 480, 1920, 1500) > 0.2) n15++; }
        printf("  random: 700 Hz %d times, 1.5 kHz %d times\n", n7, n15);
        check("a random one of your files each time", n7 > 0 && n15 > 0 && n7 + n15 == 12); }
    gBlClip[1] = nullptr; gBlClipSel = 1;
    { const size_t a = bleepAt(tone300); check("a removed file: silence, nothing breaks", goertzel(rec, a + 480, 3840, 300) < 0.01); }
    gBlClip[0] = nullptr; gBlSound = 0; gBlClipSel = 0;
    run(100, tone300);
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

    printf("Live bleep key (1.59.1)\n");
    gBlLive = true; rec.clear(); run(10, tone300);
    check("held: a bleep at once (no delay), no voice", goertzel(rec, 480, 3840, 1000) > 0.18 && goertzel(rec, 480, 3840, 300) < 0.01);
    gBlLive = false; rec.clear(); run(10, tone300);
    check("let go: your voice at once", goertzel(rec, 480, 3840, 300) > 0.17 && goertzel(rec, 480, 3840, 1000) < 0.01);
    gBlSound = BLS_BACK; gBlLive = true; rec.clear(); run(10, tone300);
    check("Backwards can't be live: a beep instead", goertzel(rec, 480, 3840, 1000) > 0.18);
    gBlLive = false; gBlSound = 0; run(10, tone300);
    gRowMode[0] = MODE_APPS; gBlLive = true; rec.clear(); run(10, tone300);
    double ea = 0; for (float v : rec) ea += v * v;
    check("not on an output without your voice (Apps only)", sqrt(ea / rec.size()) < 0.001);
    gBlLive = false; gRowMode[0] = MODE_ALL; run(10, tone300);

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
