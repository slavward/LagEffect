// (1.70.0) Morse voice: text to Morse timing (PARIS standard), the tone and the sounder clicks, through the real
// audio code; faster when behind, skipping ahead when far behind, your voice muted or kept, off = silence.
#include "stubs.h"
#include AUDIO
#include <cstdio>
#include <cstring>
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
static void run(int blocks, Src src)
{
    for (int b = 0; b < blocks; b++) {
        for (int j = 0; j < BLK; j++) mic[j] = src(pos + j);
        pos += BLK;
        AudioCallback(nullptr, outb, mic, BLK);
        for (int j = 0; j < BLK; j++) rec.push_back(outb[2 * j]);
    }
}
static double goertzel(const std::vector<float>& x, size_t a, size_t n, double hz)
{
    const double w = 2 * M_PI * hz / R, c = 2 * cos(w); double s1 = 0, s2 = 0;
    for (size_t i = a; i < a + n && i < x.size(); i++) { const double s0 = x[i] + c * s1 - s2; s2 = s1; s1 = s0; }
    return sqrt(s1 * s1 + s2 * s2 - c * s1 * s2) / (n / 2.0);
}
struct Mark { long a, b; };
static std::vector<Mark> marks(const std::vector<float>& x, float thr, int hold)   // key-downs: where the sound is (gaps < hold joined)
{
    std::vector<Mark> m; long last = -1000000, start = -1;
    for (long i = 0; i < (long)x.size(); i++) if (fabsf(x[i]) > thr) {
        if (i - last > hold) { if (start >= 0) m.push_back({ start, last }); start = i; }
        last = i;
    }
    if (start >= 0) m.push_back({ start, last });
    return m;
}
static bool drained() { return gMoR.load() == gMoW.load(); }
int main()
{
    MicReset(); gMicMuted = false; gNsOn = false; gGateMode = GATE_OFF; gLowCutHz = 0;
    gRowMode[0] = MODE_ALL; gRowVol[0] = 100;
    gFeatSpeech = true;

    printf("Text to Morse\n");
    unsigned char e[512];
    int n = MorseEncode(L"SOS", e, 512), downs = 0, units = 0;
    for (int i = 0; i < n; i++) { if (e[i] & 0x80) downs++; units += e[i] & 0x7F; }
    check("SOS: 9 marks (... --- ...)", downs == 9 && (e[0] & 0x80) && (e[0] & 0x7F) == 1 && (e[6] & 0x7F) == 3);
    n = MorseEncode(L"PARIS", e, 512); units = 0; for (int i = 0; i < n; i++) units += e[i] & 0x7F;
    check("PARIS is 50 units with its word gap (the speed standard)", units == 50);
    n = MorseEncode(L"Hi,  there!", e, 512); downs = 0; for (int i = 0; i < n; i++) if (e[i] & 0x80) downs++;
    check("lower case, punctuation, double spaces: 'hi, there!' = 4+2+6 + 1+4+1+3+1+6 marks", downs == 28);
    check("nothing with a code: nothing to play", MorseEncode(L"\x263A \x263A", e, 512) == 0);
    wchar_t t[200]; MorseText(L"Hi there ****", t, 200);
    printf("  \"Hi there ****\" shows as \"%ls\"\n", t);
    check("captions: letters spaced, words split by /, a bleeped word kept", !wcscmp(t, L".... .. / - .... . .-. . / ****"));

    printf("The tone, through the audio code\n");
    gMoOn = true; gMoWpm = 20; gMoHz = 700; gMoVolPc = 100; gMoSound = 0;
    run(10, silence); rec.clear();
    MoPush(L"PARIS");
    for (int i = 0; i < 400 && !drained(); i++) run(1, silence);
    run(20, silence);
    std::vector<Mark> m = marks(rec, 0.05f, 400);
    const double unit = R * 1.2 / 20;
    long span = m.empty() ? 0 : m.back().b - m.front().a;
    printf("  %zu marks, first to last %.2f s (43 units = %.2f s), 700 Hz at %.3f\n", m.size(), span / (double)R, 43 * unit / R, goertzel(rec, m.empty() ? 0 : m[1].a, 2400, 700));
    check("PARIS: 14 marks", m.size() == 14);
    check("at 20 words a minute: the right length (within 10 ms)", fabs(span - 43 * unit) < 480);
    bool dashOk = m.size() == 14 && fabs((m[1].b - m[1].a) - 3 * unit) < 480 && fabs((m[0].b - m[0].a) - unit) < 480;
    check("a dot is one unit, a dash three", dashOk);
    check("a 700 Hz tone", m.size() > 1 && goertzel(rec, m[1].a + 240, 2400, 700) > 0.2);
    { float jump = 0; for (size_t i = 1; i < rec.size(); i++) jump = fmaxf(jump, fabsf(rec[i] - rec[i - 1])); check("its edges are soft (no click: no step bigger than the tone's own)", jump < 0.03f); }

    printf("Your voice\n");
    run(40, silence);                           // (PARIS's last word gap)
    gSpMuteVoice = false; rec.clear(); MoPush(L"T"); run(40, tone300);
    check("kept: your voice and the Morse together", goertzel(rec, 4800, 4800, 300) > 0.15 && goertzel(rec, 480, 2400, 700) > 0.2);
    run(30, silence);
    gSpMuteVoice = true; run(30, tone300); rec.clear(); MoPush(L"T"); run(40, tone300);
    check("muted: only the Morse", goertzel(rec, 4800, 4800, 300) < 0.005 && goertzel(rec, 480, 2400, 700) > 0.2);
    gSpMuteVoice = false; run(30, silence);

    printf("An \"Any effect\" output (1.70.1)\n");
    gRowMode[0] = MODE_ANYFX; run(60, silence); rec.clear(); MoPush(L"T"); run(40, tone300);
    printf("  no effect on: 300 Hz (your voice) %.4f, 700 Hz (the Morse) %.3f\n", goertzel(rec, 4800, 4800, 300), goertzel(rec, 480, 2400, 700));
    check("no effect on: the Morse plays there, your voice doesn't", goertzel(rec, 4800, 4800, 300) < 0.005 && goertzel(rec, 480, 2400, 700) > 0.2);
    run(30, silence);
    gRowMode[0] = MODE_ALL; run(30, silence);

    printf("Keeping up with you, no limit (\"as fast as it needs\")\n");
    gMoMaxPc = 0;
    const wchar_t* longText = L"the quick brown fox jumps over the lazy dog";
    n = MorseEncode(longText, e, 512); units = 0; for (int i = 0; i < n; i++) units += e[i] & 0x7F;
    const double nominal = units * unit / R;
    auto playTime = [&](const wchar_t* txt, double said) { MoPush(txt, said); int bl = 0; while (!drained() && bl < 6000) { run(1, silence); bl++; } run(30, silence); return bl * BLK / (double)R; };
    double took = playTime(longText, 3.0);
    printf("  a sentence said in 3 s (%.1f s of Morse at 20 wpm): plays in %.2f s\n", nominal, took);
    check("it takes about as long as you took to say it (3.3 s)", took > 3.0 && took < 3.7);
    took = playTime(longText, 0.5);
    printf("  said in 0.5 s: plays in %.2f s (10x = %.2f s)\n", took, nominal / 10);
    check("never more than 10x the set speed", took > nominal / 10.5 && took < nominal / 9.0);
    took = playTime(L"hi", 3.0);
    check("a short word said slowly: at the set speed (never slower)", fabs(took - 13 * unit / R) < 0.03);
    MoPush(L"paris"); MoPush(L"paris paris"); rec.clear();
    int blocks = 0, top = 100;
    while (!drained() && blocks < 6000) { run(1, silence); blocks++; top = Imax(top, gMoSpeedPc.load()); }
    took = blocks * BLK / (double)R; const double nom3 = 150 * unit / R;   // (from when the second came in)
    printf("  %.1f s queued with no timing: played in %.1f s, up to %d%% speed\n", nom3, took, top);
    check("still behind: plays faster (up to 2x on top)", took < nom3 * 0.85 && top > 130 && top <= 200 && took > nom3 / 2.05);
    run(60, silence);
    check("back to normal speed after", gMoSpeedPc.load() < 105);
    MoPush(longText); MoPush(longText);
    const unsigned before = gMoR.load(); MoPush(L"E");
    run(400, silence);
    check("far behind: skips ahead to the newest sentence", gMoSkip.load() > before && drained());
    for (int i = 0; i < 2000 && !drained(); i++) run(1, silence);
    run(60, silence);

    printf("The fastest it may play (1.70.1: the default 2x, so it still sounds like Morse)\n");
    gMoMaxPc = 200;
    took = playTime(longText, 3.0);
    printf("  a sentence said in 3 s (%.1f s at 20 wpm): plays in %.2f s (2x = %.2f s)\n", nominal, took, nominal / 2);
    check("never faster than 2x: a dot stays 30 ms or longer", took > nominal / 2.05 && took < nominal / 1.9);
    gMoMaxPc = 100;
    took = playTime(L"paris paris", 0.5);
    check("\"never faster than the speed you set\": PARIS PARIS at 20 wpm, even said fast", fabs(took - 93 * unit / R) < 0.05);
    gMoMaxPc = 200; run(60, silence);
    {   // skip ahead (the default): a second sentence while over 4 s behind skips the rest
        MoPush(longText, 3.0); run(100, silence);
        const unsigned b4 = gMoR.load(); MoPush(L"E", 0.3); run(5, silence);
        check("limited, still behind: skips to the newest sentence", gMoSkip.load() > b4);
        for (int i = 0; i < 2000 && !drained(); i++) run(1, silence);
        run(60, silence);
    }
    {   // play every word: nothing skipped, it all plays (later)
        gMoPlayAll = 1;
        const unsigned sk = gMoSkip.load();
        MoPush(longText, 3.0); run(100, silence); MoPush(longText, 3.0);
        int bl = 0; while (!drained() && bl < 8000) { run(1, silence); bl++; }
        const double t2 = (bl + 100) * BLK / (double)R;
        printf("  play every word: two sentences (%.1f s at 20 wpm) took %.1f s\n", 2 * nominal, t2);
        check("\"play every word\": nothing is skipped", gMoSkip.load() == sk && drained());
        check("... and none of it faster than 2x", t2 > 2 * nominal / 2.05);
        gMoPlayAll = 0; run(60, silence);
    }

    printf("The sounder\n");
    gMoSound = 1; run(30, silence); rec.clear();
    MoPush(L"EE");
    for (int i = 0; i < 300 && !drained(); i++) run(1, silence);
    run(20, silence);
    m = marks(rec, 0.05f, 960);
    printf("  %zu clicks\n", m.size());
    check("E E: a click down and a clack up for each (4)", m.size() == 4);
    check("a click is short (under 30 ms)", !m.empty() && m[0].b - m[0].a < 1440);
    gMoSound = 0;

    printf("Off\n");
    rec.clear(); MoPush(L"TTTTTTTT"); run(5, silence); gMoOn = false; run(5, silence);
    { double en = 0; for (size_t i = 2400 + 480; i < rec.size(); i++) en += rec[i] * rec[i]; check("switched off: silent within 10 ms", sqrt(en / (rec.size() - 2880)) < 0.001); }
    gMoOn = true; gFeatSpeech = false; rec.clear(); MoPush(L"T"); run(30, silence);
    { double en = 0; for (float v : rec) en += v * v; check("Speech off in Features: nothing plays", sqrt(en / rec.size()) < 0.001); }
    printf(fails ? "%d FAILED\n" : "all ok\n", fails);
    return fails ? 1 : 0;
}
