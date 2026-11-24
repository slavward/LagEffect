// (1.69.0) Sound triggers: made-up claps, snaps, tongue clicks and whistles are found and told apart; words and
// music aren't taken for them; off = nothing runs.
#include "stubs.h"
#include AUDIO
#include <cstdio>
#include <cstdlib>
#include <vector>
#define R 48000
static int fails = 0;
static void check(const char* what, bool ok) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
static unsigned gRng = 7;
static float rnd() { gRng = gRng * 1664525u + 1013904223u; return (float)((int)gRng) / 2147483648.0f; }
struct BP { double x1 = 0, x2 = 0, y1 = 0, y2 = 0, b0, b2, a1, a2;
    BP(double hz, double q) { const double w = 2 * M_PI * hz / R, al = sin(w) / (2 * q), a0 = 1 + al; b0 = al / a0; b2 = -al / a0; a1 = -2 * cos(w) / a0; a2 = (1 - al) / a0; }
    float run(double x) { const double y = b0 * x + b2 * x2 - a1 * y1 - a2 * y2; x2 = x1; x1 = x; y2 = y1; y1 = y; return (float)y; } };
static std::vector<float> clap()  { std::vector<float> v(R / 4); BP b(1800, 0.6); for (int i = 0; i < (int)v.size(); i++) v[i] = 1.6f * b.run(rnd()) * (float)exp(-i / (0.010 * R)); return v; }
static std::vector<float> snap()  { std::vector<float> v(R / 4); BP b(4200, 1.1); for (int i = 0; i < (int)v.size(); i++) v[i] = 1.8f * b.run(rnd()) * (float)exp(-i / (0.004 * R)); return v; }
static std::vector<float> click() { std::vector<float> v(R / 4); for (int i = 0; i < (int)v.size(); i++) v[i] = 0.5f * (float)(sin(2 * M_PI * 900 * i / R) * exp(-i / (0.0025 * R)) + 0.6 * sin(2 * M_PI * 350 * i / R) * exp(-i / (0.003 * R))); return v; }
static std::vector<float> whistle(double hz, double secs) { std::vector<float> v((size_t)(R * secs)); for (size_t i = 0; i < v.size(); i++) { const double env = std::min(1.0, std::min(i, v.size() - i) / 2400.0); v[i] = (float)(0.12 * env * sin(2 * M_PI * (hz * i / R + 0.002 * sin(2 * M_PI * 5 * i / R)))); } return v; }
static std::vector<float> speech(double secs)   // a voice-ish sound: syllables with "t" bursts before vowels and an "s"
{
    std::vector<float> v((size_t)(R * secs)); BP f1(700, 4), f2(1200, 5), s(6000, 1.5); double ph = 0;
    for (size_t i = 0; i < v.size(); i++) {
        const double t = (double)i / R, syl = fmod(t, 0.25);
        ph += (130 + 20 * sin(2 * M_PI * 1.3 * t)) / R; const double pulse = ph - floor(ph) < 0.08 ? 1 : 0;
        const double vow = syl > 0.03 && syl < 0.2 ? sin(M_PI * (syl - 0.03) / 0.17) : 0;
        const double burst = syl < 0.012 ? 0.8 * exp(-syl / 0.003) : 0;   // "t": a burst, then the vowel straight on
        const double ss = fmod(t, 1.0) > 0.6 && fmod(t, 1.0) < 0.7 ? 0.3 : 0;
        v[i] = (float)(0.25 * vow * (f1.run(pulse) + 0.6 * f2.run(pulse)) + burst * rnd() * 0.5 + s.run(rnd()) * ss);
    }
    return v;
}
static std::vector<float> music(double secs)    // a steady chord with a beat: never "alone"
{
    std::vector<float> v((size_t)(R * secs));
    for (size_t i = 0; i < v.size(); i++) { const double t = (double)i / R; v[i] = (float)(0.05 * (sin(2 * M_PI * 220 * t) + sin(2 * M_PI * 277 * t) + sin(2 * M_PI * 330 * t)) + 0.4 * exp(-fmod(t, 0.5) / 0.03) * sin(2 * M_PI * 60 * t)); }
    return v;
}
static TrigCore tg;
static std::vector<TrigEv> evs;
static void feed(const std::vector<float>& x, double gapSecs = 0.4)
{
    std::vector<float> all((size_t)(R * gapSecs), 0.0f); all.insert(all.end(), x.begin(), x.end()); all.resize(all.size() + (size_t)(R * gapSecs), 0.0f);
    for (size_t i = 0; i < all.size(); i++) all[i] += 0.0005f * rnd();   // (a quiet room)
    for (size_t a = 0; a < all.size(); a += 480) TrigBlock(tg, &all[a], (unsigned)std::min<size_t>(480, all.size() - a), 1, 0, 1.0f, 5);
    while (gTrigQR.load() != gTrigQW.load()) { evs.push_back(gTrigQ[gTrigQR.load() & 15]); gTrigQR.fetch_add(1); }
}
static int classify(const TrigEv& e) { const bool use[TRIG_N] = { true, true, true, true }; return e.kind == TRIG_WHISTLE ? TRIG_WHISTLE : TrigClassify(e.f, TRIG_DEFAULTS, use, 5); }
static const char* NM[] = { "clap", "snap", "whistle", "click", "?" };
int main()
{
    TrigReset(tg); tg.active = true;
    printf("Sound triggers (1.69.0)\n");
    struct { const char* nm; std::vector<float> (*make)(); int want; } kinds[] = { { "clap", clap, TRIG_CLAP }, { "snap", snap, TRIG_SNAP }, { "tongue click", click, TRIG_CLICK } };
    for (auto& k : kinds) {
        evs.clear(); int right = 0;
        for (int i = 0; i < 6; i++) feed(k.make());
        float m[TRIG_FEAT] = {};
        for (auto& e : evs) { if (classify(e) == k.want) right++; for (int j = 0; j < TRIG_FEAT; j++) m[j] += e.f[j] / (evs.empty() ? 1 : evs.size()); }
        printf("  6 %ss: %d found, %d named right; they look like %.2f %.2f %.2f %.2f %.2f  %.2f %.2f\n", k.nm, (int)evs.size(), right, m[0], m[1], m[2], m[3], m[4], m[5], m[6]);
        char t[80]; snprintf(t, 80, "each %s is found once and named right", k.nm); check(t, evs.size() == 6 && right == 6);
    }
    evs.clear(); feed(whistle(1800, 0.6)); feed(whistle(900, 0.5));
    check("two whistles (1.8 kHz, 900 Hz): two whistles", evs.size() == 2 && classify(evs[0]) == TRIG_WHISTLE && classify(evs[1]) == TRIG_WHISTLE);
    if (evs.size() == 2) printf("  their pitch: %.0f Hz, %.0f Hz\n", evs[0].f[0], evs[1].f[0]);
    evs.clear(); feed(whistle(1800, 0.15));
    check("a short beep (0.15 s): not a whistle", evs.empty());
    evs.clear(); feed(speech(4)); int named = 0; for (auto& e : evs) if (classify(e) >= 0) named++;
    printf("  4 s of talking: %d short sounds stood alone, %d taken for a trigger\n", (int)evs.size(), named);
    check("talking isn't taken for triggers", named == 0);
    evs.clear(); feed(music(4)); named = 0; for (auto& e : evs) if (classify(e) >= 0) named++;
    check("music with a beat isn't either", named == 0);
    evs.clear(); { std::vector<float> c = clap(); for (auto& x : c) x *= 0.01f; feed(c); }
    check("a very quiet clap (far away) is ignored", evs.empty());
    {                                           // off: the audio code doesn't run it
        gTrigOn = false; static float outb[960], mic[480]; unsigned w0 = gTrigQW.load();
        std::vector<float> c = clap();
        for (int b = 0; b < 40; b++) { for (int j = 0; j < 480; j++) mic[j] = b * 480 + j < (int)c.size() ? c[b * 480 + j] : 0; AudioCallback(nullptr, outb, mic, 480); }
        check("switched off: nothing listens", gTrigQW.load() == w0);
        gTrigOn = true; unsigned w1 = gTrigQW.load();
        for (int b = 0; b < 40; b++) { for (int j = 0; j < 480; j++) mic[j] = b >= 10 && (b - 10) * 480 + j < (int)c.size() ? c[(b - 10) * 480 + j] : 0; AudioCallback(nullptr, outb, mic, 480); }
        check("switched on: the audio code hears the clap", gTrigQW.load() == w1 + 1);
        gTrigOn = false;
    }
    printf("%s\n", fails ? "SOME FAILED" : "all ok");
    return fails ? 1 : 0;
}
