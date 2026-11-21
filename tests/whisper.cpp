// Mic > Speech since 1.58.0: the Whisper engine core, for real: whisper.cpp's sample recording (JFK, "ask not what your
// country can do for you") is fed through gSpRing as fast as it would be spoken, with a real model (tests.yml
// downloads Fast = tiny.en). Checks the words, where they are on the clock, and how soon a word is known.
#include "stubs.h"
#include <vector>
#include <mutex>
#include <string>
#include <cstdio>
#include AUDIO
#include "whisper.h"
#include WS
static int fails = 0;
static void check(const char* what, bool ok) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
static std::mutex mu;
struct Got { WsResult r; long long fedClock; };
static std::vector<Got> got;
static std::atomic<long long> fed{ 0 };         // the clock of the audio fed so far
static const long long T0 = 480000;             // (the clock when feeding starts: any number)
static void cb(const WsResult* r, void*) { std::lock_guard<std::mutex> g(mu); got.push_back({ *r, fed.load() }); }
static std::string norm(const char* s)          // lower case, letters and spaces
{
    std::string o; for (; *s; s++) { char c = *s; if (c >= 'A' && c <= 'Z') c += 32; if ((c >= 'a' && c <= 'z') || c == ' ') o += c; else if (c == '\'') continue; else o += ' '; }
    std::string t; for (char c : o) if (!(c == ' ' && (t.empty() || t.back() == ' '))) t += c;
    return t;
}
static void feed(const short* x, size_t n)      // as fast as it's spoken: 20 ms at a time
{
    for (size_t i = 0; i < n; i += 320) {
        const size_t k = n - i < 320 ? n - i : 320;
        const unsigned w = gSpW.load();
        for (size_t j = 0; j < k; j++) gSpRing[(w + j) & (SP_RING - 1)] = x[i + j];
        gSpW.store(w + (unsigned)k);
        fed.store(T0 + 3LL * (w + (unsigned)k));
        std::this_thread::sleep_for(std::chrono::milliseconds(20));
    }
}
int main(int argc, char** argv)
{
    if (argc < 3) { printf("usage: whisper <model.bin> <jfk.wav>\n"); return 1; }
    FILE* f = fopen(argv[2], "rb"); if (!f) { printf("no %s\n", argv[2]); return 1; }
    std::vector<unsigned char> b; { unsigned char t[65536]; size_t n; while ((n = fread(t, 1, sizeof t, f)) > 0) b.insert(b.end(), t, t + n); } fclose(f);
    size_t p = 12, dataAt = 0, dataLen = 0;     // the "data" chunk of the WAV
    while (p + 8 <= b.size()) { const unsigned len = b[p + 4] | b[p + 5] << 8 | b[p + 6] << 16 | (unsigned)b[p + 7] << 24;
        if (!memcmp(&b[p], "data", 4)) { dataAt = p + 8; dataLen = len; break; } p += 8 + len + (len & 1); }
    std::vector<short> pcm(dataLen / 2); memcpy(pcm.data(), &b[dataAt], pcm.size() * 2);
    printf("JFK: %.2f s\n", pcm.size() / 16000.0);
    gSpW = 0; gSpRead = 0; gSpBaseW = 0; gSpT0 = T0; gSpStartReq = false; fed = T0;
    static WsEngine E;
    WsStart(E, argv[1], cb, nullptr);
    for (int i = 0; i < 500 && E.running.load() && E.state.load() < 2; i++) std::this_thread::sleep_for(std::chrono::milliseconds(20));
    check("the model loads", E.running.load() && E.state.load() == 2);
    std::vector<short> quiet(16000 * 3); unsigned rng = 1;
    for (auto& q : quiet) { rng = rng * 1664525u + 1013904223u; q = (short)((int)(rng >> 16) % 60 - 30); }   // (a quiet room: -60 dBFS hiss)
    feed(quiet.data(), quiet.size());
    { std::lock_guard<std::mutex> g(mu); check("a quiet room: nothing heard (no made-up words)", got.empty()); }
    const long long speechAt = fed.load();
    feed(pcm.data(), pcm.size());
    std::vector<short> sil(16000 * 3, 0); feed(sil.data(), sil.size());
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    WsStop(E);
    std::string all; int finals = 0, quick = 0;
    long long countryA = -1, countryB = -1, countryKnown = -1, lastCountry = -1;
    for (const Got& g : got) {
        if (g.r.kind == 1) { finals++; all += " "; all += g.r.text; } else quick++;
        for (int i = 0; i < g.r.n; i++) {
            const std::string w = norm(g.r.w[i].text);
            if (w.find("country") == std::string::npos) continue;
            if (countryA < 0 || g.r.w[i].a < countryA + 48000) {   // the first "country"
                if (countryA < 0 || g.r.kind == 1) { countryA = g.r.w[i].a; countryB = g.r.w[i].b; }
                if (countryKnown < 0) countryKnown = g.fedClock;
            }
            if (g.r.kind == 1) lastCountry = g.r.w[i].a;
        }
    }
    printf("  heard (%d final, %d quick guesses; %u passes, last %u ms):%s\n", finals, quick, E.passes.load(), E.lastMs.load(), all.c_str());
    const std::string n = norm(all.c_str());
    check("the words: \"(ask) not what your country can do for you\"", n.find("not what your country can do for you") != std::string::npos);
    check("... and \"ask what you can do for your country\" (11 s without a pause: cut between words, not through them)",
          n.find("what you can do for your country") != std::string::npos);
    const double ca = (countryA - speechAt) / 48000.0, cb2 = (countryB - speechAt) / 48000.0, cl = (lastCountry - speechAt) / 48000.0;
    printf("  the first \"country\": %.2f-%.2f s into the speech; the last one at %.2f s\n", ca, cb2, cl);
    check("the first \"country\" is placed where it's said (about 5 s in, within 0.5 s)", countryA >= 0 && ca > 4.3 && ca < 6.0);
    check("the last one too (about 10 s in)", lastCountry >= 0 && cl > 9.0 && cl < 10.9);
    const double lag = countryKnown >= 0 ? (countryKnown - countryB) / 48000.0 : 99;
    printf("  \"country\" was known %.2f s after it was said\n", lag);
    check("a word is known within 2 s (so a 3 s bleep delay catches it)", lag < 2.0);
    printf(fails ? "%d FAILED\n" : "all ok\n", fails);
    return fails ? 1 : 0;
}
