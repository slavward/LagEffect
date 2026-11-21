// The Recorder's core (1.52.0): 3 tracks, 60 s each, 16-bit and float, with and without the disk falling behind, split into parts.
// Every frame must come back exactly (16-bit: to the nearest step), a gap must be silence in place (so all tracks keep the
// same length), and each WAV header must agree with its file.
#include <cstdio>
#include <cstring>
#include <cmath>
#include <cwchar>
#include <atomic>
#include <thread>
#include <chrono>
#include <new>
#include <vector>
#include <cstdlib>
#define RATE 48000
#define MAX_PATH 260
static int Imin(int a, int b) { return a < b ? a : b; }
static float Max(float a, float b) { return a > b ? a : b; }
static wchar_t* lstrcpynW(wchar_t* d, const wchar_t* s, int n) { wcsncpy(d, s, n - 1); d[n - 1] = 0; return d; }
#include RCD

static unsigned gHdrLen = 0;
static std::vector<float> ReadWav(const char* path, int& fmt, unsigned& hdrData, long& fileSize)
{
    FILE* f = fopen(path, "rb"); std::vector<float> v;
    if (!f) return v;
    fseek(f, 0, SEEK_END); fileSize = ftell(f); fseek(f, 0, SEEK_SET);
    unsigned char h[12]; if (fread(h, 1, 12, f) != 12) { fclose(f); return v; }
    fmt = 0; unsigned hl = 12;
    for (;;) {                                  // (walk the chunks like a player: "data" found by the chunk sizes)
        unsigned char c[8]; if (fread(c, 1, 8, f) != 8) break; unsigned sz; memcpy(&sz, c + 4, 4); hl += 8;
        if (!memcmp(c, "fmt ", 4)) { unsigned char fm[16]; if (fread(fm, 1, 16, f) != 16) break; fmt = fm[0] == 3; hl += 16; if (sz > 16) { fseek(f, sz - 16, SEEK_CUR); hl += sz - 16; } }
        else if (!memcmp(c, "data", 4)) { hdrData = sz; break; }
        else { fseek(f, sz, SEEK_CUR); hl += sz; }
    }
    gHdrLen = hl;
    if (fmt) { float x; while (fread(&x, 4, 1, f) == 1) v.push_back(x); }
    else { short x; while (fread(&x, 2, 1, f) == 1) v.push_back(x / 32767.0f); }
    fclose(f); return v;
}
static float SampleAt(int track, unsigned long long frame, int ch) { return 0.5f * sinf((float)(frame * (track + 1) * 0.001 + ch)); }

static int Case(int fmt, bool stall, unsigned split, const char* dir)
{
    gRcdSplitBytes = split;
    wchar_t names[3][MAX_PATH];
    for (int i = 0; i < 3; i++) swprintf(names[i], MAX_PATH, L"%s/t%d", dir, i);
    RcdState* s = RcdBegin(3, fmt, names);
    const unsigned B = 480; static float blk[RCD_BLOCK * 2];
    const unsigned long long total = RATE * 60ULL;
    for (unsigned long long frame = 0; frame < total; frame += B) {
        for (int t = 0; t < 3; t++) {
            for (unsigned f = 0; f < B; f++) { blk[f * 2] = SampleAt(t, frame + f, 0); blk[f * 2 + 1] = SampleAt(t, frame + f, 1); }
            RcdPush(s->t[t], blk, B);
        }
        if (!stall && (frame / B) % 20 == 0) std::this_thread::sleep_for(std::chrono::microseconds(300));   // (stall: faster than any disk)
    }
    RcdEnd(s);
    int fails = 0;
    printf("%s, %s, parts of %u bytes: silence put in %llu, failed %d\n", fmt ? "float" : "16-bit", stall ? "disk far behind" : "normal",
           split, (unsigned long long)s->silence, (int)s->failed);
    for (int t = 0; t < 3; t++) {
        std::vector<float> all; int part = 1; unsigned long long hdrSum = 0, fileBytes = 0;
        for (;;) {
            char p[200];
            if (part == 1) snprintf(p, 200, "%s/t%d.wav", dir, t); else snprintf(p, 200, "%s/t%d (part %d).wav", dir, t, part);
            FILE* f = fopen(p, "rb"); if (!f) break; fclose(f);
            int ff; unsigned hd = 0; long fs = 0; auto v = ReadWav(p, ff, hd, fs);
            hdrSum += hd; fileBytes += fs - gHdrLen;
            all.insert(all.end(), v.begin(), v.end()); part++;
        }
        const unsigned long long frames = all.size() / 2; unsigned long long bad = 0, zeros = 0;
        const float tol = fmt ? 0.0f : 1.0f / 32767 + 1e-6f;
        for (unsigned long long i = 0; i < frames; i++) {
            const float a = all[i * 2], b = all[i * 2 + 1];
            const bool ok = fabsf(a - SampleAt(t, i, 0)) <= tol && fabsf(b - SampleAt(t, i, 1)) <= tol;
            if (!ok && a == 0 && b == 0) zeros++; else if (!ok) bad++;
        }
        const bool ok = frames == total && bad == 0 && hdrSum == fileBytes && !s->failed;   // (silent frames: where the disk fell behind)
        printf("  %s track %d: %d part(s), %llu of %llu frames, %llu wrong, %llu silent, headers %s\n", ok ? "ok  " : "FAIL",
               t, part - 1, frames, total, bad, zeros, hdrSum == fileBytes ? "match" : "DON'T match");
        if (!ok) fails++;
    }
    delete s;
    return fails;
}
int main(int argc, char** argv)
{
    if (argc < 2) return 2;
    int fails = 0; char d[240];
    const struct { int fmt; bool stall; unsigned split; } cases[] = { { 0, false, 0x7F000000u }, { 1, false, 0x7F000000u }, { 0, true, 2000000u }, { 1, true, 3000000u } };
    for (int i = 0; i < 4; i++) {
        snprintf(d, 240, "%s/c%d", argv[1], i);
        char cmd[300]; snprintf(cmd, 300, "mkdir -p '%s'", d); if (system(cmd)) return 2;
        fails += Case(cases[i].fmt, cases[i].stall, cases[i].split, d);
    }
    printf(fails ? "recorder: %d FAILED\n" : "recorder: all ok\n", fails);
    return fails ? 1 : 0;
}
