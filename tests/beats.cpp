// Soundboard > Looper and Beatbox to drums (1.56.0), through the real audio code.
#include "stubs.h"
#include AUDIO
#include <cstdio>
#include <cstdlib>
#include <vector>
#define R 48000
#define BLK 480
static float outb[BLK * 2], mic[BLK]; static long pos = 0;
static int fails = 0;
static void check(const char* what, bool ok) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
static std::vector<float> rec;                  // output 1 (left), everything since the last clear
typedef float (*Src)(long);                     // a mic signal, by sample number
static float silence(long) { return 0.0f; }
static double gHz = 440; static float gAmp = 0.2f;
static float tone(long n) { return gAmp * (float)sin(2 * M_PI * gHz * n / R); }
static void run(int blocks, Src src)
{
    for (int b = 0; b < blocks; b++) {
        for (int j = 0; j < BLK; j++) mic[j] = src(pos + j);
        pos += BLK;
        AudioCallback(nullptr, outb, mic, BLK);
        for (int j = 0; j < BLK; j++) rec.push_back(outb[2 * j]);
    }
}
static double goertzel(const std::vector<float>& x, size_t a, size_t n, double hz)   // the level of one frequency
{
    const double w = 2 * M_PI * hz / R, c = 2 * cos(w); double s1 = 0, s2 = 0;
    for (size_t i = a; i < a + n && i < x.size(); i++) { const double s0 = x[i] + c * s1 - s2; s2 = s1; s1 = s0; }
    return sqrt(s1 * s1 + s2 * s2 - c * s1 * s2) / (n / 2.0);
}
static double rms(const std::vector<float>& x, size_t a, size_t n)
{
    double e = 0; size_t k = 0; for (size_t i = a; i < a + n && i < x.size(); i++, k++) e += x[i] * x[i]; return k ? sqrt(e / k) : 0;
}
static void press(unsigned c) { gLpCmd.fetch_or(c); }

// mouth-like sounds
static int gKind = 0; static long gHitAt = 0; static unsigned gRng = 1;
static float rnd() { gRng = gRng * 1664525u + 1013904223u; return (float)((int)gRng) / 2147483648.0f; }
static float hpS = 0, hpS2 = 0, lpS = 0;
static float hitSound(long n)                   // one mouth sound at gHitAt, then silence
{
    const long t = n - gHitAt;
    if (t < 0 || t > R / 5) return 0.0f;
    const float e = (float)exp(-t / (0.012 * R)) * (t < 48 ? t / 48.0f : 1.0f);
    const float nz = rnd();
    if (gKind == 0) {                           // kick: a low "b" thump (100 Hz falling a little, some breath)
        return 0.5f * e * (float)sin(2 * M_PI * (100 - 20 * t / (double)R * 5) * t / R) + 0.02f * e * nz;
    } else if (gKind == 1) {                    // snare: "pf", a lip burst then a breathy band around 2 kHz
        const double w = 2 * M_PI * 2000.0 / R, q = 0.8, al = sin(w) / (2 * q), a0 = 1 + al;   // band-pass biquad
        static double x1 = 0, x2 = 0, y1 = 0, y2 = 0;
        const double y = ((al / a0) * nz - (al / a0) * x2 - (-2 * cos(w) / a0) * y1 - ((1 - al) / a0) * y2);
        x2 = x1; x1 = nz; y2 = y1; y1 = y;
        return 0.9f * e * (float)y + 0.12f * e * (float)sin(2 * M_PI * 150 * t / R);
    } else {                                    // hi-hat: "ts", hiss up high
        hpS += (nz - hpS) * 0.55f; hpS2 += ((nz - hpS) - hpS2) * 0.55f;
        return 0.5f * e * ((nz - hpS) - hpS2);
    }
}
static void hits(int kind, int count, unsigned* got)   // `count` sounds of one kind, 300 ms apart; returns hits per drum
{
    unsigned before[3]; for (int i = 0; i < 3; i++) before[i] = gBbHits[i].load();
    gKind = kind;
    for (int k = 0; k < count; k++) { gHitAt = pos + 960; run(30, hitSound); }
    for (int i = 0; i < 3; i++) got[i] = gBbHits[i].load() - before[i];
}

int main()
{
    MicReset(); gMicMuted = false; gNsOn = false; gGateMode = GATE_OFF; gLowCutHz = 0;
    gRowMode[0] = MODE_ALL; gRowVol[0] = 100;
    gFeatSound = true; gFeatFx = false; gFxOn = false;
    for (int c = 0; c < BB_SOUNDS; c++) for (int i = 0; i < 4; i++) gBbCent[c][i] = BB_DEFAULT[c][i];
    gBbCentGen.fetch_add(1);
    run(50, silence);

    printf("Looper\n");
    float* mem = (float*)calloc((size_t)LP_LAYERS * LP_MAXF, sizeof(float));
    gLpMem.store(mem);
    press(LPC_REC); gHz = 440; run(100, tone);  // 1 s of A4
    check("recording the first layer", gLpState.load() == LP_REC);
    press(LPC_REC); rec.clear(); run(1, silence);
    const int len = gLpLen.load();
    printf("  loop length %d frames (%.2f s)\n", len, len / (double)R);
    check("the loop is as long as the first layer (1 s)", abs(len - R) <= BLK);
    check("playing, 1 layer", gLpState.load() == LP_PLAY && gLpLayers.load() == 1);
    rec.clear(); run(200, silence);             // 2 s: the loop plays twice
    const double a1 = goertzel(rec, 2400, 24000, 440), a2 = goertzel(rec, len + 2400, 24000, 440);
    printf("  A4 in the loop: %.3f, next time round %.3f (sang %.3f)\n", a1, a2, gAmp);
    check("it plays back what you sang, every time round", a1 > 0.15 && a2 > 0.15 && fabs(a1 - a2) < 0.02);

    press(LPC_REC); gHz = 660; gAmp = 0.15f; run(1, tone);   // layering: E5 for one time round
    check("layering", gLpState.load() == LP_DUB && gLpLayers.load() == 2);
    run(len / BLK + 1, tone);
    press(LPC_REC); rec.clear(); run(300, silence);
    check("2 layers", gLpState.load() == LP_PLAY && gLpLayers.load() == 2);
    const double b440 = goertzel(rec, 2400, 24000, 440), b660 = goertzel(rec, 2400, 24000, 660);
    printf("  both: A4 %.3f, E5 %.3f\n", b440, b660);
    check("both layers play", b440 > 0.15 && b660 > 0.1);
    gLpMute.store(2); rec.clear(); run(150, silence);
    check("muting layer 2 takes E5 out, A4 stays", goertzel(rec, 2400, 24000, 660) < 0.01 && goertzel(rec, 2400, 24000, 440) > 0.15);
    gLpMute.store(0); press(LPC_UNDO); rec.clear(); run(150, silence);
    check("undo takes layer 2 off", gLpLayers.load() == 1 && goertzel(rec, 2400, 24000, 660) < 0.01 && goertzel(rec, 2400, 24000, 440) > 0.15);
    press(LPC_PLAY); rec.clear(); run(100, silence);
    check("stop: silent", gLpState.load() == LP_STOP && rms(rec, 960, 40000) < 1e-4);
    press(LPC_PLAY); rec.clear(); run(100, silence);
    check("play again", gLpState.load() == LP_PLAY && goertzel(rec, 2400, 24000, 440) > 0.15);
    {   // no click where the loop goes round: no jump bigger than the tone's own steps
        double worst = 0; for (size_t i = 1; i < rec.size(); i++) worst = std::max(worst, (double)fabs(rec[i] - rec[i - 1]));
        printf("  biggest step between samples %.4f (the tone's own: %.4f)\n", worst, 2 * M_PI * 440 / R * 0.2);
        check("no clicks", worst < 2 * M_PI * 440 / R * 0.2 * 1.3);
    }
    // what you add lines up with what you heard: written gLpLatF earlier
    press(LPC_CLEAR); run(5, silence);
    check("clear: empty", gLpState.load() == LP_EMPTY);
    press(LPC_REC); run(100, silence); press(LPC_REC); run(1, silence);   // a quiet 1 s loop (block 0 of it played)
    const int len2 = gLpLen.load();
    gLpLatF.store(4800);                        // 100 ms
    press(LPC_REC);                             // layering starts with the next block (loop position BLK)
    long at = -1;
    gKind = 0; gHitAt = pos + BLK + 10000;      // a thump at loop position BLK + 10000 + BLK (the first block is the command's)
    { const long loopStart = pos - BLK; at = gHitAt - loopStart; }
    run(len2 / BLK + 2, hitSound);
    press(LPC_REC); run(1, silence);
    rec.clear(); run(len2 / BLK + 1, silence);
    // find the thump in the playback (rec starts at a loop position we know: count from the loop's start)
    const long recStartPos = (long)((pos - (long)rec.size()) - (gHitAt - at)) % len2;
    int peakAt = 0; float pk = 0; for (size_t i = 0; i < rec.size(); i++) if (fabs(rec[i]) > pk) { pk = fabs(rec[i]); peakAt = (int)i; }
    const long loopPosOfPeak = (recStartPos + peakAt) % len2;
    const long sungPos = at % len2;
    long shift = sungPos - loopPosOfPeak; if (shift < 0) shift += len2;
    printf("  sung at loop position %ld, plays at %ld: %ld frames earlier (asked 4800; the thump's peak is a little after its start)\n", sungPos, loopPosOfPeak, shift);
    check("layers are moved earlier by the delay you heard the loop with", shift > 4800 - 200 && shift < 4800 + 200);
    gLpLatF.store(0);
    press(LPC_CLEAR); run(5, silence);
    press(LPC_REC); run(60, silence); press(LPC_REC); run(1, silence);
    for (int i = 0; i < 8; i++) { press(LPC_REC); run(3, silence); press(LPC_REC); run(3, silence); }
    check("8 layers at most", gLpLayers.load() == 8 && gLpFull.load());
    press(LPC_CLEAR); run(5, silence);
    rec.clear(); run(50, silence);
    check("cleared: silent", gLpState.load() == LP_EMPTY && rms(rec, 0, rec.size()) == 0.0);

    {   // 1.61.0: the looper records a Mixer channel (an app like Discord), before its fader: muted, it's still recorded
        printf("Looper from a Mixer channel (1.61.0)\n");
        gMicMuted = true;
        gCh[0].type = CH_APP; gCh[0].db10 = 0; gCh[0].routes = 1; gCh[0].mute = true; gChA[0].live = true;
        static long chn = 0; static float pkt[480 * 2];
        auto runCh = [&](int blocks) {
            for (int b = 0; b < blocks; b++) {
                while (chn < pos + BLK * 4) { for (int i = 0; i < 480; i++) { const float v = 0.2f * (float)sin(2 * M_PI * 523 * (chn + i) / R); pkt[2 * i] = v; pkt[2 * i + 1] = v; } ChanPush(0, pkt, 480, 2); chn += 480; }
                run(1, silence);
            }
        };
        chn = pos;                              // (the app's audio starts now)
        gCh[0].mute = false; runCh(50); rec.clear(); runCh(50);
        const double heard = goertzel(rec, 2400, 19200, 523);
        gCh[0].mute = true; runCh(20); rec.clear(); runCh(50);
        printf("  the app on output 1: %.3f unmuted, %.3f muted\n", heard, goertzel(rec, 2400, 19200, 523));
        check("the channel plays, and muted it doesn't", heard > 0.15 && goertzel(rec, 2400, 19200, 523) < 0.01);
        gLpSrcCh.store(0);
        press(LPC_REC); runCh(100); press(LPC_REC); runCh(1);
        gCh[0].type = CH_NONE; gChA[0].live = false;   // (the app goes quiet: what plays now is the loop)
        rec.clear(); run(100, silence);
        const double c = goertzel(rec, 2400, 24000, 523);
        printf("  the loop plays the app's 523 Hz at %.3f (state %d, len %d, layers %d)\n", c, gLpState.load(), gLpLen.load(), gLpLayers.load());
        check("the loop has the app in it", c > 0.1);
        gLpSrcCh.store(-1); press(LPC_CLEAR); run(5, silence);
        gMicMuted = false; gCh[0].mute = false;
    }
    {   // 1.61.0: pads through the voice effects go through the mic plugins too (a fake plugin halving here)
        printf("Pads through the voice effects, and the mic plugins (1.61.0)\n");
        static short pad[R]; for (int i = 0; i < R; i++) pad[i] = (short)(0.4 * 32767 * sin(2 * M_PI * 880 * i / R));
        gPads[0].data = pad; gPads[0].len = R; gPads[0].vol = 100; gPads[0].speed = 0;
        gFeatVst = true; gVstLive.v = 1; gStubMicPlug = true; gStubPlugGain = 0.5f;
        auto padLevel = [&]() { gPads[0].trigger = true; rec.clear(); run(40, silence); gPads[0].stop = true; run(10, silence); return goertzel(rec, 2400, 9600, 880); };
        gPadsFx = false; const double direct = padLevel();
        gPadsFx = true; const double through = padLevel();
        printf("  pad 880 Hz: straight to the outputs %.3f, through the voice effects (and the plugin) %.3f\n", direct, through);
        check("a pad not through the effects skips the mic plugin", direct > 0.37);
        check("a pad through the effects goes through the mic plugin too", through > 0.17 && through < 0.23);
        gPadsFx = false; gFeatVst = false; gVstLive.v = 0; gStubMicPlug = false; gStubPlugGain = 1.0f; gPads[0].data = nullptr; gPads[0].len = 0;
        run(10, silence);
    }
    {   // 1.61.0: music on the outputs you pick
        printf("Music (1.61.0)\n");
        for (unsigned i = 0; i < MUS_RING; i++) { const float v = 0.25f * (float)sin(2 * M_PI * 660 * i / R); gMusRing[i * 2] = v; gMusRing[i * 2 + 1] = v; }
        gMusR = 0; gMusW = MUS_RING - 1; gMusVolPc = 100; gMusOuts = 1;
        gMicMuted = true; gMusPlay = true; rec.clear(); run(50, silence);
        const double on = goertzel(rec, 2400, 19200, 660);
        gMusOuts = 2; rec.clear(); run(50, silence);
        const double other = goertzel(rec, 2400, 19200, 660);
        gMusOuts = 1; gMusVolPc = 50; rec.clear(); run(50, silence);
        const double half = goertzel(rec, 2400, 19200, 660);
        printf("  660 Hz on output 1: %.3f; only on output 2: %.3f; at 50%%: %.3f\n", on, other, half);
        check("plays on the output picked (100% = 9 dB under the file, 1.64.0)", on > 0.25 * 0.33 && on < 0.25 * 0.37);
        check("not on an output that isn't picked", other < 0.001);
        check("its volume (50% = a quarter of 100%: the ear's scale)", half > on * 0.23 && half < on * 0.27);
        const unsigned at = gMusR.load();
        gMusPlay = false; rec.clear(); run(50, silence);
        check("pause: silent, and it keeps its place", goertzel(rec, 2400, 19200, 660) < 0.001 && gMusR.load() - at < 3000);
        gMusPlay = true; run(10, silence);
        {   // a new song / a seek: fades out, jumps, fades in (no click)
            gMusJump.store(gMusR.load() + 30000); gMusJumpGen.fetch_add(1);
            rec.clear(); run(20, silence);
            double worst = 0; for (size_t i = 1; i < rec.size(); i++) worst = std::max(worst, (double)fabs(rec[i] - rec[i - 1]));
            check("a jump fades out and in (no click)", worst < 2 * M_PI * 660 / R * 0.25 * MusGain(50) * 1.3 && gMusR.load() > at + 30000);
        }
        {   // 1.64.0: the music as a Mixer channel: through its fader and routes, not on "Plays on" as well
            gMusOuts = 2; gMusVolPc = 100; gMusR = 0; gMusW = MUS_RING - 1;   // (the song again from the top)
            gCh[1].type = CH_MUS; gCh[1].db10 = 0; gCh[1].routes = 1; gCh[1].mute = false; gChA[1].w = gChA[1].r = 0; gChA[1].primed = false; gChA[1].live = true;
            run(20, silence); rec.clear(); run(50, silence);
            const double viaCh = goertzel(rec, 2400, 19200, 660);
            gCh[1].db10 = -60; run(20, silence); rec.clear(); run(50, silence);
            const double down6 = goertzel(rec, 2400, 19200, 660);
            printf("  as a Mixer channel on output 1: %.3f; its fader at -6 dB: %.3f\n", viaCh, down6);
            check("the Mixer's Music channel plays it (100%)", viaCh > 0.25 * 0.33 && viaCh < 0.25 * 0.37);
            check("its fader works on it", down6 > viaCh * 0.45 && down6 < viaCh * 0.55);
            // (1.65.0) its own duck amount: while you talk it goes down by that, not by the Mixer's "Duck by"
            gCh[1].db10 = 0; gCh[1].duck = true; gDuckDb = 12; gMicMuted = false;
            const double sHz = gHz; const float sAmp = gAmp; gHz = 5000; gAmp = 0.2f;   // (you talk: a high tone, far from the music's 660 Hz)
            auto ducked = [&](int own) {
                gCh[1].duckDb = own; gMusR = 0; gMusW = MUS_RING - 1;   // (the song from the top: the ring holds 2.7 s)
                run(40, tone); rec.clear(); run(50, tone);
                return goertzel(rec, 2400, 19200, 660);
            };
            const double d12 = ducked(0), d24 = ducked(24), d6 = ducked(6);
            gHz = sHz; gAmp = sAmp; gMicMuted = true;
            printf("  ducked while you talk: shared 12 dB %.4f (%.1f dB), its own 24 dB %.4f (%.1f dB), its own 6 dB %.4f (%.1f dB)\n",
                   d12, 20 * log10(d12 / viaCh), d24, 20 * log10(d24 / viaCh), d6, 20 * log10(d6 / viaCh));
            check("Duck by 12 dB takes it down 12 dB", fabs(20 * log10(d12 / viaCh) + 12) < 1.0);
            check("a channel's own duck amount (24 dB) is used", fabs(20 * log10(d24 / viaCh) + 24) < 1.5);
            check("a smaller one (6 dB) too", fabs(20 * log10(d6 / viaCh) + 6) < 1.0);
            gCh[1].duck = false; gCh[1].duckDb = 0; run(60, silence);
            // (1.66.0) a bus: the music channel goes through it; the bus's fader, mute and outputs decide, not the channel's own routes
            auto measure = [&]() { gMusR = 0; gMusW = MUS_RING - 1; run(40, silence); rec.clear(); run(50, silence); return goertzel(rec, 2400, 19200, 660); };
            gCh[2].type = CH_BUS; gCh[2].src[0] = L'1'; gCh[2].src[1] = 0; gCh[2].db10 = 0; gCh[2].routes = 1; gCh[2].mute = false;
            gChA[2].w = gChA[2].r = 0; gChA[2].live = true;
            gCh[1].busId = 1; gCh[1].routes = 2;    // (its own routes: output 2 only; they don't count while it's in the bus)
            const double viaBus = measure();
            gCh[2].db10 = -60; const double busDown = measure();
            gCh[2].db10 = 0; gCh[1].db10 = -60; const double memberDown = measure();
            gCh[1].db10 = 0; gCh[2].routes = 2; const double busElsewhere = measure();
            gCh[2].routes = 1; gCh[2].mute = true; const double busMuted = measure();
            gCh[2].mute = false; gCh[1].busId = 0; gCh[1].routes = 1; const double outAgain = measure();
            gCh[1].busId = 1; gCh[2].type = CH_NONE; gChA[2].live = false; const double busGone = measure();
            printf("  through a bus: %.3f; bus -6 dB %.3f; member -6 dB %.3f; bus to output 2 %.4f; bus muted %.4f; out of the bus %.3f; bus removed %.3f\n",
                   viaBus, busDown, memberDown, busElsewhere, busMuted, outAgain, busGone);
            check("a bus plays its member (0 dB: the same level)", fabs(viaBus / viaCh - 1) < 0.03);
            check("the bus's fader works on it", busDown > viaCh * 0.45 && busDown < viaCh * 0.55);
            check("the member's own fader still works", memberDown > viaCh * 0.45 && memberDown < viaCh * 0.55);
            check("the bus's outputs decide (not the member's own)", busElsewhere < viaCh * 0.01);
            check("muting the bus mutes it", busMuted < viaCh * 0.01);
            check("taken out of the bus: straight to its outputs again", fabs(outAgain / viaCh - 1) < 0.03);
            check("bus removed: its member plays on its own routes", busGone < viaCh * 0.01 || fabs(busGone / viaCh - 1) < 0.03);
            gCh[1].busId = 0; gCh[2].src[0] = 0;
            gCh[1].type = CH_NONE; gChA[1].live = false; gCh[1].db10 = 0; gMusOuts = 1;
        }
        gMusPlay = false; run(10, silence); gMusR = 0; gMusW = 0; gMicMuted = false;
    }
    printf("Beatbox to drums\n");
    gBbOn.store(true); gBbMode.store(0); gBbKit.store(0); gBbSens.store(5); gBbVolPct.store(100);
    run(20, silence);
    const char* names[3] = { "kick", "snare", "hi-hat" };
    for (int k = 0; k < 3; k++) {
        gBbTeach.store(k); gBbTeachN.store(0);
        unsigned g[3]; hits(k, 4, g);
        float m[4] = {}; for (int n = 0; n < gBbTeachN.load(); n++) for (int i = 0; i < 4; i++) m[i] += gBbTeachF[n][i] / 4;
        printf("  a %s sound looks like %.2f %.2f %.2f %.2f (defaults %.2f %.2f %.2f %.2f)\n", names[k], m[0], m[1], m[2], m[3],
               BB_DEFAULT[k][0], BB_DEFAULT[k][1], BB_DEFAULT[k][2], BB_DEFAULT[k][3]);
    }
    gBbTeach.store(-1);
    for (int k = 0; k < 3; k++) {
        unsigned g[3]; hits(k, 8, g);
        printf("  8 %s sounds: kick %u, snare %u, hi-hat %u\n", names[k], g[0], g[1], g[2]);
        char what[80]; snprintf(what, 80, "each %s sound plays a %s", names[k], names[k]);
        check(what, g[k] == 8 && g[0] + g[1] + g[2] == 8);
    }
    {   // how soon the drum plays (drums only: the output is only drums)
        gBbMode.store(1); run(30, silence);
        gKind = 0; gHitAt = pos + 960; rec.clear(); run(30, hitSound);
        int first = -1; for (size_t i = 0; i < rec.size(); i++) if (fabs(rec[i]) > 0.01f) { first = (int)i; break; }
        const double ms = (first - 960) * 1000.0 / R;
        printf("  drums only: the kick starts %.1f ms after your sound\n", ms);
        check("the drum follows within 12 ms", first > 0 && ms < 12);
        gHz = 300; gAmp = 0.2f; rec.clear(); run(50, tone);   // a held note (no new hits after its start)
        check("drums only: your voice is muted", goertzel(rec, 4800, 15000, 300) < 0.005);
        gBbMode.store(0); run(10, silence);
    }
    {   // too quiet for sensitivity 5: nothing
        unsigned before = gBbHits[0] + gBbHits[1] + gBbHits[2];
        gKind = 0; for (int k = 0; k < 4; k++) { gHitAt = pos + 960; run(30, [](long n) { return hitSound(n) * 0.005f; }); }
        check("very quiet sounds don't play drums", gBbHits[0] + gBbHits[1] + gBbHits[2] == before);
    }
    {   // teaching: snare hits taught as "kick" become kicks
        gBbTeach.store(0); gBbTeachN.store(0);
        unsigned g[3]; hits(1, 4, g);
        check("teaching collects 4 hits and plays the sound being taught", gBbTeachN.load() == 4 && g[0] == 4);
        gBbTeach.store(-1);
    }
    gBbOn.store(false); run(100, silence);
    {
        unsigned before = gBbHits[0] + gBbHits[1] + gBbHits[2];
        gKind = 0; gHitAt = pos + 960; rec.clear(); run(30, hitSound);
        check("off: no drums", gBbHits[0] + gBbHits[1] + gBbHits[2] == before);
    }
    printf(fails ? "%d FAILED\n" : "all ok\n", fails);
    return fails ? 1 : 0;
}
