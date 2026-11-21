// The vocoder's "Synth plugin" style (1.55.0), through the real audio code with a fake synth (tests/stubs.h):
// your pitch becomes notes (snapped to the key), the synth's sound becomes the vocoder's voice.
#include "stubs.h"
#include AUDIO
#include <cstdio>
#define R 48000
static float outb[960], mic[480]; static long pos = 0;
static int fails = 0;
static void check(const char* what, bool ok) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
static double sing(int blocks, double hz, float amp = 0.2f)   // a voice-like tone (fundamental + harmonics); returns the output's rms
{
    double e = 0; int cnt = 0;
    for (int b = 0; b < blocks; b++) {
        for (int j = 0; j < 480; j++, pos++) {
            const double t = (double)pos / R;
            mic[j] = hz > 0 ? amp * (float)(sin(2 * M_PI * hz * t) + 0.5 * sin(4 * M_PI * hz * t) + 0.3 * sin(6 * M_PI * hz * t)) : 0.0f;
        }
        AudioCallback(nullptr, outb, mic, 480);
        if (b >= blocks / 2) for (int j = 0; j < 480; j++) { e += outb[2 * j] * outb[2 * j]; cnt++; }
    }
    return cnt ? sqrt(e / cnt) : 0;
}
static double pitchOf(int blocks, double hz)    // sing, and find the output's pitch (autocorrelation over the last 4 blocks)
{
    static float rec[480 * 4];
    for (int b = 0; b < blocks; b++) {
        sing(1, hz);
        if (b >= blocks - 4) for (int j = 0; j < 480; j++) rec[(b - (blocks - 4)) * 480 + j] = outb[2 * j];
    }
    int best = 0; double bv = -1;
    for (int lag = 40; lag < 600; lag++) {      // 80-1200 Hz
        double c = 0, e1 = 0, e2 = 0;
        for (int i = 0; i + lag < 480 * 4; i++) { c += rec[i] * rec[i + lag]; e1 += rec[i] * rec[i]; e2 += rec[i + lag] * rec[i + lag]; }
        const double v = c / sqrt(e1 * e2 + 1e-20);
        if (v > bv + 0.02) { bv = v; best = lag; }
    }
    return best ? (double)R / best : 0;
}
int main()
{
    MicReset(); gMicMuted = false; gNsOn = false; gGateMode = GATE_OFF; gLowCutHz = 0;
    gRowMode[0] = MODE_ALL; gRowVol[0] = 100;
    gFeatFx = true; gFxOn = true; gFxVocOn = true; gFeatVst = true;
    gFxPitchOn = false; gFxRevOn = false;      // (just the vocoder: the effects that start on, off)
    gVocKey = 0; gVocScale = 1; gVocRetuneMs = 0; gVocSynth = 100; gVocMix = 100; gVocRange = VR_HIGH;
    // the built-in Robot voice first, for its loudness
    gVocStyle = VOC_ROBOT; sing(150, 220); const double robot = sing(100, 220);
    // Synth plugin style, a synth "loaded"
    gFakeSynth = true; gVocStyle = VOC_PLUGIN; gSynNotes = 0; gSynOct = 0;
    const double synth = sing(150, 220);
    printf("A3 (220 Hz) in C major: synth playing key %d, %d held; out %.3f rms (Robot %.3f)\n", gFakeLastKey, gFakeHeld, synth, robot);
    check("your note (A3 = 57) goes to the synth", gFakeLastKey == 57 && gFakeHeld == 1);
    check("about as loud as the built-in Robot voice (within 6 dB)", synth > robot / 2 && synth < robot * 2);
    const double p = pitchOf(40, 220);
    printf("output pitch %.1f Hz\n", p);
    check("the output is at the synth's note (220 Hz)", fabs(p - 220) < 8);
    // sing slightly sharp (225 Hz, +0.4 semitone): with Retune 0 it's pulled back to A3; the synth stays on 57
    sing(60, 225); check("a slightly sharp A still plays A3", gFakeLastKey == 57 && gFakeHeld == 1);
    // stop singing: notes off after ~40 ms
    sing(20, 0); printf("after 0.2 s of silence: %d held, %d note-offs\n", gFakeHeld, gFakeOffs);
    check("notes stop when you stop", gFakeHeld == 0 && gFakeOffs >= 1);
    // chord: A C E
    gSynNotes = 2; const int ons0 = gFakeOns; sing(60, 220);
    int keys[3] = {}, nk = 0; for (auto& x : gFakeNote) if (x.on && nk < 3) keys[nk++] = x.key;
    printf("chord: %d held (%d %d %d), %d new notes\n", gFakeHeld, keys[0], keys[1], keys[2], gFakeOns - ons0);
    check("a chord is three notes", gFakeHeld == 3);
    bool a = false, c = false, e = false; for (int i = 0; i < nk; i++) { a |= keys[i] == 57; c |= keys[i] == 60; e |= keys[i] == 64; }
    check("...A, C and E (in the key)", a && c && e);
    // octave up
    gSynNotes = 0; gSynOct = 1; sing(40, 220);
    check("Octave +1 plays A4 (69)", gFakeLastKey == 69 && gFakeHeld == 1);
    gSynOct = 0;
    // switch to another style while singing, then back: nothing left hanging
    sing(20, 220); gVocStyle = VOC_ROBOT; sing(20, 220); const int offs0 = gFakeOffs; gVocStyle = VOC_PLUGIN; sing(20, 220);
    printf("back from Robot: %d held, %d note-offs on the way back\n", gFakeHeld, gFakeOffs - offs0);
    check("switching away and back leaves no stuck notes", gFakeHeld == 1 && gFakeOffs > offs0);
    // no synth loaded: the built-in Robot voice, not silence
    gFakeSynth = false; const double none = sing(100, 220);
    printf("no synth loaded: out %.3f rms\n", none);
    check("no synth: falls back to the Robot voice", none > robot / 2 && none < robot * 2);
    printf(fails ? "synth: %d FAILED\n" : "synth: all ok\n", fails);
    return fails ? 1 : 0;
}
