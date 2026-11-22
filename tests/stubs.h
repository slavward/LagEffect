// Just enough of Windows / miniaudio / the plugin host for LagEffect.cpp's audio code to build and run on Linux.
typedef unsigned char BYTE;
#include <climits>
#include <math.h>
typedef void* HWND;
#include <stdint.h>
typedef intptr_t INT_PTR;
#include <string.h>
#include <stdio.h>
#include <stddef.h>
#include <time.h>
#include <initializer_list>
#include "rnnoise.h"
typedef unsigned int ma_uint32;
typedef struct { void* pUserData; struct { unsigned internalPeriodSizeInFrames, internalPeriods, internalSampleRate; } playback, capture; } ma_device;
static unsigned long long gFakeMs = 1000000;     // (the tests set the clock)
static unsigned long long GetTickCount64() { return gFakeMs; }
#define VK_F8 0x77
static short GetAsyncKeyState(int){ return 0; }
#define MemoryBarrier() __sync_synchronize()
static inline int MulDiv(int a,int b,int c){ return (int)((long long)a*b/c); }
#ifndef STUBS_MORE
#define STUBS_MORE
#include <cwchar>
#include <ctime>
typedef unsigned DWORD;
static DWORD GetTickCount(){ timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return (DWORD)(t.tv_sec*1000+t.tv_nsec/1000000); }
static wchar_t* lstrcpynW(wchar_t* d, const wchar_t* s, int n){ wcsncpy(d,s,n-1); d[n-1]=0; return d; }
#define wsprintfW(buf, fmt, ...) swprintf(buf, 64, fmt, __VA_ARGS__)
#endif
#ifndef VST_STUBS_OWN
#define VST_STUBS_OWN
#define VST_MAXFRAMES 8192
#define VST_MIC 4
#define VST_PER 2
#define VST_CHANS 8
#define VST_RACKS 8
#define VST_OUTS 5
#define VST_CH0 VST_MIC
#define VST_OUT0 (VST_CH0 + VST_RACKS * VST_PER)
struct VstLiveStub { int v; int load() const { return v; } };   // (v: plugins loaded; tests can set it)
static VstLiveStub gVstLive = { 0 };
static VstLiveStub gVstChMap[VST_CHANS];
static bool gStubMicPlug = false; static float gStubPlugGain = 1.0f;   // (tests/beats.cpp: a fake mic plugin before the voice effects)
static bool VstRangeOn(int first, int, int post = -1) { return gStubMicPlug && first == 0 && post == 0; }
static void VstRunRange(int, int, float*, float*, int, int = -1) {}
static void VstRun(float* b, int n) { for (int i = 0; i < n; i++) b[i] *= gStubPlugGain; }
#endif
static bool gStubFxAny = false;
static bool FxAnyOn() { return gStubFxAny; }
// The vocoder's synth plugin (1.55.0): a small fake one here (a sawtooth per note, notes counted), so the
// "Synth plugin" style can be tested end to end without a real plugin.
struct SynEv { int type; int key; int id; float vel; float tune; };   // (as in LagEffect.cpp)
#define SYN_EVMAX 48
static bool gFakeSynth = false;                 // a synth is "loaded"
static struct FakeNote { int key, id; float tune; double ph; bool on; } gFakeNote[16];
static int gFakeOns = 0, gFakeOffs = 0, gFakeTunes = 0, gFakeLastKey = -1, gFakeHeld = 0;
static bool SynthLive() { return gFakeSynth; }
static bool SynthPluginRun(const SynEv* ev, int nev, float* l, float* r, int n)
{
    if (!gFakeSynth) return false;
    for (int i = 0; i < nev; i++) {
        const SynEv& e = ev[i];
        if (e.type == 0) { gFakeOns++; gFakeLastKey = e.key; for (auto& x : gFakeNote) if (!x.on) { x = { e.key, e.id, 0.0f, 0.0, true }; break; } }
        else if (e.type == 1) { gFakeOffs++; for (auto& x : gFakeNote) if (x.on && x.id == e.id) x.on = false; }
        else { gFakeTunes++; for (auto& x : gFakeNote) if (x.on && x.id == e.id) x.tune = e.tune; }
    }
    gFakeHeld = 0;
    for (auto& x : gFakeNote) if (x.on) gFakeHeld++;
    for (int i = 0; i < n; i++) {
        float s = 0;
        for (auto& x : gFakeNote) if (x.on) {
            const double hz = 440.0 * pow(2.0, (x.key + x.tune - 69) / 12.0);
            x.ph += hz / 48000.0; if (x.ph >= 1) x.ph -= 1;
            s += (float)(x.ph * 2 - 1) * 0.2f;
        }
        l[i] = r[i] = s;
    }
    return true;
}
