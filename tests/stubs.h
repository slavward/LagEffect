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
struct VstLiveStub { int v; int load() const { return v; } };
static VstLiveStub gVstLive = { 0 };
static VstLiveStub gVstChMap[VST_CHANS];
static bool VstRangeOn(int, int, int = -1) { return false; }
static void VstRunRange(int, int, float*, float*, int, int = -1) {}
static void VstRun(float*, int) {}
#endif
static bool gStubFxAny = false;
static bool FxAnyOn() { return gStubFxAny; }
