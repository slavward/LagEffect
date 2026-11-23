// (1.67.0) Streamer.bot's plain-word commands, turned into JSON (WsPlain), and plugin-setting names (VstNameMatch).
// Cut from LagEffect.cpp by run.sh: no Windows needed.
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cwchar>
#include <cwctype>
#include <cctype>
#include <strings.h>
static int _stricmp(const char* a, const char* b) { return strcasecmp(a, b); }
static void lstrcpynA(char* d, const char* s, int n) { if (n <= 0) return; strncpy(d, s, n - 1); d[n - 1] = 0; }
static int lstrcmpiW(const wchar_t* a, const wchar_t* b) { return wcscasecmp(a, b); }
static int lstrlenW(const wchar_t* s) { return (int)wcslen(s); }
#include PLAIN

static int fails = 0;
static void same(const char* in, const char* want)
{
    char out[4096]; WsPlain(in, out, sizeof(out));
    const bool ok = !strcmp(out, want);
    printf("  %s %-46s -> %s\n", ok ? "ok  " : "FAIL", in, out);
    if (!ok) { printf("       wanted %s\n", want); fails++; }
}
static void match(const wchar_t* have, const wchar_t* want, int q)
{
    const int got = VstNameMatch(have, want);
    printf("  %s \"%ls\" for \"%ls\": %d\n", got == q ? "ok  " : "FAIL", have, want, got);
    if (got != q) fails++;
}
int main()
{
    same("mute toggle", "{\"do\":\"mute\",\"on\":\"toggle\"}");                    // (as before)
    same("channel Spotify -12 mute", "{\"do\":\"channel\",\"name\":\"Spotify\",\"db\":-12,\"mute\":true}");
    same("macro Intro", "{\"do\":\"macro\",\"name\":\"Intro\"}");
    same("macro Big laugh", "{\"do\":\"macro\",\"name\":\"Big laugh\"}");
    same("macro 'Big laugh' off", "{\"do\":\"macro\",\"on\":false,\"name\":\"Big laugh\"}");
    same("macro Intro on", "{\"do\":\"macro\",\"on\":true,\"name\":\"Intro\"}");
    same("macro 2", "{\"do\":\"macro\",\"n\":2}");
    same("macro on", "{\"do\":\"macro\",\"name\":\"on\"}");                        // (a macro called "on")
    same("plugin 1 on", "{\"do\":\"plugin\",\"n\":1,\"on\":true}");
    same("plugin OTT off", "{\"do\":\"plugin\",\"name\":\"OTT\",\"on\":false}");
    same("plugin 2 mix 50", "{\"do\":\"plugin\",\"n\":2,\"mix\":50}");
    same("plugin 1 set 'Threshold' -20", "{\"do\":\"plugin\",\"n\":1,\"param\":\"Threshold\",\"value\":-20}");
    same("plugin 1 set Drive 50%", "{\"do\":\"plugin\",\"n\":1,\"param\":\"Drive\",\"value\":\"50%\"}");
    same("plugin channel Discord 1 off", "{\"do\":\"plugin\",\"channel\":\"Discord\",\"n\":1,\"on\":false}");
    same("plugin channel 'Game audio' 2 toggle", "{\"do\":\"plugin\",\"channel\":\"Game audio\",\"n\":2,\"on\":\"toggle\"}");
    same("plugin output 2 1 toggle", "{\"do\":\"plugin\",\"output\":2,\"n\":1,\"on\":\"toggle\"}");
    same("plugin 1 params", "{\"do\":\"plugin\",\"n\":1,\"list\":true}");
    same("plugin toggle", "{\"do\":\"plugin\",\"on\":\"toggle\"}");
    same("plugin mic Reverb on", "{\"do\":\"plugin\",\"mic\":1,\"name\":\"Reverb\",\"on\":true}");
    match(L"Threshold", L"threshold", 3);
    match(L"Threshold (dB)", L"Threshold", 2);
    match(L"Input Gain", L"gain", 1);
    match(L"Ratio", L"Threshold", 0);
    match(L"Ratio", L"", 0);
    printf("%s\n", fails ? "SOME FAILED" : "all ok");
    return fails ? 1 : 0;
}
