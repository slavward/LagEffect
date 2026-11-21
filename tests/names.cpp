// Short device names (1.53.0): what the lists show for real Windows device names.
#include <cwchar>
#include <cwctype>
#include <cstring>
#include <cstdio>
#include <clocale>
static int Imin(int a, int b) { return a < b ? a : b; }
static void lstrcpynW(wchar_t* d, const wchar_t* s, int n) { if (n <= 0) return; wcsncpy(d, s, n - 1); d[n - 1] = 0; }
static int lstrlenW(const wchar_t* s) { return (int)wcslen(s); }
static int lstrcmpiW(const wchar_t* a, const wchar_t* b) { return wcscasecmp(a, b); }
static void CharLowerW(wchar_t* s) { for (; *s; s++) *s = towlower(*s); }
#include NAMES
int main()
{
    setlocale(LC_ALL, "C.UTF-8");
    static const wchar_t* t[][2] = {
        { L"CABLE Input (VB-Audio Virtual Cable)", L"CABLE Input" },
        { L"CABLE-A Input (VB-Audio Virtual Cable A)", L"CABLE-A Input" },
        { L"Microphone (fifine Microphone)", L"fifine Microphone" },
        { L"Speakers (Realtek(R) Audio)", L"Realtek Audio Speakers" },
        { L"Headphones (2- Arctis 7 Game)", L"Arctis 7 Game Headphones" },
        { L"Realtek HD Audio 2nd output (Realtek(R) Audio)", L"Realtek HD Audio 2nd output" },
        { L"Line (Elgato Wave:3)", L"Line (Elgato Wave:3)" },                                   // ("Elgato Wave:3 Line" isn't shorter: kept)
        { L"Headset Earphone (HyperX Cloud II Wireless)", L"Headset Earphone (HyperX Cloud II Wireless)" },   // (same)
        { L"Speakers", L"Speakers" },
        { L"Mic (Yeti (Stereo))", L"Mic (Yeti (Stereo))" },                                     // (same)
        { L"Speakers (Logitech G733 Gaming Headset)", L"Speakers (Logitech G733 Gaming Headset)" },   // (only 3 shorter: kept)
        { L"(weird)", L"(weird)" },
        { L"Microphone Array (Intel® Smart Sound Technology for Digital Microphones)",
          L"Microphone Array (Intel® Smart Sound Technology for Digital Microphones)" },   // (not shorter: kept)
    };
    int fails = 0;
    for (auto& c : t) {
        wchar_t o[512]; ShortDevName(c[0], o, 512);
        const bool ok = !wcscmp(o, c[1]);
        printf("  %s %ls -> %ls%s%ls\n", ok ? "ok  " : "FAIL", c[0], o, ok ? L"" : L"   want ", ok ? L"" : c[1]);
        if (!ok) fails++;
    }
    printf(fails ? "names: %d FAILED\n" : "names: all ok\n", fails);
    return fails ? 1 : 0;
}
