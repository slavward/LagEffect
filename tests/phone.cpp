// (1.68.0) The phone remote's HTTP side (PhoneHttp, WsAccept): what the phone port serves, and what it refuses.
// Cut from LagEffect.cpp by run.sh (from Sha1 to the end of PhoneHttp): no Windows needed.
#include <cstdio>
#include <cstring>
#include <cstdint>
#include <strings.h>
static int _stricmp(const char* a, const char* b) { return strcasecmp(a, b); }
static int _strnicmp(const char* a, const char* b, size_t n) { return strncasecmp(a, b, n); }
#include PHONE

static int fails = 0;
static void check(bool ok, const char* what) { printf("  %s %s\n", ok ? "ok  " : "FAIL", what); if (!ok) fails++; }
int main()
{
    char r[600];
    check(PhoneHttp("GET / HTTP/1.1\r\nHost: 192.168.1.20:8790\r\n\r\n", r, 600) == 1, "GET / is the page");
    check(PhoneHttp("GET /index.html HTTP/1.1\r\nHost: x\r\n\r\n", r, 600) == 1, "GET /index.html is the page");
    check(PhoneHttp("GET /?from=qr HTTP/1.1\r\nHost: x\r\n\r\n", r, 600) == 1, "a query after / is still the page");
    check(PhoneHttp("GET /favicon.ico HTTP/1.1\r\nHost: x\r\n\r\n", r, 600) == 3, "the icon: nothing");
    check(PhoneHttp("GET /../LagEffect.ini HTTP/1.1\r\nHost: x\r\n\r\n", r, 600) == 0, "any other path: not found");
    check(PhoneHttp("POST / HTTP/1.1\r\nHost: x\r\n\r\n", r, 600) == 0, "not GET: refused");
    const char* ws = "GET /ws HTTP/1.1\r\nHost: 192.168.1.20:8790\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                     "Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nOrigin: http://192.168.1.20:8790\r\nSec-WebSocket-Version: 13\r\n\r\n";
    check(PhoneHttp(ws, r, 600) == 2, "the page's own WebSocket: accepted");
    check(strstr(r, "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=") != nullptr, "...with the right Sec-WebSocket-Accept (RFC 6455's example)");
    const char* evil = "GET /ws HTTP/1.1\r\nHost: 192.168.1.20:8790\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                       "Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nOrigin: http://evil.example\r\n\r\n";
    check(PhoneHttp(evil, r, 600) == 0, "a WebSocket from another site: refused");
    const char* noorigin = "GET /ws HTTP/1.1\r\nHost: 192.168.1.20:8790\r\nUpgrade: websocket\r\nSec-WebSocket-Key: abc==\r\n\r\n";
    check(PhoneHttp(noorigin, r, 600) == 2, "no Origin (not a browser): accepted (it still has to pair)");
    const char* noup = "GET /ws HTTP/1.1\r\nHost: 192.168.1.20:8790\r\nSec-WebSocket-Key: abc==\r\n\r\n";
    check(PhoneHttp(noup, r, 600) == 0, "/ws without Upgrade: refused");
    const char* local = "GET / HTTP/1.1\r\nHost: 127.0.0.1:7600\r\nUpgrade: websocket\r\nSec-WebSocket-Key: abc==\r\nOrigin: http://127.0.0.1:7600\r\n\r\n";
    check(!WsAccept(local, r, 600), "remote control's own port still refuses any web page");
    printf("%s\n", fails ? "SOME FAILED" : "all ok");
    return fails ? 1 : 0;
}
