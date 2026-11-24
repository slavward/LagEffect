// (1.68.0) Run by run.sh when node and jsdom are there (tests.yml installs them): node tests/phone_page.js phone.html
// Drives phone.html in jsdom with a fake Lag Effect on the other end of its WebSocket.
const { JSDOM } = require("jsdom");
const fs = require("fs");
const html = fs.readFileSync(process.argv[2], "utf8");
let fails = 0; const ok = (c, w) => { console.log((c ? "  ok   " : "  FAIL ") + w); if (!c) fails++; };
const sent = []; let sock = null;
const layout = { ok: true, do: "layout", title: "Lag Effect", h: 7,
  pads: [{ n: 1, name: "Air horn" }, { n: 3, name: "Bruh <b>" }],
  voice: [{ g: "Mic", name: "Mute", k: "mute_hotkey", t: "tog" }, { g: "Mic", name: "Push-to-talk", k: "ptt_hotkey", t: "hold" },
          { g: "Lag", name: "Stutter", k: "lag", t: "lag" }],
  ch: [{ n: 1, name: "Discord" }], out: [{ n: 1, name: "Out 1" }],
  scenes: [{ n: 1, name: "Gaming" }], macros: [{ n: 1, name: "Intro", k: "macro1_hotkey", hold: false }, { n: 2, name: "Big", k: "macro2_hotkey", hold: true }],
  mine: [{ g: "", name: "Laugh", k: "pad5_hotkey", t: "tap" }] };
const dom = new JSDOM(html, { runScripts: "dangerously", url: "http://192.168.1.20:8790/", pretendToBeVisual: true,
  beforeParse(win) {
    win.WebSocket = class { constructor(u) { this.url = u; this.readyState = 0; sock = this; setTimeout(() => { this.readyState = 1; this.onopen && this.onopen(); }, 5); }
      send(t) { const m = JSON.parse(t); sent.push(m); setTimeout(() => this.reply(m), 1); }
      reply(m) { const r = (o) => this.onmessage && this.onmessage({ data: JSON.stringify(o) });
        if (m.do === "pair") r(m.pin === "1234" ? { ok: true, do: "pair", token: "abc" } : { ok: false, do: "pair", error: "Wrong PIN" });
        else if (m.do === "hello") r(m.token === "abc" ? { ok: true, do: "hello" } : { ok: false, do: "hello", error: "This phone isn't paired" });
        else if (m.do === "layout") r(layout);
        else if (m.do === "state") r({ ok: true, do: "state", h: 7, lag: false, scene: 1, on: { mute_hotkey: true }, ch: [[1, -12.5, true]], out: [[1, 80, false]], mrun: [2] });
        else r({ ok: true, do: m.do }); }
      close() {} };
  } });
const w = dom.window, d = w.document;
const wait = (ms) => new Promise((r) => setTimeout(r, ms));
(async () => {
  await wait(50);
  ok(!d.getElementById("pair").classList.contains("hidden"), "no token: the pairing screen shows");
  d.getElementById("pin").value = "9999"; d.getElementById("pairgo").click(); await wait(20);
  ok(/Wrong/.test(d.getElementById("pairmsg").textContent), "a wrong PIN says so");
  d.getElementById("pin").value = "1234"; d.getElementById("pin").dispatchEvent(new w.Event("input")); await wait(40);
  ok(w.localStorage.getItem("lagfx-token") === "abc", "the right PIN: the token is kept");
  ok(sent.some((m) => m.do === "layout"), "then it asks for the layout");
  ok(d.querySelectorAll("nav button").length === 6, "six tabs (all have something)");
  ok(d.querySelectorAll("#view .btn").length === 2, "Pads tab: 2 pads");
  ok(d.querySelector("#view .btn:nth-child(2)").textContent === "Bruh <b>", "names are text, not HTML");
  d.querySelector("#view .btn").click(); await wait(5);
  ok(sent.some((m) => m.do === "pad" && m.n === 1), "a pad tap sends pad 1");
  // Voice tab
  [...d.querySelectorAll("nav button")].find((b) => /Voice/.test(b.textContent)).click(); await wait(5);
  sock.send(JSON.stringify({ do: "state" })); await wait(10);
  const mute = d.querySelector('.btn[data-k="mute_hotkey"]');
  ok(mute && mute.classList.contains("on"), "Mute lights up from the state");
  const ptt = d.querySelector('.btn[data-k="ptt_hotkey"]');
  ptt.dispatchEvent(new w.Event("pointerdown")); await wait(5);
  ok(sent.some((m) => m.do === "key" && m.name === "ptt_hotkey" && m.down === true), "holding PTT sends key down");
  ptt.dispatchEvent(new w.Event("pointerup")); await wait(5);
  ok(sent.some((m) => m.do === "key" && m.name === "ptt_hotkey" && m.down === false), "letting go sends key up");
  const lag = d.querySelector('.btn[data-k="lag"]');
  lag.dispatchEvent(new w.Event("pointerdown")); await wait(5);
  ok(sent.some((m) => m.do === "lag" && m.ms === 30000), "holding Stutter starts the lag");
  w.dispatchEvent(new w.Event("blur")); await wait(5);
  ok(sent.some((m) => m.do === "lag" && m.on === false), "leaving the page lets go of what's held");
  // Mixer
  [...d.querySelectorAll("nav button")].find((b) => /Mixer/.test(b.textContent)).click(); await wait(5);
  sock.send(JSON.stringify({ do: "state" })); await wait(10);
  const r = d.querySelector('.strip[data-ch="1"] input');
  ok(r && +r.value === -12.5, "the channel slider follows the state (-12.5 dB)");
  ok(d.querySelector('.strip[data-ch="1"] .m').classList.contains("on"), "...and its mute");
  r.value = "-3"; r.dispatchEvent(new w.Event("input")); await wait(120);
  ok(sent.some((m) => m.do === "channel" && m.n === 1 && m.db === -3), "moving it sends channel 1 db -3");
  // Macros
  [...d.querySelectorAll("nav button")].find((b) => /Macros/.test(b.textContent)).click(); await wait(5);
  sock.send(JSON.stringify({ do: "state" })); await wait(10);
  ok(d.querySelector('.btn[data-macro="2"]').classList.contains("run"), "a running macro is marked");
  d.querySelector('.btn[data-macro="1"]').click(); await wait(5);
  ok(sent.some((m) => m.do === "key" && m.name === "macro1_hotkey" && m.down === undefined), "a run-once macro is a tap");
  // reconnect with the token
  sent.length = 0; sock.onclose(); await wait(1000);
  ok(sent.some((m) => m.do === "hello" && m.token === "abc"), "after a drop it reconnects and says hello with its token");
  console.log(fails ? "SOME FAILED" : "all ok"); process.exit(fails ? 1 : 0);
})().catch((e) => { console.log("FAIL " + e.stack); process.exit(1); });
