#!/usr/bin/env bash
# Lag Effect's tests, on Linux (GitHub runs them on every push: .github/workflows/tests.yml).
#   tests/run.sh [base.cpp]     (tests: gate, synth, beats, sound triggers, morse, speech, [whisper], outputs, names, plain commands, phone remote, recorder; "same sound": mic, a Mixer channel, the vocoder)
# Cuts the audio code out of LagEffect.cpp and runs it with stubs for Windows / miniaudio. With a base file (main's
# LagEffect.cpp), also checks that default settings sound bit-for-bit the same as there.
# Skip that one check for a commit meant to change the sound: put [audio-change] in its message (AUDIO_CHANGE=1 here).
set -euo pipefail
cd "$(dirname "$0")/.."
T=tests; B=$(mktemp -d); trap 'rm -r "$B"' EXIT
CXX="${CXX:-g++}"
# Built like the Windows exe: plain x86-64 (no FMA) and no multiply-add contraction, so "same sound" compares what ships.
# (A runner whose compiler defaults to a newer CPU would otherwise fuse a * b + c differently in old and new code.)
CF=(-O2 -std=c++17 -w -march=x86-64 -mtune=generic -ffp-contract=off -I rnnoise/include -I "$T" -DHAVE_SSE_FLAGS=1 -include xmmintrin.h -include atomic -include thread -include chrono -DMAX_PATH=260 -pthread)

# RNNoise (the noise suppression), from the copy in the repo
for f in denoise rnn rnn_data pitch kiss_fft celt_lpc; do gcc -O2 -w -c -I rnnoise/include "rnnoise/src/$f.c" -o "$B/$f.o"; done
# RNNoise 0.2 (the "New" model, 1.60.0): its release (rnnoise2/get.sh), every name prefixed rn2_, CPU picked at run time
[ -d rnnoise2/rnnoise-0.2 ] || bash rnnoise2/get.sh
R2=rnnoise2/rnnoise-0.2/src
D2=(-O2 -w -DRNN_ENABLE_X86_RTCD -DCPU_INFO_BY_C -include rnnoise2/names.h -I rnnoise2/rnnoise-0.2/include -I "$R2")
for f in denoise rnn rnnoise_data rnnoise_tables pitch kiss_fft celt_lpc nnet nnet_default parse_lpcnet_weights x86/x86cpu x86/x86_dnn_map; do
  gcc "${D2[@]}" -c "$R2/$f.c" -o "$B/rn2_$(basename "$f").o"
done
gcc "${D2[@]}" -msse4.1 -c "$R2/x86/nnet_sse4_1.c" -o "$B/rn2_nnet_sse4_1.o"
gcc "${D2[@]}" -mavx -mfma -mavx2 -c "$R2/x86/nnet_avx2.c" -o "$B/rn2_nnet_avx2.o"
ar rcs "$B/rn.a" "$B"/*.o

# the pieces of LagEffect.cpp the tests use
cut_audio() {   # the audio code: from Imin to the end of AudioCallback
  local a b; a=$(grep -n '^static int Imin(int a, int b)' "$1" | head -1 | cut -d: -f1)
  b=$(grep -n 'gMeterGateOpen = gateHold > 0;' "$1" | head -1 | cut -d: -f1)
  [ -n "$a" ] && [ -n "$b" ] || { echo "can't find the audio code in $1"; exit 1; }
  sed -n "${a},$((b + 1))p" "$1"
}
cut_from_to() { # from the line matching $2 up to the first "}" at the start of a line after it
  local a; a=$(grep -n "$2" "$1" | head -1 | cut -d: -f1); [ -n "$a" ] || { echo "can't find: $2"; exit 1; }
  awk -v s="$a" 'NR >= s { print } NR > s && /^}/ { exit }' "$1"
}
cut_audio LagEffect.cpp > "$B/audio.inc"
cut_from_to LagEffect.cpp '^static float    gExtFill' > "$B/ext.inc"
awk '/^static void ShortDevName\(const wchar_t\* full, wchar_t\* out, int cap\)$/{p=1} /^static void DevTipUpdate/{p=0} p' LagEffect.cpp > "$B/names.inc"
awk '/^\/\/ =+ Recorder \(1\.52\.0\): the core/{p=1} p{print} p && /^    for \(int i = 0; i < s->n; i\+\+\) free\(s->t\[i\]\.ring\);/{getline; print; exit}' LagEffect.cpp > "$B/rcd.inc"
awk '/^\/\/ =+ Whisper speech engine \(1\.58\.0\): the core/{p=1} p{print} /^\/\/ =+ Whisper speech engine: end of the core/{exit}' LagEffect.cpp > "$B/ws.inc"
{ cut_from_to LagEffect.cpp '^static void JsonEsc'; cut_from_to LagEffect.cpp '^static int VstNameMatch'
  awk '/^struct WsTok /{p=1} p{print} p && /^static bool WsPlain/{q=1} q && /^}/{exit}' LagEffect.cpp; } > "$B/plain.inc"   # (1.67.0)
awk '/^static void Sha1\(/{p=1} p{print} p && /^static int PhoneHttp\(/{q=1} q && /^}/{exit}' LagEffect.cpp > "$B/phone.inc"   # (1.68.0)

fail=0
run() { echo; echo "== $1"; shift; if ! "$@"; then fail=1; fi; }

"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/gate" "$T/gate.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/synth" "$T/synth.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/beats" "$T/beats.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/triggers" "$T/triggers.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/morse" "$T/morse.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/speech" "$T/speech.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/noise" "$T/noise.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -DEXT="\"$B/ext.inc\"" -o "$B/outputs" "$T/outputs.cpp" "$B/rn.a"
"$CXX" -O2 -std=c++17 -w -DNAMES="\"$B/names.inc\"" -o "$B/names" "$T/names.cpp"
"$CXX" -O2 -std=c++17 -w -DPLAIN="\"$B/plain.inc\"" -o "$B/plain" "$T/plain.cpp"
"$CXX" -O2 -std=c++17 -w -DPHONE="\"$B/phone.inc\"" -o "$B/phone" "$T/phone.cpp"
"$CXX" -O2 -std=c++17 -w -pthread -DRCD="\"$B/rcd.inc\"" -o "$B/recorder" "$T/recorder.cpp"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/same_new" "$T/audio_same.cpp" "$B/rn.a"

run "Mixer channel gate" "$B/gate"
run "vocoder: Synth plugin style (a fake synth)" "$B/synth"
run "Soundboard: looper and beatbox to drums" "$B/beats"
run "Sound triggers (1.69.0)" "$B/triggers"
run "Morse voice (1.70.0)" "$B/morse"
run "Mic > Speech: the clock, the recognizer's feed, bleeps, muting your voice" "$B/speech"
run "Mic > Noise suppression: Classic and New models" "$B/noise"
# Whisper (Mic > Speech, 1.58.0) with a real model: only where whisper.cpp is built and a model is there (tests.yml does both)
if [ -n "${WHISPER_DIR:-}" ] && [ -n "${WHISPER_MODELS:-}" ]; then
  W="$WHISPER_DIR"
  "$CXX" "${CF[@]}" -I "$W/include" -I "$W/ggml/include" -DAUDIO="\"$B/audio.inc\"" -DWS="\"$B/ws.inc\"" -o "$B/whisper" "$T/whisper.cpp" \
    "$W/build/src/libwhisper.a" "$W/build/ggml/src/libggml.a" "$W/build/ggml/src/libggml-cpu.a" "$W/build/ggml/src/libggml-base.a" "$B/rn.a" -lm -ldl
  for m in $WHISPER_MODELS; do run "Mic > Speech: Whisper on a real recording (JFK), $(basename "$m")" "$B/whisper" "$m" "$W/samples/jfk.wav" ${NOISE_CLIPS:-}; done
else
  echo; echo "== (Whisper on a real recording: skipped, no WHISPER_DIR / WHISPER_MODELS)"
fi
run "extra outputs don't run dry" "$B/outputs"
run "short device names" "$B/names"
run "Streamer.bot plain commands: macro, plugin (1.67.0)" "$B/plain"
run "phone remote: what its port serves (1.68.0)" "$B/phone"
if command -v node >/dev/null && node -e 'require("jsdom")' 2>/dev/null; then
  run "phone remote: the page, against a fake Lag Effect (1.68.0)" node "$T/phone_page.js" phone.html
else
  echo; echo "== (the phone page: skipped, no node / jsdom)"
fi
mkdir -p "$B/rec"; run "recorder" "$B/recorder" "$B/rec"

echo; echo "== same sound as main with default settings"
if [ $# -ge 1 ] && [ -f "$1" ]; then
  cut_audio "$1" > "$B/audio_base.inc"
  "$CXX" "${CF[@]}" -DAUDIO="\"$B/audio_base.inc\"" -o "$B/same_base" "$T/audio_same.cpp" "$B/rn.a"
  new=$("$B/same_new"); base=$("$B/same_base")
  echo "this commit: $(echo $new)"; echo "main:        $(echo $base)"
  if [ "$new" == "$base" ]; then echo "  ok   bit-identical"
  elif [ "${AUDIO_CHANGE:-0}" == "1" ]; then echo "  different, as this commit says ([audio-change])"
  else echo "  FAIL default settings sound different from main (add [audio-change] to the commit message if that's meant)"; fail=1; fi
else
  echo "(no base file given: hashes only)"; "$B/same_new"
fi

echo; [ $fail -eq 0 ] && echo "ALL TESTS PASSED" || echo "SOME TESTS FAILED"
exit $fail
