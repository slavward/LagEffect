#!/usr/bin/env bash
# Lag Effect's tests, on Linux (GitHub runs them on every push: .github/workflows/tests.yml).
#   tests/run.sh [base.cpp]     (tests: gate, synth, outputs, names, recorder; "same sound": mic, a Mixer channel, the vocoder)
# Cuts the audio code out of LagEffect.cpp and runs it with stubs for Windows / miniaudio. With a base file (main's
# LagEffect.cpp), also checks that default settings sound bit-for-bit the same as there.
# Skip that one check for a commit meant to change the sound: put [audio-change] in its message (AUDIO_CHANGE=1 here).
set -euo pipefail
cd "$(dirname "$0")/.."
T=tests; B=$(mktemp -d); trap 'rm -r "$B"' EXIT
CXX="${CXX:-g++}"
CF=(-O2 -std=c++17 -w -I rnnoise/include -I "$T" -DHAVE_SSE_FLAGS=1 -include xmmintrin.h -include atomic -include thread -include chrono -DMAX_PATH=260 -pthread)

# RNNoise (the noise suppression), from the copy in the repo
for f in denoise rnn rnn_data pitch kiss_fft celt_lpc; do gcc -O2 -w -c -I rnnoise/include "rnnoise/src/$f.c" -o "$B/$f.o"; done
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

fail=0
run() { echo; echo "== $1"; shift; if ! "$@"; then fail=1; fi; }

"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/gate" "$T/gate.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/synth" "$T/synth.cpp" "$B/rn.a"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -DEXT="\"$B/ext.inc\"" -o "$B/outputs" "$T/outputs.cpp" "$B/rn.a"
"$CXX" -O2 -std=c++17 -w -DNAMES="\"$B/names.inc\"" -o "$B/names" "$T/names.cpp"
"$CXX" -O2 -std=c++17 -w -pthread -DRCD="\"$B/rcd.inc\"" -o "$B/recorder" "$T/recorder.cpp"
"$CXX" "${CF[@]}" -DAUDIO="\"$B/audio.inc\"" -o "$B/same_new" "$T/audio_same.cpp" "$B/rn.a"

run "Mixer channel gate" "$B/gate"
run "vocoder: Synth plugin style (a fake synth)" "$B/synth"
run "extra outputs don't run dry" "$B/outputs"
run "short device names" "$B/names"
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
