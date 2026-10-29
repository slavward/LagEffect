RNNoise v0.1.1 (https://github.com/xiph/rnnoise, tag v0.1.1).
Only the files needed to build the library are included. Licence: see COPYING (BSD 3-clause).

One change for Microsoft Visual C++, which has no variable-length arrays: four arrays in
celt_lpc.c and pitch.c were given fixed sizes larger than RNNoise ever needs (marked "LagEffect").
