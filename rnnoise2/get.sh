#!/usr/bin/env bash
# Gets RNNoise 0.2's release (Lag Effect's "New" noise model, 1.60.0) into rnnoise2/rnnoise-0.2, checked against its
# SHA-256. Its .c files are built with rnnoise2/names.h force-included (every name prefixed rn2_), so they link next to
# the 0.1.1 copy in rnnoise/. Licence: BSD (rnnoise-0.2/COPYING), the same as 0.1.1.
set -euo pipefail
cd "$(dirname "$0")"
URL=https://github.com/xiph/rnnoise/releases/download/v0.2/rnnoise-0.2.tar.gz
SHA=90fce4b00b9ff24c08dbfe31b82ffd43bae383d85c5535676d28b0a2b11c0d37
curl -sSfL -o rnnoise-0.2.tar.gz "$URL"
echo "$SHA  rnnoise-0.2.tar.gz" | sha256sum -c -
tar xzf rnnoise-0.2.tar.gz
rm rnnoise-0.2.tar.gz
