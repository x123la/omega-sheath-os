#!/usr/bin/env bash
set -euo pipefail
out=${1:-examples/sample.omega}
mkdir -p "$(dirname "$out")"
python3 - <<'PY' "$out"
import sys
out = sys.argv[1]
b = bytearray(64)
b[0:8] = bytes([79,77,69,71,65,0,1,0])
b[8:10] = (1).to_bytes(2,'little')
b[10] = 1
b[11] = 1
with open(out,'wb') as f:
    f.write(b)
PY
