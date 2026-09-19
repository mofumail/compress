#!/usr/bin/env bash
# Image benchmark: ./bench_img.sh image.png|image.webp ...  (median of 3)
# For each image: decoding it (serial), making the .bzi, and decoding the
# .bzi, on 1 and 16 threads; and Pillow's decode time for comparison.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.bend/bin:$PATH"
[ -x bz ] || bend main.bend -o bz
W=${BENCH_DIR:-/tmp/bz-bench-img}; mkdir -p "$W"
ms() { local ts=""; for _ in 1 2 3; do local s; s=$(date +%s%N); "$@" >/dev/null 2>&1; ts="$ts $(( ($(date +%s%N) - s) / 1000000 ))"; done
       echo $ts | tr ' ' '\n' | sort -n | sed -n 2p; }
run() { env BZ_MODE="$1" BZ_IN="$2" BZ_OUT="$3" BZ_SIZE="$(stat -c%s "$2")" BZ_DEPTH=8 ./bz --threads "$4"; }
printf "%-14s %10s %10s %7s %9s %9s %9s %9s %9s\n" image "input B" ".bzi B" "size" "decode" "to 1c" "to 16c" "from 1c" "from 16c"
for img in "$@"; do
  b=$W/$(basename "$img")
  d=$(ms run 24 "$img" "$b.pam" 1)
  t1=$(ms run 20 "$img" "$b.bzi" 1); t16=$(ms run 20 "$img" "$b.bzi" 16)
  f1=$(ms run 22 "$b.bzi" "$b.out.pam" 1); f16=$(ms run 22 "$b.bzi" "$b.out.pam" 16)
  cmp -s "$b.pam" "$b.out.pam" || { echo "MISMATCH: $img"; exit 1; }
  S=$(stat -c%s "$img"); B=$(stat -c%s "$b.bzi")
  printf "%-14s %10s %10s %6s%% %7s ms %6s ms %6s ms %6s ms %6s ms\n" "$(basename "$img")" "$S" "$B" \
    "$(awk "BEGIN{printf \"%+.0f\", ($B-$S)*100/$S}")" "$d" "$t1" "$t16" "$f1" "$f16"
done
if python3 -c 'import PIL' 2>/dev/null; then
  python3 - "$@" <<'PY'
import sys, time
from PIL import Image
for p in sys.argv[1:]:
    ts = []
    for _ in range(3):
        t = time.time(); Image.open(p).load(); ts.append(time.time() - t)
    print(f'{p.split("/")[-1]:14s} Pillow decode {sorted(ts)[1]*1000:.0f} ms')
PY
fi
