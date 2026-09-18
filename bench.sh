#!/usr/bin/env bash
# Benchmark bz (Bend LZ77/Huffman) against gzip on 1 and 16 cores.
#   ./bench.sh [size_mb] [runs]
# gzip is single-threaded; its 16-core figure splits the input into 16
# slices and gzips them concurrently (what pigz does; the concatenated
# members are a valid .gz stream).
set -euo pipefail
cd "$(dirname "$0")"
MB=${1:-16}; RUNS=${2:-3}; DEPTH=${DEPTH:-8}
W=${BENCH_DIR:-/tmp/bz-bench}; mkdir -p "$W"
IN=$W/corpus-${MB}m.txt
export PATH="$HOME/.bend/bin:$PATH"

if [ ! -s "$IN" ]; then
  find /usr/share/doc /usr/include /usr/share/licenses -type f \
    \( -name '*.txt' -o -name '*.h' -o -name '*.md' -o -name 'LICENSE*' -o -name 'COPYING*' \) \
    2>/dev/null | sort | xargs cat 2>/dev/null | head -c $((MB * 1048576)) > "$IN" || true
fi
[ -x bz ] || bend main.bend -o bz
SIZE=$(stat -c%s "$IN")

div() { awk "BEGIN{printf \"%.$3f\", $1 / $2}"; }

# median wall-clock seconds of RUNS runs of "$@"
t() { for _ in $(seq "$RUNS"); do
        s=$(date +%s.%N); "$@" >/dev/null; e=$(date +%s.%N); awk "BEGIN{printf \"%.3f\n\", $e - $s}"
      done | sort -n | sed -n "$(( (RUNS + 1) / 2 ))p"; }

bz_c() { BZ_MODE=0 BZ_IN=$IN BZ_OUT=$W/out.bz BZ_SIZE=$SIZE BZ_DEPTH=$DEPTH ./bz --threads "$1"; }
bz_d() { BZ_MODE=2 BZ_IN=$W/out.bz BZ_OUT=$W/out.raw BZ_SIZE=$(stat -c%s $W/out.bz) BZ_DEPTH=$DEPTH ./bz --threads "$1"; }
gz_c1() { gzip -"$1" -c "$IN" > $W/out.gz; }
gz_d1() { gzip -dc $W/out.gz > $W/out.gzraw; }
gz_cN() { rm -f $W/part.*; split -n 16 -d "$IN" $W/part.
          ls $W/part.?? | xargs -P16 -I{} sh -c "gzip -$1 -c {} > {}.gz"
          cat $W/part.??.gz > $W/out.gz; }
gz_dN() { ls $W/part.??.gz | xargs -P16 -I{} sh -c 'gzip -dc {} > {}.raw'; }

row() { printf "%-26s %9s %9s %8s %8s\n" "$@"; }
echo "input: $IN  ($SIZE bytes, $((SIZE / 1048576)) MiB), bz depth $DEPTH ($((1 << DEPTH)) chunks), median of $RUNS"
row "" "comp 1c" "comp 16c" "speedup" "ratio"

c1=$(t bz_c 1); c16=$(t bz_c 16); sz=$(stat -c%s $W/out.bz)
d1=$(t bz_d 1); d16=$(t bz_d 16)
cmp -s "$IN" $W/out.raw || { echo "bz ROUNDTRIP FAILED"; exit 1; }
row "bz (Bend)" "$c1" "$c16" "$(div $c1 $c16 1)x" "$(div $SIZE $sz 2)"
bzrow="$d1 $d16"

for L in 1 6; do
  g1=$(t gz_c1 $L); gd1=$(t gz_d1); gs1=$(stat -c%s $W/out.gz)
  cmp -s "$IN" $W/out.gzraw || { echo "gzip roundtrip failed"; exit 1; }
  gN=$(t gz_cN $L); gdN=$(t gz_dN); gsN=$(stat -c%s $W/out.gz)
  row "gzip -$L" "$g1" "$gN" "$(div $g1 $gN 1)x" "$(div $SIZE $gs1 2)"
  eval "gzd$L=\"$gd1 $gdN\""
done

echo; row "" "dec 1c" "dec 16c" "speedup" ""
set -- $bzrow;  row "bz (Bend)" "$1" "$2" "$(div $1 $2 1)x" ""
set -- $gzd1;   row "gzip -1 stream" "$1" "$2" "$(div $1 $2 1)x" ""
set -- $gzd6;   row "gzip -6 stream" "$1" "$2" "$(div $1 $2 1)x" ""
