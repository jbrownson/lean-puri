#!/bin/sh
# Measures the incremental view against drawing the whole window, with no
# display (Bench.lean). Run from the repository's root.
#
#   scripts/bench.sh               check, then time 5 rounds of 600 frames
#   scripts/bench.sh --callgrind   also count instructions per frame (slow;
#                                  needs valgrind and python3)
#
# Other arguments go to the benchmark: --frames N, --rounds N, --scale 1|1.5|2,
# --no-check, --images DIR.
set -eu

callgrind=no
args=""
for a in "$@"; do
  if [ "$a" = "--callgrind" ]; then callgrind=yes; else args="$args $a"; fi
done

lake build bench
# shellcheck disable=SC2086
.lake/build/bin/bench $args

if [ "$callgrind" = yes ]; then
  out=$(mktemp -d)
  # --trace-children: without it, valgrind doesn't count the thread Lean
  # runs main on.
  valgrind --tool=callgrind --trace-children=yes --callgrind-out-file="$out/callgrind.out.%p" \
    .lake/build/bin/bench --frames 200 --callgrind 2> "$out/valgrind.log"
  echo
  python3 scripts/callgrind-summary.py "$out"
  rm -r "$out"
fi
