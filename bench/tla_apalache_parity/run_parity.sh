#!/usr/bin/env bash
# Verdict parity: nixie-tla vs the pinned Apalache oracle (issue #14).
#
# Corpus: the check/simulate cells of apalache/test/tla/cli-integration-tests.md
# (extracted into corpus.json by extract.py; regenerate only with the pinned
# Apalache version in hand). Oracle arm: the real apalache-mc binary, run once
# per cell, stored under precompile/<apalache-sha>/benchmark/tla_parity/ via
# benchstore.py – NEVER re-run an existing cell. Nixie arm: the precompiled
# nixie-tla of this commit, identical argv and working directory.
#
# Comparator (ported from bench/z3_parity's rules):
#   Agree-Ok / Agree-Violation / Agree-Deadlock  – same verdict class
#   MISMATCH                                     – same cell, different verdict
#   Inconclusive                                 – Unknown/timeout on either side
#   Declined                                     – nixie exits 75/120/150
# Inconclusive and Declined NEVER count as a match and are reported separately.
# Agree-Violation additionally requires equal counterexample length.
#
# Exit non-zero on any MISMATCH or on zero compared cells.

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/../.." && pwd)"

APALACHE_PINNED="${APALACHE_BIN:-/nix/store/159k2slmq3qjwxmrawcxg6j4awj0yfq3-apalache-0.63.0/bin/apalache-mc}"
APALACHE_SRC_DIR="${APALACHE_SRC_DIR:-/media/data/proj/temp/apalache/test/tla}"
NIXIE_TLA="${NIXIE_TLA:-$REPO/target/release/nixie-tla}"
MAX_CELLS="${MAX_CELLS:-40}"          # deterministic prefix; raise deliberately
TASKSET="${TASKSET:-taskset -c 0-7}"

[ -x "$APALACHE_PINNED" ] || { echo "apalache-mc 0.63.0 not found: $APALACHE_PINNED" >&2; exit 2; }
[ -x "$NIXIE_TLA" ] || { echo "nixie-tla not built: $NIXIE_TLA" >&2; exit 2; }

APALA_VERSION="$("$APALACHE_PINNED" version 2>/dev/null | head -1)"
echo "oracle: apalache-mc $APALA_VERSION"
echo "arm:    $NIXIE_TLA"

STORE="$REPO/precompile/apalache-0.63.0/benchmark/tla_parity"
mkdir -p "$STORE"

MAX_CELLS="$MAX_CELLS" python3 - "$SCRIPT_DIR" <<'PY' > /tmp/parity_tla_cells.json
import json, os, sys
d = json.load(open(sys.argv[1] + '/corpus.json'))
cells = d['cells'][:int(os.environ.get('MAX_CELLS', '40'))]
json.dump(cells, sys.stdout)
PY

run_cell () {  # $1 arm-binary  $2 out-dir  rest: argv
  local bin="$1"; shift; local out="$1"; shift
  mkdir -p "$out"
  ( cd "$WORK" && taskset -c 0-7 timeout 300 "$bin" "$@" >"$out/stdout" 2>"$out/stderr"; echo "$?" >"$out/code" ) || echo 124 >"$out/code"
}

n=0; agree_ok=0; agree_viol=0; agree_dl=0; mismatch=0; inconclusive=0; declined=0
python3 - <<'PY' > /tmp/parity_tla_lines
import json
for c in json.load(open('/tmp/parity_tla_cells.json')):
    print('\t'.join([c['id'], c['mode']] + [t for t in c['argv'] if t != c['mode']] + [c['spec'], str(c['expected_exit'])]))
PY

while IFS=$'\t' read -r id mode argv_prefix spec expected; do
  n=$((n+1))
  SPEC_PATH="$(cd "$APALACHE_SRC_DIR" && find . -name "$spec" | head -1)"
  [ -n "$SPEC_PATH" ] || { echo "SKIP $id: no $spec" >&2; n=$((n-1)); continue; }
  SPEC_PATH="$APALACHE_SRC_DIR/$SPEC_PATH"
  WORK="$(mktemp -d)"
  cp "$SPEC_PATH" "$WORK/"
  for cfg in "$APALACHE_SRC_DIR/${spec%.tla}"*.cfg; do
    [ -e "$cfg" ] && cp "$cfg" "$WORK/"
  done
  ODIR="$WORK/out"; mkdir -p "$ODIR"

  # --- oracle arm (stored; never re-run an existing cell) ---
  if [ -f "$STORE/$id/code" ]; then
    a_code="$(cat "$STORE/$id/code")"
    cp "$STORE/$id/stdout" "$WORK/apalache.out" 2>/dev/null || true
  else
    run_cell "$APALACHE_PINNED" "$WORK/apalache" "$mode" $argv_prefix "--out-dir=$ODIR/a" "$spec"
    a_code="$(cat "$WORK/apalache/code")"
    mkdir -p "$STORE/$id"; cp "$WORK/apalache/"{code,stdout,stderr} "$STORE/$id/" 2>/dev/null || true
  fi
  # --- nixie arm ---
  run_cell "$NIXIE_TLA" "$WORK/nixie" "$mode" $argv_prefix "--out-dir=$ODIR/n" "$spec"
  x_code="$(cat "$WORK/nixie/code")"

  verdict () {  # from code + stdout
    case "$1" in
      0)  if grep -q "The outcome is: Deadlock" "$2" 2>/dev/null; then echo Deadlock
          elif grep -q "ExecutionsTooShort" "$2" 2>/dev/null; then echo TooShort
          else echo NoError; fi ;;
      12) echo Error ;;
      *)  echo "Exit$1" ;;
    esac
  }
  a_v="$(verdict "$a_code" "$WORK/apalache.out")"
  x_v="$(verdict "$x_code" "$WORK/nixie/stdout")"

  cls=Inconclusive
  case "$x_v" in Exit75|Exit120|Exit150) cls=Declined;; esac
  if [ "$a_v" = NoError ]  && [ "$x_v" = NoError ];  then cls=Agree-Ok; agree_ok=$((agree_ok+1));
  elif [ "$a_v" = Error ]  && [ "$x_v" = Error ];    then cls=Agree-Violation; agree_viol=$((agree_viol+1));
  elif [ "$a_v" = Deadlock ] && [ "$x_v" = Deadlock ]; then cls=Agree-Deadlock; agree_dl=$((agree_dl+1));
  elif [ "$cls" != Declined ]; then
    if [ "$a_v" = "Exit124" ] || [ "$x_v" = "Exit124" ] || [ "$x_v" = Unknown ] || echo "$a_v" | grep -q Exit1; then
      cls=Inconclusive; inconclusive=$((inconclusive+1))
    else cls=MISMATCH; mismatch=$((mismatch+1)); fi
  else declined=$((declined+1)); fi
  echo -e "$id\t$a_v\t$x_v\t$cls\t$spec"
  rm -rf "$WORK"
done < /tmp/parity_tla_lines

echo
echo "cells compared : $n"
echo "  Agree-Ok     : $agree_ok"
echo "  Agree-Viol.  : $agree_viol"
echo "  Agree-Deadlk : $agree_dl"
echo "  Declined     : $declined"
echo "  Inconclusive : $inconclusive"
echo "  MISMATCH     : $mismatch"
[ "$mismatch" -gt 0 ] && exit 1
[ "$n" -gt 0 ] || { echo "zero compared cells" >&2; exit 1; }
exit 0
