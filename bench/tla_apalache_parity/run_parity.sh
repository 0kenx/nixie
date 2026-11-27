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

# Scratch files private to this run: two concurrent runs (a full one and a
# cell subset) shared /tmp/parity_tla_lines, and the later one truncated it
# under the earlier one's `read` loop, which then stopped after 40 cells.
CELLS_JSON="$(mktemp)"
LINES="$(mktemp)"
trap 'rm -f "$CELLS_JSON" "$LINES"' EXIT
# `CELL_MATCH=<regex>` keeps the cells whose argv matches; `CELL_IDS=a,b`
# keeps those ids. For re-running a class of cells (every Agree-Violation,
# say) without the prefix.
MAX_CELLS="$MAX_CELLS" python3 - "$SCRIPT_DIR" <<'PY' > "$CELLS_JSON"
import json, os, re, sys
d = json.load(open(sys.argv[1] + '/corpus.json'))
cells = d['cells']
if os.environ.get('CELL_MATCH'):
    pat = re.compile(os.environ['CELL_MATCH'])
    cells = [c for c in cells if pat.search(' '.join(c['argv']))]
if os.environ.get('CELL_IDS'):
    ids = set(os.environ['CELL_IDS'].split(','))
    cells = [c for c in cells if c['id'] in ids]
json.dump(cells[:int(os.environ.get('MAX_CELLS', '40'))], sys.stdout)
PY

run_cell () {  # $1 arm-binary  $2 out-dir  rest: argv
  local bin="$1"; shift; local out="$1"; shift
  mkdir -p "$out"
  ( cd "$WORK" && taskset -c 0-7 timeout 300 "$bin" "$@" >"$out/stdout" 2>"$out/stderr"; echo "$?" >"$out/code" ) || echo 124 >"$out/code"
}

n=0; agree_ok=0; agree_viol=0; agree_dl=0; agree_ref=0; mismatch=0; inconclusive=0; declined=0; oracle_failed=0
python3 - "$CELLS_JSON" <<'PY' > "$LINES"
import json, sys
# One field for the options: `argv` is `mode, options…, spec`, and the spec
# is its own field. (One field per option misaligned every cell with two or
# more options – `read` gives the last variable the remainder – and those
# cells were skipped as "no <option>".) The separator is the ASCII unit
# separator: a tab is IFS whitespace, so an EMPTY options field (`check
# Spec.tla`) collapsed and the exit code landed in `spec`.
US = chr(31)
for c in json.load(open(sys.argv[1])):
    print(US.join([c['id'], c['mode'], ' '.join(c['argv'][1:-1]), c['spec'], str(c['expected_exit'])]))
PY

while IFS=$'\x1f' read -r id mode argv_prefix spec expected; do
  n=$((n+1))
  # A cell's spec may carry a directory (`antipatterns/fold-except/X.tla`):
  # `find -name` matches basenames only, so the path is tried first.
  SPEC_PATH="$(cd "$APALACHE_SRC_DIR" && { [ -f "$spec" ] && echo "./$spec"; } || find . -name "$spec" | head -1)"
  [ -n "$SPEC_PATH" ] || { echo "SKIP $id: no $spec" >&2; n=$((n-1)); continue; }
  SPEC_PATH="$APALACHE_SRC_DIR/$SPEC_PATH"
  WORK="$(mktemp -d)"
  # At the spec's own relative path: the cell's argv names it that way
  # (`antipatterns/fold-except/X.tla`), and a copy at the top of the work
  # directory gave both tools a file that was not there.
  mkdir -p "$WORK/$(dirname "$spec")"
  cp "$SPEC_PATH" "$WORK/$spec"
  for cfg in "$APALACHE_SRC_DIR/${spec%.tla}"*.cfg "$APALACHE_SRC_DIR/${spec%.tla}"*.properties; do
    [ -e "$cfg" ] && cp "$cfg" "$WORK/$(dirname "$spec")/"
  done
  # A spec in a subdirectory may EXTEND its siblings (`MC_FoldExcept3`
  # extends `FoldExcept`); they come along.
  case "$spec" in */*)
    for dep in "$(dirname "$SPEC_PATH")"/*.tla; do
      [ -e "$dep" ] && cp "$dep" "$WORK/$(dirname "$spec")/"
    done;;
  esac
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

  # The oracle arm's verdict classes that carry no verdict of its own: an
  # exit code that is not one of Apalache's outcomes (`Exit1` its crash,
  # `Exit120` its type checker, `Exit255` a configuration error that still
  # printed the outcome line), and `Refused` – a 255 with no outcome line at
  # all, its type errors and documented refusals (`Rec3.tla`,
  # `reorderTest --next=MustFail`). Both are the oracle failing to answer,
  # never a mismatch when Nixie does.
  oracle_without_verdict () {  # $1 = the oracle's class
    case "$1" in Exit124|NoError|TooShort|Error|Deadlock|Unknown) return 1;; esac
    echo "$1" | grep -q '^Exit' || [ "$1" = Refused ]
  }
  verdict () {  # from code + stdout
    case "$1" in
      0)  if grep -q "The outcome is: Deadlock" "$2" 2>/dev/null; then echo Deadlock
          elif grep -q "ExecutionsTooShort" "$2" 2>/dev/null; then echo TooShort
          else echo NoError; fi ;;
      12) echo Error ;;
      # `Unknown` is an answer too – the honest one (exit 255, "The outcome
      # is: Unknown") – and it is Inconclusive, never a mismatch. Any other
      # 255 gave no verdict (a refused option, a role the module lacks):
      # `Refused`, which is a decline like 75.
      255) if grep -q "The outcome is: Unknown" "$2" 2>/dev/null; then echo Unknown
          elif grep -q "The outcome is:" "$2" 2>/dev/null; then echo "Exit$1"
          else echo Refused; fi ;;
      *)  echo "Exit$1" ;;
    esac
  }
  a_v="$(verdict "$a_code" "$WORK/apalache.out")"
  x_v="$(verdict "$x_code" "$WORK/nixie/stdout")"

  cls=Inconclusive
  case "$x_v" in Exit75|Exit120|Exit150|Refused) cls=Declined;; esac
  if [ "$a_v" = NoError ]  && [ "$x_v" = NoError ];  then cls=Agree-Ok; agree_ok=$((agree_ok+1));
  elif [ "$a_v" = TooShort ] && [ "$x_v" = TooShort ]; then cls=Agree-Ok; agree_ok=$((agree_ok+1));
  elif [ "$a_v" = Error ]  && [ "$x_v" = Error ];    then
    # The counterexample length must also agree: both tools search lengths
    # in increasing order, so each one's first counterexample is the
    # shortest, and two different shortest lengths are two different
    # answers about the specification. Apalache prints the first violated
    # state as `State N: state invariant … violated.`; Nixie as
    # `counterexample 1: N step(s)`. A length neither output names (a
    # deadlock, a lasso) is not held against the cell.
    # (`|| true` on the grep: no match is an empty length, not the exit
    # `set -o pipefail` would give the assignment – and the script.)
    # An action invariant is violated on a transition: Apalache reports it at
    # the state the transition leaves ("State 0: action invariant ..."), Nixie
    # as the step taken ("1 step(s)") - the same counterexample, counted from
    # one end or the other.
    a_viol="$(grep -m1 -E '^State [0-9]+: .*violated' "$WORK/apalache.out" 2>/dev/null || true)"
    a_len="$(printf '%s\n' "$a_viol" | awk '{print $2}' | tr -d ':')"
    case "$a_viol" in
      *"action invariant"*) [ -n "$a_len" ] && a_len="$((a_len + 1))";;
    esac
    x_len="$({ grep -m1 -E '^counterexample 1: [0-9]+ step' "$WORK/nixie/stdout" 2>/dev/null || true; } | awk '{print $3}')"
    if [ -n "$a_len" ] && [ -n "$x_len" ] && [ "$a_len" != "$x_len" ]; then
      cls=Agree-Violation-DiffLength; mismatch=$((mismatch+1))
    else cls=Agree-Violation; agree_viol=$((agree_viol+1)); fi
  elif [ "$a_v" = Deadlock ] && [ "$x_v" = Deadlock ]; then cls=Agree-Deadlock; agree_dl=$((agree_dl+1));
  # Both refuse the cell with the same non-verdict exit code (a malformed
  # configuration, say): an agreement that it cannot be checked, reported
  # apart from the verdict classes and never as a mismatch.
  elif [ "$a_v" = "$x_v" ] && oracle_without_verdict "$a_v"; then cls=Agree-Refused; agree_ref=$((agree_ref+1));
  # The oracle itself failed (any exit that is not a verdict of its own:
  # 1 is its crash, 255 its configuration and type errors) – a cell with no
  # oracle verdict to compare against. Reported apart from Inconclusive,
  # because it is the drop-in superset's own count: the cells where Nixie
  # answers and the oracle does not are visible in the rows.
  elif oracle_without_verdict "$a_v" && [ "$a_v" != "$x_v" ]; then cls=OracleFailed; oracle_failed=$((oracle_failed+1))
  elif [ "$cls" != Declined ]; then
    if [ "$a_v" = "Exit124" ] || [ "$x_v" = "Exit124" ] || [ "$x_v" = Unknown ]; then
      cls=Inconclusive; inconclusive=$((inconclusive+1))
    else cls=MISMATCH; mismatch=$((mismatch+1)); fi
  else declined=$((declined+1)); fi
  echo -e "$id\t$a_v\t$x_v\t$cls\t$spec"
  rm -rf "$WORK"
done < "$LINES"

echo
echo "cells compared : $n"
echo "  Agree-Ok     : $agree_ok"
echo "  Agree-Viol.  : $agree_viol"
echo "  Agree-Deadlk : $agree_dl"
echo "  Agree-Refus. : $agree_ref"
echo "  Declined     : $declined"
echo "  Inconclusive : $inconclusive"
echo "  OracleFailed : $oracle_failed"
echo "  MISMATCH     : $mismatch"
[ "$mismatch" -gt 0 ] && exit 1   # a length disagreement counts as a mismatch
[ "$n" -gt 0 ] || { echo "zero compared cells" >&2; exit 1; }
exit 0
