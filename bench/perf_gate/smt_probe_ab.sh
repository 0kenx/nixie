#!/usr/bin/env bash
# Paired SMT probe corpus – the theory-path counterpart of
# `paired_instructions.sh` (which runs the CNF gate corpus, where no theory
# code executes).
#
# Why: the perf gate and `paired_instructions.sh` are both pure CNF, so a
# change on the CDCL(T)/theory path (arithmetic assertion, EUF, combination)
# passes them while being unmeasured – and a uniform instruction-cost change
# there is invisible to every existing gate (trap 23's shape, on the SMT
# side). This harness measures it directly: deterministic instruction counts
# (`perf stat -x, -e cpu_core/instructions/u`), both arms, same cell, run
# back to back (interleaved), with the solver's deterministic search counters
# (conflicts / decisions / propagations / theory_props, `STATS=1`) checked for
# identity. Reproducibility of the counter on this box: ~2e-7 across repeats
# (wisa xs_8_13: 15 786 844 590 / 15 786 841 004); cycle counts and wall vary
# with load and are printed for context only.
#
# Usage:
#   bench/perf_gate/smt_probe_ab.sh <candidate> [baseline] [cells-file]
#   CORE=5 GATE_CAP=60 ... same invocation
#
# Baseline defaults to the pinned BASELINE sha's precompile binary (note: for
# theory-path work pin a CURRENT baseline – the pinned one predates every
# landing since it was cut, and its SMT trajectories differ).
# Cells file: `<path relative to smt-lib/non-incremental><TAB><extra nixie
# args>`; blank extra = plain verdict cell, `--conflict-limit N` = fixed-budget
# cell (counters print on the budget path; they do NOT print on a time-cap
# timeout, so never let a cell hit `-t`).
#
# Verdict or counter mismatch on any cell is a hard failure (exit 1) – for a
# semantics-inert change the pairing must be bit-identical; for a deliberate
# heuristic landing pass EXPECT_TRAJECTORY_SHIFT=1 to downgrade it to a note
# (the instruction ratio is then a comparison of two different searches).
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CORPUS="${SMT_CORPUS:-$SCRIPT_DIR/../../smt-lib/non-incremental}"
CORE="${CORE:-3}"
CAP="${GATE_CAP:-60}"

CAND="${1:-}"
[ -n "$CAND" ] && [ -x "$CAND" ] || {
    echo "usage: $0 <candidate-binary> [baseline-binary] [cells-file]" >&2
    exit 2
}
BASE="${2:-}"
if [ -z "$BASE" ]; then
    SHA=$(cat "$SCRIPT_DIR/BASELINE")
    BASE="$SCRIPT_DIR/../../precompile/$SHA/nixie"
fi
[ -x "$BASE" ] || { echo "error: baseline binary not found: $BASE" >&2; exit 2; }
CELLS="${3:-$SCRIPT_DIR/smt_probe_cells.txt}"
[ -f "$CELLS" ] || { echo "error: cells file not found: $CELLS" >&2; exit 2; }
[ -d "$CORPUS" ] || { echo "error: SMT corpus not found: $CORPUS (set SMT_CORPUS)" >&2; exit 2; }
command -v perf >/dev/null || { echo "error: perf not installed" >&2; exit 2; }

EV='cpu_core/instructions/u'
# One (bin, file, args) run -> "verdict|conf|dec|props|theory_props|instructions"
# (counters `NA` when the run printed no `; stats:` line).
run_cell() {
    local bin="$1" file="$2"; shift 2
    local out st v c d p tp inst
    out=$(taskset -c "$CORE" env STATS=1 timeout $((CAP + 60)) \
          perf stat -x, -e "$EV" "$bin" "$file" -t "$CAP" "$@" 2>&1) || true
    v=$(grep -E '^(sat|unsat|unknown)$' <<<"$out" | tail -1)
    st=$(grep '^; stats:' <<<"$out")
    c=$(grep -oP 'conflicts=\K[0-9]+' <<<"$st")
    d=$(grep -oP 'decisions=\K[0-9]+' <<<"$st")
    p=$(grep -oP 'propagations=\K[0-9]+' <<<"$st")
    tp=$(grep -oP 'theory_props=\K[0-9]+' <<<"$st")
    inst=$(grep ",$EV," <<<"$out" | head -1 | cut -d, -f1 | tr -d ' ')
    echo "${v:-none}|${c:-NA}|${d:-NA}|${p:-NA}|${tp:-NA}|${inst:-NA}"
}

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
printf '%-44s %-7s %-7s %13s %13s %8s  %s\n' \
    instance base_v cand_v base_inst cand_inst inst_r counters
fail=0
while IFS=$'\t' read -r f extra; do
    case "$f" in ''|'#'*) continue ;; esac
    file="$CORPUS/$f"
    [ -f "$file" ] || { echo "error: missing cell file $file" >&2; exit 2; }
    # shellcheck disable=SC2086
    IFS='|' read -r bv bc bd bp btp bi <<<"$(run_cell "$BASE" "$file" $extra)"
    # shellcheck disable=SC2086
    IFS='|' read -r cv cc cd cp ctp ci <<<"$(run_cell "$CAND" "$file" $extra)"
    note=""
    if [ "$bv" != "$cv" ]; then
        note="VERDICT-MISMATCH"; fail=1
    elif [ "$bc$bd$bp$btp" != "$cc$cd$cp$ctp" ]; then
        note="COUNTERS-DIFF($bc/$cc $bd/$cd $btp/$ctp)"
        [ "${EXPECT_TRAJECTORY_SHIFT:-0}" = "1" ] || fail=1
    fi
    r=$(awk -v a="$bi" -v b="$ci" \
        'BEGIN { if (a=="NA" || b=="NA" || a==0 || b==0) print "n/a"; else printf "%.4f", b/a }')
    printf '%-44s %-7s %-7s %13s %13s %8s  %s\n' \
        "$(basename "$f" .smt2 | cut -c1-43)" "$bv" "$cv" "$bi" "$ci" "$r" "$note"
    [ "$r" != "n/a" ] && echo "$bi $ci" >> "$tmp/pairs"
done < "$CELLS"

awk '{ lr += log($2/$1); n++ }
     END { if (n > 0)
             printf "geomean instruction ratio (cand/base): %.4f over %d cells\n", exp(lr/n), n;
           else print "no valid pairs" }' "$tmp/pairs"
[ "$fail" -ne 0 ] && {
    echo "PAIRING FAILURE: verdicts/counters are not identical – the instruction comparison is void." >&2
    exit 1
}
exit 0
