#!/usr/bin/env bash
# Paired instruction-count corpus — trap 23's required check for any
# landing that claims cost-neutrality (or a win) on the solving path.
#
# Why: the perf gate's wall band and its trajectory-identity counters are
# BOTH blind to a uniform instruction-cost change (the CSR flip shipped a
# geomean 1.16x instruction regression through both gates —
# docs/studies/2026-09-20-csr-slice6-load-path.md, addendum 7).  This
# script measures the cost directly: deterministic instruction counts
# (`perf stat -e cpu_core/instructions/u`), every gate-corpus cell, both
# arms, same seeds, paired.  A candidate is cost-neutral only if this
# geomean is ~1.000; run it on the standing corpus, never only on the
# motivating class.
#
# Usage:
#   bench/perf_gate/paired_instructions.sh <candidate> [baseline]
#   GATE_CAP=... bench/perf_gate/paired_instructions.sh <candidate>
#
# Baseline defaults to the pinned BASELINE sha's precompile binary.
# Verdict or conflict mismatch on any cell is a hard failure (the pairing
# must be bit-identical for semantics-inert changes; for deliberate
# heuristic landings pass EXPECT_TRAJECTORY_SHIFT=1 to downgrade that
# check to a warning).
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CAP="${GATE_CAP:-150}"

CAND="${1:-}"
[ -n "$CAND" ] && [ -x "$CAND" ] || {
    echo "usage: $0 <candidate-binary> [baseline-binary]" >&2
    exit 2
}
BASE="${2:-}"
if [ -z "$BASE" ]; then
    SHA=$(cat "$SCRIPT_DIR/BASELINE")
    BASE="$SCRIPT_DIR/../../precompile/$SHA/nixie"
fi
[ -x "$BASE" ] || { echo "error: baseline binary not found: $BASE" >&2; exit 2; }

EV='cpu_core/instructions/u'
command -v perf >/dev/null || { echo "error: perf not installed" >&2; exit 2; }

mkdir -p "$SCRIPT_DIR/.cache"
FILES=()
for xz in "$SCRIPT_DIR"/corpus/*.cnf.xz; do
    out="$SCRIPT_DIR/.cache/$(basename "${xz%.xz}")"
    [ -s "$out" ] || xz -dc "$xz" > "$out"
    FILES+=("$out")
done
for ext in "$SCRIPT_DIR"/external.d/*.list; do
    [ -e "$ext" ] || break
    while read -r p; do
        [ -f "$p" ] && FILES+=("$p")
    done < "$ext"
done

# One (bin, file) pair -> "instructions verdict conflicts" (empty on miss).
run_cell() {
    local out inst v c
    out=$(taskset -c 0-7 timeout "$CAP" perf stat -x, -e "$EV" \
          "$1" --stats --dimacs "$2" 2>&1) || true
    inst=$(grep ",$EV," <<<"$out" | head -1 | cut -d, -f1 | tr -d ' ')
    v=$(grep -E '^(sat|unsat|unknown)$' <<<"$out" | tail -1)
    c=$(grep -oP '^  Conflicts: \K[0-9]+' <<<"$out" | tail -1)
    echo "${inst:-0} ${v:-none} ${c:-0}"
}

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
printf '%-52s %12s %12s %9s %10s\n' instance base_inst cand_inst inst_ratio conflicts_pair
fail=0
for f in "${FILES[@]}"; do
    name=$(basename "$f" .cnf)
    IFS=' ' read -r bi bv bc <<<"$(run_cell "$BASE" "$f")"
    IFS=' ' read -r ci cv cc <<<"$(run_cell "$CAND" "$f")"
    if [ "$bv" != "$cv" ]; then
        echo "VERDICT MISMATCH on $name: base=$bv cand=$cv" >&2
        fail=1
    fi
    if [ "$bc" != "$cc" ]; then
        if [ "${EXPECT_TRAJECTORY_SHIFT:-0}" = "1" ]; then
            echo "note: trajectory shift on $name (conflicts $bc -> $cc)" >&2
        else
            echo "CONFLICT MISMATCH on $name: base=$bc cand=$cc (not bit-identical)" >&2
            fail=1
        fi
    fi
    ratio=$(awk -v a="$bi" -v b="$ci" 'BEGIN {
        if (a <= 0 || b <= 0) { print "n/a" } else { printf "%.4f", b/a } }')
    printf '%-52s %12s %12s %9s %10s\n' "$name" "$bi" "$ci" "$ratio" "${bc}->${cc}"
    [ "$bi" -gt 0 ] && [ "$ci" -gt 0 ] && echo "$bi $ci" >> "$tmp/pairs"
done
if [ "$fail" -ne 0 ]; then
    echo "PAIRING FAILURE: verdicts/conflicts are not identical — the instruction comparison is void." >&2
    exit 1
fi
awk '{ if ($1 > 0 && $2 > 0) { lr += log($2/$1); n++ } }
     END { if (n > 0) printf "\ngeomean instruction ratio (cand/base): %.4f  over %d cells\n", exp(lr/n), n;
           else print "\nno valid pairs" }' "$tmp/pairs"
