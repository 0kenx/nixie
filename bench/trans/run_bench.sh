#!/usr/bin/env bash
# Transcendental-theory (QF_NRT) differential benchmark: nixie vs z3.
#
# Honest comparator, mirroring bench/z3_parity/METHODOLOGY.md:
#   - `unknown` never counts as a match or as a decision;
#   - a z3 PARSE ERROR (z3 4.16.0 has no exp/log/sqrt on Reals) is recorded
#     as `z3-error`, not as a verdict;
#   - wall time is informational only (per AGENTS.md, wall-clock is never
#     a policy input inside the solver; here it is the reported metric of
#     a finished run, over a deterministic corpus, one process per file).
#
# Usage:
#   ./run_bench.sh [nixie-binary]     (default: ../../precompile/<BASELINE>/nixie
#                                      or target/release/nixie when present)
#
# Output: TSV on stdout (file, nixie-verdict, nixie-ms, z3-verdict, z3-ms).

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

NIXIE="${1:-}"
if [ -z "$NIXIE" ]; then
    if [ -x "$SCRIPT_DIR/../../target/release/nixie" ]; then
        NIXIE="$SCRIPT_DIR/../../target/release/nixie"
    else
        BASE_SHA="$(cat "$SCRIPT_DIR/../../bench/perf_gate/BASELINE" 2>/dev/null || true)"
        NIXIE="$SCRIPT_DIR/../../precompile/$BASE_SHA/nixie"
    fi
fi
# Resolve to an absolute path BEFORE the cd below.
NIXIE="$(cd "$(dirname "$NIXIE")" 2>/dev/null && pwd)/$(basename "$NIXIE")"
if [ ! -x "$NIXIE" ]; then
    echo "error: nixie binary not found/executable: $NIXIE" >&2
    exit 1
fi

Z3_BIN="${Z3:-z3}"
TIMEOUT_S="${TIMEOUT_S:-60}"

printf 'file\tnixie\tnixie_ms\tz3\tz3_ms\n'
for f in corpus/*.smt2; do
    name="$(basename "$f")"

    start=$(date +%s%N)
    nout=$(timeout "$TIMEOUT_S" "$NIXIE" solve "$f" 2>/dev/null | grep -m1 -E '^(sat|unsat|delta-sat|unknown)$' || echo timeout)
    end=$(date +%s%N)
    nms=$(( (end - start) / 1000000 ))

    start=$(date +%s%N)
    # z3 4.16.0 has no exp/log/sqrt on Reals: it interprets them as
    # UNINTERPRETED functions and answers a DIFFERENT (UF-relaxed)
    # problem.  Record that honestly rather than as a verdict.
    if grep -qE '\((exp|log|sqrt) ' "$f"; then
        zout=z3-no-such-fn
        zms=0
    else
        start=$(date +%s%N)
        zout=$(timeout "$TIMEOUT_S" "$Z3_BIN" -in < "$f" 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$' || echo z3-timeout)
        end=$(date +%s%N)
        zms=$(( (end - start) / 1000000 ))
    fi
    end=$(date +%s%N)
    zms=$(( (end - start) / 1000000 ))

    printf '%s\t%s\t%d\t%s\t%d\n' "$name" "$nout" "$nms" "$zout" "$zms"
done
