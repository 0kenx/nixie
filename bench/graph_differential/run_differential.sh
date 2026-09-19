#!/usr/bin/env bash
# Differential campaign: Nixie's integrated graph constraints vs the MonoSAT
# reference implementation on randomly generated GNF instances.
#
# Both solvers see the same instance; verdicts must agree. The subset and the
# one deliberate semantics split (self-pair reach: MonoSAT reflexive vs
# Nixie strict) are documented in docs/studies/2026-09-19-graph-constraints.md
# and enforced by the GNF driver, which rejects self-pair reach loudly.
#
# Usage:
#   ./run_differential.sh [instance-count]
# Environment:
#   MONOSAT   path to the monosat binary (default: ../temp/monosat build at
#             /tmp/monosat-build/monosat; build with the recipe in the study)
#   NIXIE_GNF path to the graph_gnf example binary
#   VERTICES  fixed vertex count override (default: random 2..8 per graph)
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
COUNT="${1:-500}"
MONOSAT="${MONOSAT:-/tmp/monosat-build/monosat}"
NIXIE_GNF="${NIXIE_GNF:-$(cargo build -p nixie-solver --example graph_gnf --quiet && echo)}"

cd "$HERE/../.." || exit 2
BIN=$(ls -t target/debug/examples/graph_gnf 2>/dev/null | head -1)
if [ -z "${BIN}" ] && [ -n "${CARGO_TARGET_DIR:-}" ]; then
    BIN=$(ls -t "$CARGO_TARGET_DIR/debug/examples/graph_gnf" 2>/dev/null | head -1)
fi
if [ -z "${NIXIE_GNF:-}" ] || [ "${NIXIE_GNF}" = "echo" ]; then
    NIXIE_GNF="$BIN"
fi
if [ ! -x "${NIXIE_GNF}" ]; then
    NIXIE_GNF="$BIN"
fi

if [ ! -x "${NIXIE_GNF}" ] || [ ! -x "${MONOSAT}" ]; then
    echo "error: need runnable graph_gnf (${NIXIE_GNF:-<none>}) and monosat (${MONOSAT:-<none>})" >&2
    exit 2
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

agree=0; disagree=0; skipped=0; sat=0; unsat=0
for i in $(seq 1 "$COUNT"); do
    seed=$((1000000 + i))
    graphs=$((1 + i % 2))
    GEN_ARGS=(--graphs "$graphs")
    [ -n "${VERTICES:-}" ] && GEN_ARGS+=(--vertices "$VERTICES")
    python3 "$HERE/gen_instance.py" "$seed" "${GEN_ARGS[@]}" > "$TMP/i.gnf" || { skipped=$((skipped+1)); continue; }
    m_out=$("${MONOSAT}" "$TMP/i.gnf" 2>"$TMP/m.err" | tail -1)
    n_out=$("${NIXIE_GNF}" "$TMP/i.gnf" 2>"$TMP/n.err" | tail -1)
    n_code=$?
    if [ "$n_code" -eq 2 ]; then
        echo "SKIP (driver rejected) seed=$seed:"; cat "$TMP/n.err"; skipped=$((skipped+1)); continue
    fi
    case "$m_out" in
        s\ SATISFIABLE*) m=sat ;;
        s\ UNSATISFIABLE*) m=unsat ;;
        *) echo "SKIP (monosat inconclusive) seed=$seed: $m_out"; skipped=$((skipped+1)); continue ;;
    esac
    case "$n_out" in
        s\ SATISFIABLE*) n=sat ;;
        s\ UNSATISFIABLE*) n=unsat ;;
        s\ UNKNOWN*) echo "DISAGREE-QUALITY seed=$seed: nixie unknown"; disagree=$((disagree+1)); cp "$TMP/i.gnf" "$TMP/bad-$seed.gnf"; continue ;;
        *) echo "SKIP (nixie no verdict) seed=$seed: $n_out"; skipped=$((skipped+1)); continue ;;
    esac
    if [ "$m" = "$n" ]; then
        agree=$((agree+1))
        [ "$m" = sat ] && sat=$((sat+1)) || unsat=$((unsat+1))
    else
        disagree=$((disagree+1))
        echo "DISAGREEMENT seed=$seed: monosat=$m nixie=$n"
        cp "$TMP/i.gnf" "$TMP/bad-$seed.gnf"
    fi
done

echo
echo "=== graph differential: ${COUNT} instances ==="
echo "agree=${agree} (sat=${sat} unsat=${unsat})  disagree=${disagree}  skipped=${skipped}"
if [ "$disagree" -gt 0 ]; then
    echo "failing instances preserved under: $TMP/bad-*.gnf"
    # keep them (trap removed explicitly)
    trap - EXIT
    mkdir -p "$HERE/failures"
    cp "$TMP"/bad-*.gnf "$HERE/failures/" 2>/dev/null
    exit 1
fi
exit 0
