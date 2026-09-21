#!/usr/bin/env bash
# Powered A/B for an env-armed treatment (heuristic-class changes): the
# perf gate compares two BINARIES under one env; this harness compares
# two ENVS under one binary — the shape every `NIXIE_*` study arm needs
# (the 2026-09-21 fold-stack refusal ran on this pattern; see
# docs/studies/2026-09-21-bve-after-fold-policy.md).
#
# Method (docs/BENCHMARKING.md): standing gate corpus, >=10 seeds
# (`NIXIE_SAT_SEED`, deterministic conflict counters — never wall), the
# treatment env applied to one arm only, verdict agreement checked per
# cell/seed (a disagreement is a soundness failure, printed loudly and
# flagged in the table).
#
# Usage:
#   ARM_ENV='NIXIE_SSR_BIN=1 NIXIE_ELS_PRESEARCH=1' \
#       bench/perf_gate/env_ab.sh [binary]     # default target/release/nixie
#   SEEDS=10 CAP=150 ... same invocation
set -u
BIN="${1:-$(dirname "$0")/../../target/release/nixie}"
[ -x "$BIN" ] || { echo "error: binary not found: $BIN" >&2; exit 2; }
[ -n "${ARM_ENV:-}" ] || { echo "error: set ARM_ENV (the treatment env, e.g. ARM_ENV='NIXIE_X=1')" >&2; exit 2; }
CAP="${CAP:-150}"
SEEDS="${SEEDS:-10}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CORPUS=("$SCRIPT_DIR"/.cache/*.cnf)
for ext in "$SCRIPT_DIR"/external.d/*.list; do
    [ -e "$ext" ] || break
    while read -r p; do [ -f "$p" ] && CORPUS+=("$p"); done < "$ext"
done

run() { # file seed mode -> "verdict conflicts"
    local out
    if [ "$3" = armed ]; then
        out=$(taskset -c 0-7 env NIXIE_SAT_SEED="$2" $ARM_ENV \
              timeout "$CAP" "$BIN" --stats --dimacs "$1" 2>/dev/null) || true
    else
        out=$(taskset -c 0-7 env NIXIE_SAT_SEED="$2" \
              timeout "$CAP" "$BIN" --stats --dimacs "$1" 2>/dev/null) || true
    fi
    local v c
    v=$(grep -E '^(sat|unsat|unknown)$' <<<"$out" | tail -1)
    c=$(grep -oP '^  Conflicts: \K[0-9]+' <<<"$out" | tail -1)
    echo "${v:-none} ${c:-0}"
}

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
for f in "${CORPUS[@]}"; do
    name=$(basename "$f" .cnf)
    : > "$tmp/seeds"
    for sd in $(seq 1 "$SEEDS"); do
        seed=$((sd * 7919))
        IFS=' ' read -r v1 c1 <<<"$(run "$f" "$seed" default)"
        IFS=' ' read -r v2 c2 <<<"$(run "$f" "$seed" armed)"
        if [ "$v1" != "$v2" ]; then
            echo "VERDICT MISMATCH $name seed=$seed: default=$v1 armed=$v2" >&2
            echo "MISMATCH" >> "$tmp/seeds"
        fi
        echo "$c1 $c2" >> "$tmp/seeds"
    done
    awk -v name="$name" '
        $1 == "MISMATCH" { bad = 1 }
        $1 + 0 > 0 && $2 + 0 > 0 { ld += log($1); la += log($2); n++ }
        END {
            if (bad) { printf "%-52s VERDICT-MISMATCH\n", name }
            else if (n > 0)
                printf "%-52s n=%-3d geomean conflicts def=%9.0f armed=%9.0f ratio=%.4f\n",
                       name, n, exp(ld/n), exp(la/n), exp(la/n)/exp(ld/n)
            else printf "%-52s n=0 (no decisive seeds)\n", name
        }' "$tmp/seeds"
done
