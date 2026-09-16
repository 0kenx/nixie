#!/usr/bin/env bash
# perf landing gate — deterministic cost check for solving-path landings.
#
# Rationale (docs/studies/2026-09-15-env-probe-regression.md): a 36 h window
# landed ~15 commits each carrying soundness-only verification ("parity
# clean", "suites green") while aggregate solving cost regressed 3x (env
# probes) and a further ~1.4x content-level — because no gate measured COST.
# Chaos cancels in the geomean; a shifted geomean is a process signal.
#
# Method: fixed corpus, two binaries (baseline + candidate), deterministic
# solver counters (conflicts — verified bit-identical across repeats), NOT
# wall-clock.  Verdict changes are a hard failure (soundness canary).
#
# Usage:
#   bench/perf_gate/run_gate.sh [candidate-binary]     # baseline from BASELINE file
#   GATE_BASELINE=<bin> bench/perf_gate/run_gate.sh    # explicit baseline
#
# Thresholds (conflicts geomean candidate/baseline, both-solved set):
#   <= 1.05  PASS (neutrality band, docs/BENCHMARKING.md)
#   <= 1.15  WARN (record the delta in the landing message)
#   >  1.15  FAIL (do not land without a justified, measured trade)
#   any verdict mismatch or solved-count drop: FAIL.
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CAP="${GATE_CAP:-150}"
CACHE="$SCRIPT_DIR/.cache"

CAND="${1:-}"
[ -z "$CAND" ] && CAND="$SCRIPT_DIR/../../target/release/nixie"
if [ ! -x "$CAND" ]; then
    echo "error: candidate binary not found: $CAND (build with: cargo build --release -p nixie-cli)" >&2
    exit 2
fi
BASE="${GATE_BASELINE:-}"
if [ -z "$BASE" ]; then
    SHA=$(cat "$SCRIPT_DIR/BASELINE")
    BASE="$SCRIPT_DIR/../../precompile/$SHA/nixie"
    if [ ! -x "$BASE" ]; then
        echo "error: baseline binary precompile/$SHA/nixie missing (rebuild that commit or set GATE_BASELINE)" >&2
        exit 2
    fi
fi

mkdir -p "$CACHE"
FILES=()
for xz in "$SCRIPT_DIR"/corpus/*.cnf.xz; do
    out="$CACHE/$(basename "${xz%.xz}")"
    [ -s "$out" ] || xz -dc "$xz" > "$out"
    FILES+=("$out")
done
# Optional external extensions (big instances, gitignored corpora).
for ext in "$SCRIPT_DIR"/external.d/*.list; do
    [ -e "$ext" ] || break
    while read -r p; do
        [ -f "$p" ] && FILES+=("$p")
    done < "$ext"
done
[ "${#FILES[@]}" -ge 3 ] || { echo "error: corpus too small" >&2; exit 2; }

run() { # bin file -> "verdict conflicts decisions propagations stats_present wall_s"
    local out t0 t1 w
    t0=$(date +%s.%N)
    out=$(taskset -c 0-7 timeout "$CAP" "$1" --stats --dimacs "$2" 2>/dev/null) || true
    t1=$(date +%s.%N)
    w=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.2f", b-a}')
    local v c d p
    v=$(grep -E '^(sat|unsat|unknown)$' <<<"$out" | tail -1)
    c=$(grep -oP '^  Conflicts: \K[0-9]+' <<<"$out" | tail -1)
    d=$(grep -oP '^  Decisions: \K[0-9]+' <<<"$out" | tail -1)
    p=$(grep -oP '^  Propagations: \K[0-9]+' <<<"$out" | tail -1)
    if grep -q '^SAT Solver Statistics:$' <<<"$out"; then sp=1; else sp=0; fi
    echo "${v:-none} ${c:-0} ${d:-0} ${p:-0} $sp $w"
}

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
printf '%-52s %10s %10s %8s %8s\n' instance base_verd cand_verd conf_ratio dec_ratio
awk_ok=1
for f in "${FILES[@]}"; do
    read -r bv bc bd bp bsp bw <<<"$(run "$BASE" "$f")"
    read -r cv cc cd cp csp cw <<<"$(run "$CAND" "$f")"
    name=$(basename "$f" .cnf)
    if [ "$bv" != "$cv" ]; then
        echo "VERDICT MISMATCH on $name: base=$bv cand=$cv" >&2
        awk_ok=0
        printf '%-52s %10s %10s %8s %8s\n' "$name" "$bv" "$cv" MISMATCH ""
        continue
    fi
    if [ "$bv" != "$cv" ]; then
        :   # handled below
    fi
    if { [ "$bv" = "sat" ] || [ "$bv" = "unsat" ]; } && [ "$bsp" = 1 ] && [ "$csp" = 1 ]; then
        # Metric ladder: conflicts (search work), falling back to
        # decisions, then propagations — a propagation-decided instance
        # legitimately has conflicts=decisions=0.
        if [ "$bc" -gt 0 ]; then ma=$bc; mb=$cc
        elif [ "$bd" -gt 0 ]; then ma=$bd; mb=$cd
        elif [ "$bp" -gt 0 ] || [ "$cp" -gt 0 ]; then ma=$bp; mb=$cp
        else ma=0; mb=0; fi
        if [ "$ma" -eq 0 ] && [ "$mb" -eq 0 ]; then
            # Both arms decided with zero search work (e.g. parse-level
            # empty clause): a trivial instance, no cost signal — exclude
            # from the geomean rather than dividing by zero.
            printf '%-52s %10s %10s %8s %8s\n' "${name:0:52}" "$bv" "$cv" trivial ""
            continue
        fi
        if [ "$ma" -eq 0 ] || [ "$mb" -eq 0 ]; then
            # One arm does zero work where the other searches: a real
            # behavioural cliff — surface it loudly, do not average it.
            echo "cliff: $name base_metric=$ma cand_metric=$mb (one arm trivially decides, the other searches)" >&2
            echo L >> "$tmp/lost"
            printf '%-52s %10s %10s %8s %8s\n' "${name:0:52}" "$bv" "$cv" CLIFF ""
            continue
        fi
        cr=$(awk -v a="$ma" -v b="$mb" 'BEGIN{printf "%.3f", b/a}')
        dr=$(awk -v a="$bd" -v b="$cd" 'BEGIN{if(a>0)printf "%.3f", b/a; else printf "-"}')
        echo "$name $ma $mb $bd $cd $bw $cw $bv" >> "$tmp/pairs"
        wr=$(awk -v a="$bw" -v b="$cw" 'BEGIN{if(a>0.05)printf "%.2f", b/a; else printf "-"}')
        printf '%-52s %10s %10s %8s %8s %6s\n' "${name:0:52}" "$bv" "$cv" "$cr" "$dr" "w:$wr"
    elif { [ "$bv" = "sat" ] || [ "$bv" = "unsat" ]; } && { [ "$bsp" = 0 ] || [ "$csp" = 0 ]; }; then
        # Verdict survived but the stats block did not: a run that hit the
        # cap between verdict and stats (big cold-read file), or a baseline
        # predating the --stats fast-path fix.  A lost sample — loud, budgeted.
        echo "lost-sample: $name solved but stats block missing (base_sp=$bsp cand_sp=$csp) — raise GATE_CAP or re-pin BASELINE" >&2
        echo L >> "$tmp/lost"
        printf '%-52s %10s %10s %8s %8s\n' "${name:0:52}" "$bv" "$cv" LOST ""
    else
        printf '%-52s %10s %10s %8s %8s\n' "${name:0:52}" "$bv" "$cv" "-" "-"
    fi
done

[ -s "$tmp/pairs" ] || { echo "error: no comparable solved pairs with counters (see lost-sample notes above)" >&2; exit 2; }
if [ -e "$tmp/lost" ] && [ "$(wc -l < "$tmp/lost")" -gt 2 ]; then
    echo "GATE: FAIL (too many lost samples — raise GATE_CAP; a gate that skips its slow instances is not a gate)" >&2
    exit 1
fi
# Wall is load-noisy, so its band is wide and one-sided (improvements
# never fail): it exists to catch semantics-inert constant-factor costs —
# both 36 h regressions (env probes, CSR mirror) left every deterministic
# counter untouched and inflated wall 3-6x.
result=$(awk '
    { if ($2>0 && $3>0) { lr += log($3/$2); n++; if ($3/$2 > worst) {worst=$3/$2; wi=$1}; if ($4>0 && $5>0) { ld += log($5/$4); nd++ }; if ($6>0.05) { lw += log($7/$6); nw++ } } }
    END {
        g = exp(lr/n); gd = nd>0 ? exp(ld/nd) : 0; gw = nw>0 ? exp(lw/nw) : 1;
        printf "GEOMEAN conflicts ratio: %.3f  decisions ratio: %.3f  wall ratio: %.2f  (n=%d, worst %s %.2fx)\n", g, gd, gw, n, wi, worst;
        if (g > 1.15) { print "GATE: FAIL (conflicts geomean > 1.15 — measure, justify, or fix before landing)"; exit 1 }
        else if (gw > 1.5) { print "GATE: FAIL (wall geomean > 1.5x at identical counters — a semantics-inert constant-factor cost; profile before landing)"; exit 1 }
        else if (g > 1.05 || gw > 1.25) { print "GATE: WARN (record the cost delta in the landing message)"; exit 0 }
        else { print "GATE: PASS (counters <= 1.05, wall <= 1.25)"; exit 0 }
    }' "$tmp/pairs")
echo "$result"
gate_rc=$?
[ "$awk_ok" = 1 ] || { echo "GATE: FAIL (verdict mismatch — soundness)" >&2; exit 1; }
exit $gate_rc
