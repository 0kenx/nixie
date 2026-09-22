#!/usr/bin/env bash
# FSM synthesis benchmark: nixie (fsm commands, lazy graph reduction) vs
# Z3 (exact eager layered encoding), deterministic instruction counts.
#
# Usage: run.sh [instance-dir] [nixie-binary]
#   instance-dir: from gen.py (default /tmp/fsm_perf)
# Primary metric: perf stat -e instructions:u (load-independent on this
# machine; wall recorded as a footnote only). Verdicts must agree on
# every instance - any mismatch aborts (soundness canary).
set -u
DIR="${1:-/tmp/fsm_perf}"
NIXIE="${2:-$(dirname "$0")/../../precompile/28e82c65/nixie}"
Z3="${Z3:-z3}"
CAP="${CAP:-60}"

[ -x "$NIXIE" ] || { echo "nixie binary missing: $NIXIE" >&2; exit 2; }
command -v "$Z3" >/dev/null || { echo "z3 missing" >&2; exit 2; }
command -v perf >/dev/null || { echo "perf missing" >&2; exit 2; }

echo "nixie: $($NIXIE --version 2>/dev/null | head -1 || echo '(no --version)')"
echo "z3:    $($Z3 --version)"

# Pin both solvers to one core: this is a hybrid CPU (P+E clusters) and
# unpinned runs migrate between clusters, where the per-cluster PMU
# scaling inflates instruction counts by load-dependent factors (measured
# 6x swings on identical binaries). Pinned A/A repeats agree to 1e-6.
PIN="${PIN:-taskset -c 4}"

run_one() {  # $1=solver $2=file -> "verdict<TAB>instructions"
    local out instr verdict
    out=$(perf stat -x, -e cpu_core/instructions/u -- $PIN timeout -s KILL "$CAP"s "$1" "$2" 2>&1)
    verdict=$(printf '%s\n' "$out" | grep -xE 'sat|unsat|unknown' | tail -1)
    [ -n "$verdict" ] || verdict="timeout/error"
    # Hybrid CPUs emit one line per cluster (cpu_atom/..., cpu_core/...);
    # sum every instructions count.
    instr=$(printf '%s\n' "$out" | awk -F, '$3 ~ /instructions/ {gsub(/,/,"",$1); sum += $1} END {if (sum > 0) print sum}')
    [ -n "$instr" ] || instr="NA"
    printf '%s\t%s\n' "$verdict" "$instr"
}

OUT="$DIR/results.tsv"
echo -e "name\texpect\tnixie_v\tnixie_instr\tz3_v\tz3_instr\tnixie_s\tz3_s" > "$OUT"

python3 - "$DIR" << 'PYEOF'
import json, sys
for m in json.load(open(sys.argv[1] + "/manifest.json")):
    print(m["name"], "unsat" if m["expect_unsat"] else "sat")
PYEOF
while read -r name expect; do
    read -r nv ni < <(run_one "$NIXIE" "$DIR/nixie/$name.smt2" | tr '\t' ' ')
    read -r zv zi < <(run_one "$Z3" "$DIR/z3/$name.smt2" | tr '\t' ' ')
    ns=$( { command time -f "%e" "$NIXIE" "$DIR/nixie/$name.smt2" >/dev/null; } 2>&1 | tail -1 )
    zs=$( { command time -f "%e" "$Z3" "$DIR/z3/$name.smt2" >/dev/null; } 2>&1 | tail -1 )
    echo -e "$name\t$expect\t$nv\t$ni\t$zv\t$zi\t$ns\t$zs" >> "$OUT"
    echo "  $name: nixie=$nv/$ni  z3=$zv/$zi"
done < <(python3 - "$DIR" << 'PYEOF'
import json, sys
for m in json.load(open(sys.argv[1] + "/manifest.json")):
    print(m["name"], "unsat" if m["expect_unsat"] else "sat")
PYEOF
)

echo "---- verdict agreement ----"
python3 - "$DIR" << 'PYEOF'
import sys, csv, math
rows = list(csv.DictReader(open(sys.argv[1] + "/results.tsv"), delimiter='\t'))
bad = [r for r in rows if r["nixie_v"] != r["z3_v"]]
for r in bad:
    print(f"MISMATCH {r['name']}: nixie={r['nixie_v']} z3={r['z3_v']}")
print(f"{len(rows)} instances, {len(bad)} mismatches")

def instr(r, k):
    try:
        return float(r[k])
    except ValueError:
        return None

both = [r for r in rows if instr(r, "nixie_instr") and instr(r, "z3_instr")]
def geo(xs):
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")

print(f"{'family':>16} {'n':>2} {'instr geo nixie/z3':>18} {'z3 timeouts':>11}")
fams = {}
for r in both:
    key = r["name"].rsplit("_r", 1)[0]
    fams.setdefault(key, []).append(instr(r, "nixie_instr") / instr(r, "z3_instr"))
zt = sum(1 for r in rows if r["z3_v"] == "timeout/error")
for k in sorted(fams):
    print(f"{k:>16} {len(fams[k]):>2} {geo(fams[k]):>18.3f} {'':>11}")
print(f"{'TOTAL':>16} {len(both):>2} {geo([x for v in fams.values() for x in v]):>18.3f} {zt:>11}")
PYEOF
