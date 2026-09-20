#!/usr/bin/env bash
# Standing SMT-side performance table — nixie vs z3 on QF_LIA / QF_BV
# slices, deterministic counters as the metric.
#
# Why this exists (docs/handovers/2026-09-18-mbqi-persistent-model.md,
# continuations): the parity suite's wall-clock columns are
# harness-contaminated and mean nothing; the SMT side had no standing
# perf reference at all.  This is that reference:
#
#   * fixed, deterministic corpus slices (sorted stride samples of the
#     in-repo `smt-lib/non-incremental` extracts — same files every run),
#   * a per-instance wall *cap* only (bounding the run, never compared),
#   * deterministic conflict counters as the metric — each solver's own
#     counters are comparable across nixie revisions (the standing use);
#     cross-solver counter LEVELS are not comparable, solved-within-cap
#     counts are,
#   * verdict cross-check against z3 (any disagreement is a soundness
#     signal, not a perf datum).
#
# Usage:  bench/smt_perf/run_perf.sh [nixie-binary]
# Output: results.json (scratch, gitignored) + results.<os>-<arch>.json
#         (the tracked snapshot — commit that one, following the parity
#         suite's convention).
#
# Comparator: z3 4.16.0 (the parity suite's pinned baseline; the version
# is captured in the snapshot and must match for comparability).
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

NIXIE="${1:-}"
[ -z "$NIXIE" ] && NIXIE="$SCRIPT_DIR/../../target/release/nixie"
if [ ! -x "$NIXIE" ]; then
    echo "error: nixie binary not found: $NIXIE (build: cargo build --release -p nixie-cli)" >&2
    exit 2
fi
command -v z3 >/dev/null || { echo "error: z3 not on PATH" >&2; exit 2; }

# Per-instance wall cap (bounding only) and the slice size per family.
CAP="${SMT_PERF_CAP:-10}"
SLICE="${SMT_PERF_SLICE:-60}"

Z3_VERSION="$(z3 --version 2>/dev/null | head -1)"
NIXIE_SHA="$(git -C "$SCRIPT_DIR/../.." rev-parse --short=8 HEAD 2>/dev/null || echo unknown)"
echo "=== SMT standing perf table ==="
echo "nixie: $NIXIE (sha $NIXIE_SHA)   comparator: $Z3_VERSION"
echo "cap: ${CAP}s/instance   slice: $SLICE/family"
echo

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# Deterministic slice: sorted stride sample of each family's extract.
select_slice() {
    find "$SCRIPT_DIR/../../smt-lib/non-incremental/$1" -name '*.smt2' 2>/dev/null | LC_ALL=C sort | \
        awk -v n="$SLICE" 'NR==1{total=0; buf[NR]=$0; next} {buf[NR]=$0} END {
            total=NR; if (total<=n) {for(i=1;i<=total;i++) print buf[i]}
            else {step=total/n; for(i=0;i<n;i++) print buf[int(i*step)+1]}
        }'
}
select_slice QF_LIA > "$TMP/lia.txt"
select_slice QF_BV > "$TMP/bv.txt"

# One solve: <status> <conflicts> <wall_ms>
run_nixie() {
    local out t0 t1
    t0=$(date +%s%N)
    out=$(timeout "$CAP" "$NIXIE" --stats "$1" 2>/dev/null)
    t1=$(date +%s%N)
    local status conflicts
    status="$(printf '%s\n' "$out" | grep -m1 -oE '^(sat|unsat|unknown)')" || true
    conflicts="$(printf '%s\n' "$out" | grep -m1 -oE 'Conflicts: [0-9]+' | grep -oE '[0-9]+')" || true
    [ -z "$status" ] && status=timeout
    [ -z "$conflicts" ] && conflicts=0
    echo "$status $conflicts $(( (t1-t0)/1000000 ))"
}
run_z3() {
    local out t0 t1
    t0=$(date +%s%N)
    out=$(timeout "$CAP" z3 -st "$1" 2>/dev/null)
    t1=$(date +%s%N)
    local status conflicts
    status="$(printf '%s\n' "$out" | grep -m1 -oE '^(sat|unsat|unknown)')" || true
    # Z3's -st prints `:sat-conflicts N` (SAT-core) and `:conflicts N`
    # (SMT-core).  The historical parser grepped only `:conflicts`, which
    # QF_BV's bit-blasted path never prints — every z3 conflict count in
    # the standing snapshots' recorded `0` (the attribution studies built
    # on "z3 at 0 conflicts" partly on that artifact; see the
    # 2026-09-20 wall-watch correction).  Prefer the SAT counter, fall
    # back to the SMT one.
    conflicts="$(printf '%s\n' "$out" | grep -m1 -oE ':sat-conflicts *[0-9]+' | grep -oE '[0-9]+')" || true
    [ -z "$conflicts" ] && conflicts="$(printf '%s\n' "$out" | grep -m1 -oE ':conflicts *[0-9]+' | grep -oE '[0-9]+')" || true
    [ -z "$status" ] && status=timeout
    [ -z "$conflicts" ] && conflicts=0
    echo "$status $conflicts $(( (t1-t0)/1000000 ))"
}

emit_json() {
    # args: family, then the two result files, cap
    python3 - "$1" "$2" "$3" "$4" <<'PYEOF'
import json, sys, math
family, nixie_f, z3_f, cap = sys.argv[1:5]
cap = int(cap)
rows = []
disagree = 0
with open(nixie_f) as a, open(z3_f) as b:
    for line_a, line_b in zip(a, b):
        path, st, cf, wl = line_a.split()
        _, st2, cf2, wl2 = line_b.split()
        if st in ("sat","unsat") and st2 in ("sat","unsat") and st != st2:
            disagree += 1
        rows.append({"instance": path,
                     "nixie": {"verdict": st, "conflicts": int(cf), "wall_ms": int(wl)},
                     "z3":    {"verdict": st2, "conflicts": int(cf2), "wall_ms": int(wl2)}})
solved = lambda s: sum(1 for r in rows if r["nixie" if s=="n" else "z3"]["verdict"] in ("sat","unsat"))
def par2(key):
    return sum(2*cap*1000 if r[key]["verdict"] not in ("sat","unsat") else r[key]["wall_ms"] for r in rows)/len(rows)
def geo_all(key):
    return round(math.exp(sum(math.log(min(r[key]["wall_ms"], cap*1000)) for r in rows)/len(rows)), 1)
print(json.dumps({"family": family, "n": len(rows),
                  "nixie_solved": solved("n"), "z3_solved": solved("z"),
                  "nixie_par2_ms": round(par2("nixie"), 1), "z3_par2_ms": round(par2("z3"), 1),
                  "nixie_geomean_all_ms": geo_all("nixie"), "z3_geomean_all_ms": geo_all("z3"),
                  "verdict_disagreements": disagree, "rows": rows}, indent=1))
PYEOF
}

ALL_JSON="$TMP/all.json"
echo "[" > "$ALL_JSON"
first=1
for family in QF_LIA QF_BV; do
    slice_file="$TMP/$(echo "$family" | tr 'A-Z_' 'a-z')"  # unused; keep list per family
    list="$TMP/lia.txt"; [ "$family" = QF_BV ] && list="$TMP/bv.txt"
    : > "$TMP/nx.res"; : > "$TMP/z3.res"
    n=0
    while IFS= read -r f; do
        [ -f "$f" ] || continue
        n=$((n+1))
        echo "$(realpath --relative-to="$SCRIPT_DIR/../.." "$f" 2>/dev/null || echo "$f") $(run_nixie "$f")" >> "$TMP/nx.res"
        echo "$f $(run_z3 "$f")" >> "$TMP/z3.res"
    done < "$list"
    [ $first -eq 0 ] && echo "," >> "$ALL_JSON"
    first=0
    emit_json "$family" "$TMP/nx.res" "$TMP/z3.res" "$CAP" >> "$ALL_JSON"
    # Console table for this family
    python3 - "$family" "$TMP/nx.res" "$TMP/z3.res" "$CAP" <<'PYEOF'
import sys, math
fam, a, b, cap = sys.argv[1:5]
rows = list(zip(open(a), open(b)))
ns = sum(1 for x in rows if x[0].split()[1] in ("sat","unsat"))
zs = sum(1 for x in rows if x[1].split()[1] in ("sat","unsat"))
ncf = sum(int(x[0].split()[2]) for x in rows)
zcf = sum(int(x[1].split()[2]) for x in rows)
dis = sum(1 for x in rows if x[0].split()[1] in ("sat","unsat") and x[1].split()[1] in ("sat","unsat") and x[0].split()[1] != x[1].split()[1])
# Solved counts alone hide wall shifts (a solver can hold n while doubling
# every runtime), so the standing readout also carries two wall-based
# aggregates alongside the deterministic counters.  These are
# load-sensitive secondary metrics -- the calm-load discipline exists so
# they are comparable across snapshots; the conflict counters remain the
# primary comparison.
#
#   PAR-2  penalized average runtime: unsolved instances count as 2*cap
#          (the SMT-COMP scoring rule).
#   geomean_all   geometric mean over ALL instances, a timeout counted at
#          cap (capped time, the SMT-COMP "virtual best" companion).
def wall(cell):  # "path status conflicts wall_ms" -> ms, penalized per solver
    f = cell.split()
    st, wl = f[1], int(f[3])
    return 2*cap*1000 if st not in ("sat","unsat") else wl
def wall_capped(cell):
    f = cell.split()
    return min(int(f[3]), cap*1000)
def par2(cells):  return sum(wall(c) for c in cells)/len(cells)
def geo_all(cells):
    return math.exp(sum(math.log(wall_capped(c)) for c in cells)/len(cells))
nx_cells = [x[0].rstrip("\n") for x in rows]
z3_cells = [x[1].rstrip("\n") for x in rows]
both = [(x[0].split(), x[1].split()) for x in rows
        if x[0].split()[1] in ("sat","unsat") and x[1].split()[1] in ("sat","unsat")]
ratios = sorted(int(a[3])/int(b[3]) for a, b in both if int(b[3]) > 0)
med = ratios[len(ratios)//2] if ratios else float("nan")
print(f"{fam}: solved nixie {ns}/{len(rows)}  z3 {zs}/{len(rows)}  disagreements {dis}  conflicts nixie {ncf}  z3 {zcf}")
print(f"    par2_s nixie {par2(nx_cells):8.0f}  z3 {par2(z3_cells):8.0f}   geomean_all ms nixie {geo_all(nx_cells):8.1f}  z3 {geo_all(z3_cells):8.1f}   both-solved median nixie/z3 {med:.2f} (n={len(ratios)})")
PYEOF
done
echo "]" >> "$ALL_JSON"

ENV_RESULTS="results.$(uname -s | tr '[:upper:]' '[:lower:]' | sed 's/darwin/macos/')-$(uname -m | sed 's/x86_64/x86_64/;s/aarch64\|arm64/aarch64/').json"
{
  echo "{"
  echo "  \"z3_version\": \"$Z3_VERSION\","
  echo "  \"nixie_sha\": \"$NIXIE_SHA\","
  echo "  \"cap_s\": $CAP,"
  echo "  \"families\": $(cat "$ALL_JSON" | python3 -c 'import json,sys; print(json.dumps(json.load(sys.stdin), indent=1))')"
  echo "}"
} > results.json
cp results.json "$ENV_RESULTS"
echo
echo "snapshot: results.json (scratch) and $ENV_RESULTS (tracked — commit this one)"
