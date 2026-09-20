#!/usr/bin/env bash
# Deterministic instruction-count corpus runner (work metric, not wall):
# pinned to one P-core because this hybrid machine migrates processes
# between Core and Atom PMUs (unpinned counts diverge run-to-run; see
# docs/studies/2026-09-22-graph-epoch-static-possible-view.md), with a
# retry loop for PMU contention ("<not counted>" while another perf
# session holds slots). Pinned counts are stable to +-0.001% under load.
#
# Usage: run_instructions.sh <corpus-dir> <monosat-bin> <nixie-gnf-bin> [out.csv] [cpu]
set -u
HERE="$(cd "$(dirname "$BASH_SOURCE[0]}")" && pwd)"
CORPUS="$1"; MONOSAT="$2"; NIXIE="$3"; OUT="${4:-$HERE/ins_counts.csv}"; CPU="${5:-2}"

measure() { # binary, file -> instruction count on stdout
  local v i
  for i in $(seq 1 10); do
    v=$(taskset -c "$CPU" perf stat -x, -e instructions:u "$1" "$2" 2>&1 >/dev/null \
        | grep instructions | grep -oE "^[0-9]+" | head -1)
    [ -n "$v" ] && { echo "$v"; return 0; }
    sleep 0.3
  done
  echo "0"; return 1
}

echo "instance,mono_ins,nixie_ins,ratio" > "$OUT"
for f in "$CORPUS"/*.gnf; do
  name=$(basename "$f" .gnf)
  m=$(measure "$MONOSAT" "$f")
  n=$(measure "$NIXIE" "$f")
  if [ "$m" = "0" ] || [ "$n" = "0" ]; then
    echo "$name,0,0,na" >> "$OUT"; echo "MEASURE-FAIL $name" >&2; continue
  fi
  r=$(awk -v n="$n" -v m="$m" 'BEGIN { printf "%.3f", n/m }')
  echo "$name,$m,$n,$r" >> "$OUT"
done
awk -F, 'NR>1 && $2>0 && $3>0 { lm+=log($2); ln+=log($3); t2+=$2; t3+=$3; n++;
  if ($4+0>wo) {wo=$4+0; wname=$1} } END { printf "instances=%d geomean_gap=%.3fx totals_gap=%.3fx mono=%.2fG nixie=%.2fG worst=%s(%.2fx)\n",
  n, exp(ln/n)/exp(lm/n), t3/t2, t2/1e9, t3/1e9, wname, wo }' "$OUT"
