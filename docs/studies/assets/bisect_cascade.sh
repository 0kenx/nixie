#!/usr/bin/env bash
# Bisect z3's pre-blast cascade: which stage(s) make the file tractable for nixie?
# Usage: bisect_cascade.sh <original.smt2> <nixie-binary> <cap>
set -u
ORIG=$1; NIXIE=$2; CAP=${3:-60}
D=$(mktemp -d)
prefixes=(
  "(then simplify)"
  "(then simplify propagate-values)"
  "(then simplify propagate-values solve-eqs)"
  "(then simplify propagate-values solve-eqs elim-uncnstr)"
  "(then simplify propagate-values solve-eqs elim-uncnstr reduce-bv-size simplify)"
  "(then simplify propagate-values solve-eqs elim-uncnstr reduce-bv-size simplify max-bv-sharing)"
)
for T in "${prefixes[@]}"; do
  sed "s|(check-sat)|(apply $T :print true)|; s|(exit)||" "$ORIG" > "$D/p.smt2"
  if ! z3 "$D/p.smt2" > "$D/c.txt" 2>&1; then echo "[$T] z3 apply FAILED"; continue; fi
  if grep -q '^({' "$D/c.txt" 2>/dev/null; then :; fi
  # closed goal? (goal false) / (goal true)
  if grep -qE '\(goal (true|false)\b' "$D/c.txt"; then
    G=$(grep -oE '\(goal (true|false)' "$D/c.txt" | head -1)
    # a closed goal means the cascade decided it; reconstruct trivially
    if echo "$G" | grep -q false; then echo "[$T] CLOSED-unsat"; else echo "[$T] CLOSED-sat"; fi
    continue
  fi
  if ! python3 /tmp/perf-cjpeg/goal2smt.py "$D/c.txt" "$D/r.smt2" "$ORIG" >/dev/null 2>&1; then echo "[$T] goal2smt FAILED"; continue; fi
  ZV=$(timeout "$CAP" z3 "$D/r.smt2" 2>/dev/null | tail -1)
  NV=$( timeout "$CAP" taskset -c 10 "$NIXIE" -t "$CAP" "$D/r.smt2" 2>/dev/null | tail -1)
  SZ=$(wc -c < "$D/r.smt2")
  echo "[$T] size=$SZ z3=$ZV nixie=$NV"
done
rm -rf "$D"
