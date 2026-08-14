#!/usr/bin/env bash
# Blast-radius scan: does an inprocessing-enabled preset diverge from the
# safe default on in-tree SAT instances?
#
# Method: debug build (debug_assertions ON), so the propagation-fixpoint
# invariant ("hanging unit") is the oracle. A wrong-Sat unsoundness fires
# that invariant as a panic (exit 101) rather than silently returning the
# wrong verdict – which is exactly what we want to catch.
#
# For each .cnf we run cnf_solve twice under a conflict budget:
#   baseline : PRESET=default   (enable_inprocessing: false)
#   inproc   : PRESET=industrial (enable_inprocessing: true)
# and record the verdict line + exit code for each. A row is a DIVERGENCE
# if inproc panics (exit 101) while baseline is clean, or the verdicts
# disagree (excluding Unknown, which is just the budget running out).
#
# Usage: scripts/inproc_blast.sh <cnf-file-list>
set -u
BIN="${BIN:-target/debug/examples/cnf_solve}"
MAXC="${MAXC:-2000}"   # conflict budget; bump for harder instance sets

if [[ ! -x "$BIN" ]]; then
  echo "cnf_solve example not built at $BIN" >&2
  exit 2
fi

total=0
div=0
panic=0
while read -r f; do
  [[ -z "$f" ]] && continue
  total=$((total+1))
  base_out=$(MAXC="$MAXC" PRESET=default    "$BIN" "$f" 2>/dev/null); base_rc=$?
  inp_out=$(MAXC="$MAXC" PRESET=industrial  "$BIN" "$f" 2>/dev/null); inp_rc=$?
  # Normalize Unknown (budget) to a sentinel we don't count as divergence
  b=$(echo "$base_out" | grep -oE 'SATISFIABLE|UNSATISFIABLE|UNKNOWN')
  i=$(echo "$inp_out"  | grep -oE 'SATISFIABLE|UNSATISFIABLE|UNKNOWN')
  flag=""
  if [[ $inp_rc -eq 101 ]]; then flag="INPROC_PANIC"; panic=$((panic+1)); fi
  if [[ $base_rc -ne 0 && $base_rc -ne 101 ]]; then flag="${flag} BASE_RC=$base_rc"; fi
  if [[ "$b" != "$i" && "$i" != "UNKNOWN" && "$b" != "UNKNOWN" ]]; then flag="${flag} VERDICT($b!=$i)"; fi
  if [[ -n "$flag" ]]; then
    div=$((div+1))
    printf 'DIVERGE %-14s base=%s(rc=%s) inproc=%s(rc=%s)  [%s]  %s\n' \
      "$flag" "$b" "$base_rc" "$i" "$inp_rc" "$(basename "$f")" "$f"
  fi
done

echo "----"
echo "scanned=$total divergent=$div inproc_panics=$panic"
