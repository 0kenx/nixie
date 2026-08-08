#!/usr/bin/env bash
# Release-mode blast-radius scan: how often does an inprocessing-enabled
# preset return a *different verdict* than the sound default on in-tree SAT
# instances?
#
# This is the user-facing failure mode: in release builds debug_assertions
# are off, so the propagation-fixpoint invariant that catches the corruption
# in debug is GONE, and the solver silently returns a wrong Sat/Unsat.
# Comparing the inprocessing preset's verdict against the default-preset
# (pure CDCL, sound) verdict catches those silent wrong answers directly.
#
# A row is a DIVERGENCE when the two verdicts disagree and neither is UNKNOWN
# (UNKNOWN = budget/timeout, not a wrong answer). Both must agree on a real
# verdict, or inproc must be wrong while base is right.
#
# Usage: scripts/inproc_blast_release.sh <cnf-file-list>
# Env:   MAXC (conflict budget), TIMEOUT (per solve seconds), BIN, PRESET_ON, PRESET_OFF
set -u
BIN="${BIN:-target/release/examples/cnf_solve}"
MAXC="${MAXC:-30000}"
TIMEOUT="${TIMEOUT:-60}"
PRESET_OFF="${PRESET_OFF:-default}"      # enable_inprocessing: false
PRESET_ON="${PRESET_ON:-industrial}"     # enable_inprocessing: true

if [[ ! -x "$BIN" ]]; then echo "missing $BIN" >&2; exit 2; fi

total=0; div=0; both_unknown=0; base_only_unknown=0
while read -r f; do
  [[ -z "$f" ]] && continue
  total=$((total+1))
  b=$(timeout "$TIMEOUT" env MAXC="$MAXC" PRESET="$PRESET_OFF" "$BIN" "$f" 2>/dev/null | grep -oE 'SATISFIABLE|UNSATISFIABLE|UNKNOWN'); brc=$?
  i=$(timeout "$TIMEOUT" env MAXC="$MAXC" PRESET="$PRESET_ON"  "$BIN" "$f" 2>/dev/null | grep -oE 'SATISFIABLE|UNSATISFIABLE|UNKNOWN'); irc=$?
  [[ -z "$b" ]] && b="UNKNOWN"; [[ -z "$i" ]] && i="UNKNOWN"
  if [[ "$b" == "UNKNOWN" && "$i" == "UNKNOWN" ]]; then both_unknown=$((both_unknown+1)); continue; fi
  if [[ "$b" == "UNKNOWN" ]]; then base_only_unknown=$((base_only_unknown+1));
    printf '  [base unknown, inproc=%s] %s\n' "$i" "$(basename "$f")"; continue; fi
  if [[ "$i" == "UNKNOWN" ]]; then continue; fi
  if [[ "$b" != "$i" ]]; then
    div=$((div+1))
    printf 'DIVERGE base=%s inproc=%s  %s\n' "$b" "$i" "$(basename "$f")"
  fi
done
echo "----"
echo "scanned=$total divergent=$div both_unknown=$both_unknown base_only_unknown=$base_only_unknown"
