#!/usr/bin/env bash
# QF_AUFLIA differential parity: oxiz vs z3 over the full local SMT-LIB corpus
# (1303 files: storecomm, swap, storeinv, cvc, check, 20170829-Rodin,
# array_benchmarks).  Usage:
#
#   ./scripts/run_auflia_parity.sh [timeout_sec] [oxiz_binary]
#
# `timeout_sec` applies to EACH solver run per file (default 10).  The oxiz
# binary defaults to the release build; point the second argument at any
# build (e.g. target/perf/oxiz) to compare profiles.  Writes per-file lines
# to /tmp/auflia_parity.txt and a summary to stdout:
#   "OK <verdict> <file>" / "MISMATCH z3=<v> oxiz=<v> <file>".
# A `timeout/err` value on either side is recorded verbatim; the summary
# counts both-side timeouts as agreements only when the verdicts agree.
set -u
TIMEOUT="${1:-10}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="${SCRIPT_DIR}/.."
BIN="${2:-${ROOT}/target/release/oxiz}"
CORPUS="${ROOT}/smt-lib/non-incremental/QF_AUFLIA"
OUT="/tmp/auflia_parity.txt"

if ! command -v z3 >/dev/null 2>&1; then
    echo "error: z3 not found on PATH" >&2
    exit 1
fi
if [ ! -x "${BIN}" ]; then
    echo "error: oxiz binary not found at ${BIN} (build it or pass a path)" >&2
    exit 1
fi

: > "$OUT"
files=$(find "$CORPUS" -name '*.smt2' | sort)
total=0; agree=0; mismatch=0; to=0; z3to=0
for f in $files; do
  total=$((total+1))
  z=$(timeout "$TIMEOUT" z3 "$f" 2>/dev/null); zrc=$?
  o=$(timeout "$TIMEOUT" "$BIN" -q "$f" 2>/dev/null); orrc=$?
  if [ "$zrc" != 0 ]; then z="timeout/err"; z3to=$((z3to+1)); fi
  if [ "$orrc" != 0 ]; then o="timeout/err"; to=$((to+1)); fi
  if [ "$z" = "$o" ]; then
    agree=$((agree+1))
    echo "OK    $z $f" >> "$OUT"
  else
    mismatch=$((mismatch+1))
    echo "MISMATCH z3=$z oxiz=$o $f" >> "$OUT"
  fi
done
echo "total=$total agree=$agree mismatch=$mismatch oxiz_timeout=$to z3_timeout=$z3to"
echo "per-file log: $OUT"
