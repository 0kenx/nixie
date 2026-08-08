#!/usr/bin/env bash
# bisect helper: exit 0 if vhard7 does NOT answer sat (good), 1 if it does (bad).
# Usage from repo root. Builds release oxiz-cli, runs vhard7.
set -e
export PATH=/nix/store/gr0i02za09y1hif1japlzg1qpd5xsg49-rust-default-1.97.1/bin:$PATH
VHARD=/media/data/proj/oxiz/smt-lib/non-incremental/QF_UFIDL/mathsat/EufLaArithmetic/vhard/vhard7.smt2
if [[ ! -f "$VHARD" ]]; then echo "SKIP: $VHARD not present (smt-lib corpus is gitignored; fetch it out of band)"; exit 125; fi
cargo build --release -p oxiz-cli >/tmp/bisect_build.log 2>&1 || { echo "SKIP: build failed"; tail -5 /tmp/bisect_build.log; exit 125; }
out=$(timeout 30 /media/data/proj/oxiz/target/release/oxiz -q "$VHARD" 2>/dev/null || true)
if echo "$out" | grep -q '^sat'; then
  echo "BAD: vhard7 -> sat"
  exit 1
else
  echo "GOOD: vhard7 -> $(echo "$out" | grep -iE '^(sat|unsat|unknown)' | head -1 || echo '(no verdict)')"
  exit 0
fi
