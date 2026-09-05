#!/usr/bin/env bash
# Smoke sweep for the obligation fuzzer. Run from bench/obligation inside
# the nixie checkout (worktree).
set -euo pipefail
cd "$(dirname "$0")"

REPO_ROOT="$(cd ../.. && pwd)"
NIXIE="${NIXIE_BIN:-$REPO_ROOT/target/release/nixie}"
Z3="${Z3_BIN:-z3}"
CADICAL="${CADICAL_BIN:-$REPO_ROOT/../temp/cadical/build/cadical}"
[ -x "$CADICAL" ] || CADICAL=""

CAD_ARGS=()
if [ -n "$CADICAL" ]; then
    CAD_ARGS=(--cadical "$CADICAL")
fi

echo "== building generator/runner =="
cargo build --release --quiet

echo "== plain sweep (3 seeds, medium) =="
./target/release/obligation-run \
    --seeds 3 --size medium \
    --nixie "$NIXIE" --z3 "$Z3" \
    "${CAD_ARGS[@]}" \
    --timeout-ms 20000 --artifacts ./obligation-artifacts

echo "== stressed sweep (2 seeds, small, heavy) =="
./target/release/obligation-run \
    --seeds 2 --size small --stress heavy \
    --nixie "$NIXIE" --z3 "$Z3" \
    --timeout-ms 20000 --artifacts ./obligation-artifacts

echo "== smoke done =="
