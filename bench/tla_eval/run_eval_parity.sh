#!/usr/bin/env bash
# Semantic parity: evaluate lowered KerA terms and compare against TLC.
#
# Everything else in this front end is checked *structurally* — SANY parity,
# level parity, lowering coverage. None of that can tell a correct lowering
# from a well-formed wrong one; the INSTANCE visibility bug produced a
# perfectly valid kernel term that read the wrong module's variables and
# passed every structural check. This suite is the check that catches that
# class.
#
# How it works:
#   1. For every module with no declared constants or variables, lower each
#      nullary definition and evaluate it to a value.
#   2. Emit a probe module that EXTENDS the *original* module and `PrintT`s
#      those same definitions. TLC therefore evaluates the SOURCE, not a
#      re-printed kernel term — which is what makes this a test of lowering
#      rather than only of the evaluator.
#   3. Compare the two sets of values structurally.
#
# TLC is an oracle, never a dependency. Nothing Nixie ships needs a JVM.
set -u

# `--help` must not become a corpus path (it once did: "corpus: 0 files"
# that looked like a missing corpus and cost a session a wrong conclusion).
if [ "${1:-}" = "--help" ] || [ "${1:-}" = "-h" ]; then
  echo "usage: $0 [corpus-dir ...]   (default: tlaplus-examples + apalache)"
  exit 0
fi

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
work="${TLA_EVAL_WORK:-$(mktemp -d)}"
mkdir -p "$work/probes" "$work/out"

JAR="${TLA2TOOLS_JAR:-$(ls /nix/store/*/share/java/tla2tools.jar 2>/dev/null | head -1)}"
if [ -z "${JAR:-}" ] || [ ! -f "$JAR" ]; then
  echo "tla2tools.jar not found; set TLA2TOOLS_JAR." >&2; exit 2
fi
# Several corpus modules extend `Apalache`, whose .tla ships inside the
# Apalache checkout rather than with the community modules. Without it on the
# path TLC cannot parse them at all, and the probe silently yields nothing.
COMMUNITY="${TLA_LIBRARY:-$repo/../temp/communitymodules/modules:$repo/../temp/apalache/src/tla}"

corpora=("$@")
if [ ${#corpora[@]} -eq 0 ]; then
  corpora=("$repo/../temp/tlaplus-examples" "$repo/../temp/apalache")
fi
: > "$work/files.txt"
for c in "${corpora[@]}"; do
  [ -d "$c" ] && find "$c" -name '*.tla' >> "$work/files.txt"
done
sort -u -o "$work/files.txt" "$work/files.txt"
echo "corpus: $(wc -l < "$work/files.txt") files"

# Honor CARGO_TARGET_DIR: the shared target/ on a full disk cannot host a
# link step (SIGBUS), and a relocated build must be the binary that runs —
# the hardcoded target/ path would silently pick a stale one.
TARGET_DIR="${CARGO_TARGET_DIR:-$repo/target}"
cargo build --release -p nixie-tla --example evalcov || exit 2
NIXIE_TLA_LIB="$COMMUNITY" xargs -a "$work/files.txt" \
  "$TARGET_DIR/release/examples/evalcov" --probe-dir "$work/probes"

ls "$work"/probes/*.expected > "$work/probelist.txt" 2>/dev/null || {
  echo "no probes generated" >&2; exit 2; }
export JAR COMMUNITY OUTDIR="$work/out"
# -P 4 and a bounded heap: TLC reserves a very large heap by default, and
# parallel runs get OOM-killed, silently producing nothing at all.
xargs -a "$work/probelist.txt" -P "${TLA_EVAL_JOBS:-4}" -I{} \
  env JAR="$JAR" COMMUNITY="$COMMUNITY" OUTDIR="$OUTDIR" "$here/tlc_probe.sh" {}

python3 "$here/compare.py" "$work"
rc=$?
echo
echo "artifacts: $work"
exit $rc
