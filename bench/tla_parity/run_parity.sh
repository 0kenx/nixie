#!/usr/bin/env bash
# TLA+ front-end parity against SANY.
#
# SANY is a TEST ORACLE here, exactly as Z3 is for bench/z3_parity: it is
# consulted to check the pure-Rust front end, never linked. Nothing Nixie
# ships depends on a JVM. See METHODOLOGY.md.
#
# Two comparisons:
#   1. SYNTAX -- every file SANY parses must parse here. The gate is one-sided:
#      accepting more is allowed, because the long-term target is a superset,
#      provided the extra parse is unambiguous. Extras are listed for review.
#   2. LEVELS -- for files SANY fully resolves, every definition whose level
#      nixie actually established must match SANY's.
#
# Usage: bench/tla_parity/run_parity.sh [corpus-dir ...]
set -u

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
work="${TLA_PARITY_WORK:-$(mktemp -d)}"
mkdir -p "$work/parts"

JAR="${TLA2TOOLS_JAR:-$(ls /nix/store/*/share/java/tla2tools.jar 2>/dev/null | head -1)}"
if [ -z "${JAR:-}" ] || [ ! -f "$JAR" ]; then
  echo "tla2tools.jar not found; set TLA2TOOLS_JAR." >&2
  exit 2
fi
echo "oracle:  $JAR"
java -version 2>&1 | head -1
# Community modules widen the set of specs SANY can fully resolve, which is
# what makes the level comparison cover most of the corpus rather than a third.
TLALIB="${TLA_LIBRARY:-$repo/../temp/communitymodules/modules}"
echo "library: $TLALIB"

corpora=("$@")
if [ ${#corpora[@]} -eq 0 ]; then
  corpora=("$repo/../temp/tlaplus-examples" "$repo/../temp/apalache")
fi

: > "$work/files.txt"
for c in "${corpora[@]}"; do
  [ -d "$c" ] && find "$c" -name '*.tla' >> "$work/files.txt"
done
sort -u -o "$work/files.txt" "$work/files.txt"
n=$(wc -l < "$work/files.txt")
if [ "$n" -eq 0 ]; then
  echo "no .tla files found in: ${corpora[*]}" >&2
  exit 2
fi
echo "corpus:  $n files"

javac -cp "$JAR" -d "$work" "$here/LevelDump.java" || exit 2
cargo build --release -p nixie-tla-syntax --example tlaparity || exit 2

cat > "$work/one.sh" <<'INNER'
#!/usr/bin/env bash
# One file per invocation, into its OWN output file.
#
# Two isolation requirements, both learned the hard way:
#  * a private java.io.tmpdir -- SANY extracts the standard modules into the
#    JVM temp directory, and parallel runs sharing /tmp corrupt each other,
#    producing spurious parse failures;
#  * a private output file -- SANY's per-file output is many lines, and
#    parallel processes writing one pipe interleave them, pairing a #FILE
#    header with another process's definitions. That manufactured ~120 phantom
#    level mismatches the first time this suite was run.
f="$(realpath "$1")"; d="$(dirname "$f")"
t="$(mktemp -d)"
o="$OUTDIR/$(echo "$f" | md5sum | cut -d' ' -f1).txt"
(cd "$d" && timeout 90 java -XX:TieredStopAtLevel=1 -Djava.io.tmpdir="$t" \
   -DTLA-Library="$TLALIB" -cp "$JAR:$WORK" LevelDump "$f" 2>/dev/null) > "$o"
rm -rf "$t"
INNER
chmod +x "$work/one.sh"

export JAR TLALIB WORK="$work" OUTDIR="$work/parts"
xargs -a "$work/files.txt" -P "${TLA_PARITY_JOBS:-10}" -I{} "$work/one.sh" {}
cat "$work"/parts/*.txt > "$work/sany.txt"

"$repo/target/release/examples/tlaparity" "$work/files.txt" "$work/sany.txt"
rc=$?
echo
echo "artifacts: $work"
exit $rc
