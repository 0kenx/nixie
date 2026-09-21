#!/usr/bin/env bash
# PlusCal translation parity: our translator against pcal.trans (tla2tools).
#
# Four comparisons, in increasing strength:
#
#   1. TRANSLATE — every corpus file whose algorithm our translator accepts
#      is translated; the oracle (pcal.trans 1.7.4) must accept the same set.
#   2. PARSE+LEVELS — every translated module parses and level-checks in the
#      pure-Rust front end, and SANY resolves it with matching definition
#      levels (the same one-sided gate bench/tla_parity runs over plain
#      modules, applied to what we generate).
#   3. DEFINITIONS — the definitions our translation declares are the
#      definitions the oracle's declares, with the same levels: a missing
#      action or an undeclared variable is a failure, not a curiosity. (This
#      gate caught a real bug during development: process-local variables
#      were not declared when the algorithm had no `define` block.)
#   4. STATES — TLC explores models of the golden and of ours, printing
#      every initial state and successor pair; BOTH translations' Init and
#      Next must hold on BOTH dumps. This is the gate that catches a wrong
#      translation rather than a malformed one: label placement, UNCHANGED
#      bookkeeping, self-subscripts and pc updates all have to be right.
#
# pcal.trans is an ORACLE, never a dependency: nothing Nixie ships runs a
# JVM. See METHODOLOGY.md.
#
# Usage: bench/tla_pcal/run_parity.sh [corpus-dir ...]
set -u

if [ "${1:-}" = "--help" ] || [ "${1:-}" = "-h" ]; then
  echo "usage: $0 [corpus-dir ...]   (default: ../temp/tlaplus-examples)"
  exit 0
fi

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
work="${TLA_PCAL_WORK:-$(mktemp -d)}"
mkdir -p "$work"

JAR="${TLA2TOOLS_JAR:-$(ls /nix/store/*/share/java/tla2tools.jar 2>/dev/null | head -1)}"
if [ -z "${JAR:-}" ] || [ ! -f "$JAR" ]; then
  echo "tla2tools.jar not found; set TLA2TOOLS_JAR." >&2
  exit 2
fi
TLALIB="${TLA_LIBRARY:-$repo/../temp/communitymodules/modules}"
echo "oracle:   $JAR ($(java -version 2>&1 | head -1))"
echo "library:  $TLALIB"

# The shared target/ cannot host a link step when its disk is full; a
# relocated build must also be the binary that runs.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$HOME/.cache/nixie-tla-target}"
cargo build --release -p nixie-tla-syntax --example pcaltrans --example pcalcheck || exit 2
cargo build --release -p nixie-tla-syntax --example tlaparity || exit 2
PCALTRANS="$CARGO_TARGET_DIR/release/examples/pcaltrans"
PCALCHECK="$CARGO_TARGET_DIR/release/examples/pcalcheck"
TLAPARITY="$CARGO_TARGET_DIR/release/examples/tlaparity"

corpora=("$@")
if [ ${#corpora[@]} -eq 0 ]; then
  corpora=("$repo/../temp/tlaplus-examples")
fi
root="$(cd "${corpora[0]}" && pwd)"

# ---- stage: translate everything our translator can -------------------------
: > "$work/ours.txt"
: > "$work/declined.txt"
find "$root" -name '*.tla' ! -path '*.toolbox*' | sort > "$work/files.txt"
while read -r f; do
  rel="${f#"$root"/}"
  stage="$work/ours/$rel"
  mkdir -p "$(dirname "$stage")"
  cp "$f" "$(dirname "$stage")/"
  if "$PCALTRANS" -nocfg -o "$stage" "$f" >/dev/null 2>"$work/one.err"; then
    echo "$rel" >> "$work/ours.txt"
  elif grep -q "no --algorithm or --fair marker" "$work/one.err"; then
    : # not a PlusCal file; the corpus is mostly these
  else
    echo "$rel: $(head -1 "$work/one.err")" >> "$work/declined.txt"
  fi
done < "$work/files.txt"
n_ours=$(wc -l < "$work/ours.txt")
echo "translated by ours:  $n_ours"
[ -s "$work/declined.txt" ] && { echo "declined by ours:"; sed 's/^/  /' "$work/declined.txt"; }

# ---- 1. translation coverage parity ------------------------------------------
# The oracle translates the same files (it rewrites in place: work on copies).
: > "$work/oracle-failed.txt"
while read -r rel; do
  stage="$work/golden/$rel"
  mkdir -p "$(dirname "$stage")"
  w="$(mktemp -d)"
  cp "$root/$rel" "$w/"
  (cd "$w" && timeout 60 java -XX:TieredStopAtLevel=1 -cp "$JAR" pcal.trans -nocfg \
     "$(basename "$rel" .tla).tla" >/dev/null 2>&1)
  if [ -f "$w/$(basename "$rel")" ]; then
    cp "$w/$(basename "$rel")" "$stage"
  else
    echo "$rel" >> "$work/oracle-failed.txt"
  fi
  rm -rf "$w"
done < "$work/ours.txt"
if [ -s "$work/oracle-failed.txt" ]; then
  echo "ORACLE DECLINED files ours accepted:"; sed 's/^/  /' "$work/oracle-failed.txt"
  exit 1
fi

# ---- 2. parse + levels, ours (nixie) and SANY --------------------------------
mapfile -t ourfiles < <(sed "s|^|$work/ours/|" "$work/ours.txt")
"$TLAPARITY" "${ourfiles[@]}" /dev/null > "$work/parity.log" 2>&1
rc=$?
tail -3 "$work/parity.log"
[ $rc -eq 0 ] || { echo "parse/level parity FAILED; see $work/parity.log"; exit 1; }

javac -cp "$JAR" -d "$work" "$repo/bench/tla_parity/LevelDump.java" || exit 2
sany_bad=0
while read -r rel; do
  f="$work/ours/$rel"
  d="$(dirname "$f")"
  t="$(mktemp -d)"
  (cd "$d" && timeout 90 java -XX:TieredStopAtLevel=1 -Djava.io.tmpdir="$t" \
     -DTLA-Library="$TLALIB" -cp "$JAR:$work" LevelDump "$f" >/dev/null 2>&1) \
     || sany_bad=$((sany_bad+1))
  rm -rf "$t"
done < "$work/ours.txt"
echo "SANY accepts our translations: $((n_ours - sany_bad))/$n_ours"
[ "$sany_bad" -eq 0 ] || exit 1

# ---- 3. definition parity ours vs golden (names + levels) ---------------------
name_bad=0
while read -r rel; do
  d="$(dirname "$work/ours/$rel")"
  # Both sides see the same EXTENDS siblings: the staged directory plus the
  # spec's original directory (where modules like ClientCentric.tla live).
  orig="$(dirname "$root/$rel")"
  if ! NIXIE_TLA_LIB="$TLALIB:$d:$orig" "$PCALCHECK" \
       "$work/ours/$rel" "$work/golden/$rel" > "$work/one.log" 2>&1; then
    name_bad=$((name_bad+1))
    echo "DEFINITION DIFF $rel:"
    sed 's/^/  /' "$work/one.log" | head -8
  fi
done < "$work/ours.txt"
echo "definition parity (names+levels): $((n_ours - name_bad))/$n_ours"
[ "$name_bad" -eq 0 ] || exit 1

# ---- 4. state parity, on the models TLC can explore --------------------------
cargo build --release -p nixie-tla --example pcalsem || exit 2
PCALSEM="$CARGO_TARGET_DIR/release/examples/pcalsem"
model_bad=0
model_n=0
while IFS=$'\t' read -r spec model; do
  case "$spec" in \#*|"") continue ;; esac
  grep -qx "*/$spec" "$work/ours.txt" || grep -qx "$spec" "$work/ours.txt" || continue
  model_n=$((model_n+1))
  mod="$(basename "$spec" .tla)"
  cfg="$here/models/$model"
  for side in ours golden; do
    f="$work/$side/$spec"
    d="$work/probe-$side-$(echo "$spec" | tr '/' '_')"
    rm -rf "$d"; mkdir -p "$d"
    # The spec's directory: every sibling .tla, with our (or the golden)
    # translation in place of the original.
    find "$(dirname "$root/$spec")" -maxdepth 1 -name '*.tla' -exec cp {} "$d/" \;
    cp "$f" "$d/$(basename "$spec")"
    cat > "$d/NixieProbe.tla" <<EOF
---- MODULE NixieProbe ----
EXTENDS $mod, TLC

NixieInit == Init /\\ PrintT(<<vars>>)
NixieNext == Next /\\ PrintT(<<vars, vars'>>)

====
EOF
    { echo "INIT NixieInit"; echo "NEXT NixieNext"; cat "$cfg"; } > "$d/NixieProbe.cfg"
    t="$(mktemp -d)"
    # PrintT writes multi-line values; an entry is complete when its
    # brackets balance (counted outside string literals).
    (cd "$d" && timeout "${TLA_PCAL_TLC_SECONDS:-120}" java -Xmx512m -XX:TieredStopAtLevel=1 \
       -Djava.io.tmpdir="$t" -DTLA-Library="$TLALIB" -cp "$JAR" tlc2.TLC \
       -config NixieProbe.cfg -cleanup -workers 1 NixieProbe 2>"$d/tlc.err") \
       | awk '
         function nos(s) { gsub(/"[^"\\]*"/, "S", s); return s }
         function balanced() {
           n = nos(buf); o = gsub(/<</, "", n); c = gsub(/>>/, "", n)
           return (o == c && o > 0)
         }
         # An entry opens at a line beginning with `<<` and keeps absorbing
         # every line until its brackets balance outside strings.
         buf != ""            { buf = buf $0 "\n"; if (balanced()) { printf "%s", buf; buf = "" }; next }
         /^[[:space:]]*<</    { buf = $0 "\n";    if (balanced()) { printf "%s", buf; buf = "" } }
       ' > "$d/pairs.txt"
    rm -rf "$t"
    if [ ! -s "$d/pairs.txt" ]; then
      echo "MODEL $spec ($side): TLC produced no pairs"
      model_bad=$((model_bad+1))
      continue
    fi
    if ! "$PCALSEM" --cfg "$d/NixieProbe.cfg" --pairs "$d/pairs.txt" \
        --mine "$work/ours/$spec" --golden "$work/golden/$spec" > "$d/sem.log" 2>&1; then
      echo "MODEL $spec ($side): semantic mismatch"
      sed 's/^/  /' "$d/sem.log" | head -12
      model_bad=$((model_bad+1))
    else
      echo "MODEL $spec ($side): $(tail -1 "$d/sem.log")"
    fi
  done
done < "$here/models.txt"
echo "state parity: $((model_n - model_bad))/$model_n models agreed"
[ "$model_bad" -eq 0 ] || exit 1

echo
echo "ALL PLUSCAL PARITY GATES GREEN ($n_ours files translated)"
echo "artifacts: $work"
