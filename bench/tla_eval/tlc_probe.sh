#!/usr/bin/env bash
# Run TLC on one probe, in a PRIVATE working directory.
#
# TLC writes its metadata (states/, .st files) into the working directory, so
# parallel runs sharing one directory clobber each other and most produce no
# output at all. This is the third time an oracle harness in this project has
# been wrong because parallel processes shared something; check isolation
# before believing a low hit rate. TLC also reserves a very large heap by
# default, so -Xmx is required or parallel runs are OOM-killed and silently
# produce nothing.
# before believing a low hit rate.
exp="$1"; probe="$(basename "$exp" .expected)"; src="$(dirname "$exp")"
lib="$(head -1 "$exp" | cut -f2)"
w="$(mktemp -d)"
cp "$src/$probe.tla" "$src/$probe.cfg" "$w/" 2>/dev/null
out="$(cd "$w" && timeout 90 java -Xmx512m -XX:TieredStopAtLevel=1 -Djava.io.tmpdir="$w" \
  -DTLA-Library="$lib:$COMMUNITY" -cp "$JAR" tlc2.TLC -config "$probe.cfg" \
  -cleanup -workers 1 "$probe" 2>&1)"
rm -rf "$w"
printf '%s\n' "$out" | grep -E '^<<"' > "$OUTDIR/$probe.out"
