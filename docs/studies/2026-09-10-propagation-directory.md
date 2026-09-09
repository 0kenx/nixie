# One owning propagation directory per literal

## Registration

Continue the Kissat wall-cost task after the
[raw-header rejection](2026-09-10-raw-header-pipeline.md). The next target
removes separate metadata directories instead of adding lookahead state.
This is a representation change with exact search-state equivalence, not
a heuristic comparison. Local Kissat `src/proplit.h` combines binary and
long entries in one stream; Nixie must retain its binary-before-long order,
stable long-watch filtering, eager pair normalization and immediate moves.

Put one literal's long-watch Vec, binary overflow Vec, primary start/live
length and phantom tick count in one owned, cache-line-aligned 64-byte row
on this host. Keep the binary primary edge pool contiguous and retain the
existing Vec allocation/growth rules. `WatchLists` owns the rows and primary
pool; crate-private binary methods replace the separate solver graph field.
Public watch APIs remain available. No shared pointer, global state, custom
Send/Sync assertion or new unsafe block is needed for this first version.

Retain separate logical watch, binary and phantom extents. Watch rollback
must restore only watchers/phantoms and preserve binary edges; binary
clear/rebuild/compaction must preserve watchers/phantoms. A full solver
rebuild must discard old watch buffers but retain reusable binary storage.
Explicit primary starts must preserve physical slack after individual
retirement, and count/extent/fill overflow must fail before corrupting any
neighbor. Directory growth, clone, scope transitions, HBR, observer fields,
LRAT and exact tick charges must retain their original semantics.

Before measurement: default and all-feature SAT tests, strict SAT Clippy,
format, independent Vec-model directory tests, channel-isolation tests,
packed rollback/growth/compaction tests and native Rayon owner-move tests.
Inspect generated code for a single directory base, direct row addressing
and ordinary inlined destination append. Record scanner/driver code size
and stack use. Repair correctness or a missed intended code transformation
before timing; do not benchmark a known-broken representation.

Use ordinary portable release/perf, the retained lockfile and Rust 1.96.0 /
LLVM 22.1.2. Main's SAT source still matches qualified fd01d0b; later changes
are outside the DIMACS solving path. Reuse its j3037 cost record
`0ec1f4bfcfe8f5f9` and Kissat 4.0.4 record `45a3c8f2e3057841`. Use the same
once-only harness/configuration as those records: CPU 15, seed 0, CaDiCaL
preset, disabled sweep/definitions, MAXC=10000000, printed models, warmed
binary/input, anonymous tmpfs output and whole-process user instructions /
cycles. Clear unrelated overrides. No own build overlaps measurement.
Require byte-identical complete Nixie stdout, >=99.9% PMU coverage and
<=5% off-CPU for usable wall. Quality failure is inconclusive and retained,
not permission to retry. Record exact source/binary identities in benchstore.

Start with **one candidate j3037 cost cell**. Advance to one paired si2
confirmation only with >=5% fewer complete instructions and no usable wall
regression, or >=10% lower usable wall and cycles with at most 1% extra
instructions. Independently check si2's SAT model; require identical Nixie
output, no more than 3% si2 instruction/wall regression, and >=5% two-input
wall improvement. These are bounded engineering screens, not population
estimates or a new Kissat-suite geomean. Unchecked UNSAT stays unverified in
the store. Full workspace build/nextest/doc-test/Clippy/fmt/docs and fresh
installed-Z3 4.16.0 parity are required before production landing.

A failed cost screen gets one LBR diagnostic with the retained quality
checks. Allow at most one cost-directed measured repair if code and profile
identify removable introduced overhead; record its design before timing.
No layout/width/seed sweep or timing retry. Include growth/rebuild/rollback,
larger destination-directory stride and memory overhead in the diagnosis.
A rejected mechanism is archived with its source and finding on main;
do not infer a win by adding older compact-buffer/lookahead percentages.
