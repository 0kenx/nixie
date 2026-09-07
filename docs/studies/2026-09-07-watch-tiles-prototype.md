# Order-preserving shared-blocker tiles: registered prototype

The [shared-blocker feasibility screen](2026-09-07-nixie-propagation-redesign.md)
passed on break and circuit. This step tests a real propagation kernel,
including its maintenance cost, behind an explicit `bcp-tiles` build feature.
Ordinary builds exclude the representation. This is a reduced falsification
screen requested by the user, not a multi-seed claim of improvement.

## Fixed representation and correctness conditions

Build tiles of at most 64 consecutive watchers; group a blocker only when it
has at least four members. Keep appended entries in a scalar tail until at
least 16 entries can form another tile. Tiles can shrink after removals and
retain their boundaries instead of repacking the entire list every visit.

Each group has a blocking literal and a membership mask. At tile entry, a
currently true blocker certifies skipping its members. A false/unassigned
check authorizes no skip: subsequent individual visits still check truth.
Process remaining entries in their original order and preserve satisfied
spans during compaction. A conflict stops at exactly the same watcher and
preserves the unvisited tail. Neither cached truth nor a work mask survives
a propagation pass or backtrack.

Clear changed blockers from cached groups; delete removed mask positions in
descending order to follow stable compaction. Rebuild a tile after 64
accumulated removals/blocker changes, or when it has fewer than 16 survivors;
the latter exposes the suffix beginning at that tile for rebuilding in
logical order, charging every suffix entry scanned.
Generic mutable access, explicit removal, clear and snapshot restoration
invalidate affected caches. Appending preserves existing prefix groups.
Arena relocation changes references only and preserves blocker membership.

Keep logical watch lengths, phantom binary counts and scheduling ticks
unchanged. Skipping must preserve assignments, reasons, clause order, proof
output and conflict prefixes. Instrumentation separately counts group checks,
skipped entries/copies, mask maintenance and rebuilding. Full-process retired
instructions include all representation costs, including allocation and
external cache invalidation; internal counters are explanatory diagnostics.

## Registered comparison

Start from `284d180`. Use the same portable release profile, CPU 2, CaDiCaL
preset, seed 1 and ten-million-conflict cap as the cached eager-final controls
for `break_unsat_06_07` and `circuit_48in64out`. Reuse records
`50fa8316e92aed2a` and `a6b0151744a458c1` and their checked stdout. No new
Kissat/CaDiCaL comparison or baseline sweep.

Four new measurement cells initially: two optimized prototype runs with
`instructions:u,cycles:u,branches:u,branch-misses:u`, plus two diagnostic
build runs on those same inputs. The diagnostic build reports maintenance
counts and is not a throughput arm. Record every cell once in benchstore;
byte-compare complete stdout and independently check the SAT model. Reject
invalid/unsupported/multiplexed PMU counts rather than silently using time.

Stop this design if the geometric mean instruction ratio is above 0.95,
either input regresses by more than 5% in instructions, or trajectory identity
fails. Report cycles/conflict alongside instructions/conflict, total cost,
conflicts and completion. The reduced panel can reject a design or justify
further testing; it cannot establish benchmark-wide improvement. If the
screen passes, allow only a fresh-seed capped noL holdout pair next (seed 2,
100,000 conflicts), reusing any exact existing control cell. No parameter
retuning after seeing results. A changed trajectory requires a separately
registered heuristic study with a matched null.

Before landing solver changes, run workspace build, nextest, doctests,
clippy, fmt and strict docs; fresh Z3 parity using available Z3 4.16.0; and
additional parity with the tiled kernel enabled. Tests must cover sparse mask
compaction, tile boundaries, blocker changes, moves, appends, restoration,
mid-pass truth changes, conflicts and SAT/UNSAT trajectory/proof identity.

## Implementation and verification

The `bcp-tiles` feature now runs the tiled kernel; `bcp-tiles-stats` adds
explanatory counters. Both are outside the default feature set. The
`stats_solve` example accepts `NIXIE_WATCH_TILES=0|1` in a tiled build and
writes `nixie-watch-tiles/1` JSON on stderr in a statistics build. A depleted
tile exposes the suffix beginning at that tile for rebuilding, with every
scanned suffix entry included in the build counter.

Eight new tests cover exhaustive small-mask compaction (including high-bit
positions), mid-pass truth transitions, tile boundaries, mask repair,
appending, external invalidation, snapshot restoration and scope changes.
Two tests force real skips: one compares compaction, trail and conflict-tail
state; another compares exact LRAT transcripts after grouped propagation.

All required gates passed in the isolated worktree: all-features build,
10,645 nextest tests (12 skipped), doctests, strict clippy, fmt and strict
docs. The 100,000-case tiled SAT differential found zero mismatches and zero
invalid models. Z3 4.16.0 parity gave 169 agreements, zero disagreements and
one unresolved case in each of the ordinary and tiled builds. The standalone
parity harness exposes a `bcp-tiles` feature so its library runner, not merely
an unrelated CLI binary, exercises the experimental kernel.

The reproducible four-cell runner is `bench/suite/scripts/watch_tile_bench.py`.
Pass `--optimized`, `--diagnostic`, `--sha`, and optionally `--root` for the
primary checkout containing shared corpora and precompiled controls. It
stores complete manifests, raw outputs, PMU reports and canonical records;
existing cells are reused. Hardware counts cover the complete process.
Internal counters describe BCP maintenance and explain cost; they do not
claim to count allocator internals or replace the hardware measurement.
