# Order-preserving shared-blocker tiles: rejected cost screen

**Verdict: reject this representation.** Four registered cells found 1.818×
retired instructions and 1.744× cycles/conflict (geometric means across two
inputs), despite real watcher skips and identical printed search diagnostics.
The experimental kernel, features and runner have been removed from active
code. Their source remains in `38a4b1c`; the integrated measured revision is
`0a22e8d`. The original registration below is retained for comparison.

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

In the archived implementation, `bcp-tiles` runs the tiled kernel; `bcp-tiles-stats` adds
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

The archived four-cell runner is `bench/suite/scripts/watch_tile_bench.py`
at `0a22e8d`.
Pass `--optimized`, `--diagnostic`, `--sha`, and optionally `--root` for the
primary checkout containing shared corpora and precompiled controls. It
stores complete manifests, raw outputs, PMU reports and canonical records;
existing cells are reused. Hardware counts cover the complete process.
Internal counters describe BCP maintenance and explain cost; they do not
claim to count allocator internals or replace the hardware measurement.

## Registered result: maintenance outweighs skipped work

Exactly four new measurement cells completed: optimized and diagnostic builds
on each registered input. Both cached controls were reused. CPU 2's active
core PMU counters ran at 100%, without multiplexing; inactive atom-PMU rows
were not used. The primary instruction counts cover the complete optimized
process, including allocation and maintenance. Diagnostic-build timings are
not compared. No holdout, parameter tuning or additional performance run was
performed after the rejection.

| Input | Conflicts, both arms | Instructions control → tiles | Instructions ratio | Cycles/conflict control → tiles | Cycles ratio | Skipped logical visits |
|---|---:|---:|---:|---:|---:|---:|
| break_unsat_06_07 | 33,293 | 7,838,504,079 → 14,217,027,664 | **1.814×** | 128,845 → 235,782 | **1.830×** | 25.64% |
| circuit_48in64out | 186,114 | 70,653,168,340 → 128,777,093,550 | **1.823×** | 245,459 → 408,198 | **1.663×** | 17.57% |

Instruction and cycle ratios equal their respective per-conflict ratios
because conflicts are unchanged. Instructions/conflict were 235,440 →
427,028 for break and 379,623 → 691,926 for circuit. Total cycles were 4,289,642,501 →
7,849,890,503 for break and 45,683,371,337 → 75,971,295,776 for circuit.
Both arms reported completion on both inputs within the ten-million-conflict
cap. All four complete stdout reports match their controls byte for byte,
including printed search counters and the circuit model. That model was also
checked against every original clause. Break's reported UNSAT has no newly
checked proof here; its canonical verdict remains unverified/unknown.

The instruction geometric mean is **1.8181985**, failing the registered
≤0.95 bar; both inputs also fail the individual ≤1.05 regression limit.
The cycle geometric mean is **1.7444838**. These two inputs at one seed
reject this implementation under the registered screen. They do not estimate
a population effect, supply a confidence interval, or establish the size of
the remaining Kissat gap on a broader panel.

### What the maintenance counters explain

| Diagnostic | break | circuit |
|---|---:|---:|
| Logical watcher visits | 91,073,652 | 784,425,857 |
| Skipped watcher entries | 23,352,492 | 137,805,822 |
| Mean entries per skipped span | 3.49 | 2.59 |
| Group checks / logical visit | 0.0381 | 0.0384 |
| Rebuild entries / logical visit | 0.2813 | 0.2670 |
| Rebuild comparisons / logical visit | 1.4318 | 1.3502 |
| Mask deletions / logical visit | 0.0683 | 0.0825 |
| Skipped entries requiring compaction copies | 13.49% | 17.44% |
| Tile builds | 912,649 | 6,682,541 |
| Suffix rebuilds | 707,318 | 3,809,460 |

The kernel really skips entries, but the spans are short. It still traverses
74–82% of entries individually through its scalar cursor, while rebuilding
inspects another 0.27–0.28 entries and performs 1.35–1.43 blocker comparisons
per logical visit. Metadata traversal, mask repair and suffix rebuilding add
work to the existing flat watch vectors. Group checks alone are infrequent;
most skipped entries also avoid compaction copies, so neither group lookup
count nor copying alone explains the regression.

These counters do not isolate how much of the 82% instruction increase comes
from cursor dispatch, sorting, allocation, mask work or other maintenance.
No component ablation was run. The measured conclusion is that the combined
representation costs too much, not that one component has been identified as
the sole cause.

**Do not retry this cached flat-vector tile design by tuning 64/16/4 thresholds
or selecting favorable seeds.** A new shared-satisfaction representation would
need to remove ordinary per-entry traversal and flat-list maintenance traffic,
while preserving conflict-prefix order and explanations. Native grouped storage
would require a separately registered design and correctness argument. The
result also leaves idea 2's structured propagation blocks open; it does not
falsify every possible way to share satisfaction checks.

### Reproducibility and disposition

Registration: `30e9dfe`. Implementation: `38a4b1ce9d8011a83f9a9056809e46ad016a95e4`.
Measured integrated source: `0a22e8d6bc5b10709ad449caa6912c4bc44a6e24`.
Intervening integration touched documentation and the independent `cnf_solve`
example; the solver libraries and measured `stats_solve` source were unchanged.

| Input | Optimized record | Diagnostic record | Reused control |
|---|---|---|---|
| break_unsat_06_07 | `64c81d3184bde25e` | `0021ace50a0bd4f3` | `50fa8316e92aed2a` |
| circuit_48in64out | `44df19283ba9fe24` | `4fc17aa427c3e4cd` | `a6b0151744a458c1` |

Cached binaries under `precompile/0a22e8d/`:

- `stats_solve-tiles`, SHA-256
  `48b8ab209b2626c4e60fe2caeac48629c7726b3294fa6e7556c82c624c23a09b`;
- `stats_solve-tiles-stats`, SHA-256
  `ff57e2fce2d5be73983ae461734d4dbfd97fc3ea90803ebff787ba720f549fab`.

Both use Rust 1.96.0, the portable release profile and dependency lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
The cached control binary has SHA-256
`76a883a819c437d1e8dd4c43828975b860212027b13554219f4b8f5cde119332`.
Input hashes and exact commands are in the canonical records. Full manifests,
raw stdout/stderr, PMU reports, diagnostic counts, summary and machine-readable
verdict are retained under
`precompile/0a22e8d/benchmark/watch-tile-prototype/`; canonical records are in
that revision's `benchmark/runs/watch-tile-prototype/`. Reused controls are in
`precompile/219bed6/benchmark/runs/mode-matched-throughput/`.

The kernel verification logs and both fresh parity reports are retained in
`precompile/0a22e8d/benchmark/watch-tile-verification/`. Removing the prototype
restores the SAT crate and standalone parity manifests byte for byte to
pre-prototype `7c59161`, retaining the earlier `bcp-groups` observer. The source
and runner remain available in Git history, with cached binaries and results;
there is no failed optional kernel left for ordinary maintenance to support.

Fresh verification of the removal passed all required gates: all-features
build; 10,637 nextest tests (12 skipped); 111 doctests (29 ignored); strict
all-targets clippy, formatting and strict docs. Fresh Z3 4.16.0 parity at
`2026-09-07T22:18:07+02:00` found 169 agreements, zero disagreements and one
inconclusive case (`array_unique.smt2`: Nixie UNSAT, Z3 Unknown). The unresolved
case is not counted as an agreement. Logs, the final source fingerprint and
the parity report are under
`precompile/0a22e8d/benchmark/watch-tile-removal-verification/`. No performance
measurement was repeated during removal verification.
