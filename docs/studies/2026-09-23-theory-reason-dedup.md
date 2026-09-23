# Order-preserving theory-reason deduplication

The fresh-seed sparse 16x32 comparison uses **27.9% fewer instructions**
than the current Nixie baseline, with identical transcripts and checking.
Its ordinary **Nixie/Z3** ratio falls from **42.89 to 30.93**; the gap to
Z3 remains large. The sparse 32x16 reduction is 18.1%. Short cases and
all-present scheduling are neutral. This lands only the explanation-set
optimization; timetable and callback/model-replay costs remain follow-ups.

## Preregistration (2026-09-23)

The larger-case CP investigation identified the growing explanation-clause
vector's duplicate scan as about 30% of sampled instructions in sparse 16x32.
Replace only that membership test with a local variable set for explanations
longer than eight premises. Eight follows the existing inline SmallVec capacity;
retain the allocation-free scan for short reasons. Do not tune this threshold
using the measurements. Keep first occurrence by variable, polarity, propagated
variable exclusion, literal order, watches, LBD, proof output and search counters.
The set is never iterated and does not survive the call or introduce scope state.

This is a representation change, not a heuristic or shortened explanation.
A separate trajectory-perturbing null would answer a different question; require
exact baseline/candidate transcripts and exhaustive old/new clause construction
checks instead. Any trajectory change falsifies that classification and blocks
landing until understood. Independent model, callback and proof checks stay on.

Freeze the current main source `34285f11` as the Nixie baseline, using the
unchanged external default-feature release driver/profile/lockfile from the
preceding CP studies. The installed Z3 4.16.0 binary remains the external
reference. Use the current reference harness without changing its hash.
Existing matching Z3 cells are reused; never refresh a cell for a nicer number.
Whole-process user instructions pinned to CPU 0 are the primary metric, with
at least 99% counter coverage and the existing 120-second external cap.

Selection: seeds 10..19, ordinary and certified modes, two push/check/pop
rounds; all seven families at 4x4 and 8x16, and unknown/present/sparse at
16x32 and 32x16. Confirmation: fresh seeds 20..29 over the same grid. Report
family/shape distributions, solved-at-cap outcomes, current/previous Nixie
and current/Z3 ratios separately. The target regime is already solved below
the cap; no solved-count improvement is expected. Require more than 5% lower
instructions on sparse 16x32 in both grids, no per-family/shape regression
beyond 5%, identical Nixie transcripts and all checked verdicts retained.

Short-reason/SMT protection includes the small CP grid, full release workspace
suite and doctests, all-feature build/Clippy/docs/formatting, the installed-Z3
parity suite, and the deterministic perf landing gate. The latter's counters
do not measure this scan's cost; the instruction experiment does. All Rust
builds and checks use release mode. The existing complete CP proof chain and
push/pop oracles must still pass. No variable-duration/demand or stronger
cumulative propagation feature is part of this change.

## Implementation and audit

The long path uses a fresh `FxHashSet<Var>` solely for membership, seeded with
the propagated variable. It appends each negated first occurrence immediately
in input order. The short path has the same first-occurrence contract without
allocating a set. Neither path sorts, iterates the set, truncates variable IDs,
shortens the original callback premise list or caches state between calls.

The read-only Z3 user-propagator reference constructs explained consequences
from current signed premises and replays scoped clauses. Its generic SAT
clause simplifier sorts literals; adopting that ordering here would change
Nixie's watch ties and search, so this change preserves Nixie's existing order.
Audited Nixie layers: callback certificate/premise validation; both SAT
materialization callers and the unchanged lazy-reason path; watch ranking;
LBD/subsumption marks; clause ownership and pop; proof lemma emission; and
independent CP model replay and canonical proof reconstruction. The full
unshortened lemma is still recorded before SAT materialization. The optimized
vector feeds the same subsequent operations with identical contents.

The new exhaustive test compares both paths with the old ordered scan for
all sequences of length zero through six over six signed literals, including
self premises and widely separated IDs, and repeats the sequences to force
the long path. Additional cases reach 1,024 distinct variables. A separate
integration regression compares proof transcripts with and without duplicate
premises, checks latest-falsified watch selection and repropagation after
backtracking, and repeats clause creation/removal across push/pop.


## Measurements and verdict

Candidate `2d0af6d6` passes the preregistered bar. Selection sparse 16x32
current/previous ratios are 0.7122 ordinary and 0.7136 certified; confirmation
ratios are 0.7213 and 0.7217. No threshold or implementation variant was
selected after reading these measurements. Confirmation seeds 20..29 were
fresh to this experiment; they use the same workload families, not a new corpus.

Fresh-seed geometric means of paired instruction ratios (lower is better):

| Mode | Family / shape | Previous Nixie/Z3 | Current Nixie/Z3 | Current/previous Nixie |
|---|---|---:|---:|---:|
| certified | present-16x32 | 17.0368 | 16.8442 | 0.9887 |
| certified | sparse-16x32 | 43.0001 | 31.0352 | 0.7217 |
| certified | sparse-32x16 | 6.1867 | 5.0716 | 0.8198 |
| certified | sparse-4x4 | 0.6329 | 0.6325 | 0.9993 |
| certified | sparse-8x16 | 6.5770 | 6.2121 | 0.9445 |
| certified | unknown-16x32 | 4.7026 | 4.5018 | 0.9573 |
| solver | present-16x32 | 16.9822 | 16.7897 | 0.9887 |
| solver | sparse-16x32 | 42.8871 | 30.9340 | 0.7213 |
| solver | sparse-32x16 | 6.1748 | 5.0588 | 0.8193 |
| solver | sparse-4x4 | 0.5841 | 0.5838 | 0.9996 |
| solver | sparse-8x16 | 6.5102 | 6.1488 | 0.9445 |
| solver | unknown-16x32 | 4.6514 | 4.4523 | 0.9572 |

The small-grid aggregate is neutral (ordinary current/previous 0.9947).
Unknown 16x32 and all-present results remain in the 5% neutral band on
confirmation. Do not describe their small deltas as measured wins. Across
both grids, the worst family/shape/mode ratio is 1.0010, also neutral.

All 800 baseline and 800 candidate cells return checked SAT with identical
output hashes, including search counters. The 800 paired comparisons reuse
400 unique Z3 cells between ordinary and certified modes: 200 existing
selection cells and 200 new confirmation cells. No lost, censored, Unknown
or invalid-model cells occur. Every new counter has 100% coverage. Raw counter
totals, record IDs/paths, output hashes and model-check flags were audited.
The [per-seed data](2026-09-23-theory-reason-dedup.csv) and
[distributions](2026-09-23-theory-reason-dedup-distributions.csv) retain both
grids, including baseline/candidate min, median and max instruction counts.

The resource capacity is redundant in these integration benchmarks, except
for the blocked family which forces optional absence. These are checked SAT
admission workloads; no hard packing, UNSAT throughput or general SMT speedup
claim follows. Nixie includes its model/certificate gates in the measured
process; Z3's extracted models are validated independently outside that process.

A post-change sparse 16x32 diagnostic profile (seed 10, ten rounds,
100M-instruction period, CPU 0) has 588 samples and zero throttle/lost events.
`add_theory_reason_clause` self accounts for 1.02%, and the new materialization
helper self for 0.34%; shared hash-table/allocation samples are separate.
The dominant remaining symbols are CP callback work, snapshot reconstruction
and premise replay. These single-seed sample fractions locate remaining costs;
they are not a second end-to-end performance measurement.

## Reproduction and record handling

Nixie baseline source is `34285f114f3ab99fda4117466bb80d713a73ca6a`,
candidate source `2d0af6d6c1ac5041a579bee3c591aa6c6dc70ebb`.
The unchanged driver and external release profile/lockfile are archived with
the final landing; no feature flags, propagation rules or checking paths differ
between arms. The baseline was rebuilt from current main, rather than treating
the earlier study's older frozen binary as today's baseline.

Existing Z3 selection cells come from `df564313` (small grid) and `6973d94e`
(large grid); their input hashes and host identities match exactly. The former
uses the earlier selector-free harness, with the same encoding and model checker.
Fresh Z3 cells are under `52644cef945799c6fb06549d01c68ab210683f61`; this
revision identifies the harness source, not Z3's own Git source. All runs use
installed **Z3 4.16.0**. Its version and binary hash are in each stored record.

The first fresh Z3 cell completed measurement/model validation but record
insertion rejected an accidentally shortened Git revision label. Its original
counter/output files were preserved, moved under the full revision and
recorded without rerunning. The unavailable elapsed-wall-time metadata is
omitted for that cell; its primary instruction count and coverage are intact.
No measurement was discarded or replaced.

Timetable redundancy recognition, snapshot/event reuse and shorter explanations
remain separate follow-ups. Shortening explanations would change clauses and
needs separate search controls. Variable durations/demands and stronger
cumulative propagation remain unimplemented.

## Integration protocol (before replay)

While full release verification was compiling, main advanced to `84ff279f`
with the independently verified complete-root lucky-snapshot optimization.
Merge `098e9983` combines it with this change without conflicts. Rebuild both
the new main baseline and merged candidate using the same frozen external
CP driver and repeat the confirmation grid, seeds 20..29, before landing.
This is an integration replay, not new independent confirmation or another
selected configuration. Reuse Z3's existing confirmation cells; require the
same transcript/coverage/regression checks and target-family acceptance bar.
Keep the isolated experiment above as attribution evidence.

Restart the unfinished full-suite compilation on the merged source using the
repository's established test-only release link settings:
`CARGO_PROFILE_RELEASE_LTO=false`, `CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`,
with optimization level 3 in a separate `target-verify`. No tests ran in the
interrupted compilations. Normal release builds, Clippy, docs, doctests,
parity and measured binaries retain their original profiles. The interrupted
compile logs are preserved, not counted as completed verification.

The pre-integration 150-second perf gate printed PASS with identical counters
on eight nontrivial pairs, but one pair was jointly censored. Its candidate
path was also inside the active Cargo output directory. Preserve this as a
diagnostic only. The final integrated gate uses a frozen cached CLI and a
600-second cap, with binary hashes checked before and after; only its complete
result qualifies as landing evidence.

## Integrated result

The integrated candidate `098e9983` also passes the bar against the new main
baseline `84ff279f`. On the replayed confirmation grid:

| Mode / family / shape | Main baseline / Z3 | Integrated candidate / Z3 | Candidate / main baseline |
|---|---:|---:|---:|
| Ordinary sparse 16x32 | 42.8863 | 30.9348 | 0.7213 |
| Certified sparse 16x32 | 43.0012 | 31.0348 | 0.7217 |
| Ordinary sparse 32x16 | 6.1748 | 5.0588 | 0.8193 |
| Certified sparse 32x16 | 6.1867 | 5.0716 | 0.8198 |
| Ordinary present 16x32 | 16.9818 | 16.7898 | 0.9887 (neutral) |
| Ordinary unknown 16x32 | 4.6514 | 4.4518 | 0.9571 (neutral) |

All 400 integrated baseline/candidate pairs retain byte-identical transcripts,
checked SAT and 100% counter coverage, with no censored cells. No family/shape
regresses beyond the neutral band. The two CSVs include these rows as the
`integrated` grid, separately from the 800 isolated comparisons. Z3 reference
cells are reused, not resampled. Neither the integration replay nor its seeds
are counted as additional independent confirmation.


## Final verification and landing evidence

The integrated source `098e9983` passes all required gates:

- Full release Nextest: **12,384/12,384 passed**, 18 existing skips. This
  includes the new exhaustive/order/watch/proof/scope regressions and the
  optional scheduling oracles and complete checked CP proof tests.
- **114 doctests passed**, with 31 existing ignored examples.
- Normal all-features release build, all-target Clippy with warnings denied,
  formatting, and documentation with warnings denied all pass. Documentation
  uses the workspace's configured rustdoc flags, since Cargo does not accept
  the `-- -D warnings` passthrough for `cargo doc`.
- Installed **Z3 4.16.0** parity: **176 decisive matches, zero wrong answers,
  one inconclusive** (`array_unique`: Z3 Unknown), no timeout/error.
- Frozen default-feature CLI, 600-second perf gate: **12/12 decisive
  agreements**, no censored or lost pair, and conflict/decision geometric
  means **1.000** on nine nontrivial pairs. The three others are trivial.
  Binary hashes before/after agree. Wall ratio 1.02 is diagnostic only;
  no wall-clock speedup is claimed.
- Five Python CP reference-harness tests pass. All new instruction records
  and paired transcripts pass the independent audit; `git diff --check` is clean.

The final documentation/data landing does not alter the verified Rust source.
Frozen binaries and all build/profile/verification evidence are retained under
its `precompile/<landing-sha>/benchmark/cp-reason-dedup/`; immutable per-cell
records remain under their original measured source revisions. Temporary
worktrees, branches and build artifacts are removed after landing.
