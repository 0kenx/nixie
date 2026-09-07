# Eager watch normalization throughput experiment

## Outcome

The eager normalization implementation is retained under BENCHMARKING.md's
component-improvement rule, with all verification gates below passing. It
removes the orientation branch while preserving the exact stored pair on
every path. No search policy, watch choice, or tick accounting changes.

On the reduced final-release P-core panel (four inputs × three seeds),
whole-invocation cycles/conflict T/B is **0.9730** and instructions T/B is
**0.9890**, against cached `0263862` controls. The 2.7% cycle reduction is
**neutral under the repository's 5% band**, not a broad throughput win.
The three attribution pairs on break against matching parent `219bed6`
estimate **15.3% fewer exclusive propagation cycles** (ratio 0.8474),
clearing the separate component gate. No accepted profile has lost samples
or throttling; periodic sampling remains an estimate, not exact function
counters. The host was shared with other active solvers and builds.
Full stdout is identical on all 14 early-pilot confirmation pairs, twelve
final-release pairs, and three matching-parent component pairs.

| confirmation input | seeds | instructions T/B | cycles/conflict T/B |
|---|---:|---:|---:|
| break_unsat_06_07 | 1–3 | 0.9863 | 0.9261 |
| crn_11_99_u | 1–3 | 0.9883 | 0.9528 |
| circuit_48in64out | 1–3 | 0.9880 | 0.9853 |
| si2-b03m | 1–3 | 0.9934 | 1.0309 |

The early pilot measured cycles T/B 0.9607 across the same four-input
panel (also neutral), 0.9338 on held-out j3037 seed 1, and 0.9214 on noL
seed 1 at a 100,000-conflict cap. These holdouts were not repeated for the
final artifact. Whole-run branch misses fall 11.4% in the final panel.

Both arms report the same decisive answers except capped noL, where both
return Unknown; Unknown is not a verified agreement. UNSAT observations
have no independently checked certificates in these PMU runs. All recorded
SAT models were independently evaluated against their original clauses.
Each half of the four-input panel has two input families, with three paired
seeds per input. Both arms solve all twelve final-panel cells; the earlier
holdouts add one decisive result and one capped Unknown per arm.
No change to conflict count is claimed. The remaining Kissat gap includes
both throughput and search trajectory differences; these results do not
establish parity with Kissat or an effect on the entire competition corpus.

| component seed | baseline propagation samples | candidate samples | estimated exclusive cycles T/B |
|---|---:|---:|---:|
| 4 | 1083 | 927 | 0.8560 |
| 5 | 588 | 474 | 0.8061 |
| 6 | 1058 | 933 | 0.8819 |

The [PMU rows](data/2026-09-07-eager-normalization-pmu.csv) preserve the earlier
contested-core screens as well as the fresh CPU-2 pairs. The [summary and
binary identities](data/2026-09-07-eager-normalization-summary.json) preserve
per-seed ratios, component samples, hashes, and model audit counts. The
CPU-10 screen's apparent regression was not confirmed by the fresh-core
pairs; the allocation and raw-filename corrections are documented below
and in `2026-09-07-watch-move-value-reuse.md`.

## Registration

Baseline is `0263862` (solver source unchanged through `2bd403c`). The user
requested closing the Kissat gap while reducing the number of runs. Reuse
the completed mode-matched baseline cells; do not repeat reference runs.

Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp` compute the other
watched literal with the XOR of the watched pair and the falsified literal.
Apply that identity in Nixie, then **always** store the normalized pair
before testing satisfaction. This differs from the rejected on-demand
normalization: the final literal order remains exactly the old conditional
swap's order on every visit, including both satisfied paths. No heuristic,
watch order, counter, proof, or assignment change is intended.

For a live watch, one of the first two literals equals the falsified
literal `f`. The old code maps `[f, x]` to `[x, f]` and leaves `[x, f]`
unchanged. XOR cancels `f` in either orientation, and the two eager stores
produce exactly `[x, f]`. This argument also covers satisfied exits before
any watch movement. Every later branch therefore sees the same clause,
blocker, reason, and trail state, including SMT, proof, inprocessing, and
diagnostic configurations. The swap diagnostic retains its old predicate.
This is a representation-level substitution with no trajectory-changing
policy; a randomized heuristic null would test a different question.

Screen seed 0 on `break_unsat_06_07` and `circuit_48in64out` using cached
release baselines, the existing full-invocation PMU runner, and CPU 10. Stop
on trajectory divergence or an obvious cycle regression. If promising,
confirm on seeds 1–3 for break, crn, circuit, and si2 (12 new cells, cached
baselines), with j3037 seed 1 as a larger held-out workload. No ten-seed
sweep: this is the user's reduced-run scope. Report the small sample and
the restricted panel explicitly. Primary metric is instructions; require
cycle confirmation. A landing needs at least 5% lower geometric-mean cycles
on the confirmation panel, non-increasing instructions, and no input over
5% worse. Do not generalize this to the full competition corpus.

Before landing solver code, require exact diagnostic/model identity on
paired cells, focused tests of both watch orientations and all visit exits,
SAT differential/model checks, full workspace verification, and fresh Z3
parity using the available version. A rejected screen is recorded here.

## Verdict: rejected at the two-cell screen

Both outputs were byte-identical to baseline, including the checked circuit
SAT model. Instructions fell 1.33% / 1.19% and branch misses fell 14.56% /
14.05% on break / circuit, respectively, but cycles rose 5.65% / 23.67%.
The unconditional writes do not establish lower hardware cost. This is a
rejection screen, not a multi-seed regression estimate or an attribution
of the cycle increase. The candidate was removed; no confirmation sweep
was launched. Do not repeat eager XOR normalization solely to eliminate
the orientation branch. Archived patch, binary and PMU records are under
`precompile/2bd403c/benchmark/`.

## Measurement limitation discovered after the screen

A subsequent host process check found another task's multi-core SAT sweep
on CPUs 10–17, including this experiment's CPU 10. The recent screens may
have overlapped that workload; their cycle differences cannot be treated as
quiet paired measurements against the older cached baseline. Preserve all
rows and rejection decisions as screening outcomes; the hardware-cycle
cause is unresolved. No claim of a cycle regression is justified here.
Further cycle qualification uses fresh paired cells on a separate P-core.

## Reopened after fresh-core screen

See `2026-09-07-watch-move-value-reuse.md` for the core-allocation correction.
Fresh paired CPU-2 cells give cycles T/B 0.9127 on break and 0.9361 on
circuit, with byte-identical complete stdout. Confirm on P-core 2, seeds
1–3 across break/crn/circuit/si2 (24 new baseline/candidate cells). Add
j3037 seed 1 as registered (two cells), and noL seed 1 with a 100,000-conflict
cap (two cells) to cover the long-trajectory input without two multi-minute
completion runs. Baseline and candidate order alternate by seed. Keep the
original cycle/instruction bars; no new configuration selection within this
confirmation panel. No new reference sweep. Every raw directory now includes
the full configuration hash to distinguish core and cap changes.

## Confirmation result and component gate

The four-input, three-seed panel has cycles T/B 0.9607 and instructions
0.9888: neutral under the repository's 5% band, below the whole-run bar.
Every complete stdout is byte-identical. Per-input cycles: break 0.9567,
crn 0.9363, circuit 0.9402, si2 1.0116. Held-out j3037 gives 0.9338 and
capped noL gives 0.9214 (one seed each; no generalization from them).

BENCHMARKING.md section 3 separately allows a component improvement above
5% with neutral whole-run cost and verified inertness on every executing
path. Before deciding that gate, measure exclusive propagation cycles with
cycle sampling on break seeds 4–6, perf binaries believed source-equivalent
at registration (the source audit below corrects that assumption),
CPU 2, alternating order, full completion. Six attribution runs, no repeat
of any PMU cell. Use a fixed 500,003-cycle sample period, retain raw samples,
and compare estimated exclusive propagation cycles (symbol samples times
period), not percentages alone. Require geometric-mean component ratio
<=0.95, all three outputs identical, plus the full correctness gates. Do
not reinterpret the 3.9% whole-panel result as a >5% whole-run win.

The first attribution run at period 500,003 was invalid: 1,499 explicit
`PERF_RECORD_THROTTLE` records mean its sample totals omit execution. It is
retained as invalid telemetry and never used in the comparison. Before any
candidate attribution, increase the period to 5,000,003 for all six component
cells (a distinct sampling configuration), and require no throttle/lost
records. Symbol extraction also requires the `ip` field in `perf script`;
the stored raw data remains usable for corrected extraction.

## Final verification

The release rebuild after verification has different machine code from the
early release pilot. The propagation patch is identical, but commit
`1804de8` added a default-off restart option in the intervening source.
The attribution binary was already built from the final source, including
that change and the new test module. Do not assume the release timing
transfers: qualify the final
release artifact once on the same four inputs, seeds 1–3, reusing the
existing CPU-2 baseline cells. These twelve candidate cells get a distinct
binary hash and configuration identity. Retain every result, require exact
stdout identity, and apply the existing whole-run neutrality/regression
bar. No new reference, baseline, holdout, or component sweep.

The final release check has instructions T/B 0.9890 and cycles/conflict
T/B 0.9730: neutral. All twelve outputs are identical to their cached
controls. The instruction ratios closely match the early pilot; the host
also has other active solvers and builds, so cycle differences between
the two candidate panels are not evidence for selecting one binary.

The source audit also corrects the earlier claim of source-equivalent
component binaries: the old baseline predates `1804de8`. To isolate the
propagation change, build a baseline from current parent `219bed6`, then
sample only its three missing component cells (break seeds 4–6, same
CPU and 5,000,003-cycle period). Reuse the existing final-source candidate
samples and preserve the old comparison as historical evidence. The
same <=0.95 component bar and exact-output checks apply; no policy option
is enabled and no existing cell is repeated.

The matching-parent component comparison passes: ratios 0.8560, 0.8061,
and 0.8819, geometric mean 0.8474. All outputs match and no new baseline
profile has throttling or lost samples. The old-baseline component result
(0.8613, or 13.9% lower) is retained in the JSON as historical evidence;
the matching-parent comparison above is the landing check. Neither the
three seeds on one input nor non-contemporaneous baseline reuse establishes
a precise population-wide cycle effect. No additional policy tuning was
performed from these measurements.

- Workspace build with all features: passed.
- Full nextest suite: 10,623 passed, 12 skipped.
- Workspace doctests: 111 passed, 29 ignored.
- Clippy (all features/targets, warnings denied), formatting, and docs
  (`RUSTDOCFLAGS=-D warnings`): passed.
- 100,000 SAT differential cases: zero mismatches and zero invalid models.
- Fresh Z3 4.16.0 parity: 169 agreements, zero disagreements, one
  inconclusive case (`array_unique.smt2`: Z3 Unknown). The user authorized
  the available reference version; these are not 4.15.4 snapshot numbers.
- Targeted regression: 160 combinations covering both watched orientations,
  all literal polarities, satisfied-first, satisfied-replacement, watch
  movement, unit propagation, and conflict; exact stored order and reason
  checked. The test passes both alone and in the all-features suite.
- PMU audit: 54 recorded rows, 100% scheduled events, 25 SAT models checked;
  all paired diagnostics, ticks, decisions, conflicts and models identical.
- Final release rebuild after the comment cleanup is byte-identical to the
  measured artifact (`76a883a8…9332`). The intervening `e6daf1d` commit
  changes documentation only; the full verification still covers the
  production source being landed.

The old false-watch-orientation branch remains in diagnostic builds only
when needed to count swaps. In ordinary builds the XOR identity and eager
normalized stores remove it. A live watcher still names one of the first
two clause literals, as required by the existing two-watch invariant; the
new debug assertion checks that premise before using the identity. Deleted
watchers are discarded before the new operation.
