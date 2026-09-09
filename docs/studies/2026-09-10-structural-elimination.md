# Structural gate elimination toward the Kissat wall gap

**Verdict:** the structural prototype `54dd3ad` is not landed. On the
registered `j3037` screen, definitions-on took 49.83 s versus 46.06 s off
and 18.04 s for mode-matched Kissat. The production change retains only
the independently justified budget, frozen-variable and conflict-proof
fixes. The existing semantic-only definition mode remains opt-in.

The user's paired 2.27x wall / 1.24x conflict geomeans imply approximately
1.83x wall per conflict. Prior local loop rewrites do not establish enough
remaining opportunity. This step targets fewer clauses, auxiliary variables
and propagation events through cheap definition recognition and bounded
gate-aware elimination. References are local Kissat `gates.c`,
`equivalences.c`, `ands.c`, `ifthenelse.c`, `definition.c` and `resolve.c`.

## Scope and prerequisites

Use the existing explicit `NIXIE_DEFINITIONS=1` mode. Recognize equivalence,
AND/OR and ITE clause patterns before the embedded semantic solver; preserve
the existing semantic fallback. Share occurrence preparation and index
storage. Admit denser neighborhoods only to the structural path, with an
explicit occurrence bound, work budget and the existing resolvent growth
bound. Do not expose a larger unrestricted all-pairs resolution search.

The source audit found that the ordinary round's stop condition consults
`elim_resolutions_total`, which is unchanged until the round returns.
Repair the budget against work consumed in the current round, enforce it
inside both resolution products, and re-arm unfinished candidates. A denied
attempt must not retire its pivot or install an incomplete resolvent set;
already justified units and strengthening remain valid. Tests must cover
zero/exact/exhausted boundaries and resumption independently of recognition.

Pattern recognition must use live original clauses and the eliminator's
current root assignment. Return actual antecedent IDs, handle both pivot
polarities, and prove that the pivot-erased gate clauses are inconsistent.
The existing three-product resolver then omits the antecedent-by-antecedent
product justified by that property. Check shrinking/deletion during
resolution, eager units, model extension, removal of learned clauses over
eliminated variables, scopes, assumptions, frozen variables and proofs.
Preserve the existing proof-mode refusal for definition extraction until
the corresponding provenance is implemented and checked.

## Evidence and measurement boundary

This is a new search-transforming implementation, not an exact-trajectory
loop optimization. A matched semantic null for definition enablement is
still unresolved in the existing definition/factorization studies. Neither
a shuffled invalid gate nor an ordinary clause shuffle supplies that null.
Correctness qualification and an explicit usable mode do not establish a
default-enablement or broad performance claim.

Before any solver performance call, complete recognition/resolution/model
tests and strict SAT checks, commit the candidate and cache its binary
identity. Register the specific cost cell and its controls separately once
the implemented work counters and static opportunity audit are available.
No performance run is authorized merely by this design note. A negative
cost result must retain a profile/diagnosis and account for recognition,
resolution, maintenance and subsequent search. Before a production source
landing, run all required workspace and correctness-only parity gates.

Initial source: `c452903`. No implementation or measurement result is
claimed by this registration.

## Prototype implementation and independent correctness audit

The `54dd3ad` prototype recognizes signed equivalence, AND/OR and ITE cofactor
refutations, with stable occurrence-order selection and reusable hash/vector
storage. It reads live original clauses, verifies pivot membership and skips
satisfied, deleted, learned and stale entries. False root literals are erased.
Patterns return actual antecedent IDs. Either selector value in the ITE
cofactors forces a literal and its complement; this remains exact with
aliased data inputs. No recursion or unsafe code was added.

Structural recognition is bounded by 2,000 raw occurrences per polarity,
100,000 charged operations per candidate and 8,000,000 per round. Charges
cover clause/literal inspections, hash operations, hash-storage clearing and
pair/membership comparisons. These are scheduling proxies, not a complete
hardware-cost currency: allocation, index preparation, occurrence sorting,
resolvent construction, database maintenance and later search must all be
included in any whole-process measurement. The ordinary 100-occurrence cap,
100-literal resolvent cap and existing clause-growth bound remain.

The resolution budget now counts the current round and stops before a denied
pair in both ordinary and three-product resolution. An interrupted pivot
keeps its original clauses and does not install a partial resolvent plan;
valid eager strengthening/units are retained. Unfinished candidates are
re-armed. Semantic extraction work carries across rounds of the phase.
Its 64-million-tick threshold prevents starting another extraction; the last
bounded extraction/core shrink can overshoot it, as before.

Two additional baseline defects were exposed and repaired independently:

- Freezing a variable after it was marked left it in the elimination
  schedule. This reproduced with definitions disabled. Freezing clears its
  pending mark, and the elimination entry checks freezing again, protecting
  already prepared schedules too. The regression covers both cases.
- Both phase-entry and post-round propagation dropped the conflict clause
  ID. Later UNSAT proof finalization could emit an unjustified empty clause.
  Both exits now finalize using the actual conflict. Separate test scenarios
  force entry conflict and a round-derived unit followed by a propagation
  conflict, and check their LRAT transcripts independently.

Other examined layers: recognition under root assignments and both pivot
polarities; occurrence deletion/shrinking; three-product projection;
elimination-local eager units; proof-backed ordinary resolution fallback;
root/scope/assumption/theory gates; learned-clause retirement over eliminated
variables; and reverse-order model extension. A unit returned by a round was
unassigned in the initial trail snapshot and is recorded at most once in the
local value table; no trail propagation occurs inside that round, so its
phase-epilogue false-value arm is defensive. Empty/unit strengthening without
proof provenance remains refused under proofs. Proof-independent structural
recognition remains off when a proof is attached.

Tests exhaust all assignments of each small cofactor pattern, signed and
permuted variants, missing antecedents, aliased ITE inputs, and root values.
Projection tests compare the reduced formula with existentially eliminating
the original pivot, then validate the returned model against original CNF.
Seventy-two gate-plus-random-clause overlays are checked by exhaustive truth,
with original-model validation and independent LRAT checking on the ordinary
proof fallback. Budget tests cover zero/exact/interrupted boundaries, resume,
historical counter independence, saturation and semantic-phase carryover.

## Static opportunity census (no solver run)

The census reads original DIMACS clauses and checks exact binary equivalence
and AND/OR patterns. Counts are variables participating in a pattern, not
mutually independent gates or predicted successful eliminations. It does
not count ITEs, simplify with root units or run preprocessing.

| Input | Clauses | Equivalence pivots | AND/OR pivots | Two-sided pivots with 101–2,000 occurrences | Those also in an equivalence/AND pattern |
|---|---:|---:|---:|---:|---:|
| circuit_48in64out | 168,064 | 0 | 0 | 2,834 | 0 |
| j3037_10_mdd_bm1 | 63,952 | 346 | 2,417 | 0 | 0 |
| si2-b03m-m800-03 | 472,588 | 15 | 8,511 | 752 | 8 |
| constraints_17_0.4_1 | 58,990 | 0 | 680 | 0 | 0 |

The census selects `j3037` for the first feasibility cell: its input exposes
many inexpensive patterns and it has a substantial reported Kissat wall gap.
It does not justify using the circuit input as a structural-recognition
screen. Later root simplification may expose patterns absent in the census.

## Separate input-loading proof limitation

An earlier overlay generator allowed repeated variables to collapse clauses
to units during loading. Case 45 exposed a separate existing LRAT prefix
failure before elimination: an input-time contradiction emits a derived
empty clause immediately, then subsequent originals no longer receive
contiguous input IDs. Effective parse units can also still be awaiting their
solve-entry proof flush. The in-memory transcript rejects this state. No
wrong SAT/UNSAT verdict was observed; this is not repaired by the elimination
change. The elimination tests use distinct-variable overlay clauses to start
from a valid loaded formula; root-contradiction coverage remains in the
explicit phase-boundary tests above.

Exact failed input (including duplicate and tautological originals):

```dimacs
p cnf 6 22
1 -2 0
-1 2 0
-4 -3 -4 0
-3 -3 0
6 2 -6 0
-2 3 -1 0
3 2 0
3 -2 5 0
5 -4 0
-5 -2 0
-1 -2 2 0
-6 2 0
-5 -3 -4 0
-4 -4 0
-5 -4 0
-5 -5 -6 0
3 -4 3 0
1 3 -5 0
-2 6 0
5 5 0
6 2 1 0
1 -2 -3 0
```

Reproduce by enabling `enable_lrat_transcript()` before adding all clauses,
then solving and reading the transcript. The observed error is
`original clause id 12 is not the next sequential id`. Preserve this case
for the separate input/proof-prefix repair; do not interpret a successful
elimination proof test as evidence that this input-loading path is fixed.

## Registered first feasibility screen

Only `j3037_10_mdd_bm1`, seed 0, CPU 15 (Atom) is authorized in this screen.
Run the committed candidate with definitions off, mode-matched Kissat 4.0.4,
and the same candidate with definitions on, in that order, once each.
Existing result-store search found no compatible whole-verdict CPU-15 cells
for this input. The baseline shares the budget/freeze/proof fixes, so the
on/off comparison isolates enablement of the new definition path. It does
not separately estimate improvement over the old semantic-only mode.

Use the portable release build, CaDiCaL preset, `NIXIE_SWEEP=0`,
`MAXC=10000000`, `SEED=0`, `PRINT_MODEL=1`, and `NIXIE_DEFINITIONS=0/1`.
Clear all other study knobs. Kissat uses `--statistics --seed=0
--conflicts=10000000 --probe=0 --preprocess=0 --factor=0 --substitute=0
--sweep=0 --vivify=0 --transitive=0 --backbone=0 --congruence=0`.
Cache compiler, lockfile, source and executable identities before starting.

Count full-process user cycles/instructions with one non-multiplexed Atom
PMU group, including input loading, recognition, semantic fallback,
resolution, maintenance, search and output. Instructions are the primary
complete-work counter; report GNU-time wall and cycles/conflict alongside
conflicts and propagations. The tiny GNU-time wrapper is inside the counted
process tree in every arm. Warm input/executables by reading them without
executing them; write output to anonymous tmpfs files. Reject wall evidence
with more than 10% off-CPU time or counter coverage below 99.9%. Audit every
constrained userspace thread for CPU-15 contention. Emergency timeout is
300 seconds and is never a solver policy input. Preserve every start and
completion; do not retry failed or noisy cells.

Record reported UNSAT separately from independent certification. This
screen does not generate an original-CNF proof for definition elimination.
Consequently its result-store verdict stays `unknown`/unverified for an
UNSAT report, even if all three solvers agree. This is a feasibility/cost
screen and cannot claim a certified solved-count gain. Unexpected SAT must
pass an original-CNF model check and causes a correctness investigation.

One subsequent candidate-on LBR profile is registered regardless of the
cost outcome, using the portable `perf` build and otherwise the same solve
configuration. Require identical solver counters to its release cell; enable
terminal memory accounting only. Use Atom cycle/instruction group, period
10,472,903, LBR, sample-read/running-time, 128 mmap pages, and CPU sampling.
Require zero loss/throttle, at least 99.9% counter coverage and user samples,
at most 0.1% unresolved self cost, and at least 1,000 samples for a qualified
profile. An unqualified capture is exploratory and is not automatically
repeated. Profile counters cover a sampled prefix, not full solve cost.

No more benchmark cells follow in this registration. A negative/neutral
result gets a retained cost breakdown and an analysis of algorithmic or
combined mechanisms that could address it. Even a large single-input win
is only evidence of opportunity: no matched-null, multi-seed or family-wide
merit claim, and no default flip. Full workspace and correctness-only parity
gates remain required before any production source landing.

## Measured result and profile diagnosis

Exactly three release cost cells and one profiling cell ran. There were no
retries or secondary benchmark inputs. All three report UNSAT; no
original-CNF proof was generated in these cells, so canonical records retain
an unverified/unknown verdict and preserve the reported answer separately.
The prototype passed 779 default-library tests, 1,045 all-feature SAT tests
(two ignored), strict all-feature SAT Clippy and formatting before measurement.
It was not subjected to the full-workspace production gate after rejection.

| Arm | Wall s | Conflicts | Propagations | User cycles | User instructions | Cycles/conflict |
|---|---:|---:|---:|---:|---:|---:|
| Prototype, definitions off | 46.06 | 330,565 | 323,390,316 | 199,102,601,771 | 254,560,141,452 | 602,310 |
| Kissat, requested mode | 18.04 | 286,784 | 218,808,022 | 79,144,759,362 | 121,059,163,625 | 275,973 |
| Prototype, definitions on | 49.83 | 365,985 | 348,322,124 | 218,931,870,474 | 284,497,532,178 | 598,199 |

Definitions-on/off ratios are 1.082 wall, 1.118 instructions, 1.100 cycles,
1.107 conflicts and 1.077 propagations. Cycles/conflict is 0.993: enabling
this transformation does not meaningfully address the throughput gap in this
cell. The off/Kissat wall ratio is 2.553, and on/Kissat is 2.762. These are
single-cell observations, not statistical merit estimates or a new suite
geomean. Counter coverage was 100% in every arm; off-CPU fractions were
0.96%, 1.05% and 1.08%, with zero major faults.

The off arm spends about 770,076 instructions/conflict versus 422,127 in
Kissat: 1.824x. Its cycles/instruction is another 1.196x higher, together
accounting for the 2.182x cycles/conflict gap. This points primarily to
removing repeated work, with latency and layout also contributing. It does
not support treating prefetching or allocator tuning alone as the answer.

The on arm performed 223,813 semantic checks, recognized 306 equivalence
and 2,543 AND/OR patterns (zero ITEs), and charged 108,035,476 structural
operations across rounds. Its 12,540 total extracted definitions include
semantic cores and repeated attempts, not distinct eliminated variables.
Definition-aware resolution eliminated 2,660 variables; total elimination
was 6,958 versus 6,246 off and 8,989 in Kissat. **712 extra eliminated
variables accompanied more propagation work**, so elimination count is not
a useful success criterion by itself.

The [retained flamegraph](assets/2026-09-10-structural-elimination-j3037.svg)
contains 21,328 samples, all on CPU 15. It has zero loss/throttle, 100%
counter coverage, four kernel samples (99.981% user samples), and satisfies
the registered unresolved-self threshold. Its complete solver counters match
the release on arm. Sampled-prefix counters are diagnostic only.

Observed cycle attribution:

- Watch scans: 49.41% self, across the two compaction phases.
- Propagation driver: 21.59% self; propagation including children: 72.87%.
- Entire elimination phase: 4.78% including children.
- Semantic definition extraction: 2.08% including children.
- Structural recognition: 0.277% self.
- Subsumption: 2.61% self, 3.18% including children.

LBR caller chains can be truncated; inclusive attribution is a profile
estimate, not an exhaustive per-phase timer. Nevertheless the dominant
self-attributed cost is propagation. Removing all 4.78% attributed
elimination cost, with the search held fixed, would leave about 47.45 s,
still above the off arm. This is an opportunity bound, not an attainable
speedup claim. Detector micro-tuning is not the missing large lever here.

### What could improve it, and useful combinations

Reusing Kitten allocations or caching satisfying cofactor witnesses could
avoid rebuilding many unsuccessful semantic checks. A witness must still be
validated against current live clauses and root values. This is a plausible
local improvement, but the measured 2.08% semantic-extraction share is too
small to justify another tuning sweep toward wall parity on this input.
Combining such a cache with the cheap detector does not address the observed
increase in propagation work.

The underlying algorithmic target is the residual formula's propagation
cost: eliminating an auxiliary variable can replace compact implications
with more expensive resolvents. A larger occurrence limit or a higher
resolvent-count allowance is therefore not a success criterion. A future
elimination policy must price the resulting literals, implication fan-out
and useful learned-clause traffic, and compare that semantic policy with a
matched null. Simply admitting more variables is not a supported follow-up.

A materially larger combined route is shared propagation of learned-clause
families: retain actual antecedent/reason IDs while sharing common residual
literal checks across clauses. Structural recognition could help identify
families, but savings must occur in the repeated propagation loop. Prior
blocker grouping, delayed movement and kept-span compaction added machinery
without enough shared work; attaching those mechanisms to this detector
alone does not repair their cost model. First establish enough overlapping
residual checks and a reason-preserving representation, then price indexing,
invalidation and fallback as part of the whole solve. This is an unimplemented
next-lever hypothesis, not a measured gain from this experiment.

One concrete interaction to investigate is **lazy propagation of the
elimination-generated resolvent families**. The three-product construction
creates clauses sharing the same gate or antecedent cofactor. Recognition
supplies that exact structure; keeping those families compact could remove
the auxiliary search variable without paying for every expanded clause on
every propagation. This directly addresses the potential cost of the extra
resolvents. It would need exact reasons, eager-unit/fixpoint behavior,
backtracking, deletion and original-model/proof validation. Independently
speeding an unrelated loop would also help the off arm and would not, by
itself, demonstrate that combining it with this rejected mode is beneficial.

A read-only address drill-down of the same profile also found 4.06% of
whole sampled cycles at propagation-driver address `0x4b374`, 2.85% at
`0x4b42c`, and 1.93% at `0x4b54c`. Debug mapping places these around binary
adjacency access and watch-vector transfer; sampled IPs do not identify
individual instruction latency. This motivates considering combined literal
adjacency metadata when redesigning propagation, but not calling a small
metadata rewrite sufficient for wall parity. The exact address/source map
is retained as `propagation-driver-sites.json`; no extra solver run was used.

### Retained identities

Prototype source `54dd3ad` remains in the canonical cache with its source
patch and bundle, tests, build logs, compiler/lock identity and both binaries.
Release SHA-256: `fafa5423537be0740a79488c845d0c10a9f31743f889fac2f35f8867ab4f3f04`.
Perf SHA-256: `157e2de61e6b9ea905bf978005994e444a184ddfa224bf614d56f62b673e5f44`.
Kissat source `8af8e56f174b778aef3aa45af9f739b2a5f492c2`, version 4.0.4,
binary `5c91c37e4bcab56c71e304d610e303e239ab1de9809de409fe012d1d73d34fa4`.

Canonical record IDs:

- Off: `58792bf989fa9dc7`.
- Kissat: `45a3c8f2e3057841`.
- On: `7f9963129f813eb9`.
- On profile: `88d05f2966464b17`.

Raw files and once-only runners live under
`precompile/54dd3ad/benchmark/structural-elimination/` and
`precompile/54dd3ad/benchmark/structural-elimination-profile/`.
The input hash is recorded in each cell; these records must be reused rather
than rerun. The selected production fix is qualified separately below.

## Production qualification and landing scope

Qualified production source: `26b2872243f3d73e6a1c160607d5a7c8ed39d044`.
Only the resolution/semantic-phase budget fixes, pending-work resumption,
frozen-variable protection, conflict-proof provenance and their regressions
are included. Structural recognition, its expanded occurrence admission,
statistics and example-mode changes are absent from the production tree.
No wall-speedup claim is made for the retained fixes.

All required checks passed on that source:

- `cargo build --all-features`.
- `cargo nextest run --workspace --all-features`: 10,836 passed,
  13 existing skips.
- `cargo test --workspace --all-features --doc`: 111 passed,
  29 existing ignores.
- `cargo clippy --all-features --all-targets -- -D warnings`.
- `cargo fmt --all -- --check`.
- `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features`.
- `./bench/z3_parity/run_parity.sh`, installed Z3 4.16.0: 174 decisive
  matches, zero SAT/UNSAT disagreements, one existing inconclusive case
  (`array_unique.smt2`: Nixie UNSAT, Z3 UNKNOWN). Unknown was not counted
  as a match; this is correctness-only evidence.

The final fix also passed 773 default SAT-library tests. Qualification used
four Cargo build jobs and eight nextest test threads, offline/locked Cargo
commands where supported, Rust 1.96.0 and the recorded lockfile. Exact
commands, start/completion records, logs and parity snapshots are retained
under `precompile/26b2872/benchmark/elimination-safety/qualification/`.
The same-source release examples and CLI are cached there by source commit:

- `stats_solve`: `001c181e9aa2fc910040326e11eedd2ac7228f38fe853976004151eb8ff3fa43`.
- `nixie`: `127c469d44104c098ffa0844a5ae3d3764c09145f2985ca21a7840aad5bd2723`.

The subsequent integration includes only documentation changes beyond this
qualified solver source. The rejected prototype is preserved as a cache
bundle/patch and is not an ancestor of the production fix. Owned worktrees,
branches and uncached temporary logs are removed after landing; canonical
binaries and once-only measurement/qualification evidence are retained.
