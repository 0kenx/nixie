# Heap anchor reduction: controlled result

Start from `6925082367c2d34390616dd7b6efa4ed5f1f87a3`, including the intervening
checked-integral arithmetic fast path. Do not attribute those upstream changes
to this optimization. The previous heap specialization removed all-negative
arithmetic search; the next target is redundant positive/mixed heap comparisons.
Read-only reference inspection: CVC5 `theory_sep.cpp`, `reduceFact` introduces a
shared base label; positive points-to fixes that label to a singleton, and model
construction uses one map for that label. The existing finite-map reduction's
correctness argument allows the following exact specialization.

## Reduction and invariants

Let original assertions entail `pa`, where `Ha` is an exact heaplet. Assert its
validity `Va`. For every other heaplet assert `pi <=> (Vi and Eia)`, using the
existing non-nil/distinctness and finite-map-equality definitions. The same
concrete map `Ha` now determines every atom. All remaining pair constraints
follow by map equality, including negative or unforced atoms. Invalid heaplets
are false; different cardinalities cannot match; emp works as an empty anchor.
No arbitrary disjunct or guessed model may become the anchor.

Select the first syntactically entailed positive atom, with no cost policy or
seed-dependent choice. Use the existing private definition scope and discard
its constraints before changing user assertions/scopes. With no forced positive
heap, retain the general encoding. With all atoms forced false, retain the
previous zero-definition path. Proof-export and Unknown boundaries are unchanged.
Worst-case construction with an anchor drops from O(n²k²) to O(nk²).

A diagnostic control constructs the very same anchor constraints, then retains
the implied pair constraints between non-anchor heaplets (excluding false/false
pairs as before). Both arms share unit discovery, anchor choice, staging and
scope lifecycle. This isolates removal of redundant constraints from merely
introducing an anchor or reordering the original encoding. It cannot match the
SAT graph and work eliminated by an exact redundancy removal; no claim about
merit of a search heuristic or anchor-selection policy is intended.

## Fixed experiment before measurements

* Three arms: current baseline; new anchor encoding retaining redundant pairs;
  new anchor encoding omitting them. Fixed seeds 0–9 and fresh held-out 102.
* Original twenty cases (five families, sizes 2/4/8/16), plus `views`,
  `view_conflict`, and `unasserted_views` at 8/16/32/64 registered heaplets:
  32 cases × 11 seeds × 3 arms = **1,056 cells**. No adaptive cells or reruns.
* New cases have four cells per heaplet, separate location variables fixed to
  1,2,3,4 by exact bounds. `views` asserts every heaplet, all storing 0,1,2,3:
  SAT. `view_conflict` changes the final heaplet's final value to 4: UNSAT.
  `unasserted_views` asserts only the first heaplet and gives later heaplets
  distinct final values: SAT. The latter models the API's fixed vocabulary with
  only some assertions active; it does not measure arbitrary Boolean formulas.
* Authenticate all generated input before using those elementary oracles. Every
  SAT model must satisfy a separate finite-map evaluator. Calibrate new size-3
  instances against CVC5 before measuring; exclude calibration from the matrix.
* Whole-process user instructions on CPU 2, one counted PMU >=99.9% coverage,
  including construction, search, extraction, Rust validation, output and Python
  validation. All arms use the same Python worker wrapper; the old checker stays
  unchanged. Frozen release binaries, strip=none, incremental=false; same build
  command for baseline/candidate. Clear inherited NIXIE/HEAP_PERF tuning.
* Original budgets: 10,000 conflicts, 100,000 decisions, no internal time limit;
  outer 20-second cap plus three seconds for cleanup. Unknown never a match;
  partial capped costs excluded from paired ratios. Rotate arms by seed.
* Desired result: no wrong answer or lost solve, >=5% complete-work reduction
  versus the retained-redundancy control on new shared decisive pairs. Report
  baseline/control distributions, every family, original-suite regressions,
  held-out seed separately, structural comparisons, definitions and term counts.
  Neutral results remain neutral; record a negative finding if the bar fails.
* Keep exact commands, versions, binary/worker hashes, inputs, outputs and
  immutable benchstore records under `precompile/<candidate>/benchmark/`.
  Land only after all AGENTS verification, Z3 parity and frozen-binary perf gate.

## Soundness review

The review followed each affected layer rather than relying on the outer solver
verdict alone:

* **Unit discovery:** only consequences of asserted conjunctions, negated
  disjunctions and negation become units. Contradictory units fall back to the
  symbolic encoding. An arbitrary disjunct never selects an anchor.
* **Finite maps:** nonzero and distinct addresses make each valid heaplet a
  function. Equal cardinality and membership of every address/value pair give
  map equality. Under anchor validity, `pi <=> Vi and Eia` therefore determines
  the exact meaning of every atom, including unforced atoms, emp, invalid nil
  cells, duplicate addresses and differing cardinalities. Transitivity entails
  all removed pair constraints.
* **Backend terms:** the unchanged exact integer equality/Boolean constructors
  express these constraints; the general no-anchor path retains its previous
  assertion interleaving. The singleton case constructs the same validity
  assertion (`true => V` already simplifies to `V`).
* **Scopes:** anchor definitions use the existing private backend scope. Assert,
  push and pop retract that scope before changing user assertions. Repeated
  checks reuse it; counters reset when it is removed. Focused tests move between
  no anchor, a late registered anchor, a different anchor and emp, with nested
  assertions inside Boolean alternatives.
* **Models:** extraction and independent original-arena validation are unchanged.
  Any selected positive heap denotes the same anchor map. Missing or invalid
  concrete models still produce Unknown. Proof-export boundaries are unchanged.

The small exhaustive tests run all three encodings (unspecialized, anchor with
redundancy, anchor without redundancy), covering 256 grounded Boolean patterns
and 576 symbolic alias/value assignments per encoding. The CVC5 reference tests
check the corresponding 832 cases. A separate 20-view test checks that a late
anchor defines unasserted atoms, that a later contradictory assertion is UNSAT,
and that comparisons fall from 190 to 19. New walks are iterative; there are no
new dependencies or unchecked production unwraps.

## Pre-measurement verification

All-feature build, clippy (`--all-targets -- -D warnings`), formatting and
documentation passed. Rustdoc warnings are denied by `.cargo/config.toml`.
Full workspace/all-feature nextest: **12,216 passed, 17 skipped**; separate
doctests: **114 passed, 31 ignored**. Focused heap tests: 17 passed plus both
explicit CVC5 reference tests; Python benchmark/checker tests: 13 passed.
The 12 new-schema calibration checks (three families, baseline/reduced/control/
CVC5-SL) all agreed. CVC5 version: 1.3.4.

Installed **Z3 4.16.0** parity: 176 correct, one inconclusive, zero wrong,
timeouts or errors. The inconclusive case is the existing `array_unique.smt2`
case where Z3 returns Unknown. The general performance landing gate passed:
conflicts and decisions geomeans both **1.000**, all verdicts preserved, nine
nontrivial and three trivial cases. Heap measurements follow separately; this
general gate does not exercise the new heap reduction.


## Result

**Keep the reduction.** Candidate `40851e3e97890a7b59900b7f3db26ded09710b52`
completed **352/352** cells, baseline **334/352**, and retained-pair control
**333/352**. There were no wrong answers or lost solves. Every completed SAT
answer passed the independent finite-map checker; UNSAT answers matched the
authenticated corpus oracles. All 1,056 cells were attempted exactly once.

On the new families' 113 shared decisive pairs, reduced/control instruction cost
is **0.4675** (geometric mean): **53.3% less complete work**. The preregistered 5%
bar is exceeded. The corresponding baseline ratio is 0.1805 over 114 pairs, but
that number also includes the effect of introducing anchor definitions; it is
not evidence attributable solely to removing their redundant pairs.

The gain survives the fresh seed. On new-family seeds 0–9, reduced/control is
0.4637 over 103 pairs; on held-out seed 102 it is **0.5093** over ten pairs.
Baseline ratios are 0.1838 and 0.1520, respectively. These are paired geometric
means, excluding all Unknowns, rather than ratios of aggregate medians.

The original twenty cases remain neutral: all arms solve 220/220; paired cost is
0.9993 against baseline and 1.0001 against control. The largest original-case
paired increase is below 0.51% against baseline and 0.37% against control. The previous
study's allocation-16 seed-6 regression case is neutral here (1.00009 against the
current baseline, 1.00006 against control); this does not revise that earlier
study's comparison against an older implementation.

The following table gives completed-run medians in **millions of user
instructions**, including Python checking. Parentheses give solves out of 11;
missing/capped runs do not contribute partial costs. The adjacent
[CSV](2026-09-22-heap-anchor-reduction.csv) contains every arm's min/median/max,
solve counts, peak RSS and term/definition/comparison diagnostics.

| Case | Baseline | Retained-pair control | Reduced |
|---|---:|---:|---:|
| allocate-2 | 206.20 (11/11) | 206.22 (11/11) | 206.22 (11/11) |
| allocate-4 | 209.32 (11/11) | 209.33 (11/11) | 209.34 (11/11) |
| allocate-8 | 239.00 (11/11) | 239.01 (11/11) | 238.95 (11/11) |
| allocate-16 | 356.61 (11/11) | 356.73 (11/11) | 356.62 (11/11) |
| alias-2 | 205.12 (11/11) | 205.06 (11/11) | 205.13 (11/11) |
| alias-4 | 205.80 (11/11) | 205.81 (11/11) | 205.81 (11/11) |
| alias-8 | 208.00 (11/11) | 208.02 (11/11) | 208.02 (11/11) |
| alias-16 | 214.84 (11/11) | 214.79 (11/11) | 214.87 (11/11) |
| values-2 | 205.02 (11/11) | 204.94 (11/11) | 205.00 (11/11) |
| values-4 | 205.71 (11/11) | 205.49 (11/11) | 205.53 (11/11) |
| values-8 | 207.69 (11/11) | 206.99 (11/11) | 207.08 (11/11) |
| values-16 | 214.09 (11/11) | 211.77 (11/11) | 211.72 (11/11) |
| permutation-2 | 205.30 (11/11) | 205.33 (11/11) | 205.29 (11/11) |
| permutation-4 | 206.21 (11/11) | 206.22 (11/11) | 206.29 (11/11) |
| permutation-8 | 209.03 (11/11) | 209.11 (11/11) | 209.11 (11/11) |
| permutation-16 | 218.44 (11/11) | 218.44 (11/11) | 218.43 (11/11) |
| negative-2 | 205.05 (11/11) | 205.17 (11/11) | 205.07 (11/11) |
| negative-4 | 205.66 (11/11) | 205.72 (11/11) | 205.68 (11/11) |
| negative-8 | 206.84 (11/11) | 206.83 (11/11) | 206.91 (11/11) |
| negative-16 | 209.15 (11/11) | 209.22 (11/11) | 209.17 (11/11) |
| views-8 | 539.50 (11/11) | 528.91 (11/11) | 309.07 (11/11) |
| views-16 | 9493.59 (11/11) | 10627.88 (11/11) | 675.97 (11/11) |
| views-32 | 136271.52 (4/11) | 142014.61 (3/11) | 5148.97 (11/11) |
| views-64 | — (0/11) | — (0/11) | 22515.01 (11/11) |
| view_conflict-8 | 225.68 (11/11) | 222.22 (11/11) | 212.64 (11/11) |
| view_conflict-16 | 286.64 (11/11) | 279.03 (11/11) | 221.27 (11/11) |
| view_conflict-32 | 528.72 (11/11) | 513.05 (11/11) | 238.77 (11/11) |
| view_conflict-64 | 1496.44 (11/11) | 1463.56 (11/11) | 273.56 (11/11) |
| unasserted_views-8 | 546.70 (11/11) | 221.14 (11/11) | 218.18 (11/11) |
| unasserted_views-16 | 1690.53 (11/11) | 244.58 (11/11) | 229.65 (11/11) |
| unasserted_views-32 | 6440.44 (11/11) | 320.32 (11/11) | 255.45 (11/11) |
| unasserted_views-64 | 27424.37 (11/11) | 588.12 (11/11) | 310.72 (11/11) |

Millions of user instructions; median among completed runs. Partial Unknown costs excluded.

| Subset | Comparator | Shared pairs | Reduced / comparator cost |
|---|---|---:|---:|
| seeds-0-9 | baseline | 303 | 0.5620 |
| seeds-0-9 | redundant | 303 | 0.7701 |
| held-out-102 | baseline | 31 | 0.5123 |
| held-out-102 | redundant | 30 | 0.7987 |
| new-families | baseline | 114 | 0.1805 |
| new-families | redundant | 113 | 0.4675 |
| original-families | baseline | 220 | 0.9993 |
| original-families | redundant | 220 | 1.0001 |


## Distribution and mechanism

For `views-16`, baseline instruction counts range from 5.283 to 9.998 billion;
control ranges from 5.033 to 11.201 billion; reduced ranges from 0.632 to 0.793
billion. Its reduced/control median ratio is 0.0636 (15.7× less work), but the
seed-paired aggregate above is the primary comparison. At 32 views, baseline
solves 4/11 and control 3/11 while reduced solves 11/11. At 64 views neither
comparator finishes; reduced solves 11/11 using 13.314–22.768 billion
instructions. No cost speedup is assigned to those censored comparator runs.

The structural counters confirm the intended change. At 16 equivalent views,
comparisons fall from 120 to 15, definitions from 226 to 16, and post-check terms
from 4,576 to 1,321 versus control. At 64 partially asserted views, comparisons
fall from 2,016 to 63, definitions from 3,970 to 64 and terms from 38,490 to 3,336.
That case costs a median 588 million instructions for control and 311 million
for reduced. Its 27.4-billion-instruction baseline cost shows why a control is
needed: most of the raw baseline gain comes from introducing the anchor, with
an additional measured gain from removing redundant comparisons.

These cases pin locations with exact bounds and use four cells per heaplet.
The experiment does not establish gains for arbitrary location constraints,
large individual heaplets, or Boolean formulas lacking a positive unit. The
latter retain the original general encoding. No inductive predicates, fractions,
magic wand, proof exports or broader entailment support have been introduced.

## Missing measurements and immutable continuation

Four capped `views-32` cells produced empty perf/stdout/stderr files, stopping
the strict runner before it could store the result: baseline seed 3, control
seeds 2, 4 and 8. The frozen runner can reach its counter-reading call with empty
stdout only through its outer-timeout branch; otherwise JSON decoding fails
first. Each was therefore retained as **Unknown, unverified, unmeasured**. The
missing elapsed time is null. Zero is only the `unmeasured_region` schema sentinel,
never an instruction measurement. None contributes to a paired cost ratio.

`bench/heap_perf/resume_anchor.py` records this narrowly checked failure and
continues only untouched cells. It rejects other traces, nonempty evidence,
ambiguous interruptions and existing results. The executed supervisor is
archived with its hashes; the committed helper additionally rejects Python
`-O`, which was not used in this run. All completed records and raw files remain
unchanged. There are exactly 1,056 command files, result files and benchstore
records. The 37 total Unknowns are 18 baseline and 19 control; the four missing
captures are included in those counts, not additional failures. The final
Python suite, including recovery and reporting checks, passes **17 tests**.

## Provenance

Immutable records, inputs, exact commands, outputs, PMU coverage, binary hashes,
load samples and controller/recovery logs are under
`precompile/40851e3e/benchmark/`; the analyzer's output is in `analysis/` and full
landing-gate evidence is in `verification/`. Baseline driver:
`precompile/69250823/heap_perf`; candidate: `precompile/40851e3e/heap_perf`.
All runs used Rust 1.96.0, Python 3.13.14, perf 7.1.8, installed Z3 4.16.0 and
CVC5 1.3.4. These versions and hashes are also recorded per cell. Wall-clock
observations and externally capped partial counts are not improvement metrics.
