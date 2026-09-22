# Heap anchor reduction: preregistration

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
