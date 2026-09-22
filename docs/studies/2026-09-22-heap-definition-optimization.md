# Exact heap definition specialization: preregistration

The preceding [heap experiment](2026-09-22-exact-heap-performance.md) found
expensive arithmetic search on negated heaplets. This experiment starts from
`097ca4ad4773f27acd37927afbf567b616b38acd`, including the intervening EUF rollback
and arithmetic environment-probe improvements. Those upstream gains must not be
attributed to the heap change. Read-only reference inspection: CVC5
`src/theory/sep/theory_sep.cpp` full-effort active-assertion/refinement handling,
and Z3 `src/smt/smt_relevancy.cpp` Boolean relevance propagation and scoped state.
A sampled baseline negative-4 profile points to simplex pivot/row work; sampling
counts are diagnostic, not the primary complete-work measurement.

## Transformation and soundness obligations

Register heap atoms immediately, but install their definitions in a private
backend scope at check time. Original assertions remain active. Walk their
original Boolean DAG to extract only entailed units: true conjunctions, false
disjunctions, and negation. Substitute forced heap atoms by their constants in
all definitions. Thus the original assertions imply equivalence of specialized
and original definitions. In particular, when all heap atoms are forced false,
all guarded definitions are tautologies. The existing larger finite-heap witness
and independent original-formula validator remain mandatory.

Do not descend through true disjunctions or false conjunctions. A false atom's
validity and map comparison remain necessary when paired with a possibly true
atom. Contradictory inferred units fall back to symbolic definitions; the backend
must establish UNSAT. Before assert, user push, or successful user pop, remove the
private scope. Repeated checks reuse it. This changes neither the supported
fragment nor proof support, budgets, branching, or restart policies.

## Fixed experiment, before comparison measurements

* Reuse the original twenty inputs: allocate, alias, values, permutation and
  negative at sizes 2, 4, 8, 16. Seeds 0–9 plus held-out seed 101, fixed now.
* Three arms, 660 total cells: current baseline; deferred definitions with
  identity substitution (`HEAP_PERF_UNFOLDED=1`); deferred definitions with exact
  specialization (default). The identity control performs the same unit scan
  and scope lifecycle. This separates Boolean simplification from staging and
  assertion-order effects. Report treatment/control, alongside baseline
  distributions. It cannot equalize the work eliminated by simplification.
* Use the original unchanged Python worker and independent model validator,
  whole-process `instructions:u`, CPU 2, one counted PMU with >=99.9% coverage,
  fixed hash seed, identical optimized symbolized Rust profiles, original solver
  budgets and 20-second external cap. Rotate arm order by seed. Wall time is
  secondary only. No adaptive seeds, cases, configurations, or reruns.
* Every decisive result must satisfy the original schema proof and SAT witness
  checks. Unknown is inconclusive. Report completion and only shared decisive
  pair ratios, with medians/min/max across seeds; report seed 101 separately.
  Reuse existing CVC5/Z3 evidence; do not rerun those immutable performance cells.
* Desired result: recover all negative-8/16 solves and remove at least 5% of
  complete work relative to the identity control on shared negative cases.
  Report positive-family regressions and lost solves, even if the target wins.
  Do not infer a native SL procedure, list segments, or fractional permissions.
* Deferred construction shifts work from the old `encode` region into `solve`;
  phase counts cannot establish net improvement. This experiment measures total
  work only. Structural tests require zero definitions for all-negative inputs.
* Retain commands, inputs, binary hashes, counter coverage, raw outputs and
  immutable benchstore records under `precompile/<candidate>/benchmark/`.
  Publish the result after full verification, parity and the perf landing gate.

## Layers reviewed

* Typed handles and the original arena remain separate from generated terms.
  The unit walk uses both polarities in its visited set and an explicit stack;
  arbitrary disjunctions are not treated as unit assertions.
* The finite-map reduction retains both directions of each pair constraint.
  Only substitution justified by active original assertions removes terms;
  false/false pairs have no active antecedent. No permission semantics change.
* Backend `assert` encodes arithmetic eagerly, which explains why the old
  false guards still incurred simplex work. The optimization acts before this
  encoding seam, rather than trusting search to avoid irrelevant arithmetic.
* Backend `push`/`pop` journal assertion, term/variable, parsed-arithmetic and
  Tseitin entries. The private scope uses this existing rollback seam; its
  lifetime cannot cross an assertion mutation or user scope boundary.
* Model extraction still completes missing integer variables explicitly and
  validates the original formula with exact integers and concrete finite maps.
  No generated definition, search counter, or inferred unit certifies SAT.
* Exhaustive ground and symbolic heap patterns run through both substitution
  modes; dedicated regressions cover mixed map equality, Boolean choice,
  contradictory shared nodes, repeated checks, and nested scope rollback.

## Verification before measurement

All-feature build, Clippy (all targets, warnings denied), formatting, and rustdoc
(warnings denied through repository configuration) passed. Full nextest:
12,211 passed, 17 skipped, four test threads. Separate doctests: 114 passed,
31 ignored. Both heap reduction modes passed the small exhaustive oracle;
CVC5 **1.3.4** independently agreed on all 832 reference cases. Z3 **4.16.0**
parity: 176 decisive agreements, one inconclusive (`array_unique`, Z3 Unknown),
zero wrong answers. Ten size-three driver calibration cases passed independent
validation and are excluded from the measured matrix. Seven Python harness
checks passed.

The first performance-gate run passed but overlapped the parity build replacing
the CLI executable (same source, different Cargo feature unification). It is
retained as diagnostic evidence only. A frozen final CLI is used for the final
landing gate. Both benchmark drivers are built with exactly
`CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0 CARGO_PROFILE_RELEASE_STRIP=none
cargo build --release -p nixie-solver --example heap_perf`; binary hashes are
retained with the experiment. The heap benchmark uses frozen copies too.

The frozen-binary performance landing gate passed against baseline `097ca4ad`:
conflict and decision ratios both **1.000**, nine core cases and three external
extensions, no changed verdict or lost solve. Its wall ratio was 0.95 (secondary
only). No search heuristic or general solver source was changed.
