# Exact heap definition specialization: results and preregistration


**Verdict: retain the exact specialization in `6723d2ac`.** The fixed 660-cell
experiment completed with zero wrong answers. Specialization solved **220/220**
cases, versus **198/220** for both the current baseline and the identity control.
At negative sizes 8 and 16 it solved all eleven seeds each, where both comparison
arms hit the 20-second cap on every seed. For negative size 4, median complete
work fell from 388.24M instructions in the control to 243.11M (**37.4% less**).
This is a targeted improvement to exact-heap lowering, not a native SL procedure.

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

## Complete results

The measured candidate and preregistration are
`6723d2acb51543f78634209adaac0ee589509b33`; the baseline is `097ca4ad`.
All **616 decisive observations** passed schema proofs and, for SAT, independent
finite-map model validation. All 44 inconclusive observations were external
caps in the baseline/control negative-8/16 cells. None entered a cost ratio.
No cell was rerun, and no measured configuration or seed was selected afterward.

| Case | Baseline | Identity control | Specialized |
|---|---:|---:|---:|
| allocate-2 | 244.02 (11/11) | 243.97 (11/11) | 243.93 (11/11) |
| allocate-4 | 247.19 (11/11) | 247.23 (11/11) | 247.19 (11/11) |
| allocate-8 | 274.64 (11/11) | 275.28 (11/11) | 275.02 (11/11) |
| allocate-16 | 407.46 (11/11) | 409.09 (11/11) | 404.96 (11/11) |
| alias-2 | 242.82 (11/11) | 242.82 (11/11) | 242.79 (11/11) |
| alias-4 | 243.58 (11/11) | 243.54 (11/11) | 243.45 (11/11) |
| alias-8 | 245.54 (11/11) | 245.68 (11/11) | 245.65 (11/11) |
| alias-16 | 251.76 (11/11) | 252.61 (11/11) | 252.55 (11/11) |
| values-2 | 243.20 (11/11) | 243.07 (11/11) | 242.74 (11/11) |
| values-4 | 244.07 (11/11) | 244.05 (11/11) | 243.39 (11/11) |
| values-8 | 246.69 (11/11) | 246.81 (11/11) | 245.39 (11/11) |
| values-16 | 255.28 (11/11) | 256.05 (11/11) | 251.80 (11/11) |
| permutation-2 | 243.36 (11/11) | 243.35 (11/11) | 242.91 (11/11) |
| permutation-4 | 244.63 (11/11) | 244.67 (11/11) | 243.87 (11/11) |
| permutation-8 | 248.30 (11/11) | 248.52 (11/11) | 246.74 (11/11) |
| permutation-16 | 261.07 (11/11) | 261.98 (11/11) | 256.18 (11/11) |
| negative-2 | 253.45 (11/11) | 253.65 (11/11) | 242.61 (11/11) |
| negative-4 | 642.84 (11/11) | 388.24 (11/11) | 243.11 (11/11) |
| negative-8 | — (0/11) | — (0/11) | 244.06 (11/11) |
| negative-16 | — (0/11) | — (0/11) | 245.97 (11/11) |

Millions of user instructions; median among completed runs. Partial Unknown costs excluded.

| Subset | Comparator | Shared pairs | Specialized / comparator cost |
|---|---|---:|---:|
| seeds-0-9 | baseline | 180 | 0.9235 |
| seeds-0-9 | identity | 180 | 0.9112 |
| held-out-101 | baseline | 18 | 0.9761 |
| held-out-101 | identity | 18 | 0.9725 |
| negative | baseline | 22 | 0.5542 |
| negative | identity | 22 | 0.4991 |
| positive-families | baseline | 176 | 0.9899 |
| positive-families | identity | 176 | 0.9890 |

### Distributions, control, and limitations

The [complete CSV](2026-09-22-heap-definition-optimization.csv) records all sixty
case/arm groups, including minima, maxima, RSS and encoding diagnostics. At
negative-4 the baseline ranged **274.34M–4,503.28M** instructions; the identity
control ranged **275.40M–5,948.95M**; specialization ranged
**242.98M–243.35M**. Its negative-8/16 medians were 244.06M/245.97M, including
translation, process startup, two Rust model-validation passes (the mandatory
check plus the benchmark's explicit extra call), output and Python validation.
The roughly 242M Python/startup floor means these ratios are not kernel speedups.

All forty-four specialized negative cases emitted **zero heap definitions**,
with zero conflicts and decisions. Their post-check term counts were 15, 27,
51 and 99 at sizes 2, 4, 8 and 16. The negative-4 control emitted sixteen
definitions and reached 669 terms. This directly confirms elimination of the
irrelevant arithmetic; merely moving construction into `check` cannot explain
the complete-work measurement. Pre-check term counts alone are not comparable
across eager and deferred implementations.

The identity control matches staging, unit discovery, configuration and scope
lifecycle. Identity substitution preserves the unspecialized semantics; exact
substitution changes the generated SAT graph and therefore can change search
trajectories. The control cannot match the work and graph eliminated by the
transformation. This study does not establish a general heuristic advantage or
attribute all individual-seed differences to useful work removed.

Positive-family costs were essentially neutral: geometric mean specialized /
control **0.9890** across 176 pairs, with all solves retained. There are real
per-seed regressions: `allocate-16`, seed 6, costs **1.372×** the control
(**1.376×** baseline). Its case median is 404.96M versus control 409.09M; the
alias-16 median is 0.31% above baseline. Do not advertise a universal speedup.
The held-out seed 101 has a 0.9725 paired overall cost ratio versus control on
its eighteen shared solves, smaller than the 0.9112 ratio across seeds 0–9;
it also recovers both previously capped large negative cases. No claim of a
precisely estimated small effect follows from eleven seeds.

The corpus asserts individual heap literals and therefore exercises the unit
specialization directly. Arbitrary Boolean contexts with no syntactically
entailed units retain the general pairwise encoding and its search limits.
Worst-case encoding complexity remains O(n²k²); integer/backend resource and
model-validation Unknown boundaries, lack of heap proof export, and exclusion
of inductive predicates and fractional ownership remain unchanged. The CVC5/Z3
performance cells from the preceding study were reused as historical reference
evidence, not rerun or combined with these different-revision paired ratios.

## Reproduction and retained evidence

Linux 7.2.2, Intel Core Ultra 7 265K, CPU 2; Rust 1.96.0, Python 3.13.14,
perf 7.1.8. The unchanged measured worker SHA-256 is
`243cbf58c0ce2e1bc612bc755980264ee929af458c81470329b73831ed863d57`.
The manifest retains binary hashes and reference versions (CVC5 1.3.4,
Z3 4.16.0). Every cell used one counted instruction PMU with >=99.9% coverage.
Full inputs, outputs, command/environment records, manifest and summaries are
under `precompile/6723d2ac/benchmark/heap-definition-specialization-v1/`;
immutable records are under
`precompile/6723d2ac/benchmark/runs/heap-definition-specialization-v1/`.
Verification logs and calibration inputs are in
`precompile/6723d2ac/benchmark/heap-optimization-verification/`.
The baseline sampling diagnostic is retained under the baseline's cache.

Regenerate the report without running a solver:

```sh
python3 bench/heap_perf/analyze_optimization.py \
  precompile/6723d2ac/benchmark/runs/heap-definition-specialization-v1 \
  precompile/6723d2ac/benchmark/heap-definition-specialization-v1/analysis
```

The report reader was corrected after measurement to obtain driver diagnostics
from the paired immutable raw result: benchstore deliberately omits stdout from
secondary metrics. Two regression tests protect that join and reject mismatched
counts or missing candidate diagnostics. All nine Python checks pass. No solver,
worker, measured cell, or Rust source changed in this reporting correction.
