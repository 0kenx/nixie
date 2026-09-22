# Exact heap performance experiment: preregistration

This suite measures the implemented `HeapSolver` API, which reduces exact integer
heaplets to LIA and Boolean constraints. It is **not** a native separation-logic
procedure, and has no list-segment (`ls`) or inductive-predicate support. See
[the fragment specification](../../docs/HEAP.md). No search heuristic is changed;
these cross-solver comparisons describe implementations, not a causal heuristic
improvement. A matched-null experiment would be required for a heuristic claim.

Before looking at measurements, fix the following design:

* Five families, sizes 2, 4, 8, 16, seeds 0 through 9 for every cell. Allocation is
  satisfiable: n distinct nonzero addresses, each bounded to [1,n], store i in
  address variable i. Aliasing adds equality of the first and last address and is
  unsatisfiable. Conflicting values asserts two exact heaps with the same address
  expressions but different final values, and is unsatisfiable. Permutation
  asserts an exact heap and the negation of its reversed cell order, and is
  unsatisfiable. Negative asserts the negations of n four-cell heaplets, with
  separate unconstrained variables, and is satisfiable using a five-cell heap.
* Four arms: Nixie's exact-heap API, CVC5 native SL, CVC5 UF+arrays, Z3 UF+arrays.
  These are 800 total-work cells. No adaptive case/seed selection. Arm order
  rotates by seed independently of results. Nixie's additional encode/check
  regions at sizes 2 and 16, and extra validation regions on satisfiable cases
  at those sizes, add 240 cells. Total: 1,040.
* All locations/values are integers, nil is fixed to zero, heaps are finite
  partial functions and ownership is exclusive. No fractional permissions.
  Reference SL uses `declare-heap`, `pto`, `sep` and external Boolean negation.
  The UF+array baseline represents the domain by an array of Bool and data by an
  uninterpreted Int-to-Int function. A heaplet equates the domain with exactly
  its stores over constant false, requires nonzero distinct addresses, and
  constrains stored values. Global domain[0] is false. If all heaplets are false,
  reconstruct a finite heap larger than all heaplets; do not treat an arbitrary
  infinite array model as a heap. A positive heaplet fixes the finite domain.
* Primary cost: retired user-space instructions (`perf stat -e instructions:u`),
  pinned to CPU 2, one counted PMU, >=99.9% event coverage. Measure the complete
  pipeline: Python input translation, child process startup, solver encoding,
  search, model extraction and independent Python validation, plus destruction.
  This covers costs missed by conflict/propagation counters. It includes a
  Python/startup floor, so small-case ratios are not solver-kernel speedups.
  Nixie's extra native regions use acknowledged perf control FIFOs: encoding
  includes reading input/building the API constraints; check includes built-in
  model construction and independent validation; validation measures an *extra*
  validation call, not a disjoint component of check. FIFO control overhead is
  present; the driver checks perf's five-byte `ack\n\0` protocol. Python
  hashing is fixed with `PYTHONHASHSEED=0` in measured workers. Inherited
  `NIXIE_*` tuning overrides are cleared. Optimized Python (`-O`) is rejected
  so it cannot disable the independent checks. Do not add these regions and call the result total work.
* Report solved counts and median/min/max instructions across ten seeds. Unknown
  and timeout are never matches and their partial costs never enter completed
  cost aggregates. If a cap prevents a later measured region from being reached,
  record `unmeasured_region` with a zero placeholder, never a completed zero-cost
  observation. Only compare ratios on shared decisive case/seed pairs.
  Report encoding term counts, search counters, and child-process peak RSS as
  secondary diagnostics. RSS can include the inherited Python process floor.
  Host load averages are recorded before and after each cell. Wall time is
  secondary only, never a search-policy input.
* Fixed solver budgets: Nixie 10,000 conflicts / 100,000 decisions and no internal
  time limit; CVC5/Z3 2,000,000 resource units. A 20-second external safety cap
  (plus 3 seconds for interrupt cleanup) produces an inconclusive observation.
  CVC5 uses `--arrays-exp` for constant arrays. Resource units are **not** equivalent across solvers. Report completion, not
  a rank based on unequal budgets; exclude capped costs from speed ratios.
* Every decisive result is checked against a schema proof authenticated by the
  entire generated input. SAT models additionally pass a separate finite-map
  evaluator. UNSAT families have elementary proofs (duplicate ownership,
  contradictory function values, and H AND NOT H). CVC5 1.3.4 does not support
  `--check-models` for SL: extract its actual `(heap ...)` model and check it here.
  Array arms reconstruct a finite witness from evaluated heaplet truth values.
  This is a performance corpus, not a replacement for the exhaustive fragment
  correctness suite in `nixie-solver/tests/heap_separation.rs`.

## Running and retaining results

Build `cargo build --release -p nixie-solver --example heap_perf`. Run the harness
unit checks with `python3 -m unittest discover -s bench/heap_perf -p 'test_*.py'`.
From a committed clean checkout, run:

```sh
python3 bench/heap_perf/run.py run \
  --driver /absolute/path/to/heap_perf \
  --cvc5 /absolute/path/to/cvc5 --z3 /absolute/path/to/z3 \
  --store /absolute/path/to/nixie/precompile
```

Requires Linux perf permissions, taskset and CPU 2 (override `--cpu` before the
experiment if needed). The runner records exact binary hashes, Git revision,
reference versions, seed, flags, machine identity and counter coverage via
`benchstore.py`. Full logs, immutable input cases, commands, counters and the
manifest live under `precompile/<sha>/benchmark/heap-exact-v1/`; the result-store
records live alongside them. Existing cells are reused. Interrupted cells are
retained for investigation and never silently rerun. The final summary can be
regenerated from records with `analyze.py RECORDS_DIRECTORY OUTPUT_DIRECTORY`. Raw per-host runs are not committed; the study commits
aggregate results and their limitations. No later tuning belongs to this suite.

The Rust driver's numeric input format is `vars N`, followed by `heap K` with K
location-variable-index/value pairs, `bound INDEX LO HI`, `eq INDEX INDEX`, and
`assert HEAP_INDEX 0|1`. Define heaplets before checks/scopes. This is a benchmark
format, not new public SMT-LIB syntax. Model walks and the reference-output
S-expression parser use explicit stacks.

## Harness landing verification (2026-09-22)

Before measuring: all-feature build, 12,205 nextest tests (17 skipped), 114
passed doctests (31 ignored), Clippy with warnings denied, formatting and rustdoc
with warnings denied all passed. Nextest used four test threads. An earlier run
on the preceding main revision timed out one existing scope-rebase test during
concurrent release compilation; the complete integrated rerun passed, including
that test at 299.729 seconds. No test or timeout setting was changed.
Z3 **4.16.0** parity: 176 decisive agreements, one inconclusive (`array_unique`,
Z3 Unknown), zero wrong answers. The performance landing gate against the cached
heap-feature commit `97b2b968` passed: conflict and decision ratios both 1.000
(nine core cases plus three external extensions). Seven Python harness checks
and twenty size-three cross-solver calibration checks passed. These calibration
cases are excluded from the measured matrix. Calibration also established the
required CVC5 constant-array option and perf's NUL-terminated FIFO acknowledgement.

## Definition specialization comparison

`compare_optimization.py` runs the fixed baseline / identity-substitution /
specialized matrix specified in
[the optimization preregistration](../../docs/studies/2026-09-22-heap-definition-optimization.md).
Pass `--baseline` and `--driver` absolute binary paths, plus the same reference
and store options as above. The measured `run.py worker` is unchanged; reference
versions are recorded but reference performance cells are reused from the prior
study. The candidate driver's `HEAP_PERF_UNFOLDED=1` selects the diagnostic
identity control. `definitions COUNT TERMS` reports active definition assertions
and post-check term count; the old `sizes` line remains pre-check and therefore
excludes deferred definition construction. Compare complete-work counts.

After completing that matrix, run `analyze_optimization.py RECORDS_DIRECTORY
OUTPUT_DIRECTORY` to check its exact 660-cell coverage and write the full
median/min/max table, structural counters, and paired cost ratios. Seed 101 is
reported separately from seeds 0–9. Unknown results never enter paired costs.

## Positive-heap anchor comparison

`anchor_experiment.py` runs the fixed baseline / retained-pair control /
reduced-encoding experiment in the
[anchor preregistration](../../docs/studies/2026-09-22-heap-anchor-reduction.md).
It accepts the same baseline/driver/reference/store options as the earlier
comparison. The driver uses `HEAP_PERF_ANCHOR_REDUNDANCY=1` for the control;
`comparisons COUNT` reports actual map-comparison construction calls.
The worker wrapper adds authenticated many-view schemas and calls the existing
independent checker. No old measurements are rerun.

`analyze_anchor.py RECORDS_DIRECTORY OUTPUT_DIRECTORY` requires the complete
1,056-cell matrix and paired raw results, and writes cost distributions,
comparison/definition counts, and shared-solve ratios. All ratios exclude
Unknown costs and report the fresh held-out seed 102 separately.

The completed anchor study reports 53.3% less work than its retained-pair control
on new shared decisive pairs, with neutral original-suite cost; see the study
for held-out results, distributions and capped cases. `resume_anchor.py` handles
only the documented empty-counter timeout interruption, retaining it as an
unmeasured Unknown and continuing untouched cells. It never reruns a cell or
infers a missing instruction count. Its exact executed version and recovery
evidence are archived beside the original records.
