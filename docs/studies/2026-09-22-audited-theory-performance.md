# Audited theory APIs versus Z3: complete-trail snapshot cost

The newly audited FP conversion, set witness, arrangement search and decoded
array equality APIs are measured directly. The baseline is
`345ecfec01ae615b514452d68f61c6ff4b7b9b12`; the candidate is
`0d8032cc7eb591437a35393dc6240675478cd0cb`. The comparator is installed
**Z3 4.16.0, 64 bit**. The [registered protocol](../../bench/theory_perf/README.md)
defines the grid, acceptance bar, counter coverage and held-out inputs.

The change omits rollback copies of watch lists and long clauses when root
propagation has assigned every SAT variable. The lucky strategy sequence,
clause validation, assignments, counters, model construction and proofs are
unchanged. There is no speculative assignment to undo in that state. Partial
trails still take the original snapshots. This is an exact computation control
comparison, not a search heuristic experiment: the original implementation
performs the same work plus the unnecessary copies.

## Evidence and scope

Every measured process constructs its formula, checks SAT, pushes a
contradictory extension, checks UNSAT, pops and checks SAT again. Nixie validates
both witnesses inside the timed/counted process. Z3 evaluates FP/set/array
witness predicates and emits exact shared Real values; Python checks those
responses outside the counted process. This validation-cost asymmetry favors
Z3. Conversely, Z3 includes SMT-LIB parsing and fuller witness output whereas
Nixie uses its Rust API and prints only the three validated verdicts. Process
startup is included and significant on these small problems. These are API
workloads, not overall CLI speed or SMT competition results.

FP constants are asserted after requesting the symbolic circuit. Z3 may
simplify the complete formula before bit blasting. Set cardinality is represented
in Z3 by an exactly equivalent finite array: cardinality n with n distinct
required members fixes the entire set. Its complement is a cofinite array.
Arrays measure equality-atom decoding and chains, not store/select search.
Their SAT witness is the uniform array interpretation; the Rust driver checks
the decoded equality classes rather than extracting a full array model.
Arrangement cases force distinct shared Real values. Seeds vary declaration
order, FP inputs and rounding modes; they do not control hidden SAT random
seeds. No stochastic search-policy claim is made.

Primary cost is whole-process user instructions pinned to CPU 0. Every recorded
counter has 100% PMU coverage. Inspection of all 900 raw counter files confirms
that the generic `instructions:u` event resolved to exactly one counted
`cpu_core/instructions/u` row per cell; the atom-cluster row was not counted.
Thus the [unpinned hybrid-PMU trap](2026-09-22-fsm-perf-vs-z3.md) does not apply.
Wall time is diagnostic only. Immutable
raw transcripts, SMT-LIB, counters, hashes and per-cell records live under
`precompile/<revision>/benchmark/runs/audited-theories-z3/`; cached drivers,
manifests, locks and paired CSVs live under `precompile/<revision>/theory-perf/`.
The small diagnostic FP profile has 115 samples, zero lost; its percentages
locate a candidate, while whole-process counters determine the result.

## Held-out result

All **900 process cells** completed and validated: baseline, candidate and Z3,
each with 150 selection and 150 held-out cells. Each cell has three checks,
so this is 2,700 validated verdicts, with no Unknown, timeout or failed model.
The held-out FP instruction geomean is **0.9415 treatment/control** (5.85%
less work); selection independently gave 0.9415. The set geomean is 0.9417.
Arrays and arrangements remain within 0.1% of control. The registered 5%
target-family improvement bar and no-untargeted-regression bar both pass.

Ratios below are geometric means over ten held-out input seeds per row.
Lower is better. These are instruction ratios, not wall-clock speedups.

| Workload | Size | Candidate / control | Candidate / Z3 |
|---|---:|---:|---:|
| FP16 → FP32 | 1 conversion | 0.906 | 1.258 |
| FP16 → FP32 | 4 conversions | 0.975 | 3.723 |
| FP32 → FP16 | 1 conversion | 0.909 | 1.062 |
| FP32 → FP16 | 4 conversions | 0.976 | 3.146 |
| FP64 → FP32 | 1 conversion | 0.910 | 2.329 |
| FP64 → FP32 | 4 conversions | 0.977 | 6.349 |
| Finite/cofinite sets | 4 members | 0.958 | 0.177 |
| Finite/cofinite sets | 16 members | 0.939 | 0.430 |
| Finite/cofinite sets | 32 members | 0.929 | 0.480 |
| Arrangements | 3 terms | 0.999 | 0.095 |
| Arrangements | 5 terms | 0.999 | 0.220 |
| Arrangements | 7 terms | 1.000 | 0.470 |
| Array equality atoms | 16 terms | 1.000 | 0.045 |
| Array equality atoms | 64 terms | 1.000 | 0.033 |
| Array equality atoms | 256 terms | 1.000 | 0.021 |

The four-conversion cases benefit less: many contain a NaN, whose abstract
SMT-LIB result intentionally leaves some representation bits unconstrained.
Those trails still need rollback snapshots. The optimization does not remove
that requirement or assign a fabricated payload. FP remains the measured gap
against Z3; this change closes only the redundant-copy portion. Z3's formula
simplification advantage on inputs ultimately fixed to constants remains.
Do not interpret the small array/API ratios as a general array-solver advantage.

The paired CSVs retain every baseline observation and ratio. The report also
prints min/median/max baseline instruction distributions; no best-seed or
wall-time selection is used. Compiler/profile/lock/harness hashes are identical
between Nixie arms, and the same cases drive all three solvers.
The final example uses Clippy's equivalent `is_multiple_of(2)` spelling for
the sign parity test. Measurements use the frozen driver at `0d8032cc` and
its archived source/hash; reproduction commands reference that archived file.

## Soundness and trajectory review

The relevant reference is CaDiCaL `src/lucky.cpp`: uniform guesses first scan
clauses and skip assigned variables when making decisions. The Nixie port
additionally snapshots watches/clauses to preserve its search accounting.
The following layers were checked independently:

- Entry rejects non-root trails, external branching and existing contradictions;
  root propagation completes before testing whether all variables are assigned.
- The low-level trail append relies on the solver's uniqueness invariant:
  clause intake, binary/long propagation and incremental assignment guard
  appends with undefined-value checks; backtracking clears the corresponding
  value slots as entries leave. The solver exposes a read-only trail view.
  Its size therefore counts assigned variables, and a complete root trail
  leaves no variable a lucky strategy can decide. This is a caller invariant,
  not a duplicate-suppression check inside the low-level append primitive.
- Every lucky strategy skips assigned variables. Clause scans remain in place;
  no new SAT shortcut bypasses clause or model validation.
- Watch/clause mutations require propagation after speculation. With no new
  assignment, there is no such mutation; a failure backtracks to the same root.
- Partial trails retain the exact previous snapshot and restoration path.
- Push/pop, contradiction flags, model capture, proof emission and tick updates
  are unchanged. No new state persists across scopes.

A forced-snapshot control remains in unit tests. Across 64 assignments and
three initial trail-completeness levels (192 setups), tests compare results,
ordered clauses, trails, watch contents, all solver statistics, focused/stable
ticks and saved models, then repeat across a contradictory scope and pop.
All 60 FP selection workloads also have identical stdout and lucky conflict/tick
traces against the cached baseline; those diagnostic traces are preserved with
the candidate binary.

## Verification history

The first release workspace run built 389 test binaries and ran 12,347 tests:
12,345 passed, while `f4_and_buchberger_bases_agree` and
`odd_width_identity_pairs_hold` reached the 180-second external test limit.
No assertion failed. Release documentation and 114 doc tests passed. Z3 parity
had 176 decisive agreements, no wrong answer, and one inconclusive reference
answer (`array_unique`: Nixie UNSAT, Z3 Unknown).

Release Clippy exposed the pre-existing debug-only `check_fixpoint` probe;
main subsequently fixed its declaration's configuration in `42590d59`.
The integration includes that fix and main through `10d37a7d`. The full-LTO
workspace run on 2026-09-23 used four test workers and ran separately from
the other compilation gates, keeping all test assertions and cases intact.
All **12,365 tests passed**, with 18 existing skips. Both formerly timed-out
tests passed without changing their assertions or limits: F4/Buchberger in
63.114 seconds and odd-width BV identities in 53.988 seconds. The all-features
release build, Clippy with warnings denied, formatting and documentation
with warnings denied also passed. All 114 doc tests passed (31 existing
ignored examples). Z3 4.16.0 parity again had 176 decisive agreements,
zero wrong answers and the same single inconclusive `array_unique` reference.
The isolated performance comparisons above remain attributed to their recorded
revisions; unrelated merged graph, transcendental and array changes are not credited to
the snapshot optimization.

The initial 150-second performance gate printed PASS with identical counters
on eight search pairs, three propagation-only pairs and one jointly censored
pair. Its CLI path was mutable during concurrent Cargo compilation, so that
run is retained as **diagnostic only**, not landing evidence. The subsequent
600-second gate used an immutable default-feature CLI from `140c5aa1` against
canonical `28e82c65`: **12/12 decisive agreements**, no censored case, and
conflict/decision geomeans exactly **1.000** on all nine nontrivial pairs.
Binary hashes before and after agree; the three other pairs require no search.
The diagnostic wall geomean is 0.96. Logs and the frozen CLI are cached under
`precompile/140c5aa1ba31ec63cc1530cb70be31829096cd55/`.

While that run finished, main landed independently verified CP optimizations
through `39a258e1`. Integration `981c5e92` changes no SAT source relative to
`140c5aa1`. The combined tree passed another **12,368/12,368** tests, with
18 existing skips unchanged. Both original timeouts again passed without changing test
budgets (68.580 s and 58.875 s). The all-features release build, Clippy,
formatting, documentation and all 114 doc tests also passed. This additional
Nextest run uses release optimization level 3 with local
`CARGO_PROFILE_RELEASE_LTO=false` and
`CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16` in `target-verify`, following the CP
study's test-link setup. The production CLI, build, Clippy, documentation,
doctests and parity retain the normal workspace release profile. Neither
test-link setting changes the measured binaries or contributes to the reported
optimization gain.

Final integrated Z3 4.16.0 parity again reports **176 decisive matches, zero
wrong answers, one inconclusive**, with no timeout/error. The integrated
600-second perf gate also passes: 12/12 matching verdicts, no censored case,
and conflict/decision geomeans 1.000 on nine nontrivial pairs (diagnostic wall
1.01). Its default-feature CLI is byte-identical to the `140c5aa1` CLI:
SHA-256 `c3de762b12a12c93f7364854729df0402f9d5fe99228123fc9c7b88e8e2fba4e`.
Thus this second gate was redundant verification, not an independent cost
sample; it is retained separately and never pooled with the first gate or
the 900 instruction cells. Future integrations should compare binary hashes
before repeating a gate. The full integrated logs, manifests and binary are
under `precompile/981c5e92e625ffcba8c1383c3f5ebbfc64450f02/`.

Subsequent main updates merged through `842a1548` contain only CP benchmark
scripts and documentation. Solver source is unchanged; their five Python
tests and this harness's three tests pass. Final landing adds the report,
reproduction instructions and the equivalent Clippy spelling in the example.
