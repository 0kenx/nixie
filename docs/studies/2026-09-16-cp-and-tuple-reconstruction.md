# CP implementation verification and the tuple reconstruction blocker

The CP work adds a Boolean user-propagator adapter and finite-domain
`alldifferent`, `table`, `regular`, `circuit`, and `cumulative` constraints.
The interface, semantics, limitations, and layer-by-layer regression map are
in [CP.md](../CP.md).

## False UNSAT found by the full workspace suite

The existing TLA test
`structs::cardinality_of_a_pinned_set_variable_is_exact` failed before this
change. A clean build of parent `0163c3ab43194d68e8e69718e880cfeb43669567`
confirmed the wrong verdict; its `nixie-tla` binary is cached under that SHA.
The reduced SMT input is satisfiable:

```smt2
(set-logic ALL)
(declare-datatype Pair ((pair (@t1 Int) (@t2 Int))))
(declare-const s (Set Pair))
(assert (= s (set.union (set.singleton (pair 1 2))
                         (set.singleton (pair 3 4)))))
(assert (not (= (set.card s) 3)))
(check-sat)
```

The set contains exactly two different pairs. The old solver returned `unsat`.
The TLA counterpart pins `s = {<<1, 2>>, <<3, 4>>}` and asks whether
`Cardinality(s) = 3` is an invariant. It incorrectly reported no counterexample.

The root cause is the tuple-surjectivity reduction. It recognizes a tuple by
its `@t1`, `@t2`, ... selectors, including custom and TLA datatypes. It then
used `mk_tuple` to rebuild each element and asserted equality to the original.
`mk_tuple` constructs the canonical `@tuple{...}` datatype, which is a
**different nominal sort** from `Pair` or `@tla{...}`. Equal field shapes do
not justify that equality. The fix resolves the original declaration's
constructor and rebuilds at the original sort, following typed constructor
selection in CVC5's `src/theory/datatypes/tuple_utils.cpp::concatTuples`.

Independent layers examined:

- TLA lowering correctly creates two distinct integer pairs, their singleton
  union, a set equality, and the negated cardinality equality. The same failure
  reproduces through SMT-LIB without TLA.
- The datatype declarations correctly intern constructor and selector names in
  the term manager. The defect is not the previously fixed interner mismatch.
- Tuple recognition intentionally includes structurally shaped custom
  datatypes. Recognition does not establish nominal type equality.
- `mk_tuple` correctly creates a canonical tuple; `mk_dt_constructor` preserves
  the supplied declaration and sort. The reduction called the wrong builder.
- Surjectivity now preserves constructor, field order, and sort. A direct
  reduction regression checks newly generated equalities for sort agreement,
  independently of downstream simplification and solver decisions.
- Counting uses membership and pairwise equality to avoid duplicates; the two
  concrete pairs differ in their integer fields. Integration regressions
  require `sat` for cardinality two and for cardinality unequal to three,
  and `unsat` for cardinality three.
- The original TLA regression remains unchanged and exercises the complete
  lowering/reduction/decision path. Existing assertion-scope tests continue
  to cover reduction replay and rollback.

The correction is confined to reconstruction in the same datatype; it does
not change the semantics of relation operators that construct new tuple types.

## Verification context

Checks run in an isolated checkout to exclude another worker's uncommitted SAT
kernel experiment. Test builds use `CARGO_PROFILE_TEST_DEBUG=0`, retaining
optimization level 1, assertions, and all features while omitting debug symbols.
The isolated checkout was fast-forwarded to `bc8254bc` to include the separately
landed simplex rollback fix before the final verification run.

The initial full suite ran 11,846 tests: 11,843 passed, the TLA test failed,
and two tests hit the 180-second timeout. The arithmetic incremental fuzz test
passed directly in 157 seconds. The recursive-function test
`symbolic_argument_solves_for_the_variable` is a previously documented
nonconvergence problem, not an environmental timeout:
[existing investigation](../handovers/2026-09-15-wisas-xs-8-13-unknown-regression.md#addendum-2026-09-15-late-ff-arc-agent-the-recfun-timeout-is-not-environmental--and-it-is-layout-correlated-not-monotone).
No test is disabled or weakened in this change.

## Final verification, 2026-09-16

| Check | Result |
|---|---|
| `cargo build --all-features` | Pass |
| Full workspace/all-features nextest run | 11,848 passed, one test-fixture failure subsequently corrected, one pre-existing timeout; 14 skipped |
| Focused final regressions | Four passed: direct reconstruction, SMT cardinality, original TLA cardinality, independent model-reason validation |
| Model canary `pete_cxs_bp_is_unsat_on_every_trajectory` | Pass, 107.8 s |
| `cargo clippy --all-features --all-targets -- -D warnings` | Pass |
| `cargo fmt --all -- --check` | Pass |
| `cargo doc --no-deps --all-features` | Pass; repository rustdocflags enforce `-D warnings` |
| Workspace/all-features doctests | 114 passed, 29 ignored, zero failed |
| Z3 differential parity | Z3 **4.16.0**; 176 decisive agreements, zero wrong verdicts, one inconclusive (`array_unique.smt2`: Nixie `unsat`, Z3 `unknown`) |
| Performance landing gate vs cached `f5796de0` | Pass; conflict and decision geomeans **1.000**, ten comparable cases and two trivial cases; unchanged verdicts |

The first version of the direct reconstruction test used membership in a
singleton, which the term builder simplified to equality before reduction;
there were no set axioms to inspect. The final fixture uses equality to a set
variable and passes while exercising actual reconstruction. No production
change was needed for that fixture correction. After its focused rerun,
11,849 distinct tests have passing evidence; the sole outstanding test is
`recfun_e2e::symbolic_argument_solves_for_the_variable`.

The arithmetic replay fuzz passed in the final full run (166.1 s). The
recursive-function case hit the standard 180 s cap, and a separate bounded
900 s test run also produced no verdict. Release probes of the preceding CP
candidate and cached baseline `f5796de0` both timed out at 180 s. This is the
standing nonconvergence issue linked above; it is not counted as a pass and
its test has not been disabled, weakened, or given a fabricated result.

The final release candidate's SHA-256 is
`2dcaed0cbd88700e0340ffb1ac1b3c9354263fb755d2fb9ed0412afb27177804`.
The verified binary is cached under `precompile/<landing-commit>/nixie`;
raw verification logs, parity JSON, reproducers, and the review patch are
retained alongside it under `benchmark/cp-verification/`. Wall-clock gate
data is preserved in the raw log but is not evidence of a performance improvement.

The user explicitly approved landing with the documented pre-existing
recursive-function timeout as an exception to `AGENTS.md`'s clean-suite bar:
"Land with documented exception." This approval does not mark the timeout as
passing or waive any other check. All remaining checks above passed.
