# Generated CP instances checked by an independent exhaustive oracle

This extends the evidence for the Boolean CP user-propagator interface landed
in `9af45a71`. It adds tests, not a new filtering algorithm, search heuristic,
or proof exporter. The implementation remains trusted; the checks below are
bounded executable evidence, not a machine-checked proof for arbitrary inputs.

## Construction and independence

`nixie-solver/tests/cp_oracle/spec.rs` describes finite-domain instances and
checks **concrete assignments** without calling any CP feasibility method.
The generator uses fixed integer PRNG seeds, never time or process randomness.
It creates 40 instances for each of five globals and 40 conjunctions of three
globals, plus four explicit boundary fixtures: **244 instances** total.

Each generated instance has zero to four variables, each with at most four
values. Values include holes, reverse insertion order, negative integers, and
positive/negative 131-bit integers. Tables vary their arity, allowed rows and
repeated variables. Automata have up to four states and fourteen transitions,
allow nondeterminism and repeated variables, and include empty words and
accepting-state sets. Circuits exercise aliases, empty/singleton graphs,
self-loops, four-node tours, and negative/oversized successor indices.
Scheduling covers repeated starts, zero durations/demands, negative capacity,
touching intervals, and wide starts, durations, demands, and capacities.

The oracle uses different computations from the filters:

| Global | Concrete oracle | Implementation being checked |
|---|---|---|
| `alldifferent` | Pairwise comparison of assigned values | Augmenting-path matching and forced-value support tests |
| `table` | Construct the assigned tuple, then test relation membership | Search compatible rows in partial domains |
| `regular` | Enumerate concrete automaton runs with an explicit stack | Partial-domain reachability and forced-symbol supports |
| `circuit` | Follow successors from node zero, visiting every node exactly once and returning to zero | Matching and forced-subtour checks |
| `cumulative` | Sum actual resource usage at each task start | Mandatory-part event sweep and candidate-start filtering |

For nonnegative demands, overload can first arise only at a task start, so
checking actual load there is sufficient. Zero-length intervals are empty;
negative capacity is infeasible even without tasks. Neither the timetable
filter nor its event-sweep implementation is reused in this oracle.

## What is checked

1. **Complete semantics.** Enumerate every assignment in each instance's
   Cartesian product. Fix all indicators and require the callback's decisive
   result to agree exactly with the independent predicate.
2. **Each emitted implication.** Require every antecedent to be currently true
   and every mentioned term to belong to the indicator vocabulary or Boolean
   constants. Check the implication against **every satisfying base assignment**,
   including those outside the current partial context. Restricting this check
   to the current context would let missing antecedents escape detection.
3. **Conflicts.** Treat a conflict as an implication to false and apply the same
   exhaustive check. Independently require that the current context has no
   satisfying completion.
4. **Nested rollback.** Mix positive fixations and negative value deletions in
   two nested scope levels. Check both branches and each restored parent. A
   stale reason from a popped branch cannot pass the current-truth check.
5. **Public solver integration.** Compare root and scoped solver verdicts with
   existence of an oracle solution, repeat unchanged checks, then pop and
   recheck the parent. Decode every returned Boolean model, require exactly
   one value per variable, and independently check all constraints and facts.
6. **Checker negative control.** Deliberately omit the `x=0` antecedent from
   `x=0 => y!=0` under `alldifferent(x,y)` over `{0,1}`. Although the current
   context hides the defect, the oracle must reject the purported unconditional
   conclusion using the base solution `x=1,y=0`.

## Measured focused coverage

The three tests pass:

| Quantity | Count |
|---|---:|
| Varied instances | 244 |
| Complete assignments checked directly | 6,704 |
| Callback states checked, including restored scopes | 37,810 |
| Emitted consequences/conflicts checked | 171,301 |
| Final-check conflicts among those states | 29,147 |
| Public solver verdict/model checks | 6,100 |

The 171,301 count includes repeated emissions and conflicts; it is **not** a
count of distinct lemmas. Every family has both satisfiable and infeasible
instances, asserted by the test: the respective counts are `18/22`, `16/24`,
`15/26`, `28/14`, `20/21`, and `3/37` for the five globals and conjunctions.
No oracle disagreement was found. The negative-control test passes by rejecting
the deliberately invalid explanation.

Reproduce the focused checks with:

```bash
cargo test -p nixie-solver --all-features --test cp_oracle -- --nocapture
```

These tests do not establish completeness or soundness at arbitrary sizes,
compare performance against OR-Tools, or independently certify a CP UNSAT proof.
They cover finite generated instances and the explicit boundary cases above.
The proof-producing/certified-mode limitation documented in [CP.md](../CP.md)
remains in force.

## Repository verification and the existing exception

The initial full run, based on `c824e9bf`, ran 11,853 tests: 11,852 passed,
one timed out, and 14 additional tests were skipped. The timeout was
`recfun_e2e::symbolic_argument_solves_for_the_variable`, the same existing
exception explicitly approved for the CP implementation landing.

While verification was running, `main` gained the simplex change in
`152e8326`. After integrating it, the full suite was repeated: 11,849 passed,
one failed, three timed out, and 14 were skipped. The additional failures
were investigated and rerun without changing solver code or test assertions:

| Test | Full-run outcome | Isolated outcome |
|---|---|---|
| `qfidl_qlock_11_base_is_unsat` | `Unknown` at its internal 20-second budget | UNSAT, passed in 4.542 s |
| `odd_width_identity_pairs_hold` | Nextest 180-second timeout | Passed in 134.389 s |
| `arith_incremental_matches_replay_fuzz` | Nextest 180-second timeout | Passed in 183.36 s, using the same workspace test executable under a 600-second external cap |

The first two rechecks used nextest with one test thread; the arithmetic
recheck invoked the existing workspace test binary with `--exact`. These
passes establish that the tests complete, but do not erase the full-run
timeouts or establish a runtime guarantee under load. The recursive-function
timeout remains unresolved and is the **only carried exception**. Its
independently recorded regression is described in the
[simplex handover](../handovers/2026-09-15-wisas-layer2-simplex-24cb0567.md).
The subsequent `ecbf96af` integration changes only that handover document.

The later finite-bag integration, `bedae910`, changes shared AST and solver
code, so the full gates were repeated on that revision as well. With four
test threads, the full suite ran **11,874 tests: 11,873 passed, one timed
out, and 14 additional tests were skipped**. Only the approved recursive-
function timeout remained; all three load-sensitive tests above passed in
this full run, as did all three new CP oracle tests.

Other checks, repeated on `bedae910`:

- `cargo build --all-features`: passed.
- `cargo clippy --all-features --all-targets -- -D warnings`: passed.
- `cargo fmt --all -- --check`: passed.
- `cargo doc --no-deps --all-features`: passed, with warnings denied by the
  repository's `rustdocflags` configuration.
- Workspace all-features doctests: 114 passed, 29 ignored. Cargo also reports
  the existing lack of doctest support for the WASM `cdylib`.
- Explicit `pete_cxs_bp_is_unsat_on_every_trajectory` model-validation
  canary: passed in 101.679 s (the earlier integrated run passed in 175.174 s).
- Z3 differential parity, repeated after integration, using installed
  **Z3 4.16.0**: 176 decisive agreements, zero disagreements, one inconclusive
  case (`array_unique.smt2`: Nixie UNSAT, Z3 `Unknown`). Unknown is not a match.
- Performance gate against pinned baseline `ac8279e5`, repeated on
  `bedae910`: passed; conflict and decision geometric-mean ratios both
  **1.000**, ten measured pairs and two trivial cases, no verdict changes.
  The secondary wall-time ratio was 0.95 under shared-host load; this is
  not evidence of a speedup. The earlier two gate runs also passed.

Builds used four Cargo jobs (three for parity), with debug information disabled
for the build/test profiles; the first two full nextest runs used eight
test threads and the last used four. The
host was heavily loaded. Raw logs, exit statuses, the parity JSON, and the
release binary are retained in the landing commit's ignored
`precompile/<commit>/benchmark/cp-oracle-verification/` result directory, with
the binary at `precompile/<commit>/nixie`. This is regression evidence,
not a CP speedup measurement.
