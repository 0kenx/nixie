# Theory implementation audit, 2026-09-22

Audited revision: `1c9a2ef8` (`perf(heap): keep eager Boolean default after
controlled replay`). **Twelve confirmed findings**, eleven affecting soundness
or theory inference and one causing a panic. These are findings, not fixes.
Production source is unchanged.

## Scope and exposure

This is a targeted audit of the exported `nixie-theories` implementations,
particularly UTVPI, FP conversion, sets, arrays and theory combination. It is
not certification of every theory, operation, proof path or input size. Existing
finite-field and graph edits in the shared checkout were excluded; all executable
probes were built from the committed revision in an isolated worktree.

Searches for `UtvpiSolver`, `SetSolver`, `FpSolver`, `ArraySolver` and this crate's
`TheoryCombiner` found **no callers in `nixie-solver/src`**. The confirmed exposure
is the public Rust library API. These results do not demonstrate that the CLI
returns the same wrong answers. `nixie-core::theories::TheoryCombiner` is a
separate implementation and must not be conflated with the one audited here.

## Reproduction

The complete executable source is [probe.rs](2026-09-22-theory-audit/probe.rs).
It prints observed results without treating a wrong answer as a passing
regression test. Its temporary placement under `examples/` was removed after
execution; it is deliberately not installed as a test that expects defects.

From a disposable checkout of the audited revision, with these audit artifacts
available:

```sh
mkdir -p nixie-theories/examples
cp docs/studies/2026-09-22-theory-audit/probe.rs nixie-theories/examples/theory_audit.rs
cargo run --offline -p nixie-theories --example theory_audit
```

[probe-output.txt](2026-09-22-theory-audit/probe-output.txt) records the output.
The semantic oracle is [oracle.smt2](2026-09-22-theory-audit/oracle.smt2), run with
installed **Z3 version 4.16.0 - 64 bit**:

```sh
z3 --version
z3 docs/studies/2026-09-22-theory-audit/oracle.smt2
```

All twelve oracle checks produced their stated expected verdicts; see
[oracle-output.txt](2026-09-22-theory-audit/oracle-output.txt). These are semantic
counterparts, not a claim that the Rust APIs parse SMT-LIB or that a CLI parity
suite was run. The array rollback panic is demonstrated only by Rust.

## Confirmed findings

### F1 — P1: Polite combination promotes a candidate arrangement to a theorem

Location: `nixie-theories/src/combination.rs:356–377`.

Intern two unconstrained real variables in arithmetic and EUF; assert their
EUF disequality. `check_polite_combination()` returns `Unsat([TermId(10)])` even
though `x=0, y=1` satisfies the problem. The arithmetic candidate happens to
assign both zero. Its equality is then asserted permanently in EUF, and rejection
of that one candidate is reported as rejection of the original problem.

Politeness does not make every arrangement compatible with existing literals.
Search arrangements using justified interface literals, or return `Unknown` when
the candidate is rejected. Scope candidate assumptions separately. There is an
additional indexing hazard at lines 365/368: `TermId::raw()` is used as an EUF
node ID. The reproducer deliberately uses IDs 0 and 1 matching their interned
node IDs, so the wrong answer is independent of that hazard.

### F2 — P1: Model-based combination ignores arrangement disequalities

Location: `nixie-theories/src/combination.rs:750–777`.

With `CombinationMode::ModelBased`, assert `x=0`, `y=0` in arithmetic and `x!=y`
in EUF. `check()` returns `Sat`. The arrangement correctly contains the
disequality, but only its equalities are asserted into arithmetic; arithmetic's
`Sat` is then returned as a combined result. The comment calling this an
"honest" limitation does not supply an `Unknown` gate.

Check the complete arrangement, including disequalities and any required case
splits, before returning `Sat`. Until implemented, unresolved disequalities
must prevent a combined satisfiable verdict.

### F3 — P1: Cross-format FP conversion constrains only special cases

Location: `nixie-theories/src/fp/solver/mod.rs:827–843`.

Assert binary32 `x=1.0`, convert it to binary64 `y`, and assert `y=2.0`.
`FpSolver::check()` returns `Sat`. The nonmatching-format branch equates signs
and adds implications for NaN, infinity and zero. For ordinary positive finite
numbers every special-case antecedent is false, leaving the magnitude free.
The unsupported-conversion flag used by other conversions is never set here.

Implement exponent/significand conversion and rounding, or mark this conversion
unsupported so the final check cannot accept its unconstrained result. This
example is exact widening and cannot be explained by a rounding-mode difference.

### F4 — P1: Set relations are snapshots rather than persistent obligations

Location: `nixie-theories/src/set/solver.rs:750–779`, `1104–1171`; related subset
insertion at `666–689`.

Declare two sets, assert disjointness while both have no known members, then
assert `1` belongs to both and give each cardinality 1. `check()` returns
`Ok(true)`; both reconstructed sets are `{1}`. Disjointness only propagated the
members present when it was inserted. Although the original constraint is saved
in `constraints`, the check does not validate that list against a model.

The same architectural problem exists in subset/equality insertion: there is
no insertion into `subset_constraints`, which the propagator actually reads.
Negated subset insertion has an empty semantic branch. Preserve each relation,
propagate it to a fixed point after later mutations, and validate all constraints
before accepting a model. Determined cardinalities alone are not satisfiability.

### F5 — P1: Set Theory assertions are accepted but never processed

Location: `nixie-theories/src/set/solver.rs:1292–1308`.

On an empty `SetSolver`, call `assert_true(p)`, `assert_false(p)`, then
`Theory::check()`. The result is `Sat`. Both polarities are stored in
`pending_assertions`; its only other uses are initialization, truncation and
clearing. An empty variable list vacuously passes the cardinality-only check.

Implement assertion decoding with access to term structure, or return an error
or `Unknown` for unresolved assertions. This is independent of F4: no set
relations or variables are needed to reproduce it.

### F6 — P1: Integer UTVPI omits integer consistency and model construction

Location: `nixie-theories/src/utvpi/solver.rs:185–188`, `463–479`.

In integer mode, add `x+x<=1` and `-x-x<=-1`. Both SPFA and Bellman–Ford return
`Ok`, and `get_value(x)` returns `1/2`. The doubled graph is feasible over the
rationals, but the original integer system is not. The integer flag only
influences strict-bound adjustment; neither check nor model extraction enforces
integrality.

Implement the integer parity/SCC consistency step and an integral model procedure.
Rejecting fractional candidate models alone is insufficient to prove `Unsat`:
other inputs can have an integral solution even when one candidate is fractional.

### F7 — P1: UTVPI strict bounds are wrong over both reals and rational thresholds

Location: `nixie-theories/src/utvpi/graph.rs:129–135`.

Over reals, `x<0` and `x>=0` return `Ok` with either engine because strictness is
silently discarded. In integer mode, `0<=x<1/2` returns a conflict even though
`x=0` is a witness: subtracting 1 changes the upper bound to `-1/2`.

Represent real strictness exactly, e.g. with infinitesimal weights. For integer
left-hand sides normalize strict rational thresholds with `ceil(c)-1` and
nonstrict thresholds with `floor(c)`, using exact arithmetic. Fixing F6's parity
check would not fix either input transformation here.

### F8 — P1: UTVPI drops contradictory constant constraints

Location: `nixie-theories/src/utvpi/graph.rs:367–369`.

`add_general(0, Zero, 0, Zero, -1, reason)` represents `0<=-1`; both engines
return `Ok`. The branch says to check the bound but performs no check and adds
no graph edge. A negative constant must create a justified conflict; real strict
`0<0` also needs consideration independently of graph reachability.

### F9 — P1: Popping the first UTVPI constraint deletes synthetic source edges

Location: `nixie-theories/src/utvpi/graph.rs:232–247`, `451–457`.

Create `x`; push; add the first constraint; pop; then assert `x<=0` and `x>=1`.
Default SPFA returns `Ok`. Bellman–Ford on the same sequence returns a conflict.
All synthetic source edges carry `constraint_idx=0`, which aliases the first
real constraint. Popping that constraint removes those edges too. SPFA seeds
only the now-isolated source and visits none of the contradictory component.

Give synthetic edges a distinct identity, preserve them across pop, and ensure
consistency checking covers every component. Bellman–Ford's independent
initialization masks the damaged source connectivity; changing engines alone
would not repair the scope invariant.

### F10 — P1: UTVPI exports model potentials as entailed bounds

Location: `nixie-theories/src/utvpi/solver.rs:499–518`.

After creating an unconstrained real variable and checking consistency,
`get_lower_bound(x)` and `get_upper_bound(x)` both return `Some(0)`. There is
no such entailed bound; `x=10` is a valid assignment. Super-source distances are
feasible potentials, not implied absolute variable bounds. This also occurs
with Bellman–Ford and before any push/pop, independently of F9.

Compute bounds using the appropriate paths between complementary nodes, with
correct scaling, or return `None` when no bound is entailed. Consumers must not
use current model choices as theory propagations.

### F11 — P1: Array negative assertions manufacture self-disequalities

Location: `nixie-theories/src/array/solver.rs:583–587`.

`Theory::assert_false(eq_term)` interns the equality term itself and calls
`assert_diseq(node, node, eq_term)`. The next check returns `Unsat` for every
negative assertion. In particular, two unconstrained integer-indexed arrays can
differ, so `not (= a b)` is satisfiable.

Decode the equality's two operands and register their disequality, or reject
opaque assertions that cannot be interpreted. The public `assert_diseq(a,b,…)`
primitive correctly detects a self-disequality; the adapter supplies the wrong
operands, so changing the primitive would mask the defect rather than fix it.

### F12 — P2: Array pop indexes nodes it has already truncated

Location: `nixie-theories/src/array/solver.rs:619–630`.

Intern `a`; push; intern `b`; merge `(a,b)`; pop. `pop()` panics on an
out-of-bounds parent access. The merge trails `b`'s parent, then pop truncates
`parent` to its pre-push length before replaying that trail entry.

Undo parent mutations while all trailed nodes are still allocated, then truncate
scoped nodes and dependent tables. The probe catches the panic solely to let
other audit cases finish; catch-unwind is not proposed as a solver fix.

## Layers examined and reference evidence

- **Shared primitives:** inspected UTVPI graph translation/source initialization,
  rational strict-bound conversion, FP bit encodings and array union-find merge
  trailing. F7–F10 and F12 have independent primitive/state causes.
- **Decision procedures:** checked both UTVPI engines and integer model extraction;
  F6 reproduces with both. Read Z3 `src/smt/theory_utvpi_def.h`, especially
  `check_z_consistency`, `enforce_parity`, `mk_weight`, and `init_model`.
- **FP transformation and validation:** traced `assert_const`, `new_fp`,
  `assert_fp_to_fp`, the unsupported-conversion flag and `check`. Read Z3
  `src/ast/fpa/fpa2bv_converter.cpp::mk_to_fp_float`, including its ordinary finite
  conversion/rounding branch, not only special values.
- **Set propagation and model acceptance:** traced constraint insertion,
  propagator inputs, pending assertions, determined-cardinality check and model
  extraction. Read CVC5 `src/theory/sets/theory_sets_private.cpp`,
  `checkDownwardsClosure` and `checkUpwardsClosure`, which revisit indexed
  operations and memberships.
- **Combination:** traced arrangement extraction, both equality/disequality
  lists, candidate insertion and final results. Read Z3
  `src/smt/smt_context.cpp::assume_eq`: candidate interface equalities become
  Boolean atoms in the search instead of unconditional facts.
- **Scope:** separately reproduced UTVPI source-edge removal and array undo order.
  A control probe showed that directly inserted set cardinality bounds *are*
  restored on pop; it returned `Ok(false)` after adding a member to the now
  unbounded set, rather than a stale cardinality conflict. This does not certify
  equality notifications or all other set scope state.
- **Explanations and validation:** array self-disequality explains why the adapter
  yields an immediate conflict. Polite combination loses the status of candidate
  assumptions. The inspected arithmetic/array checker implementations return
  `Unknown` for unsupported nontrivial certification; they are not invoked by
  these direct APIs and therefore do not prevent these wrong answers. A small
  UTVPI sum-conflict probe returned both required constraints (one duplicated);
  that control does not certify the general cycle reconstruction algorithm.
- **Callers and exposure:** searched workspace callers and checked the main
  solver sources as described under Scope. No end-to-end CLI defect is claimed.

The investigation did not stop at the first UTVPI or set defect: each separate
case is preserved so a future outer-layer `Unknown` gate cannot hide the
primitive defect when its regression is added.

## Validation limits and remediation order

The probe built and executed on the audited revision. The existing theory unit
suite also passed:

```text
cargo test --offline -p nixie-theories --lib --all-features
1700 passed; 0 failed; 0 ignored
```

Those existing tests do not exercise the counterexamples above. No production fix,
performance change, or new solver binary was made, so no correctness landing or
performance verdict is claimed. The workspace-wide build/nextest/clippy/doc,
full differential parity, and perf landing gates were not run for this
report-only change; they remain required before landing fixes.

Prioritize F1–F11's wrong verdicts/unsupported inference. Implement independent
regressions with the correct expected semantics next to each affected API,
including both engines and incremental state for UTVPI. Repair F12's rollback
ordering and add the scoped-new-node test. Keep the distinction between public
library exposure and the main solver's independent implementation when
reporting fixes or expanding differential testing.
