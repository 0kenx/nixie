# Repairs for the 2026-09-22 theory implementation audit

This change addresses all twelve findings in
[the audit](2026-09-22-theory-audit.md). The original report and its observed
outputs remain historical evidence. Regressions with the corrected semantics
live in `nixie-theories/tests/audit_theory_soundness.rs`.

## Repairs and remaining completeness limits

| Finding | Repair |
| --- | --- |
| F1 | Polite combination checks an entire candidate arrangement in a scoped EUF probe, interns terms to obtain actual node IDs, and returns `Unknown` when the candidate is rejected. Candidate assumptions and conditional conflicts cannot escape. |
| F2 | Model-based combination uses the same complete arithmetic-witness arrangement, including disequalities. A combined `Sat` requires both theories to accept the arrangement. |
| F3 | Ground FP conversions use the existing exact rounding engine. Symbolic cross-format conversions return `Unknown` until their circuits are implemented. Identity conversion uses abstract FP equality, including distinct encodings of NaN. |
| F4 | Set operations and relations remain active after insertion. Pointwise membership propagation reaches a fixed point through trailed updates. Every accepted finite candidate is checked against all relations and cardinalities. |
| F5 | Opaque set assertions remain unresolved and yield `Unknown`. The adapter also declines a conflict for which it cannot supply a justified TermId explanation. |
| F6 | Integer UTVPI checks parity on tight-edge reachability and adjusts feasible potentials to construct an integral model. |
| F7 | UTVPI weights are exact big delta rationals. Integer thresholds use floor/ceiling normalization; real strict inequalities retain their infinitesimal. |
| F8 | Constant UTVPI inequalities become source self-loops, including the strict-zero case. |
| F9 | Synthetic edges have a reserved identity distinct from every user constraint. Both algorithms initialize all graph components. |
| F10 | UTVPI bounds come from paths between complementary nodes with the required factor of two, not super-source potentials. Unbounded variables return `None`. |
| F11 | The array Theory adapter rejects opaque assertions it cannot decode. Explicit `intern`, `merge` and `assert_diseq` operations retain their semantics. |
| F12 | Array undo runs before node truncation. Pending axioms are restored from their actual scope snapshot after a scoped check consumes them. |

These are soundness repairs, not claims of new completeness. Candidate-arrangement
search is still incomplete; an incompatible arithmetic candidate returns
`Unknown`, not a claim that every arrangement fails. The set solver validates
finite witnesses and declines unresolved cardinalities or cofinite/complement
models. Symbolic cross-format FP conversion remains explicitly unsupported.
The standalone public APIs remain distinct from the main SMT dispatcher.

## Independent layers and additional defects repaired

UTVPI now uses `BigDeltaRational` edge weights and exact arithmetic throughout
relaxation, parity repair and model construction. This intentionally widens the
public `UtEdge::weight` and `UtConstraint::effective_bound` result types. Narrow
model/bound getters return `None` when an exact result cannot fit; the added
`get_value_exact` exposes arbitrarily wide rational witnesses. Every candidate
is independently evaluated against the original, unnormalized constraints.

SPFA enqueue counts are not accepted as conflict certificates: exceeding the
scheduling threshold falls back to Bellman–Ford. Negative-cycle and parity
conflicts return the complete active constraint set as a sound, nonminimal core.
This removes the old explanation reconstruction that guessed which of a binary
constraint's two edges was the predecessor. Popped constraints cannot enter cores.
Integer parity repair has a deterministic effort cap that returns `Unknown`.

The integer procedure follows Z3 `theory_utvpi_def.h`'s
`check_z_consistency`/`enforce_parity`: odd complementary potentials cannot lie
in one tight SCC; otherwise decrement a tight successor closure that excludes
the complementary node. Real model instantiation follows `compute_delta`.
All reachability walks use heap stacks. No external solver is linked.

Combination arrangement validation checks equivalence closure and disequality
consistency instead of counting pairs (which also used to underflow on an empty
interface). Exact arithmetic values determine the arrangement. Shared-term maps
and pending equalities are restored across scopes. Model access no longer
fabricates equality between every pair of shared variables; it exposes only a
validated candidate arrangement and invalidates it on mutation.

FP ground constants are assertions, never guesses extracted from a SAT candidate.
Their cache and term encodings are scope-consistent, and models are invalidated
on mutations, `Unknown` and `Unsat`. Missing operands and incompatible formats
cannot silently drop assertions. Unsupported wide formats are rejected before
calling narrow classification helpers. NaN constants constrain the abstract NaN
value rather than its arbitrary sign/payload; unary operations also leave that
sign unconstrained, so the satisfiable `x = fp.neg(x)` for NaN does not become a
bit-level sign contradiction. Separate regressions protect constant insertion,
identity conversion and unary operations. These semantics follow Z3
`mk_numeral`, `mk_eq` and `mk_neg` independently of the conversion implementation.
The underlying conversion engine is checked
independently against IEEE native casts and all five rounding modes at an exact
tie. Z3 `fpa2bv_converter.cpp::mk_to_fp_float` supplies the conversion semantics;
Nixie's existing `Ieee754Engine` supplies the ground arithmetic.

Set propagation uses the standard pointwise union/intersection/difference/
complement axioms, independently tested against finite-set evaluation. This
replaces disconnected propagators that were never given the inserted relations.
Negative subset remains existential rather than being incorrectly imposed on
every element. Equality notifications add persistent, trailed relations; scoped
term/name maps, conflicts and model state are also restored. Extreme cardinality
thresholds cannot wrap around at the i64 limits. These changes were checked
against CVC5's indexed upward/downward set-closure approach.

Array scope regressions separately exercise newly allocated nodes, nested merges,
and pending read-over-write axioms consumed during a scoped check. The opaque
assertion rejection does not weaken the genuine self-disequality conflict rule.

## Verification

The focused regression file contains 28 tests. Besides the original
counterexamples, it checks 250 bounded two-variable integer systems against
exhaustive enumeration through both UTVPI algorithms, verifies returned witnesses
and conflict cores, exhaustively checks binary set operations on a two-element
universe, and compares 512 ground FP conversion samples with native IEEE casts.
Z3 4.16.0 also independently confirms that two NaN encodings asserted on one
term are satisfiable, that a NaN can equal its negation and absolute value, and
that a finite nonzero value cannot equal its negation.

The first full run exposed an existing array-interface test that expected
undecoded assertions to be accepted. It now requires the explicit `Unknown`
error. The replacement full run passed 12,288 tests; a final run includes the
additional NaN constant/unary regression. An initial Clippy run also caught
Boolean-literal assertions in the new tests; those were corrected.

Final workspace gates (offline dependencies, eight build/test workers, debug
symbols and incremental compilation disabled to fit the isolated build):

| Gate | Result |
| --- | --- |
| `cargo build --all-features` | Passed |
| `cargo nextest run --workspace --all-features` | 12,289 passed; 17 default skips |
| Required ignored `pete_cxs_bp_is_unsat_on_every_trajectory` | Passed separately |
| `cargo test --workspace --all-features --doc` | 114 passed; 31 ignored; zero failures |
| `cargo clippy --all-features --all-targets -- -D warnings` | Passed |
| `cargo fmt --all -- --check` | Passed |
| `cargo doc --no-deps --all-features` | Passed with repository `rustdocflags = ["-D", "warnings"]` |

The final release parity run used **Z3 4.16.0 (64 bit)**: 176 decisive matches,
zero disagreements, and one unresolved comparison out of 177. The unresolved
`array_unique.smt2` case is Nixie `Unsat` versus Z3 `Unknown`; it is not counted
as a match.

The performance landing gate passed against pinned baseline `28e82c65`:
conflict and decision geometric-mean ratios were both **1.000** across all nine
core benchmarks. The three available external cases also preserved their
verdicts and were trivial at the selected counters. The auxiliary wall ratio
was 1.02; deterministic counters are the primary evidence. No heuristic change
or claimed speedup is involved.

The final release rebuild produced the exact binary already measured by the
performance gate (SHA-256
`3f98e335db06936775afff4bb75cf7d5ca91b535fb1ff42d28fee4272c6d3fef`),
so that result was reused without rerunning the same cells. The NaN repairs
affect standalone library paths eliminated from the CLI binary; they are
covered by the final workspace tests. Raw verification logs and the ignored
parity JSON are retained beside the landed commit's cached binary.
