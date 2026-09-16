# LIA on wide integer literals: a panic at `i64::MAX`, `Unknown` beyond — and, underneath, a false `sat`

**Status:** FIXED (all layers), 2026-09-13/14. Regressions in
`nixie-solver/tests/arith_wide_literal_regressions.rs`,
`nixie-core/src/ast/manager/builder.rs` (`arith_folding_tests`),
`nixie-theories/tests/mixed_integer_mode.rs`, and the strengthened
`nixie-tla-check` encode tests.
**Found by:** the TLA+ front end's encoder cross-check
(`nixie-tla-check/examples/encodecheck.rs`), 2026-09-13.

## Summary of the four defects

| # | Input | Expected | Was | Root layer |
|---|---|---|---|---|
| 1 | `(9223372036854775807 + 1) = 9223372036854775808` | `unsat` | **panic** in `num-rational` (abort in release) | fixed-width accumulator in the linear parse |
| 2 | `(18446744073709551615 + 1) = …` | `unsat` | `Unknown` | same + no exact fold |
| 3 | `(26 div 2) = 13` | `unsat` | `Unknown` | default arithmetic solver in real mode refuses `div`/`mod` axioms |
| 4 | `x:Int ∧ x>3 ∧ x<4` | `unsat` | **`sat`** (x = 3.5!) — found while fixing 3 | default arithmetic solver in real mode: no integrality at all |

Defects 1–3 were the TLA front end's report. Chasing 3 turned up 4, which is
the serious one: a wrong answer, not a gap. It was reachable from the bare
`Solver::new()` API (the TLA encoder's path), from `ALL`, and from an
explicit `(set-logic QF_LIRA)` — every configuration where the arithmetic
solver ran `ArithSolver::lra()` while the problem contained `Int`-sorted
terms.

## The layer analysis (what was actually wrong, at each depth)

Per AGENTS.md the fix had to name every layer along the path, not the one
nearest the crash. Layers examined, innermost out:

1. **The linear-parse accumulator** (`extract_linear_terms`,
   `parse_arith_comparison`). Sums/updates in `Ratio<i64>`: `i64::MAX + 1`
   panicked in debug and **silently wrapped in release** (the workspace
   `[profile.release]` has no `overflow-checks`) — the wrap is a
   wrong-coefficient, wrong-verdict hazard, strictly worse than the panic.
   Fixed: every step is now checked (`CheckedAdd/CheckedSub/CheckedMul`);
   overflow fails the parse *and* records the atom in
   `arith_parse_overflow`, which the honesty gate
   (`arith_atoms_need_theory`) turns into `Unknown`. Without the record the
   failed parse would leave the atom a free Boolean — the exact
   wrong-verdict shape the gate exists for, and *invisible* to the
   structural scan (every leaf fits `i64`; only the folded sum does not).

2. **Term construction** (`TermManager::mk_add/sub/neg/mul/div/mod`). There
   was no constant folding at the builder at all, so `(+ MAX 1)` reached
   layer 1 as two separately-fitting literals. Fixed by Z3's
   `arith_rewriter` policy at mk-time: integer sums/products/quotients fold
   exactly in `BigInt` (partials collected to one numeral — `(+ x 1 2)`
   becomes `(+ x 3)`); reals fold in `BigRational`, kept only when the
   result is representable as the `Rational64` a `RealConst` stores (never
   approximated); `div`/`mod` fold **Euclidean** (`div_euclid`/`rem_euclid`)
   — the same semantics `arith_axioms` asserts, so folder and axiomatiser
   cannot disagree; a zero divisor never folds (SMT-LIB: uninterpreted).
   This alone fixes defects 1–3's literal cases (`(div 26 2)` never survives
   construction) and hands layer 1 at most *one* numeral per `Add`.

3. **The arithmetic solver's integrality regime** (`ArithSolver`). The
   solver had a single global `is_integer` flag: `lra()`/`lia()` chosen from
   the *declared logic*, with `Solver::new()` defaulting to `lra()`. Every
   `Int`-sorted term interned into a real-mode tableau was a continuous
   variable — that is defect 4 — and `instantiate_arith_axioms`' integer-mode
   gate (correctly) refused to axiomatise `div`/`mod` there — that is
   defect 3. Fixed with Z3's three-way split (`theory_lra` / `theory_lia` /
   **`theory_mi_arith`**): a new `Mixed` mode with **per-term integrality**
   (`intern_integer` from every registration site that can see the sort),
   now the default for `Solver::new()` and for every `spec.arith` logic the
   contract table records as non-integer (QF_LRA is behaviorally identical —
   a pure-real formula marks nothing integer; QF_LIRA/NIRA keep `Int`
   variables exact). Per-row reasoning that previously trusted the global
   flag is now per-row: `assert_lt/gt`'s `k-1`/`k+1` tightening fires only
   on integral rows *with integral rhs* (the old unconditional LIA tighten
   was itself unsound for fractional rhs), `assert_eq`'s GCD block only on
   integral rows, `value()` rounds per-variable, and
   `interned_int_vars` (which claimed to return integer variables but
   returned *all* of them — a latent mixed-mode unsoundness in the
   branch-and-bound) filters on the integer set.

4. **The mark's lifecycle.** Per-term integrality first landed as a mark on
   the tableau *variable*; the theory layer's `reset()`+replay (restarts,
   scope rebasing) re-interns terms through sort-blind `assert_*` paths, so
   the mark silently vanished and defect 4 briefly survived its own fix.
   Integrality is a property of the *term* (its sort), so it now lives in a
   term-keyed registry (`int_terms`) that survives tableau rebuilds.

5. **Callers/consumers audited for the same assumptions.**
   `parity_lemma` (mod-2 rows over integral coefficients) needed a
   per-column integer-sort guard — under mixed mode a row like
   `x:Int = f(y:Real)` has integral coefficients but a parity-less real
   column. `cached_row_slack*`'s slack-integrality now derives from the
   per-variable set. `set_logic`'s nonlinear fallback routes reals to mixed
   (NIRA). `emit_big_const_distinctness` and the big-const certification
   gate are unchanged in behavior (columns stay continuous — the
   abstraction argument is unchanged). `Solver::check()`'s
   `arith_atoms_need_theory` gate gained the overflow consult described in
   layer 1.

## Why the release build mattered more than the panic

The panic (`debug-assertions` on) was the *visible* symptom. In the release
profile the same `Ratio<i64>` arithmetic compiled to wrapping ops: no abort,
no error — a constraint with a wrapped constant is simply a *different*
constraint, answered with full confidence. Any fix that only de-panicked
(checked arithmetic that bails, say) without the gate would still have been
correct; any fix that only widened the accumulator would have left the wrap
in release. The checked-accumulate-then-gate fix is what makes release
sound, and it is why the residual class (defect-1 shapes hidden behind
non-foldable nesting) answers `Unknown` rather than a verdict.

## Verification

- `nixie-core` builder folding: exact `BigInt` sums/products/negations,
  Euclidean `div`/`mod` on all four sign combinations and the
  `(i64::MIN, -1)` corner, zero-divisor non-folding, real exactness-or-refusal.
- `nixie-solver` regressions: all four defects end-to-end, plus the
  mixed-mode soundness twins (a `Real` variable between adjacent integers
  stays `sat`; `x:Int = 1/4`-forcing mixed rows are `unsat`) and the
  residual overflow class gated to never-`Sat`.
- `nixie-theories`: mixed-mode unit tests (integer hole `unsat`, real
  interval `sat`) and the full pre-existing LIA/LRA/NLA suites.
- Full workspace: `cargo nextest run --workspace --all-features` —
  11,124 tests green; `cargo test --doc` green; clippy `-D warnings` clean;
  `cargo fmt --check` clean; `cargo doc -D warnings` clean.
- **Z3 differential parity** (z3 4.16.0): 175 benchmarks, **0
  disagreements**, 174 decisive agreements (1 unresolved: Z3 itself
  `Unknown` on `array_unique.smt2`) — `bench/z3_parity/run_parity.sh`.

## Continuation (2026-09-14): the follow-up differential fuzz and what it found

A targeted random differential against z3 over the changed surface (mixed
Int/Real formulas, `div`/`mod`, strict inequalities, wide constants; 1,300
instances, models validated via z3 on nixie-`sat`-vs-z3-`unknown` splits)
found **zero verdict disagreements and zero refuted models** — but chasing
the `unknown` gap it measured turned up four more defects, all fixed the
same day:

5. **`/` was `div`.**  The parser routed SMT-LIB `/` (real division,
   `Real`-sorted result even over `Int` operands) through the integer
   constructor whose sort came from the *lhs*: `(/ 7 2) = 3` answered
   **`sat`** and `(/ 7 2) > 3` answered **`unsat`** — both wrong (the
   truth is `7/2`).  Fixed with a dedicated `mk_rdiv` (`/` semantics:
   `Real` result, exact quotient folding, reciprocal linearization
   `(/ x c) ≡ (* x (1/c))` for numeral `c` — Z3's `arith_rewriter` policy),
   and parse-time sort checks: `div`/`mod` require `Int` operands (the
   standard-mandated error, matching the existing bit-vector width rule;
   z3's silent `to_int` coercion is nonstandard and deliberately not
   imitated).
6. **Mixed `Int`/`Real` sums were sorted by `args[0]`.**  `(+ xi yr)` was
   `Int`-sorted while `(+ yr xi)` was `Real`-sorted — one value, two
   labels, and the `Int` label feeds integer-only row reasoning a row
   whose value can be fractional.  Fixed: the arithmetic builders unify
   the operand sorts (`Int` unless an operand is `Real`, per the
   standard's subsort rule).
7. **Mixed numeric comparisons/equalities did not fold.**  `3.5 = 3`
   survived as a structural atom; `mk_eq`/`mk_lt`/`mk_le`/`mk_gt`/`mk_ge`
   now fold `Int`/`Real` numeral pairs as exact rationals.
8. **The model certifier could not certify `div`/`mod` or ground goals.**
   The big-constant `sat` honesty gate accepts a model only through
   `model_certify`, which (a) had no `Div`/`Mod` vocabulary and (b)
   blanket-refused quantifier-free goals — so any ground goal carrying a
   wide constant answered `unknown` on the `sat` side however good its
   model (`(> (+ (mod (+ x 2^63) 3) y) 2)` among them).  The evaluator
   gained exact Euclidean `div_euclid`/`rem_euclid` arms (zero divisor
   declines — uninterpreted per SMT-LIB), the harvest admits `Div`/`Mod`
   children (as `Position::Value`, so a *bound variable* under a division
   still rejects — the region-enumeration argument does not hold for
   `div`'s jumps), and ground goals certify by evaluating the assertions
   under the recorded model.

Measured effect of 5–8 on the fuzz gap: `unknown`-where-z3-decides fell
from 54% to 31%; the remainder is symbolic real division (`(/ x y)` —
honestly gated: the defining identity is nonlinear) and hard disjunctive
instances that exhaust the conflict budget (both sound).

Verification for 5–8: full workspace suite (11,216 tests), doc tests,
clippy/fmt/rustdoc gates clean, Z3 parity 0 disagreements (177 benchmarks),
differential bench with model validation 0 disagreements / 0 invalid
models, and the 1,300-instance random differential above.  Regressions in
`nixie-solver/tests/arith_wide_literal_regressions.rs` (the `/`-vs-`div`
semantics pair, mixed-sort pins, ill-sorted parse errors, ground
certification) and the builder folding tests in `nixie-core`.

## Continuation 2 (2026-09-14): the residual class chased to the tableau wall

The documented residual (constants assembled across nesting that overflow
only in the parse) got its principled treatment, and the chase found two
more live defects on the way:

9. **The constant pipeline is now exact.**  `extract_linear_terms`
   accumulates constants in `BigRational` end-to-end (levels, `Mul`
   const-products, the parse total): constant arithmetic can no longer
   overflow, panic (debug), or wrap (release) at any nesting.  Only
   COEFFICIENT arithmetic can still gate (`narrow_rational64` at the `Mul`
   finalize and the combine loop).  A final constant too wide for
   `Rational64` synthesizes as a wide `IntConst` COLUMN — the existing
   big-constant abstraction — registered with the honesty gate and the
   distinctness pass exactly like a wide literal (the synthesis must run
   BEFORE the big-const scan; landing it after was a false-`sat` bug the
   fuzz caught in minutes).  The `-2^63` corner (fits `i64`, its negation
   does not — `row_key`/DL normalization flip it) travels sign-flipped as a
   `+2^63` column; `narrow_rational64` rejects `i64::MIN` numerators
   everywhere it is used.  `record_prop_bound`'s bound division is checked
   now (propagation is an optimization; declining is sound — unchecked, it
   wrapped in release and propagated a fabricated bound).
10. **Empty-row fractional equalities were silently dropped.**  An
    equality whose coefficients all cancel (`xr - xr`) leaves an EMPTY
    row; with a fractional constant (`0 = 5/3`) the infeasibility planted
    its crossed bounds only on `expr.terms.first()` — which an empty row
    does not have — so the constraint vanished and the atom stayed a free
    Boolean: **`sat` for `0 = 5/3`**.  Both plant sites (the
    fractional-constant branch and the GCD branch) now use a witness
    variable when the row is empty.  Found by the fuzz once `/`
    linearization made constant-folded dividends under `(/ x 3)` produce
    exactly this shape.
11. **The wall, precisely located.**  What stays honestly `Unknown` is the
    *value-dependent refutation over constants ≥ 2^63*: proving
    `(= (+ x i64::MAX 1) (+ x 2^63))` needs row combinations and column
    values AT `2^63`, which leave `Rational64` width inside the simplex
    itself.  Scaled pin rows (`λ·C = λ·v`) encode the exact meaning with
    representable coefficients, but the LP's pivot arithmetic still
    overflows computing the derived values — the boundary is the
    tableau's fixed width, not the encoding.  Z3 decides these because
    its tableau computes in `mpz`.  Moving Nixie's LP to exact arithmetic
    is the (large) fix; until then the honest answer is `Unknown`, never a
    wrapped verdict.

Verification for 9–11: 11,259 workspace tests, all gates clean; Z3 parity
0 disagreements; differential bench with model validation 0 disagreements,
88/88 models valid; 2,400 fresh fuzz instances across six seeds (the two
seeds that found the bugs among them) clean.

## Continuation 3 (2026-09-14): the boundary arithmetic, checked and scaled

Two more members of the fixed-width family, plus a decidability extension:

12. **The strict-inequality tightening `k ± 1` was unchecked** — in
    `assert_lt`/`assert_gt` AND in the case-split bound computation
    (`compute_int_bounds`).  At `k = i64::MAX`, `MAX + 1` is a debug panic
    and a SILENT WRAP to `i64::MIN` in release — a *different constraint*
    than the one asserted (`-x > i64::MAX`, satisfiable at `x = -2^63`,
    could wrap into `-x ≥ MIN`, trivially true — a false-verdict hazard,
    and a live debug abort).  Both sites are checked now; an unshiftable
    bound falls through to the exact delta-rational representation, which
    handles strict bounds at any width.  Found by fuzzing the *debug*
    binary (overflow-checks on): every remaining unchecked site panics
    there, making the hunt mechanical — 1,200 debug-mode fuzz instances
    now run panic-free.
13. **Row scaling at the parse boundary.**  A linear row scaled by a
    nonzero rational `λ` has the same solution set, so before falling back
    to the big-constant column abstraction the parse now tries
    `λ ∈ {1, 1/2, 1/4, …} ∪ {-1, -1/2, …}` (flipping an ordered
    comparison when `λ < 0`): a row whose constant leaves `i64` width in
    one orientation is often exactly representable in another.  `-x >
    i64::MAX` becomes `(-1/2)·x > 2^62` — all parts in range, DECIDED
    (`sat` at `x = -2^63`, agreeing with z3) where the answer was
    `unknown`.  The column synthesis and the honesty gate remain the
    fallback when no orientation fits.

Verification: 11,273 workspace tests, all gates clean; Z3 parity 0
disagreements; differential with model validation 0 disagreements, 88/88
models valid; 1,200 debug-mode + 1,100 release-mode fuzz instances clean
(seeds that previously found bugs included).

## The debug-panic oracle, swept over the corpora

The technique from item 12 — fuzz the DEBUG binary, where overflow-checks
turn every silent release wrap into a loud abort naming its site — was
swept over everything available, not just the random generator:

* the Z3 parity corpus (177 benchmarks): **0 panics**, all 177 decided;
* the 270-instance pinned differential sample (QF_ANIA/AUFNIA/BV/LRA/
  NIA/UFLIA...): **0 panics**;
* the extended-theories corpus (43 files): **0 panics** (the two nonzero
  exits are honest logic-contract rejections of nonlinear-under-AUFLIRA
  input, not crashes).

490 corpus files + 1,200 generator instances, panic-free: the unchecked
fixed-width hunt is converged on every surface we can currently throw at
the solver. The sweep ships as
`bench/differential/debug_panic_sweep.py` so the next theory that grows
boundary arithmetic can re-run it in one command.

## Continuation 4 (2026-09-14): the oracle stratified over SMT-LIB, and inside the simplex

The debug-panic oracle, stratified over a 615-file sample of
`smt-lib/non-incremental` (40 per logic family, seed 20260915), found three
panics — two unchecked sites inside the simplex, one canary in the SAT core:

14. **`update_assignment` multiplied unchecked** (`mul_r64_fast`'s
    non-integer fallback): a product/sum that left `Rational64` width
    PANICKED in debug (QF_NIA/VeryMax reproducer) and silently WRAPPED in
    release — a corrupted assignment vector the pivots then reasoned over.
    Fixed with checked accumulation plus an EXACT fallback: an i64 overflow
    mid-sum retries that one row in `BigRational` and narrows the final —
    intermediates legitimately overflow while the final fits (denominators
    cancel), so the retry recovers completeness — and only a final that
    still does not fit sets `resource_limit`, the existing honest-`Unknown`
    channel.  `check`/`pivot`/`on_nonbasic_bound_change`/`state_feasible`/
    `dual_simplex` all bail on the flag before deciding or propagating.
    Same pattern for the delta-propagation sums (`delta_acc` +
    `derive_bound_exact`): operands are given bounds and reasons are IDs,
    so an exact final that fits is a sound bound.
15. **Two canaries recorded for their owners** (deliberately left loud):
    * `QF_NIA/.../From_T2__streamserver...` still trips the delta-vs-full-
      re-evaluation `debug_assert` in `pivot` (got ≠ want with compounding
      pivot denominators ~3^16): the canary for arithmetic that leaves
      representable range inside the LP's incremental bookkeeping — the
      named entry point for the wide-LP project.
    * `AUFLIA/20170829-Rodin/smt3878551918658299427` (and one sibling)
      trips `debug_verify_model_input` (`learn.rs`): an intermediate `Sat`
      candidate whose assignment violates an ORIGINAL clause — the CDCL(T)
      fixpoint gap class that assert exists to catch.  SAT-core territory;
      reproducer recorded here for the owning agent.

Release verdicts on both canary instances are `unknown` before and after
(no regression, no fabricated verdict); the fixes remove the aborts and
the wrapped-arithmetic exposure.

Verification: 11,330 workspace tests, all gates clean; Z3 parity 0
disagreements; differential with model validation 0 disagreements, 88/88
models valid; 1,200 fuzz instances clean; the stratified SMT-LIB sweep's
two hard panics gone.

## Continuation 5 (2026-09-14): the Rodin canary root-caused — a disabled guard and an invalid-model snapshot class

The `debug_verify_model_input` trips on `AUFLIA/20170829-Rodin/
smt3878551918658299427` were chased to two findings in the SAT core:

16. **`trail_falsifies_live_clause` was dead code for CDCL(T).**  The
    guard that checks a `Sat` candidate's trail against live clauses
    before `save_model` returned `false` unconditionally once the caller
    had ever `push`ed — and the CDCL(T) layer (the path's main consumer)
    always scopes.  The bypass existed because LEARNED clauses from
    popped scopes fire it spuriously; but ORIGINAL clauses are never
    retracted, and a trail falsifying one is an invalid candidate under
    any scoping history.  Fixed: originals are scanned unconditionally,
    learned clauses only in never-pushed sessions (preserving the old
    strictness where it was sound).  On the Rodin family this turns the
    invalid-model exit into an honest `Unknown` (the refinement loop
    retries, so those instances get slower — they were `unknown`-class
    already); on any instance whose upstream lacks a model-certification
    gate it converts a printed INVALID WITNESS into `Unknown`.
17. **The invalid-model snapshot class itself (open, SAT core).**  The
    instrumented trace shows the failing save_model snapshotting a trail
    state whose var (505 in the probe) disagrees with the trail the
    search validated, across theory-refinement rounds: the last write
    came from `trail.value` at save time, yet the panic-time trail reads
    the opposite — the candidate the search accepted and the candidate
    snapshotted diverge through the final_check/rejection/re-entry cycle.
    Full probe data (per-save var values, BIG edge presence — both edges
    live, `pure=[]`, `ext_stack` empty, clause flags
    `(deleted=false, learned=false, len=2)`) is in the session record;
    the guard fix contains the symptom, the snapshot divergence is the
    SAT agent's to root-cause.  Reproducer:
    `smt-lib/non-incremental/AUFLIA/20170829-Rodin/smt3878551918658299427.smt2`
    (debug build, `solve_with_theory`).

Verification: 11,378 workspace tests, fmt/clippy/rustdoc clean, Z3 parity
0 disagreements.

## Residual known incompleteness (sound, documented)

- A constant sum that overflows `i64` *only in the linear parse* (leaves
  folded, nesting not — e.g. `(- (+ x i64::MAX) (0 - 1))`) answers
  `Unknown` via the gate. Making it decidable would require synthesising a
  wide-constant term mid-parse (`&mut TermManager` through the extract walk)
  to reuse the big-const column abstraction; recorded as future work, not
  attempted here.
- A `div`/`mod` with a symbolic or out-of-`i64` divisor keeps its
  pre-existing (honest) gate.
- Symbolic real division `(/ x y)` (variable divisor) keeps its honest
  gate: the defining identity `x = y·q` is nonlinear.  Division by a
  numeral constant is linearized exactly (item 5).

## History

Originally found, reported and left unfixed by the TLA+ front end's agent in
commit `6be6cc25` ("reported rather than fixed: the arithmetic subsystem is
another agent's territory"). This document is the fix's record; the original
reproducer lives on as `nixie-tla-check/examples/widerepro.rs`, whose five
wide-literal cases now all print `Unsat (correct)`.

## Continuation 6 (2026-09-15): item 17 closed — the snapshot divergence was elimination-reintroduction, three layers deep

The SAT-core snapshot divergence (item 17) is root-caused and fixed. The
guard-time trail and the panic-time trail never disagreed — the divergence
was between the *trail* (which satisfied every live clause) and the *model*
`save_model` wrote: its pure-literal phase had pinned var 1778 to the
polarity recorded when inprocessing eliminated it mid-search, and a clause
added *after* that elimination (an MBQI instantiation lemma, `(¬g ∨ body)`,
from `check_core`'s refinement loop) reintroduced the opposite polarity
`¬x1778`. The pinned model violated live original clause 38293
`(¬x1778 ∨ x11767)`. Release behavior: an invalid `sat` witness handed to
the theory layer. Three layers, each with its own defect and regression:

18. **Pure-literal pins are voided and their clauses restored on
    remention.** Pure-literal elimination deletes clauses on a promise
    about the *future clause set* ("no live clause carries the opposite
    polarity"). CDCL(T) refinement breaks that promise between
    `solve_with_theory` rounds; `save_model`'s unconditional pin then
    forces the variable against a live clause. Fix (`nixie-sat`):
    `add_clause` (and the assumptions intake) detects the opposite-polarity
    mention, drops the pin, and **re-asserts every clause the pass retired**
    through the full `add_clause` machinery — fresh ids, watches, proof
    lines, unit/conflict handling — restoring exactly the information the
    deletion removed. This is the sibling of the ELS gatekeeper
    (`resolve_reintroduced_literal`, the SK-1 fix) which already existed for
    ELS-folded variables; pure literals simply never got one. Unpinning
    without restoring is unsound (the deleted clauses lose their
    guarantee); pinning-as-unit is unsound too (a later opposite clause
    would yield false `unsat`). Only restoration preserves decidability.
    Regression: `pure_literal_pin_is_voided_and_restored_on_reintroduction`
    (fails pre-fix at the pin-void assert), plus the own-polarity
    non-trigger pin.
19. **BVE-eliminated variables: resurrect + void the walk.** The same
    refinement loop re-mentions BVE-eliminated variables *routinely* (lazy
    Tseitin `encode_depth` clauses — the probe showed dozens per run), and
    a new clause over such a variable constrains it while its retired
    clauses exist only as extension-stack obligations whose backward walk
    *toggles the pivot witness* — the toggle can falsify the new live
    clause. `fatal_error`, the documented "refuse once a BVE-eliminated
    variable was reintroduced" gate, was **never set anywhere** (dead
    machinery). Fix: any remention resurrects the variable's witness
    entries as live clauses, voids its walk obligations, and makes it
    branchable again (`branchable()` — without this, a clause whose
    satisfaction needs a *decision* on the variable, e.g. `(x ∨ y)` over
    two eliminated vars with no propagation possible, can never be
    satisfied and the model defaults both to false in violation). The
    eliminated markers stay set so no later round re-eliminates it — which
    is also what keeps the per-var walk skip exact. Regressions:
    `bve_eliminated_var_remention_resurrects_its_retired_clauses` (unsat
    twin) and `bve_remention_model_keeps_the_reintroduced_constraint` (sat
    twin) — both fail pre-fix with the exact `debug_verify_model_input`
    invalid-model panic. The fixtures use ternary parents: binary parents
    leave stale binary-graph edges that propagate the entailed literal and
    mask the mechanism.
20. **`equiv_substitution`'s grown tail was poisoned.** The compose step
    grew the map with `resize(num_vars, Lit::pos(Var::new(0)))` — a
    *non-identity* fill. Every variable created after the first ELS round
    (refinement-loop atoms and Tseitin helpers — all of them) became
    fake-eliminated into var 0: skipped by branching, its later mentions
    rewritten into a foreign variable by `resolve_reintroduced_literal`,
    and — the observed flip — the compose loop pushed **fabricated
    equivalence obligations** onto the extension stack, whose walk then
    toggled the variable to var 0's value against live clauses. Fix: the
    grown tail starts at identity. Regression:
    `equiv_substitution_grown_tail_stays_identity` (fails pre-fix at the
    fake-elimination assert; the compose step only runs when a round
    actually moves, so the fixture needs a real equivalence among the new
    variables to reach the resize).

Two process finds worth recording: (a) the first cut of the gatekeeper
early-out scanned `elim_var_flag` whole per `add_clause` — O(vars) per
clause made define-heavy ingestion quadratic (2.5 s → 142 s, caught by
`chained_defines_ingest_linearly`); the early-out must be O(1), with the
flag consulted per-literal in the filter. (b) A candidate "resurrected
clause over a *third* eliminated variable" cascade is real and handled:
resurrection goes through `add_clause`, so the gatekeeper applies to the
restored clauses themselves.

**Verification:** 11,505/11,519 workspace tests on the merged tree (the
14 failures are all `[corpus-missing]` — the external SMT/SAT corpora were
removed from the shared tree mid-session by an outside intervention,
independent of this change; they also fail on clean main); clippy/fmt/
rustdoc clean for `nixie-sat`/`nixie-solver` (clippy `-D warnings` over
the whole workspace currently trips on the freshly-landed
`nixie-core` finite-field code — `zero_prefixed_literal` in
`sort/field.rs`, collapsible ifs in `ast/manager/ff_fold.rs` — the owning
agent's debt, not touched here); Z3 parity 0 disagreements (z3 4.16.0,
176/177 correct + the 1 documented Z3-itself-Unknown); debug-panic sweep
clean over the whole Rodin family (3,272 files, zero panics — the canary
family that fired) and the parity corpus (177); mixed-arith differential
fuzz 2,200 instances across 6 seeds (4 release, 2 debug): 0 verdict
disagreements, 0 refuted models. `bench_diff --validate-models` was not
run — it needs the vanished corpus; rerun when the corpora return.

## Continuation 7 (2026-09-15): open item 3 — symbolic real division decided via NL dispatch

`(/ x y)` with a symbolic divisor (the handoff's item 3) is decided by the
nonlinear dispatcher now, closing the named half of the fuzz `unknown`-gap
remainder. Four coordinated changes:

21. **The encoding** (`nixie-theories/src/nlsat.rs`): a Real-sorted `Div`
    node (the parser's `/`; node sort is the exact discriminator against
    Euclidean `div`) translates to a fresh quotient variable `t` under the
    **guarded defining clause `(y = 0) ∨ (y·t − x = 0)`**, conjoined by the
    dispatcher as a two-literal clause — never a unit (it is a disjunction)
    and never the Euclidean remainder identities (those force an integer
    quotient on `2.5`). SMT-LIB's zero-divisor corner is faithful: a
    constant-zero divisor emits *no* clause (the term is uninterpreted, `t`
    floats; forcing `x = 0` through the degenerate clause would be wrong),
    and identical division terms share one `t` (operand-pair key ≡ hashcons
    term identity), which is the congruence `(/ a 0)` needs. The first cut
    of the clause had the guard **inverted** (`¬(y=0) ∨ y·t=x` satisfies
    itself for every nonzero divisor and drops the identity) — caught by the
    `x=9 ∧ y=2 ∧ (/ x y)=5` differential as a wrong `sat`, fixed, and pinned
    by `real_division_unsat_twin_stays_honest`.
22. **A latent wrong-`sat` in `NlsatSolver`, closed**
    (`witness_algebraic.rs`): `algebraic_model_is_verified` returned `true`
    for every *rational* model without checking anything — `Sat` was the
    search's word alone. Harmless while all clauses were units (watches
    force their Booleans); the moment genuine disjunctions exist, `decide()`
    can assign an Eq-atom Boolean its arithmetic does not support. The gate
    now concretely verifies every atom *and every clause* against the final
    assignment, rational or algebraic (the codebase's
    model-certify-before-`Sat` rule). Regressions:
    `eq_disjunction_clause_is_sat`, `division_shaped_clause_set_never_
    reports_wrong_sat`, `contradictory_eq_units_are_unsat`.
23. **Routing** (`check_nlsat.rs`): `term_is_nonlinear` flags Real-sorted
    division (and now *walks into* `Div`/`Mod` operands, so a product hidden
    under a `div` is detected); `assertions_have_int_arith` no longer counts
    a bare Int numeral as "Int-sorted arithmetic" (SMT-LIB coerces Int
    literals in Real contexts — counting them sent pure-Real goals with
    decimal-free literals to the integer backend; the `has_real_symbols`
    unsat-guard made that benign, but NRA is the right engine).
    `check_with_arith_refinement`'s `arith_defs_incomplete` gate no longer
    vetoes verdicts from the dispatcher that *encoded exactly those terms*
    (`nl_dispatch_answered`, cleared per check) — the gate exists for the
    linear path's free Booleans.
24. **Trust split, documented**: division goals keep the NRA dispatcher's
    historical Eq-distrust for `unsat` (now extended to the Eq-bearing
    defining clauses), so their refutations fall through honestly; `sat` is
    verified concretely. Known residual: a free dividend/divisor whose
    witness needs values the greedy sampler cannot enumerate (e.g. `x/y > 3`
    with both free — the defining identity couples them, and the resampler
    enumerates small integers) stays `unknown`: pre-existing sampler
    capacity, the same class as coupled products with free operands; and
    QF_LIRA-*declared* symbolic division still routes linear (the
    declared-logic contract; open logics auto-detect).

Measured: the previously-gated classes `(= x 5) (= y 2) (= (/ x y) 2.5)`,
nested `(/ x (/ y 2))`, zero-divisor `(= y 0) (= (/ x y) 5)`, and
NIRA-beside-division all now match z3. Verification: 11,564/11,579
workspace tests (15 failures all `[corpus-missing]` — the corpora are still
absent from the shared tree), clippy/fmt/rustdoc clean for the touched
crates, Z3 parity 176/177 correct + 0 disagreements (z3 4.16.0), mixed-arith
differential fuzz 2,600 instances across 6 seeds (4 release + 2 debug):
0 verdict disagreements, 0 refuted models; debug-panic sweep over the
parity corpus clean. New regressions:
`nixie-solver/tests/real_division_dispatch.rs` (8 tests) and three
`nixie-nlsat` witness tests.

## Continuation 8 (2026-09-15): the wide-LP wall, first slice — the row/value layer recovers from intermediate overflow

The corpora are still absent, so the wall (open item 2) was reproduced
**synthetically** before touching it: cancellation rows whose coefficients
and constants each fit `i64` while the row-value intermediates do not
(`2^62·2 = 2^63`) with finals that fit (`v0 = 2^62·1 − 2^62·2 + 1 =
1 − 2^62`) answered honest `unknown` where z3 says `sat`/`unsat` (both
directions). A second family — 40-deep chains whose row constants combine
to `≈ 2^102` — pins the *genuine* wall (no `Rational64` final exists;
`unknown` forever until exact row storage).

25. **The slice** (`nixie-theories/src/arithmetic/simplex/mod.rs`): the
    item-14 checked-plus-exact-retry pattern applied to the three sites
    that stood between the solver and width-limited values —
    (a) `pivot`'s entering-row build (`build_pivot_expr` +
    `build_pivot_expr_exact`: `−c/coef` intermediates overflow while finals
    cancel), (b) `pivot`'s row substitution (`substitute_row_fast` +
    `substitute_row_exact`: per-variable `BigRational` accumulation,
    narrowed finals), and (c) `intern_row`'s basic-variable substitution —
    which was **unchecked** (`coef * basic_expr.constant` on the bare
    `Ratio` operators): a debug panic and a silent release WRAP, i.e. a
    wrong row every later decision trusted. The retry is transactional: a
    genuinely unrepresentable final declines the row (no tableau entry) and
    sets `resource_limit` — `unknown`, never a wrapped verdict.
26. **`eval_expr` was unchecked too** — the release-wrap class in the
    value layer directly (assignment snapshots, the pivot's entering
    value). Now checked accumulation with the `update_row_exact` fallback
    (which item 14 built for `update_assignment`; `eval_expr` now shares
    it).
27. **Measured**: the cancellation family decides both directions
    (`sat`/`unsat` matching z3); the genuine-width family stays honest
    `unknown`; the debug-panic sweep, mixed fuzz (2,000 instances), and a
    dedicated wide-cancellation differential (1,400 instances across 5
    seeds — coefficients at 2^58–2^63, cancellation shapes, model
    validation on nixie-sat-vs-z3-unknown splits) all clean; Z3 parity
    176/177 correct, 0 disagreements; the full workspace suite green
    except the standing `[corpus-missing]` set. The remaining wide-LP
    territory — rows whose *finals* exceed width (exact row storage,
    `c7`/`c8` class) — stays open, pinned by
    `genuinely_wide_rows_stay_honest`.

Regressions in `nixie-solver/tests/arith_wide_literal_regressions.rs`:
`wide_cancellation_value_is_decidable_sat`,
`wide_cancellation_refutation_is_decidable_unsat`,
`wide_cancellation_bound_comparison_decides`,
`genuinely_wide_rows_stay_honest`. The synthetic wall corpus generator is
`/tmp/wide_fuzz.py`'s shape (wide-literal cancellation differential —
recreate from this description when needed; it is the tool that owns this
surface now that the corpora are gone).

## Continuation 9 (2026-09-15): the wide-LP wall, slice 2 — the wide-row side table

Slice 1 recovered rows whose *intermediates* overflow while finals fit;
this slice handles rows whose **finals** genuinely exceed `Rational64` (the
`c7`/`c8` chain class, constants combining to `≈ 2^102`). The design:
rows that cannot be narrowed are **captured exactly** in a side table
(`Simplex::wide_rows`, `BigLinExpr`) instead of declining the check —
their meaning survives, only the *pivoting and propagation through them*
is lost:

28. **Capture sites**: `intern_row`'s exact-retry failure now interns the
    exact row into the wide store (`intern_wide_row`: slack allocated,
    column index maintained, value derived exactly); `pivot`'s substitution
    commits a non-narrowing result to `wide_updates` instead of returning
    `false`. `intern_row`'s fast path also routes WIDE-basic terms through
    the exact substitution — treating a wide basic variable as nonbasic
    leaked its term into new rows, breaking the "rows reference only
    nonbasics" invariant (the debug column check caught a stale `columns`
    entry and a pivot choosing a basic variable as entering: the
    `a_product_of_two_negatives_is_sat` canary).
29. **Transient failures, convergence classification**: an unrepresentable
    wide value is mid-search TRANSIENT (a satisfied constraint's slack is
    often exactly 0) — it flags `wide_pending` instead of setting
    `resource_limit`; `check` (after `make_feasible`) and
    `state_feasible` (the model-snapshot gate) classify pending rows
    EXACTLY (`wide_row_violated`: BigRational comparison against the
    bounds, δ only breaking real ties) — a final violation or an
    undecidable row declines; a within-bounds row certifies regardless of
    whether its value could be stored. Unbounded wide slacks' values are
    irrelevant (nothing reads them) and are skipped.
30. **Measured**: the contradictory-pins chain (`c8`) decides `unsat`
    matching z3 (the pin conflict runs through narrow rows while the wide
    chain sits captured — the old global decline killed it before the
    conflict could fire); the satisfiable twin (`c7`) stays honestly
    `unknown` — the narrow search converges on points that violate the
    wide equalities and nothing guides it (wide-row *propagation/pivoting*
    is the named remaining work). Verification: 18/18 wide-literal
    regressions (the `pivot_overflow` unit test updated to the
    capture-not-refuse contract), full theories+solver suites green except
    the standing `[corpus-missing]` set, wide differential 1,100 instances
    across 4 seeds + mixed fuzz 1,200 + debug-panic sweep + Z3 parity
    176/177 correct / 0 disagreements (z3 4.16.0).

## Continuation 10 (2026-09-15): the wide-LP wall, slice 3 — positive rescaling decides the chain class; a wide-coefficient wrong-`sat` found and closed

31. **Positive row rescaling at intern** (`scale_big_to_narrow`): a row
    whose finals do not fit `Rational64` is rescaled by a POSITIVE factor
    into width before any wide-store capture. Every constraint bound in
    this encoding is ZERO (constants live in the row), and a positive
    multiple of a row preserves zero bounds — so the scaled row carries
    the same constraints with fitting coefficients and the FULL narrow
    machinery applies. The scale's common denominator is a power of two
    sized from the maximum magnitude, EXTENDED with small odd primes
    stripped from that maximum: an odd numerator beyond `i64::MAX` is not
    fixed by any power of two (the fraction is irreducible — the chain
    class hits exactly `3·i64::MAX` shapes), and narrowing must go through
    the REDUCED fraction, never the raw pair. A magnitude with no small
    odd factor left (a `2^100`-scale prime, say) stays unrepresentable at
    every scale — the wide store remains that fallback. Measured: the
    40-deep `i64::MAX`-increment chain now decides BOTH directions
    (`c7` sat, `c8` unsat), matching z3; a large-prime-constant goal
    stays honestly `unknown` (pinned by regression).
32. **A pre-existing wrong `sat`, found by the differential and closed**:
    a COEFFICIENT past `i64` (`(= v0 (+ (* 9223372036854775808 v1) 1))`
    with `v0 = 0, v1 > 0` — unsatisfiable) answered `sat` on landed
    binaries two revisions back. Root cause: the big-const abstraction
    turns a wide constant LEAF into an opaque COLUMN (a variable), so
    `const·var` parses as `var·var` — the parse fails as "nonlinear"
    with no overflow record, and the shape-based honesty gate sees a
    linear-looking term, so the atom floats as a free Boolean the SAT
    core satisfies at will. Two coordinated fixes: the parse records the
    overflow when the nonlinearity was CAUSED by the abstraction
    (`Level::wide_const` marking), and `arith_atoms_need_theory` gates on
    any recorded reason (parse-failed atoms never reach
    `var_to_constraint`, so the loop alone could not see them). Both
    shapes now answer honest `unknown`; the additive wide-constant path
    (the designed abstraction, certified-sat side) is unchanged.
    Mid-development, a pivot-site linking-row variant (`var = σ·t`)
    was built and REJECTED: a row between two basic variables breaks the
    "rows reference only nonbasics" invariant (find_pivot_col offered a
    basic variable as entering; the debug column checker caught it).
    Recorded so it is not retried without redesign.

Verification: 27/27 wide-literal + division regressions (new:
`wide_chain_is_decidable_sat_after_scaling`,
`large_prime_constant_rows_stay_honest`); theories+solver suites green
except the standing `[corpus-missing]`; the wide differential — now
generating `2^63`, `2^64+13` and `2^100`-prime COEFFICIENTS, the class
that found item 32 — 1,150 instances across 4 seeds: 0 verdict
disagreements, 0 refuted models; mixed fuzz, debug-panic sweep, and Z3
parity 176/177 correct / 0 disagreements (z3 4.16.0).

## Continuation 11 (2026-09-15): the wide-LP wall, slice 4 — the exact-coefficient parse retry

33. **Uniform-magnitude wide coefficients decide** (`extract_linear_terms_
    exact` + `parse_arith_comparison_exact`): when the narrow walk fails
    on coefficient width, the whole comparison is re-parsed with exact
    `BigRational` coefficients — wide constants are PLAIN constants there
    (no big-const column abstraction, so `const·var` stays linear: in the
    narrow walk the abstraction turns it into `var·var`, which is exactly
    the failure being retried) — and the row is rescaled into width by
    the shared positive scaler (`scale_exact_row`, now public in
    `nixie-theories::arithmetic`; zero bounds are preserved). Rows whose
    coefficients are all of comparable magnitude (`2^63`-scale sums, the
    item-32 shapes) decide BOTH directions; the parse-cache stores the
    retried result so rounds do not redo it.
34. **The mixed-magnitude wall, precisely located**: a row carrying both
    `1`-ish and `2^63`-ish coefficients parses and scales into the
    tableau, but a pivot THROUGH it needs the quotient `1/2^63` — an
    irreducible denominator beyond `i64` — so `build_pivot_expr_exact`
    declines and the honest `resource_limit` applies at the pivot site
    (`mixed_magnitude_wide_rows_stay_honest` pins never-wrong-verdict).
    That is the same wall the rejected pivot-site linking row targeted;
    the systemic answer remains dual-width pivots. A comparator trap
    recorded for the differential: z3's `QF_LRA` front end ERRORS on
    `(- 0 9223372036854775808)`-shaped literals ("logic does not support
    nonlinear arithmetic") — its no-logic mode decides the same formula
    correctly, so the differential now treats z3 error output as
    non-evidence rather than reading a garbage verdict.

Verification: 21/21 wide-literal + division regressions (new: the
uniform both-directions pair and the mixed-magnitude honesty pin);
theories+solver suites green except standing `[corpus-missing]`; wide
differential 1,100 instances across 4 seeds (z3-error-aware): 0 verdict
disagreements, 0 refuted models; mixed fuzz, debug-panic sweep, Z3 parity
176/177 correct / 0 disagreements (z3 4.16.0).

## Continuation 12 (2026-09-15): the wide-LP wall, slice 5 — the dual-width entering row

35. **Wide entering rows** (`build_pivot_expr_big` + generalized exact
    substitutions): when even the exact build cannot narrow the entering
    row (the mixed-magnitude quotient `1/2^63`), the pivot no longer
    declines — the entering variable's defining row lives EXACTLY in the
    wide store, every substitution through it runs exactly (the
    substitution helpers now take the entering row as `BigLinExpr`,
    narrow or wide alike), the entering value is derived exactly
    (`eval_big_expr`), and the assignment defers when unrepresentable.
    The satisfiable mixed-magnitude twin (`v0 = 1` forces `v1 = 0` — a
    representable value) now decides `sat`.
36. **Interval refutation at convergence**
    (`wide_row_refuted_by_bounds`): a violated wide row whose achievable
    value range (exact, delta-aware interval arithmetic over the
    variables' bounds — the lexicographic `(real, delta)` order keeps
    endpoint arithmetic valid) is DISJOINT from its basic's bounds is a
    genuine Farkas conflict, explained through the determining bounds'
    reasons. A merely-singleton test was too shallow (the observed
    violation reasoned through a one-sided slack); the interval test
    subsumes it. The unsat twin above needs CHAINED bound reasoning
    (wide-row propagation to fixpoint) — recorded as the remaining work,
    honestly `unknown` meanwhile.
37. **One more unchecked site closed**: the pivot's snap delta
    (`v - old` on bare `DeltaRational`) — a debug panic / release wrap on
    the wider trajectories the dual-width pivot newly reaches; now
    checked, deferring to the full re-derivation on overflow.

Verification: 22/22 wide-literal + division regressions (new: the
mixed-magnitude sat-twin decision; the honesty pin re-scoped to the
chained-reasoning gap); theories+solver suites green except standing
`[corpus-missing]`; wide differential 1,100 instances across 4 seeds
(z3-error-aware): 0 disagreements, 0 refuted models; mixed fuzz, panic
sweep, Z3 parity 176/177 correct / 0 disagreements (z3 4.16.0).


## Continuation 13 (2026-09-15, UNRESOLVED — read first): slice 3 introduced a false `unsat`; reproducer and analysis

**A live wrong verdict is on `main` since `625957a9` (slice 3, positive row
rescaling).** The wide differential found it; every landed slice since
inherits it. Reproducer (QF_LIA, div/mod + wide constants — exact bytes
preserved in `docs/studies/assets/2026-09-15/false-unsat-f1.smt2` if
written, else inline below):

```smt2
(set-logic QF_LIA)
(declare-const xi Int)
(declare-const yi Int)
(assert (and (not (and (= (+ (* 3 xi) (+ (+ (* 10 xi) (* -2 yi) (* 5 xi)) 90 (+ (* 2 yi) (* 3 yi) (* -1 xi)))) (mod (* -2 yi) 1)) (and (> 1099511627776 0) (> (* 3 xi) 37) (= (* -1 yi) 5)) (> (+ (mod (div -3 7) 4) (mod -5 5)) 2))) (<= (* 10 xi) -1) (> (+ (+ (* -2 xi) 4611686018427387905 (div (* -1 xi) 4)) (div (* 1 yi) 1)) 5)))
(check-sat)
```

* z3: `sat`. df13616e (slices 1–2): honest `unknown`. **625957a9 (slice 3)
  through HEAD: `unsat` — wrong.** Debug builds fire the delta-vs-reeval
  canary in `pivot` (the item-15 canary, now with a 2-variable reproducer).
* Analysis so far (the staleness chain): the mismatch fires at a pivot with
  leaving=10, entering=0 on row 9's rewritten content `var9 = var10` —
  `assignment[9] = 58` while the row's pre-snap value is 75: the assignment
  entry is stale w.r.t. its OWN row by 17 BEFORE this pivot. The
  substitution itself is value-preserving (small integers, no overflow —
  this is a *structural* staleness, not width). The staleness event is a
  silent value change of a term variable of row 9's earlier content
  (`17·v0 + v19 + 3·v20 + 75`) — candidates: a nonbasic value change that
  skipped `note_bound_change`, a column-index gap skipping row 9 in an
  entering substitution, or a wide-store transition losing an update.
  Instrumentation pattern that got this far: trace `note_bound_change` +
  row-9 commits + the delta-loop mismatch dump together
  (`NIXIE_DBG_H`/`NIXIE_DBG_D` markers, since removed).
* Two unchecked release-wrap sites were found on these trajectories and are
  fixed ONLY in the abandoned slice-6 worktree (snap delta
  `v - old`; `on_nonbasic_bound_change`'s `delta * c`): they are real
  hazards independent of this bug but were not verified far enough to land.
* The slice-6 wide-row bound propagation (exact both-direction derivations,
  exact crossing tests, weakened integer storage) is sound on every oracle
  (fuzz/parity/suites) but was NOT landed: landing on top of an unexplained
  false `unsat` in the same subsystem compounds risk. It lives in this
  session's worktree record; rebuild from this description.

**RESOLVED 2026-09-15 (same day, next session): see Continuation 14 — the
root cause is the forced `assignment_current = true` at the re-derivation
guard sites; fixed, verified, landed.** Bisect inside slice 3's diff (the scaler, the intern
wiring, the item-32 encode gate) with the reproducer; the debug canary
localizes the divergence; the release wrongness confirms it escapes.


## Continuation 14 (2026-09-15): the f1 false `unsat` root-caused and fixed — the lying `assignment_current` flag

38. **The mechanism, end to end** (bisected to `5bda924d` — slice 2, the
    wide-row side table — by building the window's binaries: slices 1,
    ff-Phase-5, and the mbqi fix all answer honestly): `update_assignment`
    breaks its row loop EARLY when a row's exact (`BigRational`) retry
    overflows, leaving every later row's assignment STALE, and signals
    through the documented pair `resource_limit = true` +
    `assignment_current = false`. The re-derivation guard sites
    (`check`, `pivot`, `on_nonbasic_bound_change`, `state_feasible`)
    then forced `assignment_current = true` UNCONDITIONALLY after
    `crash_basis`, checking `resource_limit` only afterwards — and
    `check` clears `resource_limit` at entry. With the flag lying
    "current" and the limit cleared, the next pivot consumed the stale
    vector: its delta formula inherited the stale base (the canary's
    `got ≠ want`, off by exactly the stale row's error), and in RELEASE
    the phony violation drove `explain_conflict` to an invalid clause —
    a wrong `unsat`. The delta-vs-reeval debug assert was the canary all
    along; the reproducer made it a 2-variable input.
39. **The fix**: `crash_basis` alone owns the flag, ending with
    `assignment_current = !resource_limit` — the flag may only say
    "current" through a FULL successful derivation. The four guard sites
    drop their forced `= true` (they keep their `resource_limit`
    bail-outs; `reset`'s site stays — an empty state is trivially
    current). f1 now answers honest `unknown` (z3: `sat`; the class
    overflows the derivation, so unknown is the honest decline), the
    debug canary is silent, and every wide-family win is preserved
    (chain sat/unsat, cancellation, uniform-coefficient, mixed-magnitude
    sat twin). Regression:
    `stale_assignment_never_drives_false_unsat` (the f1 bytes, pinned
    never-`unsat`).
40. **Process debts recorded**: the false `unsat` lived on `main` for six
    landings because the wide differential only gained the f1 shape
    (`not/and` nesting over div/mod + wide constants) in its fourth
    extension — the generator's shape coverage, not its seed count, was
    the gap. And the first attribution (slice 3, by commit adjacency)
    was wrong by one slice: binary-level bisection of the window
    (df13616e..625957a9) pinned slice 2 in four builds.

Verification: 23/23 wide-literal + division regressions; theories+solver
suites green except standing `[corpus-missing]`; wide differential 1,100
instances across 4 seeds (z3-error-aware): 0 disagreements, 0 refuted
models; mixed fuzz, debug-panic sweep, Z3 parity 176/177 correct / 0
disagreements (z3 4.16.0); fmt/clippy clean.

## Continuation 15 (2026-09-15): executing the continuation handoff — and the fresh-seed re-run that found two more live wrong verdicts

The handoff's open item 1 (the last unchecked release-wrap site in the
simplex) landed first, exactly as prescribed — but the wide differential's
**fresh seeds** (the generator shipped in-repo with `db97824c`; seeds
`20260971`/`20260973`) found a wrong verdict in **each direction** on
clean main within 300 instances. Both are root-caused and closed below,
with the layer analysis and the per-layer regressions. Items 41–45.

41. **`on_nonbasic_bound_change`'s two unchecked sites closed** (the
    handoff's item 1): the snap delta `new − old` (a non-basic jumping
    between deep opposite bounds overflows `i64`) and the delta
    propagation `Δ·c` + `+=` (`mul_r64_fast`'s fallback wraps in
    release). Fix shape: item-14 — checked ops, an exact `BigRational`
    retry of that one row (`eval_expr`) with a narrowed final, and a
    staleness-flag defer when the final does not fit (`crash_basis`
    alone owns the honest `resource_limit`). Both sites panicked in
    debug pre-fix (regressions
    `nonbasic_bound_change_delta_overflow_recovers_exact_and_never_wraps`,
    `nonbasic_bound_change_snap_delta_overflow_defers_instead_of_wrapping`).
42. **The false `sat` — a wide-basic integer variable's FABRICATED
    value** (`(= (+ (* 27670116100584327436 v2) (* 9223372036854775808
    v1)) -5)` with `v2 = 3`; z3: `unsat`, nixie: `sat` with the INVALID
    witness `v1 = 0`). Layers: (a) the parse retry rescales the row
    exactly (scale `1/88`) — sound; (b) the mixed-magnitude pivot sends
    v1's defining row to the WIDE store with exact content — sound;
    (c) v1's exact value `−9 − 41/2⁶³` does not narrow, so its
    `assignment` entry is stale-by-design (item 29's `wide_pending`
    contract) — but `Simplex::value`/`find_fractional_int_var` read the
    RAW entry, which fabricated the INTEGRAL `0`; (d) branch-and-bound
    accepted it and `snapshot_lia_model` published it. Root fix:
    `delta_value_exact` (wide-aware exact read, `None` = no honest
    value), tri-state `find_fractional_int_var` (`Branch` with exact
    bounds / `Underivable` → honest `Unknown`), **branch bounds derived
    from the exact UN-NARROWED value** (`wide_floor_ceil_big`: floor/ceil
    of a 2⁶³-scale rational are small integers, so the search stays
    DECIDABLE — both branch directions are refuted by the wide-row
    interval argument and the goal answers `unsat`, matching z3), a Sat
    gate requiring every term-backed variable to have a derivable value
    (`wide_underivable_blocks_sat` — covers pure-real acceptance too),
    and an honest `None` in `ArithSolver::value` (no fabricated model
    entries). Regressions:
    `wide_basic_int_var_fabricated_value_never_drives_false_sat`
    (pinned DECIDABLY unsat),
    `wide_coefficient_eq_row_with_pins_is_decidably_unsat`,
    simplex unit `wide_basic_reads_and_branch_bounds_are_exact`.
43. **The false `unsat` — a wide row's narrow-back kept its frozen
    entry** (the wrong1 shape; z3: `sat`, nixie: `unsat`; the f1-class
    delta-vs-reeval canary fired with a 2-variable reproducer).
    Layers: (a) the row's exact value is unrepresentable mid-search, so
    a pivot captures it in the wide store — its `assignment` entry is
    then NEVER updated (the wide pass only stores narrowing values);
    (b) a bound change on a dependent non-basic SKIPPED the wide row
    silently (`tableau.get` → `None` → `continue`, no flag) in BOTH
    `on_nonbasic_bound_change` and `soi_bound_flip`; (c) a later
    pivot's substitution NARROWED the row back into the tableau and the
    commit inserted it WITHOUT recomputing the entry (the substitution
    preserves the row's FUNCTION, not the entry's value); (d) the snap
    deltas then propagated from the stale base — debug: the canary;
    release: a phony violation drove an invalid conflict. Root fixes:
    wide dependents flag staleness (`assignment_current = false`) or
    decline the flip; `row_updates` entries carry `was_wide`, are
    EXCLUDED from the delta loop, and their entry is RECOMPUTED exactly
    at commit (deferring on a non-narrowing recomputation).
    Regressions: `wide_row_narrow_back_recomputes_its_assignment_entry`
    (pinned never-`unsat`), simplex unit
    `wide_dependent_bound_change_flags_staleness`.
44. **Two unchecked cut sites** (found by the corpus-return panic sweep,
    not by the wrong verdicts): `gomory_cut`'s `fj / f0` (and siblings,
    plus the `γ_j·bound` accumulation) and the old-LiaSolver
    `tableau_row_cut`'s identical shape — debug PANIC (QF_LIA/dillig
    `45-23.smt2`, QF_NIA/VeryMax
    `From_T2__streamserver.bug.t2_fixed__terminationS_1_0.smt2`) and a
    release WRAP that would publish a cut NOT implied by its row — an
    unsound lemma, not just a bad heuristic. Both now run checked and
    decline the cut on overflow (branch-and-bound stays complete).
    Also `static_features`' `vars` accumulation (the same file's own
    `const_term`/`const_prod` saturating discipline): two same-variable
    `Mul` terms at `i64::MAX`-scale overflowed the coefficient map — a
    debug abort that MASKED items 42/43 (removing it is what let the
    canaries fire). Regression:
    `static_features_wide_mul_accumulation_does_not_panic`.
45. **Process debts recorded**: (a) the handoff's "wrong-verdict debt is
    paid" claim did not survive FRESH SEEDS on the same generator —
    parity-of-coverage claims must be dated to the seed set that
    produced them, and re-running the differential after ANY landing on
    the same surface is not optional (the false `sat` and false `unsat`
    were both one `python3 wide_fuzz.py <bin> 300 <new-seed>` away for
    the whole six-landing window). (b) The debug-panic oracle found a
    THIRD bug (the masked static_features abort) that had to be fixed
    before the canaries could even fire — layer isolation includes
    ABORT layers, not just verdict layers. (c) Attribution discipline
    held: clean-main binaries (`precompile/db97824c/`, built and cached
    same-session) pinned both wrong verdicts as pre-existing before any
    fix was written.

Verification: 11,671/11,671 workspace tests (the standing slow five are
wall-clock gates that pass in isolation); fmt/clippy/rustdoc clean
(whole tree — including the slice-4 clippy debt in `encode.rs`, fixed
here); Z3 parity 176/177 correct, 0 disagreements (z3 4.16.0); wide
differential 9 seeds × 300 (both finder seeds included): 0 verdict
disagreements, 0 refuted models; mixed fuzz 3 × 400 clean; debug-panic
sweep over the parity corpus (177: 0 panics) and the returned
`smt-lib/non-incremental` stratified sample (434 files, seed 20260915:
0 panics after item 44); `bench_diff --validate-models` on the returned
corpora: TRUSTED_TOTAL=173, 0 disagreements, **0 invalid models** (the
owed item-17 rerun); the VeryMax canary family panic-free and honest.
The corpora are PARTIALLY back (`smt-lib/non-incremental` restored;
`satlib` and most of `satcomp2024/2025` still absent — the `[corpus-missing]`
class persists for those files).

## Continuation 16 (2026-09-15): slice 6 attempted and NOT landed — see the negative-result study

The unlanded slice-6 (wide-row bound propagation) was rebuilt per
Continuation 13's description: exact both-direction derivations through
wide rows, exact crossing tests, weakened-integer storage, bounded
fixpoint, per-final-check cadence. It closed the mixed-magnitude LRA
unsat twin decidably (matching z3) — and produced TWO false `unsat`s on
the wide regressions (the slice-1 cancellation sat twin via narrow
direction-2; the c7 chain-sat twin via the wide propagation, with a
stored bound wrong by exactly 10^9 — the fingerprint for the rebuild).
The code was REVERTED in full; the design, the traps (reason-id
recycling, branch-local bounds, endpoint orientation), and the next
entry points are recorded in
[`2026-09-15-wide-row-bound-propagation-negative-result.md`](2026-09-15-wide-row-bound-propagation-negative-result.md).
Slice 6 remains open, exactly as the handoff left it.

## Continuation 17 (2026-09-16): the slice-6 blocker was a pre-existing propagation bug — found by the auditors, fixed, landed (item 46)

46. **`derive_basic_bound`'s exact-retry double-count** (found by the
    corner-enumeration auditor built per the negative-result study's
    corrected entry points): the mid-walk retry recomputes the WHOLE
    directional sum, but the walk continued adding the post-overflow
    terms on top of the full result — a corrupted bound with SOUND
    reasons, i.e. an unjustified refutation wearing a justified one's
    clothes. This single defect produced BOTH of slice-6's recorded
    false `unsat`s (the chain-sat twin and, via narrow direction-2's
    enriched bound graph, the cancellation sat-twin) and had been live
    on `main` behind an overflow trigger the ordinary corpus never
    reached. Fix: after the retry the walk is reasons-only
    (`lower_done`/`upper_done`); regression
    `basic_bound_exact_retry_does_not_double_count`. The wide-row
    propagation itself stays unlanded (three NEW false-`unsat` shapes
    on fresh differential seeds — see the negative-result study's
    resolution section); its rebuild now stands on a sound narrow base,
    with the corner auditors and the model audit as the standing
    instruments.

Verification: theories+solver suites green except the genuine
`[corpus-missing]` set (the returned corpus lacks QF_BV/sage and three
other families); wide differential 5×300 (fresh seeds included) clean;
mixed fuzz 2×400 clean; Z3 parity 176/177, 0 disagreements (z3 4.16.0);
fmt/clippy/rustdoc clean for the touched crate.

## Continuation 18 (2026-09-16): round three — the strict-atom one-sided endpoint; the wide-row propagation LANDS (items 47–48)

47. **The strict-`>` false-`unsat` root cause** (the round-two residual,
    minimized to `(> (* 6927366777083328576 v2) -3) ∧ v2 = 3`): deriving
    a bound's SUPREMUM through a variable with only a LOWER bound used
    the lone lower as the sup endpoint — fabricating the tightest
    possible "upper". On the strict shape the `>` atom slack's lone
    `(0, +1)` lower became a phony `−3−ε` upper on the row's variable,
    crossed the real bounds, and refuted a satisfiable goal (the
    corner auditor + the crossing probe localized it in one run). A
    ONE-SIDED pair now serves its own direction only — a lone lower is
    an infimum, never a supremum (+∞); both derivation helpers'
    endpoint selections enforce it. Regressions:
    `strict_wide_row_one_sided_endpoint_never_drives_false_unsat`,
    `strict_multi_term_wide_row_never_drives_false_unsat`.
48. **The wide-row propagation lands** (slice 6, third build, at last
    sound): exact both-direction `BigRational` derivations through the
    wide store (basic-ward + variable-ward solving
    `xᵢ = (basic − k − Σ_{j≠i} cⱼxⱼ)/cᵢ`), lex-comparison endpoint
    selection (inverted pairs exist mid-search in genuinely
    contradictory atom states), exact lexicographic `(real, delta)`
    crossing tests planted through the pending-crossing channel
    (never on weakened forms), `ceil/floor ± 1, delta = 0` integer
    storage for non-narrowing bounds, `BRANCH_REASON` filter on all
    derivations, and the per-final-check cadence with
    discard-stale-first consumption. The corner-enumeration auditor
    ships env-gated (`NIXIE_S6_AUDIT=1`, debug builds). NARROW
    direction-2 stays env-gated OFF (`NIXIE_S6_NDIR2=1`): with it the
    mixed-magnitude LRA unsat twin decides `unsat` (matching z3 — the
    named residual closes!), but the chain-sat twin degrades to
    `unknown` (a completeness trade, not a soundness one — some sound
    derivation deflects the search into an honest decline); turning it
    on by default needs that interaction understood. The propagated
    bound state is sound on every oracle: wide differential 9×300
    across the round (every prior finder seed included), mixed fuzz,
    parity 176/177 (z3 4.16.0), the full suites.

The three-round arc, in one line each: round one found the false
verdicts (and a wrong fingerprint), round two found the pre-existing
double-count underneath them, round three found the one-sided endpoint
underneath THAT — and the propagation that exposed all three is now
sound and landed.

## Continuation 19 (2026-09-16): the value-overflow migration — f1 decides `sat`; the ndir2 trade mapped to its wall (items 49–51)

49. **The value-overflow migration** (the round's landing): when
    `update_assignment`'s exact retry finds a NARROW row whose final
    VALUE does not fit `Rational64`, the row now MIGRATES to the wide
    store (item 28's capture, applied at re-derivation) instead of
    setting `resource_limit` — the meaning survives exactly, the
    basic's value is re-derived exactly each pass, and the convergence
    classification owns the verdict. Measured: **f1 (the original
    false-`unsat` reproducer) now decides `sat`** (z3-correct; its
    trajectory passes such a point and previously declined); the
    chain-sat twin stays `sat` (its trajectory never visits the
    migration); the f1 regression pin strengthened to `sat`.
50. **The ndir2/pinned trade, mapped end to end**: narrow direction-2
    (general OR pinned-basic-only) closes the mixed-magnitude LRA
    unsat twin (`unsat`, matching z3) — and deflects the chain's pivot
    trajectory into the width wall: first `update_assignment`'s
    value-overflow decline (site 3713 — now migrated away by item 49),
    then the CONVERGENCE wall (site 1950: a violated wide row whose
    achievable range OVERLAPS its bounds but no pivot can repair it —
    wide rows are unpivable). Both gates stay env-gated
    (`NIXIE_S6_NDIR2`, `NIXIE_S6_PINNED`); turning them on by default
    needs wide-driven repair steps (a pivot-analogue through wide
    rows — Z3's `lar_solver` has no such wall because it computes
    exactly everywhere). With item 49's migration the pinned gate
    yields: twin `unsat` ✓, f1 `sat` ✓, chain `unknown` (the landed
    chain regression blocks default-on).
51. **A fresh pre-existing false `unsat` found by the mixed fuzz**
    (seed 41; NOT this round's regression — the landed 83b985a6
    binary reproduces it): a three-disjunct nested `not(or(= (mod …)
    (div …)), (> … (mod …) …), (and (> … (mod …) …) (< … (div …) …)))`
    with `yi = 2^62` pinned answers `unsat` where z3 says `sat`; any
    two-disjunct subset stays honest `unknown`. The exact bytes are in
    `/tmp/mi1.smt2` of the session (reproducible from the fuzz seed).
    **This is the arithmetic arc's top open item** — a live
    wrong-verdict class on `main`, shape: mod/div axiom feed + wide
    pin + three-way disjunction.

Verification for the landing: theories+solver suites green except the
pre-existing `wisas` pair (fixture-level `Unknown`, verified on earlier
parents); wide differential 4×300 clean; parity 176/177, 0
disagreements (z3 4.16.0); fmt/clippy/rustdoc clean; the mixed fuzz's
single failure is item 51's pre-existing find.

## Continuation 20 (2026-09-16): item 51's first layer closed — the mid-`make_feasible` staleness (item 52); the second layer mapped

52. **`make_feasible`'s loop consumed stale assignments mid-search** (a
    pivot can invalidate the vector BETWEEN iterations — the wide-updates
    commit and the narrow-back recompute deferral both clear
    `assignment_current`; the loop's next `find_violating` read the stale
    entries, and a bogus violation drove `explain_conflict` to an invalid
    clause). Probed live on the item-51 reproducer: **19 stale reads**
    before the fix, 0 after. The loop now re-derives when the flag goes
    down between iterations (the same guard as every other consumer;
    `crash_basis` is O(tableau) but fires only on actual wide
    transitions). LANDED. This class is independent of item 51 (it was
    reachable from any wide-transition pivot) and is now closed.
53. **Item 51's second layer, mapped but open**: with the staleness
    closed, the false `unsat` persists through a DIFFERENT path — the
    final conflict exports the core `[division-axiom]` ALONE (claiming
    the axiom `(= 3yi (+ (div 3yi 1) (mod 3yi 1)))` is self-
    contradictory — it is a theorem). The chain at the conflict:
    var 219's row `1 − s22` with var 219 ∈ [0,0] (axiom-reasoned) and
    `assignment[s22] = 0` while var 22's OWN row evaluates to `1` (the
    entry disagrees with its row UNDER `cur=true` — the re-derivation
    did not update it; the `has_stale_ref` skip was probed and is NOT
    the path). The exported core drops the row-term determining bounds
    (s22's upper carried the axiom's own reason at that moment, so the
    walk legitimately produced `[axiom]`). The remaining question:
    whether var 22's row `1 − 52·s135` is a sound consequence of the
    axiom (its coefficient −52 arose through chained substitutions; if
    the row is unsound, the defect is in the div/mod AXIOM FEED's row
    construction over wide products), or whether the s22 entry's
    missed update is a third staleness path. Probes that answered:
    XCONF/XROW (row+bounds+assignment at the conflict), XCONF-RET (the
    built core), the walk's per-term decisions, the BNB-ERR/ENTRYSCAN/
    GCD-VICTIM/HERMITE eliminations. Reproducer: `/tmp/fi1.smt2`
    bytes in item 51; attribution: introduced by `0d3d2378` (round-3
    propagation landing), absent on `d1dc7f0d`.

Verification for the landing: suites green except the pre-existing
`wisas` pair; wide differential 3×300 clean; parity 176/177, 0
disagreements (z3 4.16.0); fmt/clippy clean; chain-sat, f1-sat, and
the wcancel shape all preserved.

## Continuation 21 (2026-09-17): item 53 pinned to a wrong row SUBSTITUTION — the full mechanism decoded (item 54)

54. **Item 51/53's false `unsat`, end to end** (docs-only this round;
    every layer verified by probes, all stripped):
    * The final conflict's `[division-axiom]`-only core is *formally*
      correct given the bound set — the wrongness is one layer deeper.
    * `s22` (the axiom `(= 3·yi (+ (div 3·yi 1) (mod 3·yi 1)))`'s row
      slack) is bound `[0,0]` (reason 12 ✓ sound). Through two sound
      pivots it becomes `1 − 52·s135` (verified EXACTLY: the wide
      substitution relabels the axiom row; at the z3 model it evaluates
      to 0 ✓).
    * `s135` is the row slack of atom 72 (`1 < mod(8−xi,3)`) — its
      row, as INTERNED by `assert_lt` for atom 72, is
      `(3·var1 − s20 − s21 + 3·2^62 + 1)/52` — **which equals
      `(1 − s22_axiom)/52`, NOT `1 − mod(8−xi,3)`**: at the z3 model
      they differ (1/52 vs 1). `intern_row`'s basic-substitution
      produced a WRONG FORM for atom 72's row (`1 − s7`): the
      substituted content coincides with a rescaling of the AXIOM row
      instead of the mod row. From there everything follows: atom 72
      asserts `s135 ≤ 0` (sound FOR ITS ACTUAL ROW) → with
      `s22 = 1 − 52·s135 ∈ [0,0]` this forces `s135 = 1/52` →
      contradiction → and the core folds to `[12]` because s135's
      determining bound carries only `[72]` while the ROW equivalence
      itself is the (invisible) lie.
    * Attribution unchanged: introduced by `0d3d2378` (the propagation
      landing enriched the bound state so the wrong-form row's bound
      became load-bearing); the substitution defect itself is older.
    * **The next session's entry point**: dump, at s135's intern
      (backtrace `assert_lt → cached_row_slack → intern_row`), the
      PRE-substitution expr (`1 − s7`) and every tableau row the
      substitution consumed (s7's row and the xi-rows it chains
      through). One of them is already corrupted — the probe set that
      answered here (INTERN/WIDE-UPD/SUB-BIG/SET-UPPER-with-backtrace/
      CACHE-HIT, plus the exact-arithmetic row validation at the z3
      model) localizes it in one run. The honest quick check for any
      candidate fix: `{12, 72}` is satisfiable (z3), so no sound
      derivation may refute it.

Verification: no code change this round (diagnosis only; probes
stripped, tree pristine, `fi1` still reproduces — the open item).

## Continuation 22 (2026-09-17): item 54 closed at the root — the integer mark on a RESCALED row's slack (items 55–57)

55. **The item-54 false `unsat`, end to end** (the reproducer's exact bytes
    preserved at
    `docs/studies/assets/2026-09-17/false-unsat-fi1.smt2`; z3: `sat` at
    `xi=5, yi=2^62`; found by the mixed differential, seed 41, instance 16).
    Item 54's diagnosis was one layer off: the `/52` row form is NOT the
    defect — it is `intern_row`'s positive width rescale doing exactly its
    designed job, and every equation it produced was verified sound at z3's
    model. The chain, as the probes decoded it live (INTERN/CONSUME dumps,
    SET-BOUND backtraces, ECONF row+bounds dumps, REASON registrations):
    * the trichotomy machinery (sound: a tautologous clause over the axiom
      equality `(= 3yi (+ (div 3yi 1) (mod 3yi 1)))`) lets the SAT core
      pick the arm `3yi < div(3yi,1) + mod(3yi,1)`;
    * that arm interns its row `3yi − div − mod + 1` (an INTEGRAL form);
      the pin `yi = 2^62` makes the substituted constant `3·2^62 + 1`
      overflow `i64`, so `intern_row` rescaled by `1/52` into width —
      the slack then means `(3yi−div−mod+1)/52`, NOT the requested form;
    * `cached_row_slack` marked the slack INTEGER from the UNSCALED form's
      integrality (`is_integral_form` on the pre-intern expr);
    * `gomory_cut` sourced a cut from that integer-marked slack: over the
      row `slack = (1 − s_axiom)/52`, the GMI lemma with `slack ∈ ℤ`
      fabricates `52 | (1 − s_axiom)` — a divisibility constraint implied
      by NOTHING — and asserts the cut `1 − s_axiom ≤ 0` (i.e.
      `s_axiom ≥ 1`) with the axiom's own reason set (the cut's
      antecedents are the row's nonbasics' bounds: `s_axiom ∈ [0,0]`);
    * with `s_axiom ∈ [0,0]` (the axiom's equality bounds) the cut is
      violated, `explain_conflict` exports the core `[division-axiom]`
      ALONE, and the SAT core refutes a theorem: `unsat` for a `sat` goal.
    **The fix**: `intern_row_reported` returns a `RowInternMode`
    (`Exact`/`Rescaled`); `cached_row_slack`/`cached_row_slack_strict`
    mark a rescaled slack integer only when the RESCALED row is itself an
    integral form (`is_integral_form` on the actual row) — the exact
    condition under which the slack is integer-valued. Cuts and
    branch-and-bound then never reason from a fabricated integrality; the
    GCD canonicalization stays `Exact` (dividing an integral form by its
    GCD keeps it integral). fi1 now answers honest `unknown` (the 2^62
    width wall; the pre-propagation control `d1dc7f0d` also said
    `unknown`); regressions `rescaled_row_slack_never_drives_false_unsat`
    (end-to-end, pinned never-`unsat`) and
    `intern_row_reports_rescaled_for_width_rescale` (simplex unit).
56. **The `i64::MIN`-bound corner, closed with honest declines** (found by
    the debug-panic sweep on `QF_ANIA/…/diskperf…_2.smt2`, stratified
    sample seed 20260919): `x < i64::MIN + 1` tightens to `x ≤ i64::MIN`,
    whose row `lhs − rhs` needs the constant `+2^63` — and the unchecked
    `-rhs` in the assert path PANICKED in debug and silently WRAPPED in
    release, building a row for a different constraint. The parse layer
    gates its own overflow but the assert-time negation was uncovered.
    Fix (the item-9/12 pattern): every `assert_*` entry verifies
    `checked_neg_r64(rhs)` and, on overflow, declines through the sticky
    `unrepresentable_row_assert` flag — the atom stays unconstrained and
    `check()` answers `Unknown` for the solver instance's lifetime
    (sticky across `reset()` like `int_terms`, because the replay
    re-asserts the same atom); the equality sign-flips in `row_key` and
    `normalize_expr` skip on an unrepresentable negation through the
    shared `try_flip_terms` (same predicate in both, so key and row stay
    consistent — only canonical-form sharing is lost); the
    `fixed_to_const_reason` probe declines with `None`. diskperf and the
    `< x MIN+1` shape now answer honest `unknown` (z3: `sat` at
    `x = i64::MIN`); regression
    `i64_min_bound_rows_decline_instead_of_wrapping`. The DECIDABILITY
    follow-up (not taken: the corner is measure-zero in the corpora) is a
    non-strict row built as `rhs − lhs ≥ 0` — representable at the
    corner — but it moves the overflow into the coefficient negations and
    cannot serve the strict/δ encodings; recorded so the next agent does
    not rediscover the flip design.
57. **The optimizer's wrap class closed — the wisas handover's open
    soundness question answered** (`docs/handovers/
    2026-09-15-wisas-layer2-simplex-24cb0567.md` asked: is the
    `[ceil(min), floor(max)]` superset guarantee intact under the
    wide-store derivations?). Answer: the wide store itself can only
    WIDEN the range — wide rows are invisible to the optimizer's pivots,
    so the optimized problem is a relaxation, min ≤ true min and max ≥
    true max (the sound direction); `compute_int_bounds` uses only direct
    single-variable level-0 facts with checked tightening (no wide
    derivations feed it); `lp_int_bounds` optimizes over `pop_to_base`
    state (propagated bounds are scope-trailed and pop). The one real
    NARROWING vector was the optimizer's unchecked fixed-width
    arithmetic: `eval_linexpr`/`reduced_obj_coef` (wrapped objective and
    reduced costs), the ratio-test gaps (`hi − bv_val`, `gap / −eff`),
    the ignored declined `pivot()` return, and `-neg_max` in
    `lp_int_bounds` — any wrap fabricates an "optimum", the case-split
    range narrows, and the emitted `(or (= t lo) … (= t hi))` clause
    permanently excludes reachable values: the false-`unsat` direction.
    All are now checked with `SimplexOptStatus::Unknown` declines, plus
    `resource_limit` consults after every re-derivation. The wisas
    COMPLETENESS regression (unknown-since-`24cb0567`, the cadence/
    lemma-starvation signature) is untouched by this — it stays the open
    heuristic item, to be measured per `docs/BENCHMARKING.md`.

Verification for the landing: full workspace suite (11 810 tests; the
pre-existing non-corpus failures only: the wisas pair, the TLA sets
cardinality test — verified failing on clean `28426243` too, the sets
front's — and the two documented slow-but-correct 180 s-cap timeouts);
fmt/clippy/rustdoc clean; Z3 parity 176/177 correct, 0 disagreements
(z3 4.16.0); wide differential 6×300 + mixed differential 6×400 across
fresh seeds (20260918–20260935, both finder-adjacent surfaces): 0
verdict disagreements, 0 refuted models; debug-panic sweep over the
parity corpus (177) and a 345-file stratified `smt-lib/non-incremental`
sample (seed 20260919, 30 per family): 0 panics after item 56 (the
`diskperf_…_2` panic was the finder; `…_1` was a stale-shared-target
binary trap, clean on rebuild).

Infrastructure notes for the next session: the shared `target/` was
deleted TWICE mid-session (recreate it — every worktree symlinks it);
after a deletion, a sweep or differential may run ANOTHER agent's stale
binary (the `diskperf_…_1` false alarm) — rebuild before believing a
surprise; disk hit 100% mid-verification (repoint the worktree's target
symlink to a private dir on the root disk and `rm -rf
target/debug/incremental`).

## Continuation 23 (2026-09-17): the wisas layer-2 completeness regression closed — the repair pivot's snap overshoot (item 58)

58. **`wisas_xs_8_13`'s `unknown`, end to end** (the regression the
    wisas front attributed to `24cb0567` and left as an open soundness
    question plus a completeness loss; see
    `docs/handovers/2026-09-15-wisas-layer2-simplex-24cb0567.md`).
    The termination chain, decoded by probes (verdict-site
    instrumentation down through `resource_exhausted` →
    `simplex.resource_limit` → the setting site): the search's
    `make_feasible` burned its ENTIRE 100k-pivot budget in ONE final
    check, `check` answered theory-`Unknown`, the manager's `Ok(_) =>
    resource_exhausted` arm degraded the solve to `unknown`.
    * The budget burn was a **frozen 2-cycle**: `v165 ↔ v176` swapped
      basis positions for 75k+ consecutive pivots (identical leaver
      counts, identical violating var, 7 distinct leavers total).  The
      two rows are mirror images (`vX = K − vY` plus 13 shared columns);
      with the propagation pinning all 13 shared columns two-sided, the
      ONLY mobile columns were v165/v176 — each the other's reverse
      repair.
    * The arithmetic at the cycle point: `v176 = K − v165` with
      `K = −1/2`; both bounds `[-1,0]`; the repair that moves `v165` to
      `−1/2` lands `v176` EXACTLY on its violated upper `0` — a fully
      successful repair existed at every step.  The pivot machinery
      never took it: it snapped the leaving variable **lower-preferred**
      (`−1`) instead of to *the bound it violated* (`0`), so the
      overshoot (the entire bound interval) landed on the entering
      variable through the row equation — manufacturing a fresh
      violation of the same size on the other side, forever.  The
      Dutertre–de Moura CAV'06 repair step snaps the leaving variable to
      the bound it violates; that is precisely the property that makes
      the violation measure decrease monotonically.
    * Why the propagation landing exposed it: the derived bounds pin
      columns two-sided, shrinking the eligible entering set until only
      the mirrored pair remains — the old snap rule's overshoot then
      livelocks where the pre-propagation search always had a third
      column to escape through.  (The handover's search signature — ⅓
      conflicts, 1/15 restarts, 3× slower — is the CDCL view of the
      same starvation.)
    * **The fix**: the snap target is now an explicit `SnapBound`
      parameter of `pivot` — each driver passes its own semantics.  The
      standard repair loop (`make_feasible`) and the dual loop
      (`dual_simplex`) pass `SnapBound::from_violated(bound.kind)` (the
      DdM rule).  The SOI driver and `optimize_linexpr` deliberately
      KEEP the historical lower-preferred snap: their progress
      invariants are calibrated to it (snapping the SOI driver's
      blocking basic to its ratio bound spins `soi_differential` seed 5
      into that driver's own budget — measured both ways before
      choosing).  wisas now answers `unsat` (z3-certified),
      deterministic across repeats, 1.4 s, and the search signature
      returns to the healthy regime (3 624 conflicts / 492 restarts vs
      the good parent's 2 866 / 455).  Regressions:
      `repair_pivot_snaps_the_leaving_var_to_its_violated_bound` (the
      simplex unit that FAILS pre-fix — two mirrored rows over pinned
      bounds) and the now-green `wisas_xs_8_13_is_unsat` /
      `..._verdict_is_stable_across_repeats` pair.
    * The handover's open soundness question (the `[ceil(min),
      floor(max)]` superset guarantee) was answered separately
      (continuation 22, item 57): the wide store can only widen the
      optimized range, and the optimizer's wrap class is closed.  The
      completeness question is answered here.

Verification for the landing: workspace suite green except the standing
non-arc set (the TLA sets cardinality test — pre-existing on clean
`28426243`, the sets front's; the recfun 180 s-cap timeout — documented
slow-but-correct); clippy/fmt/rustdoc clean for the touched crates;
Z3 parity 176/177, 0 disagreements (z3 4.16.0); wide 3×300 + mixed 4×400
fresh seeds: 0 verdict disagreements, 0 refuted models; debug-panic
sweep over the parity corpus (177) and a 235-file stratified
`smt-lib/non-incremental` sample (seed 20260920): 0 panics; wisas
`unsat` deterministic ×3.

## Continuation 24 (2026-09-17): the wide-driven repair step — the convergence wall is gone (item 59)

59. **The site-1950 wall, closed** (open item 2's unblocker; the
    negative-result study's named residual): a violated wide row whose
    achievable value range OVERLAPS its bound window is repairable in
    principle, but wide rows had no pivot — the convergence
    classification declined the whole check (`resource_limit`, honest
    `unknown`), the wall the `NIXIE_S6_PINNED` trade analysis measured.
    * **The repair step**: `pivot`'s new wide-leaving branch.  When the
      leaving basic's defining row lives in the wide store, the entering
      row is solved EXACTLY from it
      (`build_pivot_expr_big_wide`: `x_e = (x_B − Σ a_k x_k − c)/a_e`,
      all `BigRational`), narrowed when it fits (a wide row solved for a
      different variable can become narrow), and the ordinary pivot
      machinery takes over — every row referencing the entering column
      is substituted through the exact result (item 28's
      `substitute_big_row` path), the leaving basic is snapped to the
      bound its driver chose (item 58's `SnapBound`; the classification
      passes `from_violated`), and the column index is diffed for the
      wide leaving row exactly as for a narrow one.
    * **The driver**: the convergence classification in `check` now runs
      a bounded repair loop (≤ 32 per check): classify every bounded
      wide row; a violated row with a DISJOINT range still refutes
      through the interval argument (unchanged); a violated row with an
      OVERLAPPING range attempts one wide pivot (entering column by
      exact-sign eligibility, smallest index) and re-feasibilizes; an
      undecidable row, an exhausted budget, or no eligible column still
      declines honestly.
    * **Measured**: the chain-sat twin under `NIXIE_S6_PINNED=1` — the
      trade's documented blocker — now PASSES (`sat`, matching z3).  The
      pinned gate's remaining cost is a different, non-wide shape (the
      trivial mixed twin `2x+y=1 ∧ y=½` degrades to `unknown` under the
      gate with the corner auditor silent — sound derivations, a
      completeness loss local to pinned direction-2; the gate stays
      env-gated OFF, and default-on still needs the matched-null
      campaign per `docs/BENCHMARKING.md` since the gate re-paths the
      search).  Default-mode canaries unchanged: f1 `sat`, fi1 honest
      `unknown`, wisas `unsat`.
    * Regression: `violated_wide_row_with_overlapping_range_is_repaired`
      (the wall shape at the simplex level — FAILS pre-fix: the
      overlapping-range decline; PASSES post-fix: the repair converges
      and the entering variable lands inside its window).
    * **The provenance question** (the structural gap that let item 54's
      conflict core fold to a single atom) remains OPEN and is now the
      main soundness-hardening item on this surface: rows built by
      substitution carry no defining-reason provenance, so a conflict
      explained through a substituted row can export an incomplete
      core.  No wrong verdict is demonstrated (the differentials are
      clean across a dozen fresh seeds this round); the design work is
      scoped for the next session.

Verification for the landing: workspace suite green except the standing
non-arc set (the TLA sets cardinality test — pre-existing, the sets
front's; two documented slow tests + the incremental-replay fuzz, which
passes in isolation at 136 s and only hit the 180 s cap under machine
load 34); clippy/fmt/rustdoc clean for the touched crates (also restored
fmt for `simplex_opt.rs`, which had drifted on main); Z3 parity 176/177,
0 disagreements (z3 4.16.0); wide 3×300 + mixed 3×400 fresh seeds
(20260952–20260957): 0 verdict disagreements, 0 refuted models;
debug-panic sweep over the parity corpus: 0 panics.

## Continuation 25 (2026-09-17): the provenance question answered — and the strengthened definitional invariant that paid for it immediately (item 60)

60. **The provenance question, answered by construction.**  The worry
    (from the item-53/54 chase): rows built by substitution carry no
    defining-reason provenance, so a conflict explained through a
    substituted row could export an incomplete core.  Worked through to
    the bottom, the architecture is already safe: **rows are
    DEFINITIONS** (`slack := form`, true by introduction, constraining
    nothing alone), while **constraints live only in bounds**, each
    carrying its full reason set (asserted atoms; cut antecedents via
    `add_le_with_reasons`; propagation antecedents via `aux_reasons`;
    branch case-splits via the scoped `BRANCH_REASON` sentinel).
    Substitution through a basic consumes only the DEFINITIONAL equation
    — never the bound — so every row the pivot machinery produces is
    again definitional, and a conflict explained through it cites the
    columns' BOUNDS with their reasons.  Item 54's single-atom core was
    NOT a provenance failure: the core was complete over a FABRICATED
    constraint (the false-integrality cut); the provenance layer was
    innocent.  A provenance-carrying redesign is therefore unnecessary —
    what IS necessary are the three properties the argument rests on,
    each now mechanically enforced:
    1. *Row contents are equation-preserving across every mutation* —
       pivot algebra, the wide migration, the rescale, intern
       substitution.  The strengthened invariant below checks the
       shape (rows reference only nonbasics) and the values
       (entry == row eval; exact eval for wide basics).
    2. *Integrality marks are truthful* — item 54's `RowInternMode`.
    3. *Every stored bound carries its full justification* — the reason
       resolution assert, the slice-6 full-reason planting, the corner
       auditor.
    * **The strengthened `debug_verify_invariant`** now checks: every
      row (narrow and wide) references only NONBASIC variables (the
      definitional shape — a basic in a row's terms would make the
      one-level substitutions unsound); every basic's value sits inside
      its bound window (the stored entry for narrow rows, the EXACT
      evaluation for wide basics — an unrepresentable wide entry is
      stale-by-design under `wide_pending` and is not a witness); and
      every narrow entry equals its row's evaluation (checked — the old
      inline `+=`/`*` aborted debug builds on wide trajectories).  It is
      wired as a `debug_assert` at `check`'s true convergence point
      (after the wide classification/repair, not before — an earlier
      placement misfires on states the classification itself repairs).
    * **What it found immediately**: `pop` could leave a NONBASIC
      outside its restored window.  The old contract ("pops only relax
      bounds, and a nonbasic only ever moves by a snap into the
      then-current window") misses the crossed-probe shape: a scoped
      probe may tighten a bound PAST the opposite one (the probe's
      infeasibility signal — the NLA interval probes build exactly
      this, `reason u32::MAX-1`), the snap parks the nonbasic at a
      point only the tightened side justified, and restoring that side
      widens the window away from the point.  The out-of-window
      nonbasic is invisible to `find_violating` (basics only) — a
      latent wrong-verdict site (delta propagation and Farkas
      explanations assume nonbasics at their windows).  **Fix**: `pop`
      re-snaps every nonbasic the undo left outside its window and
      flags the assignment stale for its dependents' re-derivation (no
      flag when nothing moved — the common relax-only pop keeps the
      incremental maintenance).  Regression:
      `pop_resnaps_a_nonbasic_left_outside_its_restored_window`
      (fails pre-fix).
    * A ten-seed differential soak (5×400 mixed + 5×300 wide, seeds
      20260958–20260967) over the landed main before any change: clean —
      the pop hole had no demonstrated verdict impact on the generated
      surface; the fix is prophylactic hardening, the invariant is the
      tripwire that keeps it closed.

Verification for the landing: workspace suite (11 832 tests) green
except the standing non-arc set (the TLA sets cardinality test — the
sets front's; the recfun 180 s-cap timeout — documented) with the
invariant live in every debug test; clippy/fmt/rustdoc clean; Z3 parity
176/177, 0 disagreements (z3 4.16.0); wide 3×300 + mixed 3×400 fresh
seeds (20260970–20260975): 0 verdict disagreements, 0 refuted models;
debug-panic sweep over the parity corpus: 0 panics.

## Continuation 26 (2026-09-17): pinned direction-2 default-ON, scoped to wide states (item 61)

61. **The `NIXIE_S6_PINNED` gate is on by default — scoped.**  The
    gate's trade map is now clean end to end: every previously-documented
    cost was a downstream symptom of the two closed defects — the chain-sat
    twin's wall deflection (item 59's repair step) and the trivial mixed
    twin's crossed-probe pop hole (item 60's re-snap — the auditor-silent
    "pinned completeness loss" was never a pinned-derivation defect at
    all).  `NIXIE_S6_NDIR2` (the general form) stays default-off: its
    deflection cost persists, now as a 180 s timeout on the fi1
    regression instead of the pre-repair-step `unknown`.
    * **The screening that shaped the scoping**: flipping the gate on
      UNCONDITIONALLY failed the enablement rule's screening condition —
      an MBQI-heavy `scope_rebase` test (no wide row in sight) went
      36 s → cap-timeout: the per-final-check derivation cost lands on
      every instance while only wide-row states can benefit.  The landed
      default is `pinned_dir2 = !wide_rows.is_empty() && env-not-0` —
      wide-free instances are bit-identical to the gate-off binary
      (perf-gate conflict/decision ratios 1.000 on all 10 corpus
      instances), and the gate's win cases (mixed-magnitude LRA unsat
      twin, chain-sat twin, f1) are wide-row states by construction.
    * Screening at the new default: wide 3×300 + mixed 4×400 fresh seeds
      (20260977–20260983): 0 verdict disagreements, 0 refuted models;
      parity 176/177, 0 disagreements (z3 4.16.0); the wide-regression
      file 31/31 at the new default; the workspace suite green except
      the standing non-arc set; perf gate PASS (counters ≤ 1.05);
      panic sweep clean.  `NIXIE_S6_PINNED=0` remains the escape hatch,
      and the revert is the one-line flip the enablement rule prescribes.
