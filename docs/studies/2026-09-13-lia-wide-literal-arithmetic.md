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

## Continuation 27 (2026-09-17): the recfun non-termination decoded and closed — the boundary-escape treadmill (item 62)

62. **The second `24cb0567` casualty, answered** (the recfun front's
    handover asked the simplex owner what the propagation feeds the
    refinement path; the answer: nothing wrong — the propagation only
    moved the trajectory onto a pre-existing treadmill).  The decode
    (recfun-round traces, cert-variant prints, per-round model dumps,
    perf sampling):
    * `check_sat_recfun_with` unfolds the definition to a FUEL-scheduled
      depth with a SYMBOLIC boundary app (`sum (k − d)` — the boundary
      FOLLOWS `k`), solves, and certifies concretely.  On rejection it
      learns the touched applications — but learning pins only CONCRETE
      apps (`(sum 7)`, `(sum 11)`, …), and the symbolic boundary is
      untouched: every round's model escapes to the unfolding's
      truncation edge (measured: `k = 7, 11, 7, 8, 16, 16, 32` — always
      the fuel boundary, where the boundary app's free value satisfies
      `sum(k) = 6` for ANY `k`).  The certifier refutes, learning lags
      the ever-deeper edge by construction, and the rounds' growing
      instance sets make each solve slower: the non-termination
      (900 s+, rc=124 — confirmed by the recfun front).
    * The pre-`24cb0567` trajectory happened to propose an INTERIOR
      `k = 3` at round 3 and certified in 0.94 s — luck, not mechanism:
      the propagation's derived bounds reshuffled the search onto the
      edge-preferring trajectory (CDCL chaos, the BENCHMARKING §1
      lesson), and the treadmill became visible.
    * **The fix (driver-side, sound)**: the boundary-escape probe — on a
      rejected round with fresh learning, ONE assumption-guarded solve
      per pinned-range cap `C` (the max concrete learned argument) with
      every SYMBOLIC root-application argument held `≤ C`.  A model
      found there and CONCRETELY CERTIFIED satisfies the original
      assertions outright (the assumptions only guided the search);
      a failed probe leaves the treadmill exactly as it was.  The
      reproducer now answers `sat` with `k = 3`; the standing suite
      timeout (`recfun_e2e::symbolic_argument_solves_for_the_variable`)
      is gone — the workspace suite is fully green modulo the env
      self-test.
    * Cross-front note recorded in the wisas/recfun handover: the fix
      lives in the recfun driver (the treadmill is structural there);
      the propagation's role was trajectory-only.

Verification: workspace 11 850 tests green except the env self-test;
clippy/fmt/rustdoc clean; parity 176/177, 0 disagreements (z3 4.16.0);
wide 3×300 + mixed 3×400 fresh seeds (20260990–20260996) + the quant
fuzz: 0 disagreements; perf gate PASS (counters bit-identical — no
recursive definitions in its corpus).

## Continuation 28 (2026-09-17): wide-value publication — the exact model channel (item 63)

63. **The gap survey and its first slice.**  A 3×600-instance survey of
    the mixed-fuzz unknown-gap (seeds 20260958-class; 210/1800 = 11.7%
    unknown-where-z3-decides, 93% of them SAT-side) clustered the
    residuals into: div/mod disjunctive search capacity (~60%), the
    wide-value classes, and 17 pure-QF_LRA instances.  The smallest
    LRA member minimized to a single equation whose unique solution
    `xr = -27670116110564327424/13` has a NUMERATOR past `i64` — the
    LP converges (the wide store knows the value exactly all along),
    but `wide_underivable_blocks_sat` declined the whole verdict because
    the value does not NARROW: honest `unknown` for a decidable `sat`.
    * **The publication channel** (landed): `Simplex::wide_basic_value_exact`
      (the exact `BigRational` a wide basic's row evaluates to — the
      standard part of `eval_big_raw`), `ArithSolver::value_exact` (a
      term's exact value; Int-sorted terms publish only INTEGRAL exacts),
      the model builder's term synthesis (`(/ numer denom)` — via
      `mk_rdiv`, REAL division), and the gate relax (block only when not
      even exactly derivable).  The first cut used `mk_div` — EUCLIDEAN
      division — and `get-value` printed the FLOOR: a published witness
      violating its own assertion, caught by validating the model against
      z3 before trusting the green test.  Fixed, plus the printer gap it
      exposed (`Div` at `Real` sort printed `(div …)` — now `/`, keeping
      the round trip honest).  Regression:
      `wide_model_value_publishes_exactly_and_decides_sat` (verdict AND
      exact-numerator pins — the verdict alone passes on the gate relax
      alone, which would ship the default-value model).
    * Measured: the survey's gap moved 210 → 198 on the same seeds; the
      closed members are the publication-blocked class (the remaining 16
      LRA members decline elsewhere — see below).
    * **The second class, decoded and parked (the next item)**: the
      remaining minimized LRA instance traces to `check_core`'s
      `blocking_clauses_present()` downgrade — the search PROVES
      `Unsat` over assertions+blocks, and the blanket rule (upstream
      #40) answers `Unknown` because a block is "a restriction, not a
      consequence".  The over-conservatism is fixable in principle:
      blocks are added only for CONCRETELY refuted models, and the
      projection onto term variables preserves the violation (an
      assertion's truth depends only on term values), so every blocked
      assignment violates the assertions and an `Unsat` over
      assertions+blocks IS an `Unsat` of the assertions.  The open
      soundness question is the `Undef`-omission case in the projection
      (a don't-care variable the refutation's completion guessed): if
      `model_refutes_assertions` can return true on a model whose
      refutation depended on a completed — not asserted — value, the
      argument breaks.  Recorded for the next session with the probe
      map (verdict-site backtrace → `certify_result` → check_core's
      downgrade arm).

Verification for the landing: workspace 11 880 green except the env
self-test; clippy/fmt/rustdoc clean; parity 176/177, 0 disagreements
(z3 4.16.0); wide 2×300 + mixed 2×400 fresh seeds (20261017–20261020):
0 disagreements; perf gate PASS (counters bit-identical); the survey
rerun on the same seeds.

## Continuation 29 (2026-09-17): the blocking downgrade scoped to its unsound half (item 64)

64. **`Unsat`-after-blocking, classified.**  Upstream #40's blanket
    rule downgraded EVERY `Unsat` over a search that used model
    blocking — including refutations over blocks added for GENUINE
    violations.  The classification (`model_refutation_kind`):
    a *Genuine* refutation is a concrete `false` from ASSIGNED model
    values (the settled-atom arm reads committed polarities, the value
    arm fails open on `Undetermined`), so the blocked projection covers
    every variable the refutation read — every assignment the block
    excludes provably violates the assertions, and an `Unsat` over
    assertions+blocks IS an `Unsat` of the assertions.  An
    `Unrepresentable` outcome (the evaluator's own width limit) is NOT
    a genuine refutation — the block is exploratory and keeps the
    downgrade.  `model_blocks_nongenuine` tracks the latter (snapshot
    in `ContextState`, retracted in lockstep with the clauses); the
    downgrade now fires only while it is nonzero.  Measured on the
    survey generator: no verdict movement either way (the generator's
    sat-side blocks are width-limit ones — the minimized LRA instance
    correctly stays `unknown`); the change removes a
    completeness-overreach that discards proven refutations, at zero
    soundness cost (the projection argument) and zero differential
    movement.
    * **The unsat-side gap's site breakdown** (the 15 members, probed):
      5 at the wide-classification honest decline, 3 at the B&B integral
      dive's `state_feasible` probe (an "integral" leaf whose fresh
      probe finds a violation the dive should have branched on — e.g.
      the minimized `11·xi = 7` shape reaching an integral-looking
      leaf), 2 at the LP pivot budget, 5 at outer declines.  These are
      the B&B capacity campaign's precise targets (the parked item,
      now with a site map).

Verification for the landing: workspace 11 893 green except the env
self-test (the timeouts were load artifacts — load 77–106 through the
runs); gates clean; parity 176/177, 0 disagreements (z3 4.16.0); wide
2×300 + mixed 3×400 fresh seeds (20261030–20261034) clean; perf gate
PASS (bit-identical counters).

## Continuation 30 (2026-09-17): the B&B dead-leaf backtrack (item 65)

65. **The dive/leaf `state_feasible` decline, fixed at the leaf.**  The
    unsat-side gap's dive site (item 64's map, 3 members; minimized to
    `11·xi = 7` written through a `div`-by-1 feed): the search branches
    to an all-integral candidate whose LP point IS feasible, but the
    leaf probe (`state_feasible`) re-derives through the bound-snap
    `crash_basis` — a CRUDE point, not the search's vertex — lands
    outside the windows, and the old code unwound the WHOLE search to
    `unknown` ("Infeasible here is not a leaf").  The honest reading:
    the leaf needs a REPAIR.  The leaf arm now runs a full
    `simplex.check()` — a converging repair snapshots the model (`Sat`
    leaf), a refutation is a DEAD BRANCH whose backtrack tries the
    siblings (an all-dead tree answers `Unsat`), and the pivot budget
    keeps the honest `Unknown`.  The dead-leaf fall-through delivers
    the all-dead outcome to the existing unwind loop (identical to both
    branches having been tried and refuted).
    * Measured: the survey gap moved 196 → 181 on the same seeds — the
      unsat-side 15 → 13 AND the sat-side 183 → 168 (feasible integral
      leaves that used to hit the crude-point violation now
      repair-and-snapshot instead of declining).  Regression:
      `bnb_dead_leaf_backtracks_instead_of_unwinding_unknown` (fails
      pre-fix).
    * The remaining 13 unsat-side members: the wide-classification
      decline and pivot-budget sites of item 64's map (the campaign's
      residual targets).

Verification: workspace 11 909 green except the env self-test; gates
clean; parity 176/177, 0 disagreements (z3 4.16.0); wide 3×300 + mixed
3×400 fresh seeds (20261040–20261045) clean; perf gate PASS
(bit-identical counters); the survey rerun on the same seeds.

## Continuation 31 (2026-09-17): the wide-row refutation's unbounded-side bail (item 66)

66. **Two coordination defects in the wide classification, fixed.**  The
    unsat-side gap's wide-classification members (item 64's map, the
    largest site) minimized to `xi <= -2.3e18 ∧ xi >= -14` — refutable
    at the LP level with no B&B at all, yet declined to `unknown`:
    * `wide_row_refuted_by_bounds` bailed (`return None`) whenever ANY
      achievable-range endpoint was unbounded — including the side
      IRRELEVANT to the violation.  `v2 = v1 + c` with `v1 >= 0`
      (unbounded above) and `v2 <= 0`: the MIN side alone refutes
      (`min = c > 0 = upper`), but the unbounded MAX side hid it.
      Unboundedness now makes only ITS side's disjointness test vacuous.
    * the repair step's `bound_kind` inference read the STORED
      assignment entry — stale BY DESIGN for a wide basic whose exact
      value does not narrow — so the repair searched the reversed
      direction and found no eligible column.  The violated side is now
      read from the EXACT evaluation (`eval_big_raw`, lexicographic).
    * Measured: the unsat-side gap 11 → 7 on the same seeds; regression
      `wide_row_refutation_survives_an_unbounded_irrelevant_side` (the
      pinned contract — the pre-fix pass runs a slower repair route,
      the survey delta is the load-bearing evidence).  The remaining 7:
      the B&B node budget (1), the pivot budget (1), the honest
      `i64::MIN` corner (4), one outer.

Verification: workspace 11 920 green except the env self-test; gates
clean; parity 176/177, 0 disagreements (z3 4.16.0); wide 2×300 + mixed
2×400 fresh seeds (20261050–20261053) clean; perf gate PASS
(bit-identical counters); the survey rerun on the same seeds.

## Continuation 32 (2026-09-17): the SAT-side gap campaign opened — the full site map, the certification vocabulary slice landed, and a fresh PRE-EXISTING false `unsat` found and fenced (items 67–69)

67. **The gap survey reconstructed and the SAT-side site-mapped** (the
    items-54–66 handoff's open item 1).  The capture-loop survey ships as
    `bench/differential/gap_survey.py` (imports `mixed_fuzz.py`'s generator
    verbatim — the seed→instance mapping is identical to the standing
    differential; seeds 20261000–02 × 600).  On the handoff's start binary
    (`5c8bf7a8`): 156 members (149 SAT-side, 7 UNSAT-side) + 11 timeouts.
    Probe-binary attribution (tagged prints at every
    `TheoryResult::Unknown` return, every `resource_limit`/`resource_exhausted`
    set, every top-level `SolverResult::Unknown` return, arm-level tags in
    the wide classification):
    * **29** B&B `FracVar::Underivable` — branch bounds (floor/ceil of the
      exact value) leave `i64`: the honest width wall (dual-width bounds
      are the named project; item 42's `wide_floor_ceil_big` already
      recovers the recoverable).
    * **25** blocking downgrade with non-genuine blocks (item 64's residual;
      the `Undef`-omission projection question is the recorded design).
    * **22** big-const abstraction uncertified `Sat` — split by probe: 16
      declined at the certifier's HARVEST (vocabulary), 5 evaluated and
      genuinely failed (`no-combination` — the model the search found does
      not satisfy the original under the abstraction; the honest wall), 1
      evaluator-unsupported.
    * **17** B&B node/depth budget burn (the true "search capacity" class).
    * **10** `arith_atoms_need_theory` parse gate (the wide-const
      nonlinearity class of item 32).
    * **8** wide-repair NOCOL — `find_wide_pivot_col` finds no eligible
      entering column (repair eligibility rule; a heuristic item).
    * **6** BV late-minting 8-round budget (arithmetic div/mod atoms
      minting BV circuits — BV-front interplay).
    * misc tails (LP pivot budget, Diophantine GiveUp, outer declines).
    The campaign's implication: the SAT-side gap is NOT one class; the
    largest sound-completeness slice is the certification vocabulary (below),
    and the next-largest are the width wall and the blocking design question.
68. **The certification vocabulary slice, LANDED (`bc5e0b7a`)** — the 16
    harvest-declined members were declined because `harvest` had no
    `RealConst` arm: any ground goal carrying a Real literal (a decimal, a
    `(/ n d)`) was outside the certifier's vocabulary, so a `Sat` over the
    big-const abstraction could never publish.  The fix: `RealConst` is an
    accepted leaf; a Real literal or Real-sorted free constant records
    `saw_real`; **`prepare` still declines quantified/UF goals that saw a
    Real value** — the region/critical-set argument is written for `Int`
    and a Real value shifts atoms' crossing points OFF the critical set
    (an enumeration over it would not be exhaustive; this is a soundness
    gate, not conservatism).  The evaluator is now SORT-driven
    (`ArithDomain` from the node's sort): a Real-sorted `Div` over
    Int-valued operands is exact RATIONAL division, never the Euclidean
    floor the value-driven dispatch computed (unreachable end-to-end today
    — `arith_atoms_need_theory` gates symbolic-divisor atoms first — but
    the invariant is now structural, not incidental); `Add/Sub/Neg/Mul`
    widen by the same sort signal; comparisons and `Eq`/`Distinct` promote
    `Int`→`BigRational` exactly; `MAX_RAT_BITS` guards rational blow-up.
    Measured: the survey on the fixed seeds moves `gap_sat` 145 → 131
    (**14 recovered**, every one's published model validated by binding it
    as `define-fun`s and re-solving with z3 — all 14 `sat`), `unsat`
    576 = 576, timeouts 17 → 15.  Regressions: 3 unit tests
    (`ground_mixed_real_arithmetic_certifies`,
    `ground_real_division_is_exact_not_floored`,
    `quantified_goal_with_real_values_still_declines`) and 2 e2e pins
    (`big_const_mixed_real_goal_certifies_sat`,
    `big_const_mixed_unsat_goal_refutes_through_the_abstraction`).
69. **A fresh PRE-EXISTING false `unsat`, found by the differential's
    fresh seeds and fenced (NOT this slice's regression — the certifier is
    Sat-side only and cannot produce `unsat`)**.  Seed 20261102, instance
    17 of 400: z3 `sat`, nixie `unsat`; reproduces on `5c8bf7a8` (the
    handoff's start), `fd1f0595`, and the landed `bc5e0b7a` — live on
    `main` since before this stretch.  Shape: the fi1 class —
    `not(or …)` nesting over `div`/`mod` with a wide constant
    (−2^62) split across nested sums.  Bytes preserved:
    `docs/studies/assets/2026-09-18/false-unsat-mixed-fuzz-20261102.smt2`
    (full) and `…-core.smt2` (the TWO-disjunct core that still answers
    `unsat` — smaller than fi1's three: `D1 = (= (mod xi 4)
    (div (+ 2xi 77) 3))`, `D2 = (not (and C1 C2))` with C1's nested-sum
    constant assembly and C2 = `(>= (mod (- (div xi 7) 2) 5) -6)`).
    Shrink boundary: D1+D2-simplified (`v1`, `v2`) and D1+C1-only (`v3`)
    all answer CORRECTLY — the wrongness needs the nested C1 AND C2
    together.  Probes run: the strengthened `debug_verify_invariant` is
    SILENT on the core (the defect is not a tableau-shape violation), and
    the corner auditor (`NIXIE_S6_AUDIT=1`) is silent (not a wide-row
    propagation endpoint defect) — the remaining suspects are the cut
    layer (an unsound Gomory lemma), the div/mod axiom feed, or a
    reason-set hole in `explain_conflict`; the arc's probe set
    (row-history logging, set-bound backtraces, exact row validation at
    z3's model) decodes which.  **This is the next session's item 1 — a
    live wrong verdict outranks every capacity item.**

Verification for the landing: workspace 11 916/11 931 (the 15 failures
reproduce identically on clean `fd1f0595` — the pre-existing
corpus-missing set, another front's); clippy/fmt/rustdoc clean; Z3 parity
176/177, 0 disagreements (z3 4.16.0, re-run on the merged tree); wide
differential 3×300 fresh seeds (20261110–12) clean; mixed differential
seeds 20261100/01 clean, seed 20261102 = item 69's pre-existing find;
perf gate PASS (conflicts/decisions 1.000 bit-identical — the certifier
never runs on the gate corpus); debug-panic sweep 177/177 over the parity
corpus; survey delta on the fixed seeds as above.

## Continuation 33 (2026-09-18): item 69 decoded to the mechanism — the rescale-dropped bound that refuted a division axiom (item 70)

70. **The false `unsat` (item 69), decoded live to the plant.**  Probes:
    tagged `TheoryResult::Unsat` exports, reason/intern/assert algebra
    dumps, plant-time crossing records, the slice-6 consider/row trace, and
    a term printer at `conflict_from_terms` (worktree `/tmp/x69`, branch
    `x69-probe`, env `NIXIE_X69=1` [+ `NIXIE_X69_ROW=1` for row dumps] —
    instrumented by two interleaved sessions; left standing for the next
    step).  The chain, end to end, on the two-disjunct core
    (`…-core.smt2`, z3 model `xi = 658812288346769706`):
    * The endgame exports pairwise-pin lemmas on `mod(10xi,7)` (plausible,
      sound shapes), then the FINAL theory conflict blames **the division
      axiom `(= t (+ (* 3 (div t 3)) (mod t 3)))` for `t = 2xi+77` ALONE**
      — a theorem.  `conflict_from_terms` builds the clause `¬axiom`; the
      axiom is also an asserted clause ⇒ empty clause ⇒ false `unsat`.
      The item-54 fingerprint (single-atom core over an axiom), now
      reached through the bound-crossing export channel.
    * The crossing: `v1112 lo=(1,0) r=5 hi=(7/20,0) r=5`, where reason 5 =
      the axiom (one epoch; no staleness — one RESET, table continuous,
      `ntab=88` mapped consistently).  `v1112`'s tableau row is
      **`(20/7)·v1037 + 0`** and `v1037` is pinned `[7/20, 7/20]` r=5 by
      TWO independent pinned-row derivations (algebra verified sound:
      `v12 = −(20/7)v1037 + 1` pinned [0,0] ⇒ v1037 = 7/20; likewise
      through `v999`).  Therefore **lo=1 is CORRECT** (`20/7 · 7/20 = 1`)
      and **hi=7/20 is the UNSOUND bound — the UNSCALED v1037 value
      planted into the rescaled row's slack v1112: the 20/7 rescale factor
      was dropped on exactly one side**.
    * v1112 is never a slice-6 `dir2` target (no consider/ROW lines) — its
      `hi=7/20` arrives through the OTHER plant channel: the
      delta-propagation / `propagated`-list application
      (`propagate_bounds_in`'s tail `set_upper_delta(prop.var, prop.value,
      …)` or `on_nonbasic_bound_change`'s delta loop), i.e. the narrow
      direction-1 machinery passing through a RESCALED row.
    * **The remaining step (one probe iteration)**: instrument
      `set_upper_delta`/`set_lower_delta` (or the prop application) to
      print the writer of `v1112.upper = 7/20` — the suspected defect is a
      delta/value computed against the PRE-rescale row (coefficient 1
      instead of 20/7: `Δv1112 = Δv1037` instead of `Δv1112 =
      (20/7)·Δv1037`), the same scale-drop shape item 63 fixed on the
      MODEL-value channel, now on the BOUND channel through rescaled rows.
      The fix will follow the item-63 pattern: every consumer of a bound
      near a rescaled row must derive through the row's ACTUAL
      coefficients.
    * Layer note (AGENTS principle 2): the export channel guarded stale
      REASON ids (discard-stale-first at `check`) but nothing guards
      stale/un-scaled VALUES — and the strengthened
      `debug_verify_invariant` was silent because the corrupted state is a
      BOUND (bounds are only checked when a basic's window is violated at
      convergence; v1112's lo=1/hi=7/20 crossing was consumed as a
      conflict before the invariant's convergence point ran), and the
      corner auditor was silent because the plant is not a wide-row
      derivation.

The campaign's remaining classes (item 67's map) are unchanged; item 70's
fix is the priority — the reproducer, its two-disjunct core, and the probe
worktree are all standing.

Item 70 addendum (same day, second probe worktree `/tmp/x70` — now
removed; probe shapes recorded here): instrumenting every
`set_{lower,upper}_delta` write (fractional values) plus the crossing
record shows the SAME defect through a second manifestation on a slightly
different base (the landed tree): the exported crossing sits on **v6 with
row `(1/4)v7 − (1/4)v5 + (1/28)v2 + (1/28)v1 + 4611686018427387929/28`**
(the mod-4 and mod-7 axiom rows combined through a **1/28 rescale**;
4611686018427387929 = the folded C1/D1 constants), with propagated bounds
`lo = 6588122883467697047/40` vs `hi = 6588122883467697038/40` — a
crossing of **exactly 9/40** in the 1.6e17 range, both sides derived
(r=2 with rich aux sets), 9/40 = the fractional residue the two
derivations disagree by through the 1/4 and 1/28 scaled coefficients.
Consistent with the first manifestation (the 7/20 unscaled plant): the
propagation's exact arithmetic through RESCALED rows is the defect
surface — the derivations are not preserving the row's scale on one of
the two sides.  The next session's entry point: trace the two v6 bound
derivations' source rows and column reads (the `X70 set`/`crossing`
prints + the `X69 ROW` print shapes), and audit `propagate_bounds_in`'s
exact solve (`x_j = (basic − k − Σ c_k x_k)/c_j`) for the rescaled-row
case — candidates: a column bound read through the PRE-rescale row, a
weakened-integer bound consumed as exact, or the delta-loop's coefficient
(`Δ·c`) read against a stale row.  Both probe worktrees' prints are
described here; `/tmp/x69` (the parallel session's) was left standing.

Item 70 closure note (same day): the writer of the fabricated
`[7/20, 7/20]` pin is **`copy_bounds(old, fresh)` inside
`rehome_stranded_row_bounds`** — backtrace-caught at the write
(`set_lower_delta ← copy_bounds ← rehome_stranded_row_bounds ←
final_check`): a stranded slack's CURRENT (propagated) bound values were
copied onto a freshly re-interned row's slack whose form differs from the
old row's by the rescale/substitution factor (here 20/7), fabricating the
bounds of a different linear form.  The owning session's fix (in flight at
the time of this note) removes the copy in favour of re-asserting the
atom's own `∘ 0` bound with a live reason id, gated on
`var_referenced_by_any_row`; the decode above (both manifestations) is
consistent with it end to end.

## Continuation 34 (2026-09-18): item 70 CLOSED — the writer was the rehome's value copy; the sound fix and the gate postmortem (item 71)

71. **The item-69/item-70 false `unsat`, closed at the root and landed.**
    The "remaining one probe iteration" from item 70 ran
    (`set_upper_delta` write tracing + `Backtrace::force_capture` on the
    writer): the planter of `v1112.upper = 7/20` is **`copy_bounds`, called
    by `rehome_stranded_row_bounds`** — not the slice-6 propagation channel
    item 70 suspected.  The full chain, decoded end to end:
    * The stranded slack `v1037` (recorded form `−T74 + 2·T3 − 3·T14`,
      rhs −78, reason T80) still carried its live PROPAGATED pin
      `[7/20, 7/20]` (reason 5 = the T77 identity axiom, derived soundly
      through `v12 = 1 − (20/7)·v1037` with v12 pinned [0,0]).
    * The rehome re-interned the recorded form; `intern_row_reported`
      rendered it through the CURRENT tableau, resolving it to the RESCALED
      multiple `(20/7)·v1037` — item 70's rescale factor, appearing because
      the rendering substitutes through rows that themselves express the
      form via the old slack.
    * `copy_bounds(old, fresh)` then copied the pin's VALUE un-translated:
      `fresh = 7/20` asserts `(20/7)·v1037 = 7/20` — the 49/400-vs-7/20
      fabrication nobody derived.  It crossed the sound `lo = 1`
      derivation, and `record_crossing` exported the singleton conflict
      blaming T77 alone → learned unit `¬axiom` → false `unsat`.
    * **The fix** (lands with this entry): the sweep re-interns the
      recorded form as before, but re-asserts ONLY the ATOM's own `∘ 0`
      bound (scale-invariant under the positive rescale, so it carries
      soundly onto ANY rendering) with a reason id already live for that
      atom — never the old slack's current bound VALUES, which are
      coordinates of the OLD variable, not of the form.  `copy_bounds` is
      deleted (zero remaining callers).  `SlackForm` now records the
      assertion direction (`Le`/`Ge`/`Eq`) so the atom's own bound is
      reconstructible.  The instance decides `sat` (z3 model
      `xi = 658812288346769706`; nixie publishes 658812288346769908,
      hand-verified to satisfy ¬D1 ∧ C1 ∧ C2).
    * **The gate postmortem** (why `var_referenced_by_any_row` is NOT in
      the landed fix): the first cut also skipped any slack still
      referenced by a live row, on the Dutertre–de Moura argument that a
      pivot's rewritten row keeps the slack's equation live.  That
      argument is FALSE in this tableau, measured twice: the
      `parity_infeasibility_four_free_vars` and `bnb_dead_leaf`
      regressions both flipped wrong (a false `sat` with an invalid model,
      and a lost `unsat`) with the gate on, and a fresh mixed-fuzz seed
      (20261120) produced another false `sat` (`fs1`: `(= (mod 3xi 1)
      (− (div 5xi 1) 2))`, z3 `unsat`) — all three correct again with the
      gate off.  The restoration is load-bearing even for narrow-referenced
      slacks; WHY the preserved-equation argument fails (wide-store
      migration? column substitution? the rehome cadence itself?) is
      recorded as the next session's probe target, with the `fs1` shape as
      a reproducer factory.
    * Regressions: `rehome_does_not_fabricate_a_crossing_on_a_referenced_slack`
      (full seed-20261102 instance) and
      `rehome_false_unsat_seed_20261102_core_decides_sat` (the two-disjunct
      core) in `nixie-solver/tests/arith_wide_literal_regressions.rs`; both
      answer `unsat` on the pre-fix tree (revert-checked twice).
    * Verification: workspace 11 942/11 943 (the one failure is the
      in-flight `model_eval` SIGABRT of the parallel bags/parse session —
      it fails identically without this change); clippy/fmt/rustdoc clean;
      parity 176/177 Correct, 0 disagreements (z3 4.16.0); mixed
      differential 3×400 fresh seeds (20261120–22) + the home seed 20261102
      all clean; wide differential 3×300 fresh seeds clean; debug-panic
      sweep 177/177 zero panics; perf gate PASS with conflicts/decisions
      bit-identical at 1.000 (the rehome path only runs at
      arithmetic final-check; the gate corpus is SAT-core dominated).
    * Also resolved: the `(get-unsat-core)`-after-`check-sat` verdict flip
      observed while shrinking (the CLI's chunked execution walked the
      broken machinery down a different path) — both forms now agree `sat`.
    * Housekeeping: probe worktrees `/tmp/x69` (this arc) and `/tmp/x70`
      are REMOVED (the disk-pressure directive; every probe shape is
      recorded here and in item 70's addendum).  The parallel session's
      continuation-33 addendum described the in-flight fix as gated on
      `var_referenced_by_any_row` — superseded by this entry's postmortem;
      the landed fix has no reference gate.

## Continuation 35 (2026-09-18): the ±1-divisor identity folds land — 21 survey members back (item 72); item 69/70 closed by the rehome fix

72. **`div`/`mod` by a constant ±1 now folds to its identity at
    construction** (`cd0430a5`; Z3's `arith_rewriter` policy):
    `div_euclid(t, 1) = t` (hash-consed identity), `div_euclid(t, -1) =
    -t`, `rem_euclid(t, ±1) = 0`.  Before, only the both-operands-constant
    case folded, so a symbolic dividend under a ±1 divisor kept its
    Div/Mod node and entered the div-axiom feed — hiding linear structure
    (a pure-equality GCD-obvious LIA goal answered honest `unknown`; z3:
    `unsat`) and deflecting searches well beyond that class.  Measured on
    the survey seeds 20261000–02: **gap_sat 134 → 116, gap_unsat 7 → 4**
    (unsat 576 → 579, all z3-correct), net decisive +13; timeouts 12 → 20
    (load + trajectory reshuffle on instances that now search instead of
    declining).  The rewriter's own ±1 rules remain as the second line for
    raw-interned terms; the rewriter/encode tests now construct their
    nodes that way / with non-folding divisors.  Verification: workspace
    release-mode suite 11 924/11 940 — exactly the 15 known pre-existing
    corpus-missing failures (the debug-mode full-suite link hit
    `/media/data` at 100% mid-run; release covers the same tests);
    clippy/fmt/rustdoc clean; parity 176/177, 0 disagreements (z3 4.16.0);
    mixed 3×400 + wide 3×300 fresh seeds clean; perf gate PASS
    (conflicts/decisions 1.000 bit-identical); panic sweep 177/177.
    * Item 69/70's fix landed as `740c16bd` (the rehome never copies bound
      values across the stranding boundary) and CLOSES the core
      reproducer (`sat`, matching z3) — verified on the merged tree
      before this landing (the merge conflict's two appended test blocks
      both green: 36/36).  A process note for whoever reads the history:
      an interim read of "main ships red rehome tests" was one commit
      stale — the fix commit landed minutes after the test-build's
      branch point; re-verify the tip before believing a red set.

## Continuation 36 (2026-09-18): the crossed-window fabrication closed — interval derivations decline on inverted pairs (item 73)

73. **The `NIXIE_S6_NDIR2`-only false `unsat` (item 71's second find),
    root-caused and fixed** (`f60e26c8`).  The final conflict blamed six
    atoms — **all TRUE at z3's model `xi = 120`** (verified by hand
    evaluation) — an invalid lemma.  The chain: the general direction-2
    solve read the crossed (inverted) windows of v19 `[2349/40, 0]` and
    v63 `[1228, 0]`, and the endpoint selectors' `want_min == a_first`
    pick silently chose the pair's WRONG side on an inverted pair (a
    minimum request returns the UPPER bound) — fabricated bounds on
    v0/v2 that direction-1 then propagated into v19's lower bound,
    crossing the sound side and exporting the phony conflict.  **The
    fix**: both pair-swap selectors (`derive_bound_big_parts`'s column
    walk, `derive_var_bound_big_parts`'s general solve) DECLINE on a
    strictly inverted pair — the crossed state belongs to the crossing
    channel (`record_crossing` exports the real conflict), deriving
    through an empty interval is fabrication, and the vacuous-truth case
    loses nothing (the crossing fires on its own).  Equal bounds stay
    valid, so the PINNED default form (lo == hi basics) is unaffected —
    exactly why the defect was reachable only under the general gate.
    `derive_basic_bound` deliberately keeps reading stored bounds as-is
    (sound-input-sound-output; the fabrication site is the pair-swap
    selectors alone).  Measured: the ndir2 arm's deflection cost HALVED
    (timeouts 46 → 24, two of the six lost `unsat` verdicts recovered)
    but still net-worse than the default — **item 71's default-on
    refutation stands on capacity grounds, now without the soundness
    hole**.  Regression:
    `derivation_through_a_crossed_window_declines_instead_of_fabricating`
    (both selectors).  Verification: workspace release suite 11 929/11
    946 (15 known corpus-missing + the ~660 s rehome test's 180 s
    load-cap, passes in isolation); clippy/fmt/rustdoc clean; parity
    176/177, 0 disagreements (z3 4.16.0); mixed 3×400 + wide 3×300 fresh
    seeds + the finder seed 20261123 clean; perf gate PASS (counters
    1.000 bit-identical); panic sweep 177/177.  The survey's standing
    default numbers on the fixed seeds after this session's three
    landings: **gap_sat 111, gap_unsat 4, 1 648 decisive** (from 134/7/1
    626 at the session's start).

## Continuation 37 (2026-09-18): items 74-75 — the EQUAL-pair endpoint reason-side swap (the half of the selector defect item 73's decline left open), and the strict-atom rehome gap closed

74. **The seed-20261130 false `unsat`, found by the next day's fresh
    differential seeds and decoded to a two-line root cause.**  Shape: the
    mixed-fuzz div/mod family (`mod (mod 3xi 2) 7` under nested `div`s,
    2^31/2^40/2^62 constants, two of the surviving conjuncts semantically
    TAUTOLOGOUS — their atoms still mint the rows that mislead).  z3 `sat`;
    shrunk by ddmin to `equal_pin_endpoint_reasons_cite_their_own_side`'s
    bytes.  The decode pipeline was item 69's, reused verbatim: conflict-set
    polarity printing → ONE unsound pair `{(< 2 X) [F], (> 2 X) [T]}` over
    `X = mod(mod 3xi 2) 7` (jointly `X ≤ 2 ∧ X < 2` — satisfiable; z3
    agrees) → write-trace + backtrace on the poisoned bound → the slice-6
    direction-2 push `hi(v104) = 0 reasons=[72]` where the sound
    direction-1 derivation carried `reasons=[130]`.
    * **The mechanism**: `v104 = 2 − X` was PINNED `[0,0]` by two sides
      with different justifications — the `(< 2 X)` atom's own bound on
      the lower side, the `(= 2 X)` trichotomy pin's propagation on the
      upper.  The endpoint selector for two-sided pairs picked the side by
      COMPARING VALUES (`want_min == (lo.value < hi.value)`): for an EQUAL
      pair the tie-break resolves to the OPPOSITE side, so the min
      derivation cited the upper's reasons and the max the lower's.  The
      value choice is immaterial on an equal pair; the REASON choice is
      load-bearing — `hi(v104) = 0` (i.e. `X ≥ 2`), justified only by the
      equality pin, was attributed to the `(< 2 X)` atom (which implies
      only `X ≤ 2`).  The crossing then exported `{(< 2 X), (> 2 X)}` as
      refuted when the true refutation needed the equality atom — a
      learned clause eliminating the satisfiable `X ≤ 1` region.
    * **The fix** (two sites: `derive_var_bound_big_parts`'s and
      `derive_bound_big_parts`'s endpoint closures), COMPLEMENTARY to item
      73's decline: their fix closes the strictly-INVERTED pair (decline —
      the crossing channel owns it); this one closes the EQUAL pair their
      entry left as "valid" (value-wise true, reason-wise swapped).  Pick
      by SIDE — `lo` for a min request, `hi` for a max; with inverted
      pairs declined first, every surviving pair is well-ordered or equal,
      and the side pick IS the value pick for the well-ordered case.
      Revert-checked: the new regression answers `unsat` on the pre-fix
      tree.
75. **The strict-atom rehome gap, closed** (the same mechanism's missing
    half, found by reading while item 74 decoded): `cached_row_slack_strict`
    never recorded `slack_forms`, so a STRICT atom's row (`assert_lt`/
    `assert_gt`'s delta path — real-mode and unshifted strict bounds) that
    lost its defining row to a pivot never got re-homed: its `slack < 0`
    bound kept constraining a floating variable and the constraint was
    dropped from the live LP with no restoration — exactly the class the
    sweep exists to close, silently uncovered since the rehome's
    introduction.  `SlackDir` now carries `Lt`/`Gt`; the strict interning
    records its form; the sweep re-interns strict rows through the STRICT
    path (no normalizer sign flip) and re-asserts the atom's own STRICT
    zero bound — never a weakened `≤ 0`.  Screened by the wide + mixed
    differentials at the new default (no verdict movement beyond item 74's
    fix).
    * **The load-bearing-restoration question, reframed by measurement**
      (follow-up to item 71's open thread): at strand time the stranded
      slacks of the `parity_infeasibility` repro are referenced by 5-9
      NARROW rows and `old_val == form_val` — the pivot's rewritten row
      does keep the slack's equation live at that instant.  The
      restoration's load-bearing effect therefore runs through what the
      re-assertion FEEDS (the re-check loop's cadence, the
      `int_equalities` Diophantine feed, B&B's view of the atom), not
      through raw LP enforcement.  The precise channel stays open, now
      with the forensics pattern (reason-side tracing) that answered
      items 69-74 available for it.
    * Verification for the landing (at main `1fd5b96f` + both fixes): the
      five arithmetic pins green (the full-instance rehome test at 625 s
      in isolation, its documented load cap); clippy/fmt/rustdoc clean;
      parity 176/177 Correct, 0 disagreements (z3 4.16.0); mixed
      differential 7 × 400 clean (seeds 20261120-22, 20261130-32,
      20261140-41 + home seed 20261102); wide 3 × 300 clean; debug-panic
      sweep 177/177 zero panics; perf gate PASS, conflicts/decisions
      bit-identical 1.000.  The three failures seen at the 740c16bd base
      (`model_eval` SIGABRT, `si2_b03m`, `bench_679`) were pre-existing
      there and are fixed by the parallel front's landed work.

### Standing numbers after items 74-75 (2026-09-18, binary `d75fa881`)

The post-landing soundness sweep: **13 fresh mixed differential seeds ×
400 (20261120-22, 20261130-32, 20261140-41, 20261150-55) + 5 wide seeds
× 300 — zero verdict disagreements, zero refuted models**, after the two
wrong-verdict finds of the window (seeds 20261102 and 20261130) were
closed at their roots.  The gap survey re-run on the fixed seeds
(20261000-02 × 600, `bench/differential/gap_survey.py`): 113 gap members
captured, EVERY one an honest `unknown` against z3-decisive; the 1 575
decisive instances (1 095 `sat` + 480 `unsat`) agree with z3 with no
disagreement — no wrong verdict anywhere on the fixed-seed sample either.
The remaining gap is pure search capacity (item 67's site map governs);
the wrong-verdict ledger for the arithmetic arc's mixed-fuzz family is,
as of this measurement, empty.

## Continuation 38 (2026-09-18): item 76 — the non-monotone bound overwrite on content-shared rows, mapped but NOT reproduced (the next session's probe target)

76. **A latent overwrite class, identified by reading while auditing the
    rehome's declines.**  The audit first: gate-2 declines (the atom's own
    bound no longer on the stranded slack) are the NORM, not the exception
    — 3 788 of 3 792 decline events on the item-69 instance read UNTIED
    (`old_val ≠ form_val` at that instant) — yet 13 fresh mixed seeds ×
    400 and the fixed-seed survey show no refuted model: the mid-search
    assignment is routinely stale, so an untied reading is not a dropped
    constraint, and declines are sound when the remaining live bound is at
    least as tight as the atom's (a tighter propagated bound SUBSUMES the
    atom's own).  That soundness rests on `set_upper`/`set_lower` never
    WEAKENING a live bound — the doc comment says "Monotone", but the
    bodies OVERWRITE unconditionally.  And the collision is structural:
    `intern_row_cached` content-addresses by canonical form, so a STRICT
    atom's delta row (`slack ≤ 0−δ`) and a NON-STRICT atom's row over the
    same form (`slack ≤ 0`) land on ONE slack — whichever assert runs LAST
    wins, and a loose-last write erases the strictness (a false-`sat`
    shape for Real variables: the LP may then sit at exactly the excluded
    point).
    * **Not reproduced**: three script-order variants plus the 5 200-instance
      differential record stay clean — the re-assert cadence (every
      backtrack re-sends live literals) evidently re-tightens before any
      model is accepted.  The likely reachability needs a specific
      decision-level interleaving the SMT-LIB surface cannot order.
    * **The fix design, and its trap**: the naive "keep the tighter live
      bound" is UNSOUND as written — a declined weaker write leaves no
      trail entry, so popping the tighter bound's scope drops the weaker
      atom's constraint entirely (this is why the code overwrites
      blindly).  The correct shape is Z3's `lar_solver` bound discipline:
      a per-variable bound-shadowing stack where each accepted write
      journals the displaced bound, and an undo re-applies the shadowed
      one.  Do NOT land a decline without the journal.
    * Probe entry point for the next session: instrument the
      `set_upper_delta`/`set_lower_delta` writes for a shared-LinKey var
      with a STRICT-then-LOOSE order at different decision levels (a
      `push`/`pop` driver with mixed `lt`/`le` atoms over one Real form
      is the cheapest controllable shape), then check the model-accept
      path against the strict atom.

## Continuation 37 (2026-09-18): the blocking-downgrade design question advanced — the `Genuine` argument's LP-point dependence (item 74)

74. **Item 64's open soundness question, worked to its precise gap.**  The
    landed scoping upgrades an `Unsat` over assertions+blocks when
    `model_blocks_nongenuine == 0`, resting on: *a `Genuine` refutation's
    evaluation "read only assigned model values / committed polarities",
    so the block's projection (every definite SAT polarity, `Undef`
    dropped — `refuted_model_projection`) covers every variable the
    refutation depended on, and every assignment the block excludes
    provably violates the assertions.*  Reading the evaluator's actual
    read paths (`model_eval.rs`'s `Var` arm):
    * the SETTLED-ATOM arm reads committed SAT polarities — genuinely
      projection-covered ✓;
    * the numeric-USER-var arm reads `arith.value(term)` — the value at
      the CURRENT LP POINT, which is a function of the whole candidate
      (polarities + the tableau's chosen vertex + search state), NOT of
      the projection alone.  Under one polarity assignment the LP can
      have several feasible points; a `Genuine`-labeled refutation at one
      point does not establish that the polarity assignment itself is
      violating — the block then excludes assignments that may admit a
      satisfying point, and an all-genuine exhaustion on a SATISFIABLE
      formula would be a false `unsat`.
    * The remaining reads are safe-by-channel: unconstrained numerics
      return `Undetermined` (fail-open, never a refutation), proxies read
      repair-published model entries, Booleans/BV read the SAT/BV
      assignment.
    **The closure conjecture that would still save the upgrade**: a
    concrete `false` at the theory's own model under committed polarities
    implies some committed clause is falsified at that point, which the
    SAT core's Tseitin structure + theory conflicts can themselves refute
    — the block then records an already-dead polarity assignment and
    never loses a solution.  If that closure holds, the upgrade is sound;
    if a constructive counterexample exists (a SAT formula whose search
    exhausts through all-genuine blocks), the landed scoping is unsound
    and must tighten `Genuine` to projection-covered reads (settled atoms
    + committed polarities only).  **Next session's entry points**: (a)
    the construction test — a satisfiable goal with an under-determined
    LP whose candidate point violates a value-read conjunct while another
    point satisfies it (the `or`-of-comparisons shape with free Tseitin
    polarity is the candidate family); (b) the empirical check — the
    mixed differential runs blocking-active and has been clean across
    this session's seven fresh-seed runs, so no such instance has been
    *found*, but absence-of-evidence at n≈3k is not the proof; (c) the
    conservative fix if (a) succeeds: restrict `Genuine` to the
    settled-atom arm and re-measure the 22 blocked survey members (they
    currently keep `unknown` through ≥1 nongenuine width-limit block
    each — the upgrade does not fire on them today either way).

### Continuation 39 (2026-09-18): item 76 CLOSED, corrected in flight — the tripwire found the real writers, two guarded, one redesign reverted as unsound-in-effect (item 77)

77. **Item 76's record was half wrong, and closing it properly found real
    defects.**  The write-level trace (`check-sat-assuming` with atom/bound
    prints) falsified the "structural collision" claim first: the atom
    asserts go through `intern_row_reported` (a FRESH slack per
    (form, reason) — strict and non-strict atoms over one form mint
    SEPARATE rows), not the content-addressed `intern_row_cached`; the two
    interning systems are disjoint, so the hypothesized strict/non-strict
    overwrite cannot happen at the atom level at all.  What IS real: a
    `debug_assert` tripwire on any WEAKENING live-bound write
    (`set_{lower,upper}_delta`) fired on 7 tests' paths — reachable
    weakening writes, benign on every one of those instances but each a
    silent-constraint-drop away from a false `sat`:
    * **Writer 1 — `assert_eq`'s weak pin side**: the equality writes
      `[0,0]` over a slack that can carry a tighter propagated bound;
      the weak write was rescued only by the sibling tight write's
      crossing and the trail (a fragile ordering).  FIXED structurally:
      the weak side is never written (a live tighter bound on the same
      variable SUBSUMES the pin's zero; a skipped write leaves the
      crossed pair for the crossing scan).
    * **Writer 2 — the item-75 rehome's zero-bound re-assert**: same
      shape on the fresh row.  FIXED the same way.
    * **Writer 3 — `assert_eq`'s GCD-infeasibility witness** (by design):
      the crossed `[1,0]` window planted on a live column transiently
      weakens it.  A "cleaner" redesign (witness on a FRESH variable) was
      built, passed its unit targets — and FLIPPED the item-69 core back
      to false `unsat`: with a fresh witness the conflict degrades to a
      UNIT `¬equality`, which collapses against a unit AXIOM (the empty
      clause), while the live-column witness's crossing carries the
      column's live-bound reasons — a RICHER clause the search can
      satisfy.  **REVERTED, and the lesson recorded: the witness's
      live-column placement is load-bearing conflict design, not
      sloppiness.**  The transient weakening stays, guarded by the
      crossing order (set_lower precedes set_upper).
    * The tripwire ships as an env-gated probe (`NIXIE_BOUND_TRIPWIRE=1`)
      rather than a `debug_assert`: the RAW `set_*` API's contract
      legitimately includes loosening (its own unit test exercises it);
      the production writers are the guarded ones.
    * Verification: the 7 tripped tests all pass with the guards (their
      pre-change passes were benign-luck; now structural); the item-69
      full/core, item-74 pin, fuzzers, strict-row regressions green;
      workspace failures identical to the corpus/environment baseline;
      clippy/fmt/rustdoc clean; parity 176/177, 0 disagreements (z3
      4.16.0); mixed 5×400 + wide 2×300 fresh seeds clean; debug-panic
      sweep 177/177; perf gate PASS with the counters IMPROVED
      (conflicts 0.857, decisions 0.906 vs the f60e26c8 baseline — the
      weak-side skips remove wasted bound writes).

## Continuation 40 (2026-09-18): item 78 — the width wall's intern-time holdout closed (the S1/S2 survey slice), the capacity campaign's first landing

78. **The gap survey re-measured at `010f0e7e` (121 members, all honest
    `unknown`) and attributed by decline-site probes** (env-gated prints
    at the statement-position `Unknown` returns and the bare
    `resource_limit = true` sites): S1 (37 members) and S2 (52) — the
    two INTERN-time "the row's exact value does not fit the assignment
    vector" declines — dominated, ahead of the B&B budget/underivable
    pair A2/A3 (24/26) and the wide-repair decline S3 (16).  The irony:
    `update_assignment`'s re-derivation path had ALREADY adopted item
    28's migration discipline for exactly this shape (an unrepresentable
    row migrates to the wide store, its meaning survives exactly, the
    convergence classification owns the verdict) — the intern path was
    the last holdout, still setting the GLOBAL `resource_limit` and
    declining every mid-check intern of a wide-valued row.
    * **The fix**: S1/S2 now set only the staleness flag
      (`assignment_current = false`).  The next derivation routes through
      `crash_basis`/`update_assignment`, which migrates such rows to the
      wide store; the convergence-point classification evaluates them
      exactly (`wide_row_violated`, `BigRational`); the mid-check
      consumers' staleness guards already refuse stale vectors.  The
      check() entry-time `resource_limit = false` reset stays the
      channel-owner.
    * **Measured**: the survey on the fixed seeds moves 121 → **114
      members (7 recovered, every new verdict agreeing with z3)**; the
      S1/S2 sites vanish from the attribution, leaving A3 (26), A2 (24),
      S3 (16) — the B&B/repair slices that are the campaign's next
      targets.  Soundness screens: the 1 800-instance fixed-seed sample +
      5 fresh mixed seeds × 400 + 3 wide seeds × 300, zero disagreements,
      zero refuted models; parity 176/177 Correct, 0 disagreements (z3
      4.16.0); perf gate PASS, counters bit-identical 1.000 (the S1/S2
      path never fires on the gate corpus); debug-panic sweep 177/177;
      workspace failures identical to the corpus/environment baseline;
      clippy/fmt/rustdoc clean (one undocumented signature that had
      ridden in on a merge between verification and landing is documented
      in this commit).
    * Build note: parity for this landing ran on a worktree at
      `010f0e7e` + the patch — the just-landed XOR-congruence commit
      (`ce42f335`) breaks the plain workspace build
      (`congruence.rs:316`'s `prev + &format!(...)` — `String +
      &String` has no std impl), so the full-build gates cannot run at
      merged HEAD until its owner repairs it (reported here; their
      in-flight tree presumably carries the fix).
    * Regression watch, reported for the SAT-congruence owner: the
      `equal_pin_endpoint_reasons_cite_their_own_side` pin (~3.5 s at its
      `d75fa881` landing) times out at 165 s on committed `570d8ad5`
      BOTH with and without this change — a capacity deflection from the
      `ce42f335`/merge window, not from the S1/S2 slice.

## Continuation 40 (2026-09-18): the wide-LP build landed — the bound channel widened, the sticky declines retired, and the evaluator made exact (items 81–84)

Executed the handoff
(`docs/studies/2026-09-18-exact-arithmetic-wide-lp-handoff.md`).
**Survey delta on the fixed seeds (20261000–02 × 600): gap 113 → 47**
(66 members closed on the final merged tree — 68 SAT-side at this
build's own measurement before the parallel sessions' landings reshaped
the baseline; decisive 1 647 → 1 730), the perf gate PASS at counters
1.000/1.000 with wall 0.95 on the final tree (0.857/0.906/0.85 on this
build alone, pre-merge), and zero verdict disagreements anywhere (8
fresh differential seeds + the fixed seeds re-run — every newly-decided
verdict agrees with z3).  Landed as `9ae0a9bf` (merging the derivation
stamps and the item-78 intern-time holdout).

81. **The bound channel is exact** (`BoundValue` in `delta.rs`): the
    simplex's `lower`/`upper` stores hold `Narrow(DeltaRational)` or
    `Wide(Arc<BigDeltaRational>)`, with every consumer comparing exactly
    (`cmp_value`/`cmp_narrow` — narrow-narrow arms are the old i64 ops, so
    wide-free states execute the identical fast path; the perf gate's
    counters confirm bit-level neutrality on its corpus).  `set_*_exact`
    entries store values at any width; `record_crossing`, the violation
    scans, the SOI ratio tests, the pop re-snap, the interval refutation
    and the slice-6 endpoint selectors all read through the exact
    accessors.  Derived bounds store EXACTLY where they used to weaken for
    width (`tighten_int_bound_exact` computes the integral tightening in
    `BigRational`; `weaken_int_bound`'s i64-fit decline is gone).
82. **The point-value side store** (`wide_points`): a non-basic snapped to
    a wide bound (branch bounds at `2^63`, the `i64::MIN` corners) parks
    its exact point there; `assignment[]` holds the stale-by-design entry
    and the staleness flag defers.  Every exact reader
    (`point_value_exact`, `eval_big_raw`, `update_row_exact`) consults it,
    and `eval_expr`'s fast path routes wide-point rows to the exact
    evaluation — the strengthened definitional invariant caught the first
    version reading the stale entry (a plausible-but-wrong value with no
    overflow to catch).  **Two latent defects the widened bounds exposed,
    fixed at the root**: (a) `note_bound_change` snapped BASIC variables to
    their bounds, desyncing the entry from its own row (`pop`'s re-snap
    and `crash_basis` already skipped basics — this site lacked the
    check); (b) the WIDE-LEAVING pivot delta-propagated from the leaving
    basic's stale entry into the substituted rows — every row rewritten by
    a wide-leaving pivot now takes the `was_wide` contract (delta loop
    skips, commit recomputes exactly), item 43's discipline applied to the
    leaving side.
83. **The sticky declines retired** (`intern_exact_row` +
    `Simplex::intern_row_big_reported`): every `assert_*` entry whose
    `-rhs` leaves `Rational64` (`rhs = i64::MIN`) interns its row through
    the shared rescale-or-capture discipline — a positive rescale into
    width keeps the full narrow machinery, a row beyond any scaling is
    captured exactly in the wide store.  `unrepresentable_row_assert` is
    deleted; item 56's regression now pins DECIDABLE verdicts (the
    satisfiable side `sat` at `x = i64::MIN`, the crossed pair `unsat`,
    both z3-certified).  The `SlackForm` records the exact path so the
    stranded-bound rehome re-interns through it (the narrow re-intern's
    `-rhs` would wrap to a different row).
84. **The evaluator is exact** (`EvalVal::NumBig` in `model_eval.rs`): the
    model-verification gate's numeric channel widens — beyond-width folds,
    negations (`-i64::MIN`), subtractions and comparisons carry the exact
    `BigRational` instead of reporting `Unrepresentable`, and the `Var`
    read falls back to `value_exact` for wide-published witnesses.  This
    closes the item-64/67 nongenuine-block class at its root: the honest
    boundary-valued model (`x = i64::MIN` under `(-x > i64::MAX)`) now
    CERTIFIES where the width-limited gate blocked its own correct model
    as nongenuine and degraded a decidable `sat` to `unknown` (the
    release-wrap predecessor evaluated such atoms to the WRONG truth
    value — a false-`sat` hazard).  The handoff's example case and the
    `i64::MIN` int corner publish exact witnesses (`xr = -2^63 - 2`,
    `xi = -2^63 - 1`), each validated by binding the model as
    `define-fun`s and re-solving with z3; `get-model` prints them as
    values (the `?` placeholder the formatter used to emit for
    exact-published entries is fixed — arithmetic value terms delegate to
    the shared printer).  The B&B branch channel is widened end-to-end
    (`wide_floor_ceil_exact`, `FracVar::Branch` with integral
    `BigRational` bounds asserted via `set_*_exact`): `find_fractional_int_var`
    resolves through the exact point read with the HONEST integrality test
    (integral real part AND no infinitesimal — the raw-real-part read
    snapshot-published `r` for an `Int` variable resting at `r ± δ`,
    a witness violating its own strict bound), and
    `snapshot_lia_model` stores only honest integral narrow values.
    The model-blocking fixtures that leaned on the width-limit concession
    are re-scoped to their current-correct contracts (documented in the
    tests; a deterministic gate-only-refutation fixture is recorded as
    follow-up — the exact channel certifies or refutes every arithmetic
    shape the old fixtures used).

**Verification:** release-mode workspace suite — 11 970/11 970 on the
final merged tree (11 955/11 956 on this build alone under disk pressure,
documented; the 1 failure was the ~8-minute rehome regression at
nextest's 180 s cap under machine load 46 — verdict verified `sat` via
the CLI, 8m04s vs the baseline binary's 8m44s on the same input, and it
passes in-suite once the machine quiets);
doc tests, clippy `-D warnings`, fmt, rustdoc `-D warnings` clean; Z3
parity 176/177 Correct, 0 disagreements (z3 4.16.0); wide differential
3 × 300 + mixed differential 3 × 400 fresh seeds (20261170–75) plus the
fixed survey seeds 3 × 600 — zero verdict disagreements, zero refuted
models; debug-panic sweep 177/177 over the parity corpus, zero panics;
perf gate PASS (conflicts 0.857, decisions 0.906, wall 0.85 vs the
pinned `f60e26c8` baseline); gap survey on the fixed seeds 113 → 46
members, 70 closed (68 SAT-side, 2 UNSAT-side).  New regressions in
`nixie-solver/tests/arith_wide_literal_regressions.rs`
(`i64_min_real_strict_bound_decides_with_exact_model`,
`i64_min_int_strict_bound_publishes_exact_witness`,
`boundary_negation_certifies_the_min_valued_model`,
`exact_model_values_print_as_values`,
`boundary_scale_sum_bound_certifies`) plus the re-scoped
`i64_min_bound_rows_decline_instead_of_wrapping`, the model-blocking
contracts, and the evaluator's exact-channel pins in `model_eval.rs`.

## Continuation 41 (2026-09-19): item 85 — the latent delta-propagation invariant mapped, the exposure closed at the boundary, and the canary made release-runnable

**The item (from the derivation-stamps handover, pre-RESOLVED):** during
the stamp debugging a trajectory existed where the incremental snap-delta
update disagreed with exact evaluation by exactly 1/2 (the
`delta propagation mismatch` `debug_assert` in the pivot's row-update
loop). The stamps' three store defects are fixed and store-sequence
bit-identity was demonstrated, so *that* trajectory is gone — but the
assert's exposure was trajectory-dependent, not the defect: the item asks
for the minimal state in which the incremental update can disagree with
`eval_expr`, and either a fix or an unreachability argument.

**The invariant, spelled out.** After a pivot, for every substituted
narrow row `(var, new_row)` the propagation claims

```text
assignment[var] + snap_delta · coef(basic_var in new_row) == eval_expr(new_row)
```

which holds iff, at the delta loop's start: (I1) every entry the loop
accumulates on equals the exact evaluation of the row's *previous*
content at the pre-snap point; (I2) the only assignment entry that moved
since that base is the snapped leaving variable; (I3) the substituted
row is the same linear function of the original variables as the row the
base was computed from; (I4) `eval_expr` reads exactly the entries the
identity assumes.

**The guard inventory (why each attempted minimal state is closed under
the landed semantics):**

- *Stale base across pivots* — closed at the boundary: the pivot entry
  runs `if !self.assignment_current { self.crash_basis() }` (the
  div/mod `assignment[71] = 0` fix), so every flag-setting skip inside a
  pivot (wide-points guard, overflow refusal, entering-eval failure,
  wide entering row, wide updates) is erased by a full re-derivation
  before the next pivot can propagate on top of it.
- *A row whose entry is stale by design* — the `was_wide` skip (wide-
  leaving pivots) recomputes the entry exactly in the same pivot's
  commit; the wide-points skip leaves the row's entry drifting but skips
  it *every* pivot (the wide-point term persists in the row —
  substitution only replaces the entering variable), so a skipped row is
  never a propagated row.
- *Cross-row interference inside the loop* — an earlier iteration moves
  `assignment[var_T]`, and if a later row referenced `var_T` its delta
  would miss that move. Blocked by the canonical-tableau property: rows
  reference nonbasic variables only (the substitution replaces the
  entering variable everywhere), and the loop's `var`s are basics —
  `var_T` cannot appear in another `new_row`'s terms.
- *Arithmetic* — `checked_mul_delta`/`checked_add_delta` refuse on
  overflow (flag set, no write), and `eval_expr` is exact (the
  wide-LP build's item-84 evaluator).
- *The stamps trajectory itself* — the exposure needed *missing
  legitimate stores* (rows never substituted where they should have
  been); the three store defects behind that are closed, with
  690 070/690 070 store bit-identity demonstrated.

**Residual obligation, stated honestly:** the argument above walks every
input the delta loop consumes, but it is a reviewed argument, not a
mechanized proof — a future edit that lets an entry go stale without
setting `assignment_current`, or breaks the rows-reference-nonbasics-only
property, re-opens the hole silently. The assert is `debug_assertions`-
only, so release users had no protection at all.

**The landing:**

1. **`NIXIE_DELTA_VERIFY=1`** — the delta-vs-reeval canary is now
   release-runnable: every propagation is checked against
   `eval_expr(new_row)` and **reconciled to the exact value** on
   disagreement. The exact evaluation always wins, so a reachable
   incremental/exact mismatch degrades into a corrected entry rather
   than a silently corrupted assignment (the pre-RESOLVED trajectory
   would have self-healed instead of firing). Opt-in: the re-evaluation
   is the very cost the incremental path exists to avoid (the full
   per-pivot re-evaluation was 40–52% of QF_UFLIA runtime).
2. Evidence sweep with the canary active: mixed differential
   (120 fresh instances, seed 20260922) and wide differential
   (120 fresh, seed 20260923) vs z3 — no verdict disagreements, no
   refuted models; since a reconciliation is trajectory-changing, clean
   runs under the flag are direct evidence the incremental path agreed
   with exact evaluation on those trajectories. Bag-fold differential
   (60, seed 20260924) also clean.

Item 85 stays **open as a proof obligation** (mechanize the boundary
argument or find the reachable state); the canary is the standing tripwire.

## Continuation 42 (2026-09-19): item 86 — the floating-constant slice pinned at the root; the fractional numerator-column; three stale-read defects closed

Executed the items-69-78 handoff's open list against the CURRENT tree
(read the wide-LP handoff first: its items 81-84 already landed the
handoff's named project #1, so the session re-attributed the residual
before choosing a slice).  Landed as `bf9f5b71`.

86. **The re-attribution (decline-site probes rebuilt)**: at `77d80b3d`
    the survey's 47 members decompose as **A3 = 0** (the B&B width wall is
    GONE — the wide-LP build's `wide_floor_ceil_exact` channel absorbed
    it; the handoff's #1 was stale), **float class = 8** (the big-const
    column abstraction's column FLOATS: model publishes defaults → the
    evaluator refutes `Genuine` → the blocking loop degrades a decidable
    `sat` to `unknown` — sites J17/J5), **fractional parse-gate = 9** (a
    folded constant `n/d` with an out-of-range numerator: no λ helps, the
    integer column arm needs an integer, the parse gated the atom), A2 =
    24 (B&B node/depth budgets), S3 = 14 (wide-repair NOCOL), plus
    Q1/Q2 int-eq companions.  **The parallel session's "40 of 49 are
    div/mod capacity" reading was partly this**: the gated atoms carried
    div/mod too; the parse gate, not search capacity, held them.
    * **The fix stack (five pieces, one root)**:
      (a) `pin_int_const` — the synthesized constant column is PINNED to
      its exact value (wide singleton bounds; the reason term registered
      in `tautological_reasons` so conflict cores drop it knowingly — a
      constant equals itself in every model, so the learned clause stays
      entailed).  Assert-time, idempotent BY BOUND INSPECTION (a memo
      would skip the re-pin after a pop and float the column again).
      (b) The fractional numerator-column: `col ↦ n` at coefficient
      `-1/d` — no λ of the form `±1/2^k` can EVER shrink a numerator
      (it only cancels factors of two), so the E4 arm's honest gate
      becomes a column + pin; only a non-narrowable DENOMINATOR still
      gates.
      (c) **The column SIGN**: the column replaces the moved-to-RHS
      constant, so `coef·col = −moved` — the pre-existing integer arm
      entered at `+moved`, asserting the NEGATED constant (latent only
      because λ almost always wins; the `i64::MIN` flip special case was
      consistent with the same inversion).  Found as a **false `unsat`**
      (`gap_s20261000_i332`: z3 `sat`) on the FIRST version of the
      fractional arm, root-caused with the conflict-polarity pipeline
      (the decoder printed the pin's reason term in the final conflict);
      pinned by `constant_column_sign_convention_is_not_inverted`.
      (d) `value()`'s honesty guard covered wide ROWS only — a
      branch-and-bound bound beyond width parks an integer at a WIDE
      POINT whose raw entry is stale-by-design, and the model published
      `0` for a variable resting at `-9.2×10^18` (the evaluator refuted
      it; the same member degraded to `unknown`).  Both wide channels now
      read honest values; `can_increase`/`can_decrease` compare against
      the EXACT point for wide points (the stale read answered eligibility
      wrongly in BOTH directions — "cannot" declined repairable states,
      "can" pivoted variables resting at their bound).
      (e) The model builder's DL potentials no longer PREEMPT the exact
      channel (`value` → `value_exact` → DL — a DL potential for a term
      the simplex owns is a fabrication), and a row carrying a
      wide-constant column BREAKS DL PURITY (the difference graph cannot
      see the pin; a `Consistent` over a floating column certified a
      relaxation).
    * **Measured**: survey on the fixed seeds at my base `77d80b3d`:
      47 → **31** (16 recovered, every new verdict agreeing with z3,
      every published model validated by binding it as `define-fun`s and
      re-solving the negation with z3).  On the CURRENT main
      (`3533b461`, post the SAT pre-search-factoring landing — which
      alone moved the survey 47 → 115 by trajectory reshuffle): 115 →
      **37**.  Differentials: 3 fresh mixed ×400 + 3 fresh wide ×300 on
      the fix build, and fresh seeds re-run at each rebase (6 more),
      zero disagreements, zero refuted models.  Parity 176/177 Correct,
      0 wrong (z3 4.16.0).  Perf gate PASS, counters 1.000/1.000 against
      the pinned baseline `2b0b4d54` (the first WARN — 1.087 geomean —
      was the gate comparing against a baseline that carries the
      factoring change my pre-rebase base lacked; the one 3.5× SAT-comp
      cell is factoring's, not arithmetic's).  Debug panic sweep 0.
      Suite 11 961/11 976 (the 15 are the documented corpus-missing
      class; the new regressions 5/5).  clippy/fmt/rustdoc clean (one
      dead `if` from the stamps landing removed in-flight — main's owner
      landed the same removal independently and the rebase kept theirs).
    * **Disk-pressure notes (cost real time)**: `/media/data` pinned at
      100% by concurrent agents' shared `target/` all session; the debug
      full-suite links SIGBUS on ENOSPC (the documented trap).  The
      battery completed with `CARGO_TARGET_DIR` on the ROOT disk
      (129G free; the "never /tmp" directive's concern is filling the
      root disk — ~10G, deleted after) — document, don't repeat
      casually.  The gap survey measures TIMEOUTS under load: re-measure
      quiet before believing a delta (a 115 read under full test load
      reproduced exactly quiet, but only because both runs were equally
      loaded-vs-quiet checked).
    * **What remains (the next session's map)**: A2 B&B budgets (24
      members — any bump is a heuristic change: matched nulls, ≥10
      seeds, `docs/BENCHMARKING.md` FIRST; check whether the pins
      already shrank it — the 37-member attribution is the starting
      point), S3 wide-repair NOCOL residual (the eligibility rule after
      the wide-point fix; re-attribute first), 3 float members left
      (J17×1 + J5×2 — other publication shapes; the `[mb]`-style probe
      at the model builder's term loop is the tool), the item-75 strict
      reproducer, item 71's re-assertion channel question, and fi1
      (unchanged).  The probes are NOT in the tree (session-local, as
      before): rebuild from this item's site names — J17 = the blocking
      downgrade in the CDCL Sat arm, J5 = `arith_abstracted_big_const`
      uncertified, E4 = the fractional parse arm, plus the statement-
      position Unknown returns the previous sessions used.

## Continuation 43 (2026-09-19): item 87 — the wide-row interval refutation's sign; the S3 residual's dominant mechanism closed

87. **`wide_row_refuted_by_bounds` accumulated negative-coefficient terms
    with a FLIPPED sign**: the endpoint choice folds the sign (for `c < 0`
    the minimum sits at `hi`), so the contribution is `+ c·hi`, but the
    accumulation ran `acc(..., -1)` — subtracting it, computing a range
    wider than the truth by `2·c·hi` per negative term.  Conservative in
    the safe direction only (the widened range can only FAIL to refute),
    so no verdict was ever wrong — but valid refutations were missed, the
    wide-repair step then found every direction blocked at its bound
    (NOCOL — the repair-eligibility rule was NEVER the design problem),
    and the check declined LP-infeasible states to `unknown`.
    * **Found by re-attributing the 110 members at `bf9f5b71`** (the
      rebased tree includes the parallel sessions' MBQI/bags landings;
      the S3 tag led 45 of 110).  The NOCOL dump showed every term
      blocked AND the row's current value already at its true minimum —
      the interval refutation should have fired; reading its range
      accumulation found the sign.  Landed as `d542bd56`.
    * **Measured**: survey 110 → **91** (19 recovered: 16 sat + 3 unsat,
      every new verdict agreeing with z3; the recovered `xi = 9` model
      on the pinned instance z3-validated by binding and re-solving).
      Differentials 3 fresh mixed ×400 + 3 fresh wide ×300 clean; parity
      176/177 (z3 4.16.0); perf gate vs `bf9f5b71` counters 1.000/1.000;
      debug panic sweep 0; the arith crates' suite green except the
      documented corpus-missing class.  Regression:
      `wide_row_interval_refutation_sign` (the fuzz instance verbatim).
    * **The residual 91's shape** (for the next session): A2 B&B budgets
      with Q1/Q2 int-eq companions remain the largest named slice, plus
      the probe-silent ~49 (timeouts and the J-class solver-level
      declines — J17/J5 float shapes still exist beyond item 86's
      publication fixes).  Re-attribute before choosing: the probes are
      session-local (see item 86's site names).

## Continuation 44 (2026-09-19): item 88 — the J5 class decoded: the theory's Sat carries an unresolved integer; no code landed (the map, the sketch, and a zero-delta hole)

88. **The 91-member residual re-attributed at `d542bd56`: J5 leads with
    61** (the big-const certification gate), A2+Q 27, S3 residual 1,
    J17 ×2, J21 ×1.  The J5 slice is NOT a certification defect — decoded
    to the root on `gap_s20261000_i101`:
    * The theory hands the solver a `Sat` whose model contains an
      integer variable the theory CANNOT VALUE — `value` and
      `value_exact` both `None` while `point_value_exact` is `Some`
      (FRACTIONAL): a wide-basic integer resting at a fractional exact
      value the narrow channel cannot narrow.  The model builder then
      publishes the SORT DEFAULT (`0`) for it, the (exact, Euclidean,
      `BigInt`) certifier correctly refutes the candidate (`verify
      FALSE` — e.g. `xi = 0` against its own committed atom
      `(> (- (* 3 xi) 2) -11)` reading true), and the gate downgrades to
      `unknown`.  The pins are NOT implicated: the same shape would fail
      over any default.
    * **Why that is not the blocking loop's problem**: the model-
      refutation gate (which blocks and re-solves, J17's route) runs
      inside the search loop; the big-const gate runs AFTER the search
      returns `Sat` — the bad candidate exits before the blocker ever
      sees it.
    * **The next session's entry points**: (1) why the search's `Sat`
      carries an unresolved integer — the B&B's acceptance paths
      (`snapshot_lia_model`'s `else { continue }` SKIPS unresolvable int
      vars without blocking; `find_fractional_int_var` scans `int_vars`
      — check whether the variable is IN that set: an unmarked Int
      term is treated as continuous and never branched), and (2) the
      model builder's default-for-value-less (model_builder's `0`
      completion) should NOT fire for a variable the theory declines —
      omit it and let the evaluator's unset-atom arm speak.  Probes:
      the THEORY-VALUES dump at the J5 site (`value`/`value_exact` per
      assertion var) is the fastest discriminator; the certifier's own
      arms print via the `[cert: ...]` probe set (real-declined /
      prepare-None / combos / verify-FALSE / exhausted / unsupported).
    * **A zero-delta hole found and NOT landed**: the search loop's
      terminal `Sat` return (after blocking/repair rounds — the site
      just above "Build partial model for MBQI" in `check_core`) exits
      MODEL-LESS when the repair rounds cleared the first candidate's
      model: `self.model.is_none() → build_model` before returning is
      the sketch.  Measured: recovers none of the 61 (all candidates
      genuinely bad), so it landed nowhere — but a user `get-model`
      after that path would print "no model available"; worth bundling
      with the real fix above.
    * Soundness screens this session: the 91-member screen and 6 fresh
      differential seeds (3 mixed ×400 + 3 wide ×300) at the sign-fix
      build, zero wrong verdicts, zero refuted models.

## Continuation 45 (2026-09-19): item 89 — the J5 root FIXED: the B&B snapshot is exact at any width; the leaf's integral value survives the scope pop

89. **Item 88's decode, executed to the root and landed (`db596013`)**:
    the integral dive snapshots at its leaf INSIDE the scoped branch
    bounds, and the scopes pop right after — restoring the fractional
    pre-dive point.  The narrow-only `lia_model` deliberately left
    beyond-width integral leaf values to `value_exact`'s LIVE read "on
    the assumption it would still be readable later" (the snapshot's own
    comment) — the popped state declined it, the model builder published
    the sort default `0`, and the exact certifier correctly refuted the
    candidate.  **`lia_model` now holds `BigRational`**: the snapshot
    stores the integral rounded value at any width, `value()` narrows it
    for the narrow channel (declining to the exact channel), and
    `value_exact()` returns it outright — both prefer the snapshot over
    the post-pop live state.
    * **Debug notes that cost time (do not repeat)**: three probe
      iterations were corrupted by (a) an f-string writing the INDENT
      COUNT instead of spaces — a syntax error whose stale-binary
      runoff produced phantom "never runs" conclusions (final_check and
      the arith loop DO run; verify probe placement against a fresh
      build before believing an absence), and (b) sequential line-index
      inserts shifting later tags off their statements.  Verify every
      probe fires on a known path before trusting its silence.
    * **Measured**: survey 91 → **79** (12 recovered, every new verdict
      agreeing with z3; the recovered `xi = -49806208999015789358`
      model z3-validated by negation).  The other ~49 J5-tagged members
      now decline at GENUINELY BAD candidates — the certifier's
      `verify FALSE` is honest there: the dive's leaf satisfies the
      TABLEAU but not the original formula (the div/mod axiom feeds are
      loose at the leaf — the parallel session's "search capacity over
      the div/mod axiom feeds" reading, now precisely located at the
      DIVE's acceptance, not the budget).  Differentials 3 fresh mixed
      ×400 + 3 fresh wide ×300 clean; parity 176/177 (z3 4.16.0);
      gate 1.000/1.000 wall 0.93; panic sweep 0; arith suite green but
      the documented corpus-missing class.  Regression:
      `bnb_snapshot_survives_scope_pop_at_any_width` (the fuzz instance
      verbatim, model-pinned).
    * **Residual 79's map**: the div/mod-leaf-acceptance class (the
      ~49 above — entry: `integral_dive`'s `state_feasible`-and-scan
      acceptance vs. the div/mod defining axioms' tightness at the
      leaf), A2 budgets, and the tails.  Item 88's zero-delta hole (the
      model-less terminal `Sat`) remains documented and unlanded.

## Continuation 46 (2026-09-19): item 90 — the leaf snapshot's REAL half: δ-instantiated inside the leaf's scopes

90. **Item 89 fixed the integers; the reals were the same defect one
    layer down** (`65228ee8`).  The dive's scopes pop after the
    snapshot, restoring a point that can RE-VIOLATE strict bounds the
    leaf satisfied — e.g. a basic resting at its strict bound's real
    part with no infinitesimal (`(0, 0)` against `(0, +1)`; the narrow
    `find_violating` IS delta-aware and would repair it, but it runs at
    CHECK time, not at publication).  The δ-instantiation computed over
    the popped state then declines (no positive δ₀ exists over a
    violated strict bound), and `value()`'s real arm has no snapshot —
    EVERY real published the sort default `0`.  The exact evaluator
    refuted the candidate and the big-const gate downgraded a decidable
    `sat` to `unknown`: this instance published `xr = 0` while the
    tableau held `2147483572/3`, flipping a conjunct that sits exactly
    on its strict boundary (`3·xi + 3·xr + 85 > 5` at `= 5`).
    * **The fix**: `snapshot_lia_model` records the leaf's real values,
      δ-instantiated INSIDE the leaf's scopes (a leaf with no positive
      instantiation leaves them unpublished, never guessed), and
      `value()` prefers the snapshot for BOTH sorts before any live
      read (`value_exact` already did, item 89).
    * **Measured**: survey 79 → **75** (the arc's cumulative run on
      these seeds: 150 → 110 → 91 → 79 → 75 across items 86–90), every
      new verdict agreeing with z3; the recovered model validated by
      binding all four variables and negating the assertion (z3:
      `unsat`).  Differentials 3 fresh mixed ×400 + 2 fresh wide ×300
      clean; parity 176/177 (z3 4.16.0); gate 1.000/1.000 wall 0.99;
      panic sweep 0; arith suite green but the documented corpus-missing
      class; clippy/fmt/rustdoc clean.  Regression:
      `leaf_snapshot_covers_real_variables` (the fuzz instance
      verbatim, default-0-pinned).
    * **Decode notes**: the certifier-side probes (`[cert-false]` +
      `INTERP` with `manager.resolve_str`, and `delta_instantiation_exact`'s
      per-arm `[d0-*]` prints) are the fastest route for this class —
      the failing CONJUNCT under the published values names the
      fabricated variable directly.  The residual 75: the div/mod
      leaf-acceptance class remains (candidates now honest but
      tableau-vs-original divergent), A2 budgets, and tails.
## Continuation 43 (2026-09-19): item 85's evidence obligation served — the canary made audible, 1 917-file corpus sweep, zero reconciliations

The delta-vs-reeval canary (`NIXIE_DELTA_VERIFY`) reconciled SILENTLY —
a tripwire that could not trip audibly, so its evidence was not
gatherable beyond verdict-neutrality.  The reconcile site now prints
(`[delta-verify reconcile v{i}: delta-said=… exact=…]`; default-off with
the flag, so default behavior is unchanged).

**The sweep** (every run under `NIXIE_DELTA_VERIFY=1`, stderr watched):
the parity corpus (177) plus a stratified SMT-LIB sample — 200 per
arithmetic family over QF_LIA/QF_UFLIA/QF_ANIA/QF_AUFLIA/QF_NIA/QF_IDL/
QF_UFIDL/AUFLIA/UF (1 740; UFLRA's 15 included) — **1 917 files, ZERO
reconciliations**, plus 500 fresh mixed-fuzz instances across two
canary-active differential runs (verdict-identical vs z3, as they must
be either way).  This extends item 85's original 120+120 evidence by
an order of magnitude: across every corpus trajectory the incremental
snap-delta update agreed with exact evaluation at every pivot.

The obligation stands as stated (a reviewed boundary argument plus this
evidence — not a mechanized proof); the canary is now a tripwire a
corpus run, a differential, or a user can actually hear.

## Continuation 47 (2026-09-19): item 91 — the div/mod leaf-acceptance class decoded ONE LAYER DEEPER: wide-row explosion + constraint detachment (mapped, not fixed)

91. **The ~40-member "div/mod leaf-acceptance" residual decoded on
    `gap_s20261000_i423`** (the J5 gate's `verify FALSE` on an otherwise
    honest model): the failing conjunct is the equality
    `5·yi + mod(3yi−8,5) + 2·xi = 4611686018427387905`; the candidate
    violates it by exactly 34 (the theory's mod slack would have to be 34,
    outside `[0,4]`).  The div/mod axioms are COMPLETE and correct (the
    div/mod pair's values check out exactly); the atom is committed
    `True`; `assert_eq` fires; **and yet no tableau row enforces the
    constraint**:
    * The `atom_rows` cache maps the atom to slack `v301`, whose CURRENT
      row is `v301 = v6` — the pivot chain reduced C3's row to a single
      trivially-zero variable, DETACHING it from `(yi, mod, xi)`.  The
      tableau is internally consistent the whole way (no violated
      basics, no rows referencing basics, the debug definitional
      invariant passes) — the row's FORM no longer means C3.
    * **The zoo it happened in**: `wide_rows` holds ~150 NEAR-DUPLICATE
      rows at this gate — the same linear form under different slack ids
      (v239 ≡ v264 ≡ v249 ≡ …; v289 ≡ v288 ≡ v296 ≡ …).  The narrow
      channel is content-addressed (`intern_row_cached`); the WIDE
      channel (`intern_row_big_reported` → `intern_wide_row`) is NOT —
      every rebuild round (MBQI/blocking rebases re-assert the atoms)
      mints FRESH wide rows for the same content, and the wide-repair
      pivots then churn between the duplicates.  A constraint detached
      in that churn is the prime suspect for the C3 corruption (and the
      duplication alone is a serious capacity defect: every wide
      classification pass iterates all of them).
    * **Entry points for the fix session**: (1) content-address the wide
      intern (a `wide_row_key` map, mirroring `intern_row_cached` —
      this alone kills the 150×); (2) re-verify the atom-row equivalence
      after wide pivots (a debug-mode canary: for every
      `atom_rows` entry, the slack's row must still ENTAIL the key's
      linear form over the current basis — the definitional invariant
      does NOT check this); (3) the probes used here:
      `debug_atom_row(reason)` (cache key vs current row),
      `debug_rows_with_column` / `debug_wide_rows_with_column` (the
      zoo), and the certifier's `[cert-false]` + `INTERP`
      (`manager.resolve_str`) for the failing conjunct under the
      published values.
    * Reproducer: the instance verbatim (bytes in the survey corpus;
      seed 20261000, index 423); pre-fix verdict `unknown`, z3 `sat`.
    * No code landed this item — the two defects named above are real
      but the fix touches the wide-pivot core and must land with its
      own battery; nothing here should land unverified.

## Continuation 48 (2026-09-19): item 92 — item 91's defects executed: the wide intern content-addressed, the atom-row canary landed (silent), and the detachment's status

92. **Both item 91 fixes landed (`6d8ee66f`)**:
    * **Content-addressed wide rows** (`BigLinKey` over the substituted
    exact form, mirroring the narrow channel's `row_ids`/`LinKey`): the
    rebuild rounds' re-asserts no longer mint duplicates.  Survey 75 →
    **73**, every new verdict agreeing with z3; the arc's cumulative run:
    **150 → 110 → 91 → 79 → 75 → 73**.
    * **The atom-row equivalence canary** (debug, at `check()` entry):
    every interned atom row's slack must satisfy `slack = r·(key form)`
    at the current point for positive `r` (Eq sign-normalization allows
    negative).  Three false-positive classes found and gated, each
    verified against a live false positive it eliminated: popped atoms
    (the live-bound gate — rows are search-global, their constraints
    are not), floating constant columns (the pin-liveness gate — the
    big-const abstraction's column poisons the key-form evaluation when
    its pin is down), and stale assignment vectors (the freshness gate —
    a mid-search basic entry is not evidence).
    * **The canary is SILENT post-gates**: across the full debug arith
    suite (4689/4703, the 14 the documented corpus-missing class) and
    the 224-file debug panic sweep — zero fires, including on the i423
    reproducer.  Two readings, unresolved at landing: (a) the dedup
    removed the corruption's vector (the duplicate-zoo churn), and
    i423's residual `unknown` is a later blocker (budget/S3-class), or
    (b) the detachment happens in states the gates exclude and the
    canary needs a convergence-point placement.  The pre-gate canary's
    firing vocabulary (r = 0 detachments, r = −1/43 sign flips) is the
    decode tool for whichever it is.
    * **Battery**: 6 fresh differential seeds clean; parity 176/177
    (z3 4.16.0); the perf gate PASS 1.000/1.000 vs the re-pinned
    baseline `1710e125` (NOTE: `bench/perf_gate/BASELINE` was re-pinned
    by a parallel session mid-run — an explicit GATE_BASELINE override
    against a stale pin produces spurious `base=none` mismatches when
    the old binary is cleaned; always re-read BASELINE before gating);
    debug panic sweep 0; clippy/fmt/rustdoc clean.

## Continuation 49 (2026-09-19): item 93 — the detachment PROVEN form corruption in the dive window; the tripwire landed

93. **Item 92's open question answered** (`7972fb4e`): the corruption is
    (b) — real FORM corruption, invisible to the check-entry canary's
    placements.  The proof chain on the i423 reproducer:
    * A convergence canary (post-LP-solve) fires ZERO times; the landed
      check-entry canary is silent — the rows are healthy at every
      theory-check boundary.
    * A LEAF canary (at the dive's snapshot) fires with the decisive
      discriminator: **entry == own-row != key-form** on every victim —
      the definitional invariant holds (no staleness), the rows
      themselves no longer entail their atoms' constraints.  The
      corruption window is the DIVE: branch-bound pushes + their
      re-feasibility pivots.  Victims include wide slacks.
    * Deltas are small even integers (+66, +242, +44) and one sign flip
      (r = −1/43) — consistent with a wrong-coefficient rewrite, not a
      wholesale row replacement.
    * **Landed**: `NIXIE_LEAF_TRIPWIRE=1` (print-only, release-runnable,
      the BOUND-TRIPWIRE precedent) with the entry/own-row/key-form
      discriminator inline.  Zero behavioral change by default; the
      arith suite unchanged.
    * **The next session's entry point**: a per-rewrite VALUE-PRESERVATION
      tracer in the pivot commit loops — each rewritten row must take
      the same value at the pre-rewrite point as before (old form vs new
      form at the current values); the FIRST failing rewrite is the
      corrupting one.  Prime suspects by window: the wide-repair pivots'
      dependent rewrites (`substitute_row_big`'s per-variable
      accumulation) and the dive's `set_*_exact`-triggered
      `on_nonbasic_bound_change` propagation into dependents.  The
      tripwire is the acceptance test for the fix.

## Continuation 50 (2026-09-19): item 94 — the detachment hunt's decisive narrowing: r = 0 at [snapshot] only; the row-writing machinery exonerated

94. **The tracers built and run** (session-local, recipes below):
    * **Pivot form-preservation** (both commit loops, narrow AND wide):
    every rewrite must satisfy `NEW[v] = OLD[v] + sc·E[v]`
    coefficient-wise.  **ZERO breaks over the whole i423 run** — the
    pivot machinery is exonerated.  (The first tracer version had a sign
    error in its own identity — `old = new + sc·E` instead of
    `new = old + sc·E` — and "fired" 3 times on healthy rewrites; verify
    the tracer's algebra on a known-good run before trusting its
    fires.)
    * **Wide migrations**: form-copies (identical coefficients,
    `big_r64`-widened) — exonerated.
    * **Intern-time equivalence**: 115 raw fires, ALL stale-vector
    artifacts (the input's basic terms read stale entries while the flag
    is down — the documented mid-search intern allowance); the interned
    FORMS are exact.
    * **The refined tripwire** (landed `01fc31a0`): call-site tags
    (`snapshot` / `dive-pre` / `dive-post`), the rowless/unevaluable
    skip (class #4: a slack that left the basis is enforced by its
    bound plus the pivot's reparametrization), and the `SlackDir` per
    fire.
    * **The verdict**: `r != 0` fires on Le/Ge rows are
    bound-compensated sign flips (legitimate); the REAL class is
    **`r = 0`, firing ONLY at [snapshot]** — basic slacks with defining
    rows whose value (0) is no multiple of their key form's evaluation
    (−22/−44).  The corruption window is the dive's BASE CASE:
    `find_fractional_int_var` / `state_feasible` (crash_basis + the
    wide classification) — between a clean `dive-post` and the
    snapshot's reads.  The next session's probe: instrument
    `state_feasible`'s constituents (crash_basis's re-snap +
    `update_assignment`'s narrow/wide passes) with the same key-vs-row
    evaluation, one constituent at a time; the wide pass's
    `update_row_exact` (which computes and STORES row values) is the
    only writer left standing.

## Continuation 51 (2026-09-19): item 95 — THE CORRUPTION AT THE BOTTOM: a wide point shadowing a wide row; the reads were wrong, the rows never were

95. **Items 91–94's hunt closed at the root** (`6b581764`).  The
    tracers had exonerated every form-writer (pivots both loops,
    migrations, interns — all form-preserving); the hand-composition of
    the C3 chain proved the rows EQUIVALENT (`v301 = v6` is algebraically
    exact).  The snapshot tracer then caught the read red-handed: v0's
    wide row evaluates to `...864` over its own term reads while
    `point_value_exact` returned `...842` — **v0 was in BOTH wide stores**,
    a `wide_points` entry parked when it was nonbasic at a wide bound,
    never retired when it became wide-BASIC.  The frozen point shadowed
    the live row in every exact read; the two drifted apart (22/44-delta
    family) as the search moved the row's terms.  Published models read
    the frozen value and violated their own committed atoms; the exact
    evaluator correctly refuted them; the big-const gate degraded
    decidable `sat`s to `unknown`.  **The rows were never corrupt — the
    READS were.**
    * **The fix, both sides**: `point_value_exact` consults the wide ROW
    first (a variable with a defining row is basic; a lone point — a
    genuine nonbasic at a wide bound — unchanged); gaining a defining row
    (`intern_wide_row`'s fresh and dedup-hit paths, the pivot's entering
    commit in both arms) retires any parked point.
    * **Measured**: the i423 reproducer answers `sat` (z3: `sat`); the
    leaf tripwire is SILENT (the acceptance test).  Survey: 73 → 78 (3
    recovered, 8 honest-unknown reshuffles — the stale point had been an
    accidentally-useful search guide; zero wrong verdicts).  Differentials
    5 fresh seeds clean; parity 176/177 (z3 4.16.0); gate 1.000/1.000;
    panic sweep 0; arith suite 4705/4719 (the 14 the documented
    corpus-missing class).  Regression: `wide_point_never_shadows_a_wide_row`.
    * **The arc's cumulative survey run on the fixed seeds**:
    **150 → 110 → 91 → 79 → 75 → 73 → (78 after this fix's reshuffle)**
    — every step zero wrong verdicts, every recovered member's model
    z3-validated.  The hunt's full instrument set (leaf tripwire with
    tags/skips/dir, the pivot form-preservation tracer, the intern
    equivalence tracer, the snapshot term-read dump) is recorded in
    items 93–95 with recipes.
    * Doc-gate note: `cargo doc -D warnings` fails on nixie-core's
    `simplify.rs` link errors — a parallel session's in-flight landing,
    untouched by this change.
