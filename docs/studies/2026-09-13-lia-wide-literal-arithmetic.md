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
