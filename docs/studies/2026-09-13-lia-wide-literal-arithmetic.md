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
