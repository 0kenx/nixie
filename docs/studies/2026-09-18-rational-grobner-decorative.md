# The rational Gröbner engines were decorative — three stacked defects, all fixed

**Date:** 2026-09-18
**Scope:** the follow-up named by the FF arc's T12 record: port the
sound chain criterion to `nixie-math/src/grobner/` (buchberger,
buchberger_enhanced, syzygy) before any contemplated NLSAT wiring.
**Verdict:** **ship** — and the landmine was far worse than assessed.
The rational engines were not "an unsound criterion away from correct";
stacked on top of it were VACUOUS MONOMIAL/POLYNOMIAL HELPERS that made
the main engine a decorated no-op: `grobner_basis` computed **zero
S-polynomials** on most inputs and returned `interreduce(seeds)`
dressed as a Gröbner basis.

## The three defects, in discovery order

1. **The unsound simplified chain criterion** (the known one, T12's
   rational twin): `check_criterion2`'s divisibility side-checks
   (`lcm_ik | lcm` etc.) are tautologies whenever the outer
   `lm_k | lcm` holds, so it reduced to the bare unsound form — the
   missed-refutation class root-caused in the 𝔽_p engine.
   `buchberger_enhanced::satisfies_chain_criterion` carried the same
   thing with an explicit *"For now, simplified check"* confession,
   plus a bare Gebauer–Möller pair-REMOVAL
   (`lm_new | lcm ⇒ drop pair`) with the same circularity.
2. **The `MonomialHelper` stub trait**: its `powers()` returned a
   **static EMPTY map** ("Simplified: return empty map") — so
   `are_relatively_prime` iterated nothing and returned `true` for
   every pair (criterion 1 skipped EVERYTHING), and `monomial_lcm` /
   `monomial_mul` / `monomial_div` / `monomial_divides` were all
   vacuous. This is why the battery's first seed
   (`0xF00D_CAFE` 3×4 — the 𝔽_p reproducer's rational twin,
   whole-ring) traced to zero S-polys computed: every pair was
   "coprime".
3. **The `PolynomialSyzygy` stub trait**: `mul_monomial`/`mul_scalar`
   returned `self.clone()`, `from_monomial` returned zero — so
   `SyzygyComputer::compute_s_polynomial` computed `fᵢ − fⱼ` unscaled
   (garbage through every path that used it), and `create_syzygy`
   fabricated coefficients.
   Plus a fourth, smaller: `grobner_basis`'s 1000-iteration cap
   SILENTLY truncated (returned a non-basis, indistinguishable from a
   complete one).

## What landed

* **All six monomial helpers rewritten** against the real
  `Monomial::vars()`/`from_powers` API; both stub traits deleted (the
  polynomial one replaced by thin REAL delegations to `Polynomial`'s
  native `mul_monomial`/`scale`, which the real `s_polynomial` in
  buchberger.rs had used all along).
* **The sound chain criterion ported** from the validated 𝔽_p design:
  `zero_pairs` bookkeeping in `SyzygyComputer` (processed-to-zero ∪
  coprime ∪ verified chains; a pair is discarded only when the
  classical precondition actually holds), positive-only criteria cache
  (criterion 2's truth grows monotonically — a negative cache entry
  goes stale), and the vacuous `lcm == product` early return deleted.
* **buchberger.rs**: seed leading-term deduplication (duplicate-lm
  seeds are the other unsoundness input), zero-pair recording on
  processed-to-zero, and the honest cap — `grobner_basis` now returns
  `Result<Vec<Polynomial>, GrobnerIterationCap>` and refuses rather
  than truncates; `ideal_membership` propagates (a truncated basis
  cannot decide membership); the NLSAT preprocessor's call site skips
  preprocessing on refusal (its existing timeout semantics).
* **buchberger_enhanced.rs**: its own `zero_pairs` set with the sound
  chain criterion, recording on product-criterion and zero-reduction;
  the bare G-M pair-removal deleted (the criteria-gated pair ADD is
  the sound part; the removal needed the discharged-chain discipline
  it did not have). Its degree-bound refusal is documented in place as
  an honesty gap (no live callers).

## Verification

* **The battery** (`nixie-math/tests/grobner_rational_soundness.rs`,
  the rational twin of `ff_gb_seed_dedup_regression.rs`): random
  product systems over ℚ, engine vs brute-force (no criteria, every
  pair) — whole-ring agreement (the `0xF00D_CAFE` twin included),
  mutual ideal membership both directions, inter-reduced
  leading-monomial agreement, determinism, whole-ring detection, the
  membership refusal contract. Green on shapes sized for BigRational
  test time.
* All 814 nixie-math tests (including the FF suites — the 𝔽_p engine
  is untouched), 508 nixie-nlsat tests, clippy/fmt clean.

## The honest capacity fact (price before ANY wiring)

With real criteria and real helpers the engine computes REAL
S-polynomials: whole-ring systems collapse fast (ms — the constant
arrives early); a 4×4 non-ring system completes in ~20 ms; a 4×5
non-ring system exceeds ten minutes (BigRational coefficient cascade).
The old instant-and-vacuous behavior was the bug, not a feature — any
future wiring (the NLSAT preprocessor is the contemplated one) needs
the 𝔽_p engine's budget discipline (monomial-op charging, honest
`Err`), which remains out of scope while the module stays unwired.
