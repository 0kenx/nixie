# Handover: QF_FF finite-field theory — continue from Phases 0–6 landed

You are continuing the finite-field (`QF_FF`) solver work in this repo.
Everything through Phase 6 (certifiable half) is **landed on main and
verified**; the remaining items are at the bottom. Read this top to
bottom before touching anything.

## 1. Read first (in order)

1. `docs/FF_THEORY_DESIGN.md` — the design (status header maps code).
2. The three studies, in order — each records a negative result with its
   root cause, and the third explains why they were all wrong:
   - `docs/studies/2026-09-14-ff-front-end-components-and-work-budgets.md`
   `docs/studies/2026-09-14-ff-flattening-without-split-gb.md`
   - `docs/studies/2026-09-15-ff-kernel-projection.md`
3. `AGENTS.md` (the repo's rules — soundness bar, git protocol).

## 2. What exists and works (all on main, all tested)

**Surface + sorts**: `nixie-core/src/sort/field.rs` (FieldId /
FieldTable / deterministic Miller–Rabin), five `TermKind::Ff*` variants,
`#f<v>m<p>` literals, `ff.add/mul/neg/bitsum`, `(_ FiniteField
<bignum>)`, `(as ffN …)`, cvc5-exact rewriter normal form at
construction (`nixie-core/src/ast/manager/ff_fold.rs`).

**Algebra** (`nixie-math/src/ff/`): Montgomery 𝔽_p over 64-bit limbs
(1–4 limbs inline; `field.rs`), univariate polys + deterministic
Rabin/Cantor–Zassenhaus roots (`uni_poly.rs`, `roots.rs`), sparse
multivariate polys (`poly.rs`), Buchberger + Gebauer–Möller with a
cofactor tracer that verifies (`grobner.rs`), zero-dimensionality,
standard monomials, minimal polynomials (Krylov rows carry their
defining polynomial — see trap T4).

**Procedure** (`nixie-theories/src/ff_theory.rs`): the [OKTB23] core.
Two-pass encoder (witness disequalities, bitsum definitions with
literal provenance), Phase-5 front end (linear core = RREF over 𝔽_p
with origin-traced UNSAT certificates; connected components), FindZero
(min-degree brancher, heap-stack search, one shared budget),
`FfOutcome` honesty gate, mandatory exact model validation,
`FfCertificate` (IdealMembership with encoder-replay verification,
Cardinality), tiny-field enumeration fallback (p^n ≤ 2^22).

**Dispatch** (`nixie-solver/src/solver/check_ff.rs`): eager
conjunctive dispatch + lazy DPLL(T) for Boolean structure (Tseitin
over atom abstractions into nixie-sat, blocking clauses), §7
cardinality guard on the asserted conjunct spine only.

**Certified mode** (`nixie-solver/src/solver/certification.rs` +
`nixie-core/src/ast/validation.rs`): FF `sat` model-certified with
exact modular evaluation; FF `unsat` accepted only with a verified
certificate; exhaustion fails closed.

**Current capacity** (BN254, bench/ff/): sparse R1CS 128×192 `sat` in
38 s (16×24/32×48 < 100 ms); dense 12×20 `sat` 337 ms; chain 16×24/32×48
`sat`; chain 64×96+ exceeds 120 s — genuine MQ hardness, answered
honestly.

## 3. Verification bar (run before declaring anything done)

```bash
cargo build --all-features
cargo nextest run -p nixie-math -p nixie-theories -p nixie-core -p nixie-solver --all-features
cargo clippy --workspace --all-features --all-targets -- -D warnings
cargo fmt --all -- --check
```

FF-specific oracles (the soundness canaries — no Z3 oracle exists for
FF, these replace it):
- `nixie-theories/tests/ff_oracle.rs` — exhaustive tiny-prime
  enumeration (verdicts + cores + certificate-corruption rejections).
- `nixie-theories/tests/ff_planted_fuzz.rs` — planted witnesses at
  Goldilocks/BN254/BLS12-381; any `unsat` on a planted system is a hard
  failure; runs in ~0.25 s, run it constantly.
- `nixie-solver/tests/ff_solver_regression.rs` — 24 end-to-end +
  certified-mode regressions.
- `bench/ff/` — three families (sparse = realistic R1CS, dense =
  capacity marker, chain = single-component marker); measure with
  `NIXIE_FF_STATS=1` (deterministic step counts, never wall-clock as
  policy).

Worktrees: `git worktree add outputs/wt-<name> <sha>`; symlink
`ln -s /media/data/proj/nixie/smt-lib smt-lib` inside (corpus tests
need it); delete when done. Never `git stash`/`restore` in the primary.

## 4. Traps (each one burned us — do not rediscover)

- **T1 — the grevlex comparator.** `grevlex_cmp` in
  `nixie-math/src/polynomial/types.rs` was not a term order (variable-
  index tiebreak instead of exponent at the highest differing
  position). Every "capacity limitation" for ≥6-variable systems was
  this bug. It is fixed and pinned by
  `nixie-math/tests/monomial_order_regressions.rs` (20k random pairs vs
  a dense reference + the multiplicative axiom + hand cases). If you
  touch ANY monomial comparator, that test must stay green — and note
  its first version passed vacuously because its RNG never advanced;
  keep the advance honest.
- **T2 — multi-limb Montgomery.** `FieldCtx::neg` propagated the borrow
  with the wrong sign — invisible at 1 limb, false `unsat` at BN254.
  Pinned by `multi_limb_field_axioms` in the field.rs tests. Any new
  limb arithmetic needs a ≥2-limb exactness test.
- **T3 — deferred-combine term walks.** The term→polynomial encoder
  and the term evaluator both had sibling operands bleeding across
  windows when combines ran on a separate stack. Both use ONE frame
  stack (Expand pushes Combine under its children). If you write a new
  term walk, follow that discipline; the planted fuzzer catches
  violations as false verdicts.
- **T4 — minimal-polynomial bookkeeping.** Two bugs: the dependency
  carried only row-top degrees (wrong whenever back-substitution is
  needed), and the Krylov shift appended instead of shifting. The
  rewrite pairs each quotient vector with its defining polynomial. If
  you touch it, re-run the BN254 planted fuzz immediately.
- **T5 — budget semantics.** `GrobnerBudget` charges MONOMIAL
  OPERATIONS, not steps (a reduction between s-term polys costs ~s).
  Step-counting let big-polynomial cascades grind for hours inside a
  "bounded" budget. RootBudget likewise. Never reintroduce per-step
  charging.
- **T6 — scope state.** `ff_terms_unconstrained` is restored on `pop`
  (it is a RESULT, not a snapshot invariant) because the dispatch
  legitimately clears it on a validated `Sat`. New FF solver state must
  decide snapshot-vs-result explicitly in `trail.rs`.
- **T7 — git protocol.** Land on `main` via fast-forward from a clean
  worktree; never force-push; stage only your files; delete your
  worktrees; copy release binaries to `precompile/<sha>/`.

## 5. Open work, in recommended order

1. **Chain ≥64×96 capacity (Phase 7)**: genuine MQ hardness now —
   plain Buchberger hits degree-7 bases with 253-term elements at 8×6.
   The pre-registered experiments: split-GB (maintain bases over
   variable subsets in the ORIGINAL space, exchange only
   support-fitting consequences — gets binomial cleanliness AND
   decomposition; both flattening studies converge here), then F4-style
   batched reduction. NTT untested. Follow `docs/BENCHMARKING.md`:
   these are selection/algorithm changes inside a chaotic search —
   matched nulls and ≥10 seeds per cell where applicable; the
   deterministic front-end items need only step counts.
2. **`QF_UFFF` (Phase 6 remainder)**: FF ⊕ EUF via polite combination
   (EUF is smooth/finitely witnessable); needs the arrangement
   machinery over shared FF-sorted terms and the cardinality guard at
   the interface (k pairwise-distinct shared terms satisfiable only if
   k ≤ p — vacuous at ZK primes, a false-`sat` at 𝔽₂/𝔽₃). The pure-QF_FF
   spine guard in `check_ff.rs` is the pattern; the toy-field
   regression (`distinct` over 𝔽₂) is the pin.
3. **Branch-exhaustion certificates (§8 hard half)**: when UNSAT comes
   from FindZero closing the tree, the proof is a case tree; each
   branch step is checkable (`f = ∏(x−rᵢ)·q` with `gcd(q, x^p−x)=1`).
   Until it exists, certified mode correctly downgrades those to
   `unknown` — that is by design, not a gap to paper over.
4. **Incremental trail (§7)**: recompute-don't-rollback is the current
   discipline and is correct; an incremental basis would need an
   invariant checker before it's worth the risk.

## 6. Where things plug in (quick map)

- New FF term kind → fix EVERY exhaustive match the compiler flags
  (congruence, equality walks, hashing, substitution rebuilds,
  printers, MBQI, encode paths, Nelson–Oppen classification) — the
  breakage is the forcing function, never add a `_` arm.
- Certified-mode FF `sat` evaluation: `nixie-core/src/ast/validation.rs`
  (`ModelValue::FiniteField`, `ff_*` helpers).
- UNSAT certificate flow: `traced_unsat` (compose combos) →
  `FfCertificate::verify` (encoder replay) → certified gate in
  `certification.rs`.
- Logic contract: `nixie-solver/src/solver/logic_contract.rs`
  (`LogicSpec::ff`, `QF_FF` entry, `Capabilities::ff`).

The repo's rule above all: a wrong `sat`/`unsat` is a catastrophe, an
`Unknown` is fine. When a verdict looks wrong, dig to the bottom layer
before fixing — every real bug here (T1–T4) was three layers below the
symptom.
