# Handover: QF_FF finite-field theory — the 2026-09-16 arc landed; the cascade frontier remains

You are continuing the finite-field (`QF_FF`) solver work in this repo.
Through Phase 6 AND the 2026-09-16 arc (`QF_UFFF`, split-GB, §8 case-tree
certificates, budget honesty, the untraced fast path) everything is
**landed on main and verified**; the remaining items are at the bottom.
Read this top to bottom before touching anything.

## 1. Read first (in order)

1. `docs/FF_THEORY_DESIGN.md` — the design (status header maps code;
   §7.1 is the as-built `QF_UFFF` architecture).
2. The 2026-09-14/15 flattening studies — each records a negative result
   with its root cause, and the third explains why they were all wrong
   (all three converge on the split-GB architecture):
   - `docs/studies/2026-09-14-ff-front-end-components-and-work-budgets.md`
   - `docs/studies/2026-09-14-ff-flattening-without-split-gb.md`
   - `docs/studies/2026-09-15-ff-kernel-projection.md`
3. The 2026-09-16 arc studies, in order — what each landing measured,
   which negative variants were discarded on the way, and what the next
   lever is:
   - `docs/studies/2026-09-16-ff-split-gb-chain-capacity.md`
   - `docs/studies/2026-09-16-ff-chain-frontier-budget-honesty.md`
   - `docs/studies/2026-09-16-ff-untraced-fast-path.md`
   - `docs/studies/2026-09-16-ff-branch-selection-inapplicable.md`
4. `AGENTS.md` (the repo's rules — soundness bar, git protocol) and, for
   any heuristic experiment, `docs/BENCHMARKING.md` (matched nulls,
   ≥10 seeds, tick counters only).

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
cardinality guard on the asserted conjunct spine only. **`QF_UFFF`**
(2026-09-16): `dpll_ufff` — FF ⊕ EUF by model-guided arrangement
search over OPAQUE applications (`nixie-theories/src/ff_euf.rs` batch
congruence closure; see design §7.1), with the interface cardinality
guard (k ≤ p) and destructive-conflict blocking.

**Split-GB + fast path + windows** (`nixie-theories/src/ff_theory.rs`,
`nixie-math/src/ff/grobner.rs`): per component, the monolithic cascade
first — UNTRACED for ≥40 inputs (empty cofactor rows gate every row op;
a constant basis triggers one traced re-run for the witness; trajectory
identity pinned by `nixie-math/tests/ff_gb_traced_untraced_identity.rs`)
— then cvc5's 2-way split fallback (linear ideal / binomial-admitting
nonlinear ideal, admit discipline, untraced), then the **§6.5 window
decomposition** (2026-09-17): support-driven 8-variable windows, one
Gröbner basis per window, a support-fitting exchange fixpoint (linear
polys + univariates), and one union cascade that — because the union of
window ideals IS the component ideal — completes to the component's
true basis (min-poly brancher valid). lm caching, selection-scan and
cofactor-row budget charging, bloat circuit breaker. FindZero branches
over the merged basis with lazy honest round-robin (256-value horizon;
truncation ⇒ `OutOfBudget`, never `Exhausted`; node steps charge
CHILDREN PUSHED — a 256-ary round-robin node is 256 steps, not 1) and
element-bootstrapped children.

**§8 case-tree certificates** (`FfCertificate::CaseTree`): FindZero's
exhaustions carry branch steps with root-completeness witnesses
(`f = ∏(x−rᵢ)·q`, `gcd(q, x^p−x)=1`) and leaf memberships as composed
cofactor expressions over the replayable encoding — composed through
the linear core's rewriting (which now tracks each rewritten
generator's expression; the substitution identity `g' = g − h·(x−repl)`
in closed form). Certified mode accepts branch-exhaustion UNSATs.

**Certified mode** (`nixie-solver/src/solver/certification.rs` +
`nixie-core/src/ast/validation.rs`): FF `sat` model-certified with
exact modular evaluation; FF `unsat` accepted only with a verified
certificate; exhaustion fails closed.

**Current capacity** (BN254, bench/ff/, after the window decomposition
+ worklist exchange, 2026-09-17 — see
`docs/studies/2026-09-17-ff-window-decomposition.md` and its addendum):
sparse R1CS solves at every size (8×12…64×96 in ≤0.1 s, 128×192 in
0.2 s); dense 12×20 `sat` 0.1 s; **the chain family solves at every
size through 1024×1536** — 128×192 `sat` ~2.6 s, 256×384 `sat`
~2.9 s, 512×768 `sat` ~7 s, **1024×1536 `sat` ~18-24 s** (windows +
worklist exchange + union cascade; the corpus generator is now
in-repo at `bench/ff/gen_chain.py` — its residue-pass structure is
load-bearing, see the addendum). CoCoA-enabled cvc5 for comparison:
14.4 s at 128×192, >120 s at 256×384.

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
- `nixie-solver/tests/ff_solver_regression.rs` — end-to-end +
  certified-mode regressions (incl. the four §8 case-tree acceptances,
  the planted-8×12 false-unsat pin, and the truncation-honesty pins).
- `nixie-solver/tests/ff_ufff_oracle.rs` — brute-force over EVERY
  model (variable assignments × function tables) at p ∈ {2,3,5,7}; any
  verdict disagreement vs brute force is a hard failure.
- `nixie-solver/tests/ff_ufff_regression.rs` — congruence, 𝔽₂
  cardinality pin, mixed fields, certified-mode QF_UFFF behavior.
- `nixie-math/tests/ff_gb_traced_untraced_identity.rs` — the untraced
  fast path's trajectory identity (element-for-element identical
  bases); divergence means rows influence the search — soundness-
  relevant, hard failure.
- `nixie-theories/src/ff_theory.rs` `window_tests` +
  `nixie-theories/tests/ff_window_split.rs` — the window path's
  mechanism pins (ideal membership of every merged element; partition
  coverage; planted-never-unsat; starved-window refusal).
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
- **T10 — never regex-delete instrumentation over code.** Removing the
  case-tree debug prints with a line-spanning regex ate whole features
  between distant braces (and a `cd` failure between tool calls sent
  builds and edits into the PRIMARY tree for several rounds — always
  anchor worktree commands with absolute paths or `--manifest-path`,
  and remove debug scaffolding by exact-match edits only). Also: the
  certificate machinery's correctness lives in its INDEX ALIGNMENTS
  (combo→generator, tracer row→inputs, literal atom = base + registry
  index, little-endian univariate coefficients `[−r, 1]` not `[−1, r]`,
  `x^p−x` not `x^p+x`); every one of those was a real bug found by the
  corruption/acceptance probes, and each is now pinned by a test.
- **T9 — lazy enumeration must carry its truncation flag to the verdict.**
  The lazy round-robin's first version enumerated 256 of p values, let
  the stack empty, and reported `Exhausted` — a false `unsat` on a
  planted-BN254 goal. The tiny-prime oracle CANNOT catch this class (p ≤
  256 never truncates); the planted-at-real-primes corpus can, and did.
  Pinned by `planted_bn254_sparse_8x12_is_never_unsat` and
  `all_big_solutions_stay_honest`. Any bounded-search change must
  propagate its truncation into the outcome type, and a related note for
  the editing process: python `str.replace` silently no-ops on a
  non-matching block — the missing gate was an edit that "applied"
  without applying; assert replacement counts when patching this file.
- **T11 — window routing cannot be forced at unit scale.** The
  monolithic cascade is the CHEAPEST strategy for small goals, so no
  small test routes through the windows (a budget that starves the
  monolithic path starves the windows too). The window path's pins are
  therefore at the MECHANISM level (`ff_theory::window_tests`: every
  merged element's normal form ≡ 0 mod the full monolithic basis; the
  partition covers every generator exactly once) plus the corpus
  verdicts — never at the routing level. Relatedly: FindZero's node
  budget charges CHILDREN PUSHED (T5 applied to the search tree) — a
  bounded-search change must account its fan-out or 256-ary round-robin
  walks outlast their own budget by 256×; and a skipped window's
  exclusive variables are unreachable by exchange, so the caller
  refuses fast at p > 256 instead of walking (the gate lives in
  `grobner_path`, keyed on `any_skipped`).
- **T8 — folded equalities are not atoms.** `mk_eq(#f1m2, (ff.add x0 x0))`
  folds to `true` at construction (the cvc5-exact normal form), so no
  Boolean model ever asserts its negation. A guard that treats "the
  negation is absent from the model" as "the pair is asserted distinct"
  counts such pairs toward `distinct`'s k and refutes perfectly
  satisfying assignments — a false `unsat` found by the `QF_UFFF` oracle.
  Pair literals must be classified at construction: folded-`true` kills
  the family (it is refutable outright, not by pigeonhole),
  folded-`false` is vacuously distinct, anything else is an atom.
  Pinned by `oracle_f2_unary` (instance 11 of seed 0xFF00_0001).

## 5. Open work, in recommended order

1. **F4 (the big pre-registered Phase-7 lever)**: the window arc closed
   the chain family through 1024×1536 (worklist exchange + union
   cascade; see the 2026-09-17 study addendum), so the next capacity
   lever is F4's batched linear-algebra reduction — orthogonal to and
   composable with the per-window cascades, and the matrix kernel is
   where SIMD first pays (exact modular arithmetic is order-independent,
   so vectorization is deterministic by construction). NTT for
   Goldilocks-class primes is the other named lever. Both deterministic
   front-end items — step counts, no matched null needed. The corpus
   generator (`bench/ff/gen_chain.py`) can produce the next frontier
   files when F4 needs them.
2. ~~**`QF_UFFF` (Phase 6 remainder)**~~ — **landed 2026-09-16**. FF ⊕
   EUF via model-guided arrangement search over opaque applications;
   see `docs/FF_THEORY_DESIGN.md` §7.1 for the as-built architecture,
   `nixie-theories/src/ff_euf.rs` (batch congruence closure),
   `check_ff.rs`'s `dpll_ufff` (the combination loop), and the oracles
   (`nixie-solver/tests/ff_ufff_oracle.rs` — brute force over every
   model; `ff_ufff_regression.rs` — the 𝔽₂ `distinct` pin and
   certified-mode behavior). Follow-ups if capacity demands:
   congruence explanations for multi-field core-directed blocking, and
   a case-tree certificate so FF-arithmetic combination UNSATs can
   certify.
3. ~~**Branch-exhaustion certificates (§8 hard half)**~~ — **landed
   2026-09-16**. `FfCertificate::CaseTree`: FindZero records the search
   as a case tree (branch steps with root-completeness witnesses
   `f = ∏(x−rᵢ)·q`, `gcd(q, x^p−x)=1`; leaves with membership
   cofactors composed over the replayable encoding through the tracer
   rows AND the linear core's rewriting — landing this found and fixed
   two pre-existing certificate bugs: the linear core certified over
   the REWRITTEN generator list the replay cannot reproduce, and its
   combination bookkeeping indexed the linear subsequence instead of
   the generator list). Certified mode accepts branch-exhaustion
   UNSATs; the enumeration path and aborted tracking still downgrade
   honestly (tracking runs on its own budget — a big tree can only
   lose its certificate, never its verdict). Still open within §8:
   certificates for the SPLIT root (merged inputs are not replayable)
   and for the enumeration path.
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
