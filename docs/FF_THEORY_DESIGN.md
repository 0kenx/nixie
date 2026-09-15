# Finite Fields (`QF_FF`) — theory design

**Status:** Phases 0–6 implemented (2026-09-14); `QF_UFFF` (the
Phase-6 combination remainder) landed 2026-09-16 — see §7.1 for the
as-built arrangement architecture; §6.5's split GB landed 2026-09-16 as
the monolithic-first fallback with cvc5's admit discipline (see
`docs/studies/2026-09-16-ff-split-gb-chain-capacity.md` — the study also
records why operand flattening under the split is a measured negative).
Still open: §8's branch-exhaustion case-tree proofs, §7-style
incremental trail, F4/NTT, chain ≥64×96. See `nixie-core/src/sort/field.rs`,
`nixie-math/src/ff/`, `nixie-theories/src/ff_theory.rs` (the [OKTB23]
procedure + Phase-5 front end + `FfCertificate` with its replay
verifier), `nixie-theories/src/ff_euf.rs` (the batch congruence
closure), `nixie-solver/src/solver/check_ff.rs` (eager dispatch +
Phase-4 lazy DPLL(T) + the §7 cardinality guard + the `QF_UFFF`
combination loop), the oracles in `nixie-theories/tests/ff_oracle.rs`
(exhaustive at tiny primes; certificate-corruption rejections),
`ff_planted_fuzz.rs` (planted witnesses at Goldilocks/BN254/BLS12-381),
`nixie-solver/tests/ff_ufff_oracle.rs` (brute-force over every model:
variable assignments × function tables) and
`nixie-solver/tests/ff_ufff_regression.rs`, and `bench/ff/`.
Certified mode: FF `sat` is model-certified (exact modular evaluation in
the independent AST evaluator); FF `unsat` is accepted only with a
verified `FfCertificate` (ideal-membership or pigeonhole) or through
the checker's independently-verified EUF blocking loop (pure-congruence
refutations); FF-arithmetic-involved combination UNSATs degrade to
`unknown` by design.
**Date:** 2026-09-13 (design), 2026-09-14 (implementation status).
**Reference implementation consulted:** cvc5 `src/theory/ff/` (read-only, at
`../temp/cvc5`), which implements [OKTB23] "Satisfiability Modulo Finite Fields"
(CAV 2023) "essentially un-modified" (its own `Readme.md`), plus the split-Gröbner
follow-up in `split_gb.{h,cpp}`.

---

## 0. Recommendation, and where I would push back

**Build it.** The target — `x ∈ 𝔽_p`, `p` a 254-bit prime, polynomial constraints from
R1CS/PLONK circuits — is a fragment where the two reductions available today are not
merely slow but structurally wrong (§1), and where the dedicated procedure is
*simpler* than most theories Nixie already has: no ordering, no overflow, no
rounding, no interpretation gap. The signature is four operators and one predicate.

Three places where I would not do the obvious thing:

1. **This is 80 % a computer-algebra project, not a theory-solver project.**
   `nixie-math` has no finite field. Its Gröbner engines (`grobner/buchberger.rs`,
   `buchberger_enhanced.rs`, `f4.rs`) and its univariate factorizer
   (`polynomial/factorization.rs`) are all over `BigRational`; the only 𝔽_p-shaped
   primitives that exist are scalar (`rational::{mod_pow, mod_inverse, is_prime,
   legendre_symbol, tonelli_shanks}`). The theory shell around the algebra is a few
   hundred lines; the algebra is a few thousand, and it is the part that has to be
   right. Plan the schedule around §4, not around §7.

2. **Do not make Gröbner the front line.** cvc5 shipped GB-first and has since had to
   add a whole second architecture (`split_gb.cpp`) to make real circuits tractable.
   The ZK domain's own tooling (R1CS analyzers, Picus/Ecne-style under-constrainedness
   checkers) does not start from Gröbner bases at all: it starts from *sparse linear
   algebra over 𝔽_p* and *propagation*, because circuit constraint systems are
   overwhelmingly linear-plus-a-thin-layer-of-rank-1-quadratics. Put the linear core
   and the propagator in front of the GB from the start (§6) and let the GB be the
   fallback for what survives. The transfer is direct: Nixie already runs exact sparse
   pivoting for LRA; over 𝔽_p the same discipline is *easier* (no bounds, no ordering,
   no Bland's rule, termination is trivial).

3. **cvc5's procedure is randomized and wall-clock-budgeted; ours must be neither.**
   `uni_roots.cpp` picks random shifts for Rabin/Cantor–Zassenhaus splitting, and
   `GBasisTimeout` cuts the basis computation on elapsed time. Both are forbidden
   here: wall-clock is never a policy input (`AGENTS.md` → *Heuristic changes*), and a
   nondeterministic solver breaks `run_parity.sh`, bug reproduction and differential
   fuzzing. Derandomize the shift sequence (`a = 0, 1, 2, …`, which is complete and
   just as fast in practice) and budget the GB in **S-pair reductions**, not seconds.

And one thing I would deliberately not copy: cvc5 asserts `modulus.isProbablePrime()`
and supports prime order only. Keep that restriction in the *solver*, but do not bake
it into the *sort*: carry a field description behind a `FieldId` so `GF(2^k)` (AES,
Binius-style binary towers) can be added later without an AST migration. A non-prime
modulus must produce an honest error at `declare-sort`/parse time — never a silent
reinterpretation as ℤ_n (`AGENTS.md` → *No silent fallthrough*).

Phasing and exit criteria are in §11. The short form: Phase 0–2 (AST + 𝔽_p algebra +
GB) is the critical path; a useful solver exists at Phase 3; Phase 5 is what makes it
competitive.

---

## 1. Why a dedicated theory — the reductions really are unavailable

**Bit-vectors have the wrong modulus.** Encoding `x ∈ 𝔽_p` as a 254-bit BV requires
every field operation to be followed by an explicit reduction `mod p`, and `mod` by a
non-power-of-two constant is not a BV operation: it needs a quotient variable and a
multiplication. One field multiply becomes a 254×254 bit multiplier (~1.3·10⁵ AND
gates), plus a 254×254 multiply for the quotient, plus comparisons — order 10⁵ clauses
per constraint. A small circom circuit is 10⁴–10⁶ R1CS constraints. This is not a
constant-factor problem.

**Integers need lemmas the arithmetic engines cannot close.** `(mod (+ x y) p)` over
unbounded ℤ keeps the syntax honest but throws away every fact that makes the domain
decidable: that every nonzero element is invertible, that `x(x−1) = 0 ⟹ x ∈ {0,1}`,
that the solution set is a variety over a finite field. Those arrive as nonlinear
diophantine side conditions; Nixie's NIA path (branch-and-cut, relaxation, NLSAT) has
no rule that exploits finiteness of 𝔽_p, and the invertibility encoding —
`a ≠ b ⟺ ∃w. (a−b)·w = 1`, the single most useful fact in this theory — is not
available at all in ℤ.

**The theory itself is small.** Semantics of a conjunction of 𝔽_p literals reduces
exactly to: *does this polynomial system have an 𝔽_p-rational point?* Equalities are
ideal generators; disequalities become equalities via witnesses; UNSAT is ideal
membership of 1; SAT is a point. There is no ordering to axiomatize, no overflow
semantics, no rounding mode, no partial function.

**Where a reduction *is* right:** tiny fields. For `p < 2^20` with few variables,
adding the field polynomials `x^p − x` to the ideal (cvc5's `--ff-field-polys`) or
brute enumeration of `p^n` is viable and complete. Keep that as an option on the same
code path, not as a second architecture.

---

## 2. Surface syntax and semantics — match cvc5 exactly

Verified against `../temp/cvc5/src/parser/smt2/{smt2_state,smt2_term_parser}.cpp` and
`src/theory/ff/{kinds.toml,theory_ff_rewriter.cpp}`.

| Concept | SMT-LIB surface | Notes |
|---|---|---|
| Sort | `(_ FiniteField <numeral>)` | index is an arbitrary-precision numeral (`mkFiniteFieldSort(numerals.front())` takes the *string*) |
| Literal | `#f<value>m<modulus>` | e.g. `#f5m7`; also `(as ff5 (_ FiniteField 7))` |
| Addition | `(ff.add a b …)` | n-ary, ≥ 2 |
| Multiplication | `(ff.mul a b …)` | n-ary, ≥ 2 |
| Negation | `(ff.neg a)` | unary |
| Bit-sum | `(ff.bitsum b0 b1 …)` | `Σ 2^i · b_i`, little-endian (`postRewriteFfBitsum`) |
| Predicate | `=` / `distinct` | the **only** predicates; no `<`, no `≤` |
| Logic string | `QF_FF` | cvc5 composes the letters `FF` into logic names (`logic_info.cpp`) |

There is deliberately **no subtraction, no division, no inverse**. `a − b` is
`(ff.add a (ff.neg b))`. Division is the user's job: `y = n/d` is written
`(= (ff.mul y d) n)`, which also forces the modeller to say what happens when `d = 0`
instead of inheriting a convention. **Recommendation: keep it that way.** A total
`ff.div` with a `div-by-zero` convention is precisely the shape that has produced
soundness bugs in this codebase before (`AGENTS.md` → *Math must be real, not
stubbed*), and the ZK community already writes the multiplicative form.

**Type rules.** All children of `ff.add`/`ff.mul`/`ff.neg`/`ff.bitsum` share one field
sort; the result has that sort. A literal's modulus must match the ascribed sort.
Mixing `𝔽_p` and `𝔽_q` terms in one operator is a type error, not a coercion.

**Constant normalization.** `FfConst` values are normalized into `[0, p)` at
construction. This is load-bearing for hash-consing: `#f8m7` and `#f1m7` must be the
same `TermId`, or the rewriter's constant folding and the encoder's polynomial
construction will disagree about when two literals are equal.

**Rewriter normal form** (mirroring `theory_ff_rewriter.cpp`): flatten nested n-ary
`add`/`mul`; fold constant sub-terms; drop `0` from sums and `1` from products; `0·t →
0`; sort children by term id; `(= t t) → true`; `(= c₁ c₂)` folds; orient `=` by term
order. The encoder then puts every atom into `p(x⃗) = 0` form, so the rewriter does not
need a canonical polynomial form of its own.

---

## 3. Representation in `nixie-core`

### 3.1 Sorts

```rust
// nixie-core/src/sort/mod.rs
SortKind::FiniteField(FieldId)          // new variant
```

with a `FieldTable` living beside the sort interner:

```rust
pub struct FieldId(u32);

pub struct FieldDesc {
    modulus: Arc<BigUint>,      // p, exactly; never truncated
    kind: FieldKind,            // Prime | Extension { .. }  (Extension unimplemented)
    primality: Primality,       // Verified | ProbablePrime(rounds) | Composite
    // derived, computed once: Montgomery parameters, 2-adicity, p−1 factors
}
```

Why `FieldId` and not `FiniteField(Arc<BigUint>)`: `SortKind` is the interner key —
it is hashed and compared on every sort lookup (`Sorts::intern`), and it is matched in
341 places across 41 files. A `u32` payload keeps those comparisons O(1) and gives the
derived field data (Montgomery constants, root-finding parameters) a home that is
computed once per field rather than once per query.

`FieldKind::Extension` exists in the enum from day one and is rejected everywhere with
an explicit error. That is cheaper than an AST migration later and it makes the
unsupported case *visible in the type system* instead of implied by a missing branch.

### 3.2 Terms

```rust
// nixie-core/src/ast/term.rs — mirrors the existing BitVecConst shape
TermKind::FfConst { value: BigInt, field: FieldId },
TermKind::FfAdd(SmallVec<[TermId; 4]>),
TermKind::FfMul(SmallVec<[TermId; 4]>),
TermKind::FfNeg(TermId),
TermKind::FfBitsum(SmallVec<[TermId; 4]>),
```

Flat variants, consistent with `BvAdd`/`FpAdd`, rather than one grouped
`TermKind::Ff(FfOp, …)`. The grouped form would shrink the blast radius — `TermKind::`
appears at ~8 900 sites — but every existing walker, rewriter, model evaluator and
printer is written against flat variants, and a nested enum would buy compile-time
convenience at the cost of an inconsistent AST. The breakage *is* the forcing
function: exhaustive matches that do not handle a field term must fail to compile
rather than fall through (`AGENTS.md` → *No silent fallthrough*). Budget for it.

### 3.3 Parser, printer, lexer

Three concrete wiring changes, none of them deep but none of them free:

- **Bignum sort indices.** `Parser::parse_indexed_identifier` returns `Vec<u32>`
  (`smtlib/parser/sorts.rs:353`) and errors on anything that does not fit. A 254-bit
  modulus does not fit. Add a sibling that returns the raw numeral *strings* and keep
  the `u32` path for `BitVec`/`FloatingPoint`; do not widen the existing one silently,
  because its callers rely on the range check.
- **`#f…m…` literal token.** New lexer token, split at the `m`, both halves parsed as
  `BigUint`, modulus interned into a `FieldId`, value reduced into `[0, p)`.
  Also the `(as ffN (_ FiniteField p))` ascription path.
- **Printing.** Model values and `get-value` results print as `#f<v>m<p>`; the sort
  prints as `(_ FiniteField <p>)` (`smtlib/parser/build.rs` and the printer's sort
  formatter both have `BitVec` precedents at hand).

### 3.4 Logic registry

`LogicSpec` (`nixie-solver/src/solver/logic_contract.rs`) gains a `ff: bool` field and
a `QF_FF` entry; `Capabilities::collect` learns to report the field capability from
the new sort/term kinds. Until §7's combination work lands, `QF_FF` permits FF + Bool
structure only, and an input that puts an FF-sorted term under an uninterpreted
function is rejected by the contract rather than silently handled.

---

## 4. The math layer: a new `nixie-math::ff` module

This is the critical path. None of it exists today.

### 4.1 Field elements

```rust
pub struct FieldCtx { p: BigUint, n_limbs: usize, mont: MontParams, … }
pub struct Fp { limbs: SmallVec<[u64; 4]> }   // Montgomery form, ctx-relative
```

Montgomery multiplication over 64-bit limbs, `SmallVec<[u64; 4]>` so the ZK primes
(BN254 / BLS12-381 scalar fields, Pallas/Vesta, all 4 limbs; Goldilocks
`2^64 − 2^32 + 1`, BabyBear, Mersenne31, 1 limb) stay inline and allocation-free.
Operations: `add/sub/neg/mul/square/pow/inv`, plus batch inversion (Montgomery's
trick) because inversion inside GB reduction loops is the usual hot spot.

**Exactness rule, stated because it has burned this codebase before** (`AGENTS.md` →
*Wide bit-vectors and bignums are exact*): there is no `u64` fast path that drops high
limbs. A 1-limb specialization is legitimate *only* as a `const L: usize` /
`enum Backend` dispatch whose arithmetic is exact for that width; the wide path must
never be reached with a truncated value.

Constant-time is explicitly **not** a requirement — this is a solver, not a crypto
library, and pretending otherwise costs speed for no benefit here.

### 4.2 Univariate polynomials over 𝔽_p

Dense coefficient vectors. Schoolbook multiply, Karatsuba above a measured crossover;
NTT only if it earns its place (BN254's scalar field has 2-adicity 28 and Goldilocks
is NTT-native, so the option is real — but degrees in this application are small, so
treat NTT as a later optimization with a benchmark attached, not a design premise).
Needed: `divrem`, `gcd`, `pow_mod(f)`, derivative, squarefree part, monic
normalization.

### 4.3 Root finding in 𝔽_p (Rabin / Cantor–Zassenhaus)

Mirrors `uni_roots.cpp`:

1. `distinct_roots_poly(f) = gcd(f, x^p − x mod f)`, where `x^p mod f` is computed by
   repeated squaring in `𝔽_p[x]/(f)`. The result is the product of the distinct linear
   factors of `f` — i.e. exactly the roots, squarefree.
2. Equal-degree splitting: for shift `a`, `gcd(g(x), (x+a)^((p−1)/2) − 1)` splits `g`
   with probability ≈ ½ per shift. cvc5 samples `a` at random; **we walk
   `a = 0, 1, 2, …` deterministically**, which is equally effective in practice and
   keeps the solver reproducible. `p = 2` is a special case (trace map).
3. Return roots sorted by value (not by string representation, which is the hack cvc5
   uses because CoCoA cannot order ring elements — we can).

Cost: `O(deg(f)² log p)` field multiplications. Degrees here are small; `log p ≈ 254`.

### 4.4 Multivariate polynomials over 𝔽_p

Sparse `monomial → coeff` maps. Reuse the existing `polynomial::{Monomial,
MonomialOrder}` exponent-vector machinery where it is coefficient-agnostic; do **not**
retrofit the existing `BigRational` Buchberger/F4 to be generic over the coefficient
field. The rational engines carry normalization and coefficient-growth mitigations
tied to ℚ, and NRA is a live, sound path that a generics refactor would put at risk
for no gain. Duplication here is the cheaper trade; say so out loud in the module doc
so the next agent does not "fix" it.

### 4.5 Gröbner bases over 𝔽_p

Buchberger with Gebauer–Möller criteria and the normal selection strategy;
degree-reverse-lex for the UNSAT test (cheapest order); F4-style batched linear-algebra
reduction as the scaling path. Note the reason this is tractable at all: **over 𝔽_p
there is no coefficient growth.** The pathology that makes Gröbner bases over ℚ
explode simply does not exist here — which is why [OKTB23] works.

Budget: a step counter (S-pairs processed, reductions performed), surfaced through
`ResourceManager`, never elapsed time. Exceeding the budget yields `Unknown`, and the
distinction between "budget hit" and "computation finished" must be carried in the
return type, not inferred (§5, step 4).

**Determinism trap:** the variable order and the generator order fix the entire
computation. Neither may be derived from `FxHashMap` iteration order. Every collection
that feeds the GB is an index-sorted `Vec`.

### 4.6 Ideal-membership certificates (the "tracer")

Every basis element carries cofactors expressing it in the input generators:
`g = Σ cᵢ fᵢ`. cvc5 gets this by instrumenting CoCoA's reduction callbacks
(`core.cpp`, `Tracer`); we thread a sparse cofactor row through `s_polynomial` and
through each reduction step. Memory cost is real, so make it a flag — but default it
**on** whenever a core or proof may be requested, and force it on in certified mode.

This is what turns "UNSAT because the GB is {1}" into a checkable object: verifying
`Σ cᵢ fᵢ = 1` is one pass of polynomial arithmetic, orders of magnitude cheaper than
the basis computation that produced it.

### 4.7 Dimension test and minimal polynomials

- **Zero-dimensionality:** with a degrevlex GB, the ideal is zero-dimensional iff for
  every variable some basis element has a leading monomial that is a pure power of it.
- **Minimal polynomial of a variable modulo a zero-dimensional ideal:** linear algebra
  on the quotient basis (FGLM-style Krylov iteration / Wiedemann). cvc5 calls CoCoA's
  `MinPolyQuot`; this is the one CoCoA primitive with no cheap in-house substitute, so
  budget for it explicitly.

---

## 5. The decision procedure for a conjunction ([OKTB23] core)

Input: the asserted literals in one field — `p(x⃗) = 0` and `q(x⃗) ≠ 0`.

**Step 1 — encode.** Two passes, as in `cocoa_encoder.h`, because the polynomial ring's
variables must be known before any polynomial is built:

- equality `a = b` → generator `enc(a) − enc(b)`;
- disequality `a ≠ b` → generator `(enc(a) − enc(b))·w − 1` with a fresh witness `w`
  (exact: in a field, `a ≠ b ⟺ a − b` is invertible);
- `ff.bitsum(b₀…bₙ)` → fresh `s` and generator `s − Σ 2ⁱ bᵢ`, **kept in a separate
  generator set** so the front end (§6) can exploit bit structure and so cores can
  exclude it (it is a definition, not a fact).

**Step 2 — Gröbner basis, degrevlex.** If the basis is a single nonzero constant, the
ideal is the whole ring: **UNSAT**. The core comes from the tracer (§4.6) — the subset
of *asserted facts* whose generators appear with nonzero cofactor, with definitional
generators (bitsum, witnesses, field polys) filtered out. Never return the whole fact
set as the "core" when a traced core is available; cvc5 does that when tracing is off,
and it costs the SAT core a great deal of pruning.

**Step 3 — `FindZero` (model construction).** Two explicit heap stacks — one of ideals,
one of branchers — never native recursion (`AGENTS.md` → *Deep input must not overflow
the stack*; cvc5 already flattens its Fig. 5 recursion this way in `multi_roots.cpp`).
At each node:

- `1 ∈ I` → drop the branch;
- every variable has a linear univariate `xᵢ − cᵢ` in the GB → **model found**;
- otherwise build a brancher (`ApplyRule`, Fig. 6):
  1. a **super-linear univariate** element in the GB → branch on its roots (§4.3).
     Cheap and complete for that variable;
  2. **zero-dimensional** ideal → pick an unassigned variable, compute its minimal
     polynomial modulo the ideal, branch on its roots;
  3. **positive-dimensional** → round-robin over (variable, value) pairs. This is
     complete — any solution assigns *some* value to the first variable — but it is
     `p`-sized, and for a 254-bit prime it will not finish.

**Step 4 — the honesty gate.** If the stack empties, the branching was exhaustive and
UNSAT is genuine. If it empties *because a budget was exhausted*, it is not. The return
type must distinguish these:

```rust
enum FfOutcome {
    Model(FfModel),
    Unsat(FfCertificate),          // traced core + cofactors
    Exhausted,                     // search space genuinely closed
    OutOfBudget { where_: BudgetSite },   // → Unknown, never Unsat
}
```

cvc5 collapses the last two into "trivial conflict = all facts", which is sound there
because its budget exhaustion throws instead. Ours must be explicit: this is exactly
the "unjustified conflict yields `Unknown`, never `Unsat`" rule.

**Step 5 — validate the model, always.** Substitute and evaluate every asserted literal
in 𝔽_p. This is exact and costs one pass; there is no excuse for skipping it, and a
model that fails validation is an internal error that must surface as `Unknown` plus a
loud diagnostic, never as `Sat` (`AGENTS.md` → *No fabrication*). In certified mode,
re-verify the UNSAT certificate the same way.

**Where `Unknown` comes from** (the complete list — a theory that cannot enumerate its
own incompleteness is not honest):
non-prime modulus; extension field; GB step budget exhausted; `FindZero` budget
exhausted (in practice: the positive-dimensional round-robin at a large prime);
minimal-polynomial computation budget exhausted; a model that fails validation.

---

## 6. Field-aware front end — the difference between a demo and a tool

Everything below is sound-by-construction (ideal-preserving substitution, or
propagation with an explicit reason) and all of it runs *before* the GB.

1. **Constant propagation.** A generator `x − c` eliminates `x` everywhere. On
   circuit-derived systems this cascades a long way: witness computation is mostly
   straight-line.
2. **Linear core — sparse Gaussian elimination over 𝔽_p.** Partition generators into
   linear and nonlinear; keep the linear part in reduced row-echelon form; substitute
   pivots into the nonlinear part; an inconsistent row is an immediate UNSAT whose core
   is that row's support. This is the LRA tableau discipline Nixie already runs
   (sparse exact rows, pivot selection, incremental updates) transplanted to 𝔽_p, where
   it is strictly easier — no bounds, no ordering, no anti-cycling rule, termination is
   immediate. *Hypothesis to measure, not to assume:* R1CS from circom is dominated by
   linear constraints, so this should remove most generators before any GB runs.
3. **Bit constraints and bitsums.** Detect `x·(x−1) = 0` / `x² − x = 0` → `x ∈ {0,1}`.
   Then, with bitsum definitions kept separate (§5 step 1): if `s = Σ 2ⁱ bᵢ`, all `bᵢ`
   are bits and `n < log₂ p` (no wraparound), `s` determines every `bᵢ`; and two
   bitsums of equal width that are equal propagate bitwise equalities. This is
   `split_gb.cpp`'s `BitProp::getBitEqualities` ("extraProp") and it is the rule that
   makes range checks and comparisons tractable — which is most of what a circuit does
   that is not field arithmetic.
4. **Structural decomposition.** Connected components of the variable-sharing graph are
   independent subproblems. Trivial to implement, and the single most reliable way to
   keep basis sizes sane. Do this before anything expensive.
5. **Split Gröbner bases** ([split-GB], `split_gb.cpp`): maintain several bases over
   variable subsets and exchange only the consequences each admits. Phase 7 — after
   1–4 are implemented and measured, because it only pays once the cheap structure is
   already exploited.

**Measurement discipline.** Items 1–4 change what the procedure *does*, deterministically
— report solved counts and step counts, no matched null needed. But any *selection
heuristic inside* the GB (pair selection, variable order) reshuffles a chaotic search
the same way SAT branching does, and a claimed improvement there ships with a matched
null per `docs/BENCHMARKING.md`. Tick counters only; never wall-clock.

---

## 7. CDCL(T) integration and theory combination

**Multiplexing.** `FfTheory { subs: FxHashMap<FieldId, SubTheory> }` — one sub-solver
per modulus, exactly as cvc5 does. No inference relates 𝔽_p and 𝔽_q, so the split is
free.

**Atoms.** The signature has exactly one predicate (`=`), so the Tseitin encoder
abstracts each FF equality into a Boolean variable and the theory always sees a
conjunction. No new atom shapes, no internal case splitting, no theory-specific
encoding in `encode.rs`. FF is, in wiring terms, one of the easiest theories Nixie can
gain.

**Effort levels.** Full-effort: the whole procedure (§5). Lower effort: §6.1–6.3 only —
propagation and the linear core are cheap enough to run on every theory check and can
produce conflicts and propagations long before a GB would be justified.

**Scoping.** Facts live on a level-marked trail; `push`/`pop` truncate it. Every derived
artifact — GB, echelon form, model, core — is invalidated whenever the trail moves.
**Recommendation: recompute from the trail rather than incrementally undoing a GB.**
Incremental rollback of a basis is a soundness trap, and scope leakage is a bug class
this codebase has already bled from (`AGENTS.md` → *State must be scope-consistent*).
Take the recomputation cost until there is a measured reason not to, and then only with
an invariant checker.

**Explanations.** A conflict is a subset of the *asserted* literals, taken from the
tracer. Never a synthesized clause.

**Placement.** Phase 3 can land as an eager whole-problem dispatch —
`dispatch_ff_solver`, modelled on `check_nlsat.rs`'s `dispatch_nl_solver` — which
decides pure conjunctive `QF_FF` goals (the common shape for circuit queries) without
touching the CDCL(T) loop. Phase 4 promotes it to a real theory for goals with Boolean
structure.

**Combination is the subtle part.** 𝔽_p is a *single finite structure* of cardinality
`p`; the theory is not stably infinite, so textbook Nelson–Oppen does not apply. The
correct route is polite combination: EUF is smooth and finitely witnessable, so
`T_FF ⊕ EUF` is decided by guessing arrangements over shared FF-sorted terms, with EUF
adapting to the FF side's cardinality. Two practical obligations:

- the FF solver must accept both equalities and disequalities over shared terms — it
  does, via witnesses;
- an arrangement with `k` pairwise-distinct shared terms is satisfiable only if
  `k ≤ p`. For ZK primes this is vacuous; for `𝔽_2`, `𝔽_3` it is not, and **omitting
  the check is a false `sat`**. It needs an explicit cardinality guard in the
  combination layer and a regression test built on a toy field.

Phase 1–5 scope is `QF_FF` alone, with mixed FF/UF inputs rejected by the logic
contract. `QF_UFFF` comes only after the arrangement machinery and that guard exist.

---

### 7.1 `QF_UFFF` as built (2026-09-16)

The polite combination landed with the architecture the §7 discussion
sketches, in the shape the dispatch layer could carry honestly:

- **Opaque applications.** An application with an FF result sort is an
  *opaque ring variable* to the whole `QF_FF` procedure: the encoder
  mints it a variable, the enumerator assigns it, the exact evaluator
  looks it up. Application arguments are never descended into by any
  FF walk (an application contributes exactly its result field to
  slice routing — a foreign-field argument belongs to its own field's
  slice).
- **Batch congruence closure** (`nixie-theories/src/ff_euf.rs`) over
  the FF-sorted subterms of the goal's atoms: merges from the asserted
  equalities of the current Boolean model, closed under congruence by
  a fresh-signature-table fixpoint (no incremental signature
  maintenance to get wrong — a stale entry is structurally impossible
  when every round rebuilds).
- **Model-guided arrangement search.** Per Boolean model, the closure's
  merge classes become extra literals for the FF slices; the FF
  procedure's model induces an arrangement over the shared terms; a
  function-hood violation (equal argument values, different results)
  splits on the *valid* disjunction `f(a) = f(b) ∨ ⋁ᵢ aᵢ ≠ bᵢ`, driven
  by an explicit stack. This is the arrangement guessing of polite
  combination without an `O(n²)`-literal upfront case split: the FF
  model proposes, the disjunction discharges.
- **Completion.** Unconstrained FF terms (those no literal mentions)
  get defaults, repaired to preserve function-hood; a completion the
  pass cannot build is an `unknown`, never a broken model.
- **Cardinality at both ends.** The spine guard (top-level `distinct`
  over k > p terms, pigeonhole certificate) and, per Boolean model, the
  interface guard over `distinct` families the model asserts in full —
  built from pair literals *after* construction-time folding, so a pair
  whose equality folds to `true` (the family is refutable outright)
  never inflates the count. That folding interaction was a real false
  `unsat`: "absent from the model" is not "asserted negative".
- **Honesty.** One shared tick budget (case nodes) and a bounded
  per-node FF budget; both exhaust to `unknown`. Refutations block the
  Boolean model with a **destructively minimized** conflict subset
  (each shrink re-runs the root check, so the surviving subset really
  refutes) or the traced FF core when it names only assignment literals.

Verified by `nixie-solver/tests/ff_ufff_oracle.rs` — brute force over
*every* model (variable assignments × function tables) at `p ∈
{2,3,5,7}` — plus the congruence/cardinality/certified-mode
regressions in `ff_ufff_regression.rs`.

Known gaps, deliberately honest: multi-field congruence-dependence
disables core-directed blocking (those block on the whole assignment);
compound unconstrained arguments the completion cannot separate
decline to `unknown`; combination UNSATs that need field arithmetic
have no certificate (certified mode downgrades; pure-congruence
refutations certify through the checker's independent EUF loop).

## 8. Models, proofs, certificates

**Models.** A `FieldId`-indexed map from variable to value; `get-value` on an arbitrary
FF term evaluates by exact substitution. Printing is `#f<v>m<p>`.

**UNSAT certificate — the easy half.** Cofactors `cᵢ` with `Σ cᵢ fᵢ = 1`: an explicit
ideal-membership (weak Nullstellensatz) certificate, checkable by one round of
polynomial arithmetic. Emit it as a first-class proof rule carrying the cofactors —
`ProofRule::TheoryLemma { theory: "FF" }` with an opaque payload is acceptable as a
first step, but a theory lemma with no checkable content is the "unjustified conflict"
the soundness rules forbid, so the rule should carry the certificate from the start.

**UNSAT by branch exhaustion — the hard half.** When UNSAT comes from `FindZero`
closing the tree rather than from `1 ∈ I`, there is no single cofactor certificate. The
proof is a case tree: each branch step says "these are all the roots of this univariate
polynomial in 𝔽_p", and each leaf carries a certificate. That branch step *is*
checkable — `f = ∏(x − rᵢ)·q` with `gcd(q, x^p − x) = 1` — but it is real work.
**Honest fallback:** until it exists, certified mode downgrades branch-exhaustion
UNSATs to `Unknown` rather than emitting an unchecked proof. Disequality witnesses are
fresh Skolems and must appear in the certificate's signature.

---

## 9. Soundness rules, mapped

| `AGENTS.md` rule | How this design satisfies it |
|---|---|
| No silent fallthrough | New `SortKind`/`TermKind` variants break every exhaustive match; non-prime modulus, extension fields and unsupported operators raise errors, never defaults |
| No fabrication | `FfOutcome` separates `Exhausted` from `OutOfBudget`; mandatory model validation in 𝔽_p; cores are subsets of asserted literals; certificates re-checked in certified mode |
| No stack overflow on deep input | `FindZero` is two explicit heap stacks; the term→polynomial encoder is an explicit-stack walk like every other term walk in the codebase |
| Exact bignums | Montgomery limbs sized to `p`; no `u64` fast path that truncates; the modulus is `BigUint` end to end, including through the parser (which today cannot even represent it — §3.3) |
| Scope consistency | Level-marked fact trail; every derived artifact invalidated on trail movement; recompute rather than roll back a basis |
| No `unwrap`/`expect` | Field context lookups, root extraction and cofactor bookkeeping all return `Result`; the "impossible" cases (a univariate polynomial with no variable index, an unassigned variable in a zero-dimensional ideal — both `Assert`/`Unreachable` in cvc5) become representable-state errors here |
| Determinism | Derandomized Rabin shifts; step-budgeted GB; index-sorted iteration everywhere; no wall-clock anywhere in the policy path |

---

## 10. How this gets verified — there is no Z3 oracle

**Z3 has no finite-field theory.** `./bench/z3_parity/run_parity.sh`, the project's
soundness canary, cannot cover `QF_FF` at all. That absence has to be replaced, not
waved at. In ascending order of strength:

1. **Self-validation, always on.** Every `sat` re-evaluated in 𝔽_p; every `unsat`
   certificate re-multiplied. Cheap, exact, and it catches the entire class of
   "encoder and solver disagree" bugs.
2. **Exhaustive brute force at small primes.** Random systems over `p ∈ {2,3,5,7,11,13}`
   with `n ≤ 4` variables and degree ≤ 3: enumerate all `pⁿ` points and compare
   verdicts. This is a *complete* oracle, and it is the finite-field analogue of the BV
   work already recorded in `docs/studies/2026-08-bv-exhaustive-certification.md`.
   It is also where the combination cardinality guard (§7) gets its regression.
3. **Planted-solution fuzzing at real primes.** Sample `z ∈ 𝔽_pⁿ`, generate constraints
   satisfied by `z`: ground truth is `sat`, so any `unsat` is a hard failure at n = 1.
   Mutated instances have no ground truth — use them for crash/assertion testing only,
   never for verdict scoring.
4. **Algebraic property tests.** Reduction is confluent modulo the basis; the basis
   generates the same ideal as the input (membership agrees both ways); root sets match
   brute force; every traced cofactor row verifies.
5. **Corpora.** SMT-LIB has a `QF_FF` division (from the CAV'23 artifact); vendor a
   subset under `bench/ff/` the way the other corpora live in-repo. For realism, a
   small circom → R1CS → `.smt2` converter: each R1CS row `⟨a,z⟩·⟨b,z⟩ = ⟨c,z⟩` is one
   `ff.mul`/`ff.add` equality, so the mapping is mechanical.
6. **Optional external comparator.** An *installed* cvc5 binary may be used as a
   differential oracle exactly as `z3 4.16.0` is used today — consulted as a process,
   never linked, `deny.toml` untouched. It cannot be a gate, since a cvc5 install is
   not assumable, and the comparator must stay honest (`Unknown` never counts as a
   match).

Plus a `fuzz/` target for the parser + solver on FF inputs — the `#f…m…` literal and
bignum sort index are new lexer surface, and new lexer surface is where fuzzers earn
their keep.

---

## 11. Phasing

| Phase | Content | Exit criterion |
|---|---|---|
| 0 | `SortKind::FiniteField`, `FieldId`/`FieldTable`, five `TermKind` variants, lexer/parser/printer, `QF_FF` logic entry, rewriter | FF inputs parse, print and round-trip; every solve answers `Unknown` honestly; non-prime and extension fields error |
| 1 | `nixie-math::ff`: `Fp` + Montgomery, univariate polys, Rabin root finding | Known-answer tests, brute-force-verified root sets at small `p`, property tests |
| 2 | Multivariate 𝔽_p polys, Buchberger + Gebauer–Möller, cofactor tracer, dimension test, minimal polynomial | Ideal-membership agreement tests; every cofactor certificate verifies |
| 3 | `SubTheory`: encoder, GB-UNSAT + traced core, `FindZero`, model validation; eager `dispatch_ff_solver` | Conjunctive `QF_FF` decided; brute-force oracle agreement at small `p`; the `Unknown` list of §5 is the only source of `Unknown` |
| 4 | CDCL(T) wiring: trail, scoping, cores as lemmas, Boolean structure | Goals with Boolean structure decided; scope regressions (push/pop/assert interleavings) green |
| 5 | Field-aware front end §6.1–6.4 | Measured on `bench/ff/`; step-count reductions reported with the benchmarking discipline |
| 6 | Certificates and proof rules; certified mode; `QF_UFFF` with the cardinality guard | Certificates checked end to end; toy-field combination regression green |
| 7 | F4, split GB, NTT if earned | Each with a pre-registered experiment |

A useful solver exists at the end of Phase 3; a competitive one at the end of Phase 5.

---

## 12. Open questions

- **Extension fields.** `GF(2^k)` matters for AES/Rijndael verification, and binary
  tower fields are becoming load-bearing in newer proof systems. The sort carries a
  field *description* for this reason, but the procedure (root finding, the `x^q − x`
  field polynomial, Rabin's odd-characteristic assumption) needs real work. Out of
  scope here; not designed out of the AST.
- **Is `ff.bitsum` core signature or sugar?** cvc5 has it as a kind because split-GB's
  bit propagation needs to see it. Following that is the low-risk choice.
- **Under-constrainedness is the question users actually ask.** The industrial ZK query
  is usually not "is this system satisfiable" but "is the witness unique given the
  inputs" — i.e. `∃ x, x'` agreeing on inputs and differing on outputs, expressible in
  `QF_FF` by doubling the circuit. Worth documenting as an idiom, and worth considering
  as a front-end mode once Phase 5 lands; that, not raw satisfiability, is where the
  demand is.
- **What "good" means.** No performance target is proposed here, because none can be
  honestly set before Phase 3 produces a baseline on `bench/ff/`.

---

## 13. References

- **[OKTB23]** A. Ozdemir, G. Kremer, C. Cadar, C. Barrett, *Satisfiability Modulo
  Finite Fields*, CAV 2023. <https://doi.org/10.1007/978-3-031-37703-7_8>
- **[split-GB]** A. Ozdemir et al., *Split Gröbner Bases for Satisfiability Modulo
  Finite Fields* (cited by `split_gb.h`).
- cvc5 source (read-only spec): `../temp/cvc5/src/theory/ff/` — `Readme.md` maps every
  file to its figure in [OKTB23]; `sub_theory.cpp` (Fig. 2), `core.cpp` (Fig. 4),
  `multi_roots.cpp` (Figs. 5–6), `uni_roots.cpp` (root finding), `cocoa_encoder.h`
  (two-pass encoding), `theory_ff_rewriter.cpp` (normal form),
  `../temp/cvc5/src/parser/smt2/` (surface syntax).
- M. Rabin, *Probabilistic algorithms in finite fields* (1980); Cantor–Zassenhaus
  equal-degree splitting.
- Gebauer–Möller criteria; Faugère's F4; FGLM order conversion.
- In-repo: `docs/THEORY_GUIDE.md`, `docs/TUTORIAL_CUSTOM_THEORY.md`,
  `docs/BENCHMARKING.md`, `docs/CERTIFIED_MODE.md`,
  `docs/studies/2026-08-bv-exhaustive-certification.md`.
