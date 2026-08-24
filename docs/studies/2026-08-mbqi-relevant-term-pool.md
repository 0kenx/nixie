# MBQI relevant-term pool: empty-sort candidate pools (ABV residual) (2026-08-24)

## The residual, confirmed live

The registry study's `ABV` smoke (quantified BV-indexed arrays →
`unknown` vs z3 `unsat`) was isolated to a single ingredient:

| probe | oxiz | z3 |
|---|---|---|
| Int-indexed `∀i. select a i = i` + violation (AUFLIA) | unsat | unsat |
| BV quantifier, no select (`∀i. bvult i b`) | unsat | unsat |
| **BV-indexed** `∀i. select a i = i` + violation (ABV) | **unknown** | unsat |
| same with explicit `:pattern` | **unknown** | unsat |

## Root cause (three compounding gaps)

MBQI per-round counterexample search builds, per bound-variable sort, a
candidate pool from three strategies (model universe, model assignment
values, sort defaults) plus an injected pool of ground terms.  For a
BV4-indexed quantifier with auto-trigger `(select a i)`:

1. **Ground terms were collected only from pattern subterms** — the
   pattern contains no ground BV term, so extras for the BV4 sort were
   empty.  The ground `#xb` of the violating assertion never entered
   the pool, and MBQI found no counterexample in any round (verified:
   every round returned `Unknown` from the no-witness path).
2. **`add_default_candidates` had no BitVec arm** (Int got −2..=5, Bool
   got true/false, BV got nothing).
3. **Injected extras replaced the strategies** — `inject_extra_candidates`
   wrote straight into `candidate_cache`, whose hit short-circuits every
   strategy in `build_candidate_lists`.

## Fix

- **Relevant-term pool** (`encode.rs::assert`): every ground sub-term of
  a quantifier-FREE assertion enters the pool (the z3-style relevant
  ground terms).  Quantified assertions keep their pattern-collection
  path (a naive walk would reach under binders).
- **BitVec defaults** (`add_default_candidates`): the BV domain is
  finite — width ≤ 3 enumerates exhaustively (8 ≤ candidate cap);
  wider widths get the structural set {0, 1, sign bit, all-ones}.
- **Empty-pool-only strategies**: extras still *replace* the strategies
  when present.  First attempt MERGED extras with strategies — and
  regressed a parity benchmark (`injective_unsat.smt2`, UFLIA, 0.04 s
  `unsat` → 0.13 s `unknown`): merging changed the Int pool
  composition for every sort that already had extras, perturbing the
  instantiation enumeration order.  Trajectory lesson re-learned at the
  MBQI layer: candidate-pool composition is search state.  The landed
  semantics change *nothing* for sorts that had extras (their pool is
  exactly as before) and only fill pools that were EMPTY — which is
  precisely the gap.

## Results

- `ABV` probes (auto-trigger and explicit `:pattern`): `unsat` (z3
  parity) — the registry study's residual closed.
- Parity: **167 solved / 0 wrong / 1 unknown — byte-identical to
  pre-change** (the regressed-then-recovered `injective_unsat` included).
- Differential: 0 wrong verdicts, solved 160 unchanged.
- 10 092 tests (2 new ABV regressions), clippy/fmt/doc, canaries
  unchanged.

## Residuals

- ~~Satisfiable quantified-array goals still cannot be *certified* `sat`~~
  **Closed by `2026-08-bv-exhaustive-certification.md`**: a BV-sorted
  bound variable's domain is exactly `2^width` values, so
  `bounded_domains` enumerates it exhaustively — sound with no
  relevant-term argument — and the array-over-BV sat control now answers
  `sat`.  (The counterexample-pool cap note stands, but applies to the
  MBQI search path, not certification.)
