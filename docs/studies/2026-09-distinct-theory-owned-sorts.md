# Large `distinct` over theory-owned sorts: two attacks, one landing, one enabling change identified

**Date:** 2026-09-06
**Scope:** the last row of the shape-aware `distinct` encoding table (see
`nixie-solver/src/solver/encode.rs`, `TermKind::Distinct` arm): n > 32 over
sorts the *theories* own (Int/Real today; BV/FP/String beyond), which still
pays the O(n²) pairwise encoding with a trichotomy case split per pair.

**Verdict:** the injective-map encoding is *sound* over Int/Real today on
every refutation shape tested, but the satisfiable free-variable case does
not converge without an arithmetic-side separation mechanism Z3 has and
nixie lacks. The gate stays `Uninterpreted`-only. What landed instead: one
valid clause that removes the encoding's main search-thrash mode (a 10×
measured win on the *existing* uninterpreted path), plus the inert,
documented machinery a follow-up flips on. This note is the map.

## Why the naive extension is unsound (recap, measured)

The injective map's soundness over a sort S reduces to: whenever two
arguments are equal *in a model*, the e-graph must learn `t_i = t_j` so
congruence on `dist-f` collides the distinguished values `m_i ≠ m_j`.

For EUF-owned S that is automatic. For Int/Real, equality can hold through
arithmetic the e-graph never sees:

* **pinned collisions** (`(>= x 5) (<= x 5) (= y 5)`): handled — the care
  graph's model-equal UF-argument probe merges the pair with a complete
  derived reason (`nelson_oppen_combine`), the value conflict fires.
  Verified: 44-argument bounds-pinned instance answers `unsat`.
* **mere co-location** (the tableau seats two apart-arguments at one value
  without entailing the equality): nothing separates them. The final model
  prints the collision, violating the asserted `distinct`. The certificate
  gate cannot catch it (`Distinct` is deliberately UNDETERMINED there); the
  model-blocking gate catches some of it after the fact.

## Attack 1: sorting-network order encoding — wrong tool here

Design: pad the arguments to a power of two, run a Batcher bitonic network
of comparators `c := a ≤ b; ¬c → u=a,v=b; c → u=b,v=a`, and Tseitin
`result ⟺ s_1 < s_2 < … < s_N` over the sorted outputs. O(N log² N) atoms,
zero disequality atoms.

**Total order is required, and that is a soundness boundary, not a
formality.** The chain's soundness direction needs only irreflexivity +
transitivity of the theory's `<`; the *completeness* direction — distinct
values admit a strictly increasing arrangement — needs **totality**. Over a
partial order, two incomparable distinct values admit no chain, the
encoding over-constrains, and the failure is a silent false `unsat`.
FloatingPoint is the live example (`fp.lt` is irreflexive and transitive
but NaN-incomparable), which is why any gate must be an explicit whitelist,
never a "has `<`?" probe. The comparator machinery agrees: `min`/`max`
presuppose comparability, and the 0-1 principle (exhaustive small-n
verification of the generated network) is proved for total orders only.

Int/Real pass the whitelist, so the encoding was built and measured.
**Result: the search flounders.** Comparator truth is theory-determined
(arith knows `a ≤ b` from the pins), but that knowledge reaches CDCL only
at final-check time; during the descent each comparator decision is a blind
guess with no propagation behind it. Measured on 16 wires with *fully
pinned inputs*: ~40 decisions per conflict, no convergence; phase guidance
(`set_deterministic_phase(c, true)`, the identity arrangement) did not fix
it. Sorting-network encodings earn their keep over **bounded** domains
where `≤` bit-blasts into propagating circuits — i.e. they remain the right
candidate for **BitVec** later, where pairwise equality atoms are also
cheap XOR trees rather than trichotomy splits.

Code removed; this note and the analysis above are the artifact.

## Attack 2: injective map over Int/Real + combination completion

The encoding was enabled for `Int | Real` experimentally, with three
supporting changes (all still in the tree, see "What landed"):

1. **E-clause** `result → ¬at_least_two(L_1..L_n)` — valid (two true `L`s
   plus the `F`s force `m_i = a = m_j`), and it converts the encoding's
   worst search mode from a final-check theory conflict into unit
   propagation. Without it, CDCL freely decides pairs of `L` atoms true;
   each collision is refuted only at a full assignment, one arrangement
   per ~n·30-decision re-descent (measured 4.3M decisions at n = 40).
2. **Trichotomy suppression for the A-units**: `g(f(t_i)) = t_i` is a
   level-0 unit, so the numeric-eq trichotomy clause attached to it is
   forever satisfied and its `lt`/`gt` atoms are unconstrained decision
   fodder.
3. **Pre-pass skip**: `add_arith_diseq_split` must not emit C(n,2)
   trichotomies for a distinct the injective map owns — the quadratic
   atoms the encoding exists to remove, on top of it (measured as the
   dominant thrash: 2380 parsed atoms at n = 40).

**Unsat side: fully correct and fast** — pinned collisions, forced
equalities, duplicate arguments, negated-with-all-pinned-apart, all refute
through the care graph + congruence + value marks.

**Sat side: honest but not convergent.** The tableau starts free arguments
co-located (all 0; the A-units give each argument a row, so the model
builder's unconstrained-argument default never applies). Closing each
collision needs the pair's `(= x y)` atom decided and its trichotomy split
run — the co-located care-split proposals (added, gated on the encoding's
presence) do exactly this, lazily. But for n free arguments that is ~C(n,2)
lazy atoms — the pairwise cost again — and the loop through
refine/re-solve/model-blocking eventually exhausts itself into a sound
`Unknown`. Measured: n = 40 free variables → `Unknown` in 0.3 s (was: slow
but correct `sat` under pairwise). That precision regression is why the
gate stays off.

**The enabling change (for the next session):** Z3's `theory_arith` final
check *separates* variables the e-graph holds apart — it repairs the
simplex model (or emits the split lemma `x < y ∨ x > y` and continues)
without materializing `(= x y)` atoms for every pair. The nixie-native
equivalent is one of:

* a tableau-side separation at final check for live-apart interface pairs
  (repair the basis; no atoms), or
* a model-builder repair that re-seats pinned-but-separable arguments at
  distinct feasible values, or
* batched split lemmas `[lt(x,y), gt(x,y)]` learned in-search (not via the
  from-scratch `refine_arrangement_splits` rebuild).

Any one of those, plus flipping the `Int | Real` gate in the `Distinct`
arm, re-applying the pre-pass skip, and keeping the bail-path trichotomy
emission (`emit_distinct_pairwise_trichotomies`), completes the row. The
co-located proposal block in `nelson_oppen_combine` is already wired and
gated for it.

## What landed

* **E-clause** in `encode_distinct_injective` — valid for every sort the
  encoding takes; measured 10× on the uninterpreted congruence family
  (N=200: 0.44 s → 0.044 s; N=500: parity).
* **`suppress_numeric_eq_trichotomy`** save/restore around the A-units
  (inert while the encoding is uninterpreted-only).
* **`has_injective_distinct` / `injective_distinct_specs` /
  `TrailOp::DistinctSpecAdded`** — the flag, the spec registry, and its
  pop-discipline, threaded to the `TheoryManager`.
* **Co-located care-split proposals** in `nelson_oppen_combine` — gated on
  the flag, all-pairs per co-located group, capped at 256/round, deduped;
  inert today (uninterpreted arguments carry no arithmetic values).
* The gate comment in the `Distinct` arm pointing here.

## Test evidence

`nixie-solver/tests/distinct_encoding.rs` (unchanged, 23 tests) plus the
`value_*` e-graph unit tests all green; full workspace suite green; Z3
parity 170/170 decisive, 0 disagreements; the Int/Real differential
observations above were re-verified against z3 4.16 verdict-for-verdict
(the only divergences were harness artifacts of `QF_UF` + Int sorts).
