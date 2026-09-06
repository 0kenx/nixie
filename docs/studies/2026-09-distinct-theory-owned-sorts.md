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

## Resolution: Int/Real enabled via separation clauses (2026-09-06, part 2)

The enabling change identified above is now implemented, and the
`Int | Real` gate is ON.  Three pieces:

1. **Co-located split proposals** (`nelson_oppen_combine`, gated on the
   encoding's presence): final checks group UF-argument interface terms by
   their tableau value and propose every e-graph-apart pair of a
   co-located group.  The root cause of the earlier non-convergence was
   *not* the rebuild cost alone: the old channel internalized a bare
   `(= x y)` atom with **no trichotomy**, so deciding it false left
   arithmetic unaware of the disequality and the tableau re-co-located the
   pair in every later candidate.
2. **`refine_colocated_splits`**: one *valid trichotomy clause* per pair
   (`(= x y) ∨ x < y ∨ x > y`, with the acyclic-orientation phase hint) –
   a decided-false equality now forces a strict disjunct and the tableau
   separates, permanently (the clause persists across rounds).  Round
   shape: reset + rebuild, like the other refinement rounds; 256 pairs
   per search round, 256-round cap.
3. **The honesty gate** (`injective_distinct_collisions`): every `Sat`
   exit checks the registered specs against the model the solver is about
   to print – a spec whose `distinct` term is **true** in the model must
   show pairwise-distinct argument values, else the verdict downgrades to
   `Unknown` (with budget left, the colliding pair is fed back as one more
   split round).  The result-term conditionality matters: a model that
   makes the `distinct` *false* colliding is exactly its meaning, and an
   unconditional gate wrongly degraded legitimate ¬distinct models.
   Found by measurement: before the gate existed, a cap-exhausted run
   answered `sat` with a colliding model; after it, the same run answers
   `unknown` and no test below can reproduce a dishonest print.

**Measured** (release, old = pairwise at n > 32):

| cell | old | new |
|---|---|---|
| n=40 free Int vars, sat | 15.0 s | **0.82 s** (model verified 40/40 distinct) |
| wide-range pair + 42 vars, sat | 60.4 s | **10.7 s** |
| n=60 free vars, sat | timeout@240 s | **77 s** |
| n=100 free vars, sat | timeout@240 s | timeout@240 s |
| bounds-pinned collision, unsat | fast | fast |
| ¬distinct + all pinned, unsat | fast | fast |
| bare ¬distinct, n=33 free vars | hang | 11 s (still slow; see below) |

Batching lesson: 256 pairs/round converges; emitting a full group's
clauses at once (780 at n = 40) measurably derails the re-descent (~300
full assignments between generalizing conflicts).  The search digests
small batches; the round *loop* provides the scale.

Postscript (same day): gap (b) closed, and it was not a witness-guidance
problem at all.  The co-located proposal block ignored the result
literal's polarity: a ¬distinct instance *legitimately* collides its
arguments, yet the block proposed – and the refine loop emitted –
trichotomy clauses separating exactly the pair the witness was merging,
manufacturing ~2500 final-check arith refutations of phantom work (the
measured 10 s at n = 33, timeout at n = 100).  A polarity gate (propose
only while some live encoding's result literal is TRUE in the current
assignment) plus natural-witness phase hints (the first two `L`s at
true, the `F`s at false) makes both polarities instant: bare ¬distinct
n = 33 goes 10.2 s → 0.020 s, n = 100 timeout → 0.029 s, and the
positive n = 60 cell drops 77 s → 7.4 s as a side effect (intermediate
candidates with result not-yet-true no longer burn proposal rounds).

Also landed: composite finite datatypes now count for the pigeonhole
short-circuit (Σ_ctor Π_selector cardinality, Z3 `get_num_elements`
shape, with visited-set cycle detection so recursive/mutual carriers
stay conservatively infinite) – `(declare-datatypes ((Pair 0)) (((mk (a
E2) (b E3)))))` with 7 arguments now refutes by one unit clause.

Considered and deferred: folding uninterpreted-witness equality into
`combine_eq` (so `(get-value ((= x1 x2)))` answers instead of echoing on
uninterpreted sorts).  `EvalVal` has two variants and ~37 match sites,
several of them load-bearing for the certificate gate's verdict
semantics (the deliberately-undetermined `Distinct`, the
boundary-softened strict comparisons); the echo is cosmetic, the gate is
soundness-sensitive – not worth the blast radius without its own session.

Postscript 2: gap (a) closed too, and again not by the mechanism first
reached for.  The Z3-style in-tableau repair was queued as the next
enabling change, but the actual blocker was the *shape of the
proposals*: both proposal sources emitted star/clique-shaped pairs, and
each round's candidate separated roughly one pair.  The observation that
makes it O(n): a strict trichotomy row composes by **transitivity** –
`t_1 < t_2 ∧ t_2 < t_3` already gives `t_1 ≠ t_3` in the tableau – so a
CHAIN of k−1 consecutively-paired, consistently-oriented clauses
distinctifies a k-member co-located group.  (This is exactly where the
eq-decision intuition from the earlier care-split work was wrong:
separating everyone from one witness leaves the rest free when the
separation is an equality decision, but a strict-row chain composes.)
Both sources now emit TermId-ordered chains, and the refine side orients
every clause's strict literals along that order (the existing
orientation hint in `add_arith_trichotomy_clause` is gated to
array-bearing problems for historical reasons, so the orientation is
re-created at the refine call site).

Measured (release, free-variable `distinct` over Int):

| n | before the chain | after |
|---|---|---|
| 40 | 0.82 s | 0.007 s |
| 60 | 7.4 s | 0.014 s |
| 100 | timeout | 0.040 s |
| 200 | timeout (600 s+) | 0.094 s |
| 500 | timeout | 0.150 s |
| 1000 | – | 1.48 s |
| 2000 | – | 13.4 s (model verified 2000/2000 distinct) |

Convergence is now one round for these shapes (a cap=1 build still
answers `sat` at n = 200); the honesty gate remains as the backstop for
multi-group shapes.  The whole 43-test distinct suite runs in 0.4 s.

Postscript 3: the threshold cliff.  Z3's `distinct_max_args = 32` was
inherited for every sort, but nixie's pairwise path pays a trichotomy
clause per pair on the *satisfiable* side, and the sweep shows the
cliff that buys: free-variable `distinct` over Int at n = 24/28/32 takes
254 ms / 1.6 s / timeout under pairwise vs 7 / 8 / 9 ms under the
injective map, and the negated shapes are already 30-45000× apart in
decisions at n = 12-28.  Below n ≈ 8 the two encodings are at parity
(worst pairwise deficit: single-digit decisions on 2-6-argument
positive shapes).  The numeric threshold is therefore measured, not
inherited: `DISTINCT_NUMERIC_PAIRWISE_MAX_ARGS = 8`, with Z3's 32 kept
for EUF-owned sorts (no trichotomy tax, no cliff observed).

Corpus validation of the whole program (the `smt-lib/non-incremental`
extracts): 4360 files carry `distinct`, 380 at arity >= 8 including
Dartagnan ReachSafety instances at arity 225-267 over QF_LIA/QF_NIA.
A/B of the direct parent binary against the new build over all 380:
**zero verdict mismatches**, 20 strict wins, 0 losses; the 63 shared
timeouts are hard for non-`distinct` reasons (the encoding is not
their bottleneck).  The synthetic sweep supplies the isolated wins;
the corpus certifies that nothing real regressed.

## Postscript 4: ground-constant distinctness via value marks

The e-graph's `declare_value_const` machinery (built for the injective
map) replaces the last quadratic ground-constant mechanism: the per-pair
`assert_diseq` edges among distinct Int/BV constants that
`intern_leaf_deep` / `intern_leaf_for_congruence` maintained – C(k,2)
edges for k distinct literals.  Findings along the way:

* The **Int** half was *dead code*: `intern_term_deep` had no callers
  left (an earlier refactor moved constant interning to the
  `intern_term_for_congruence` family, which never had Int edges).
  Deleted outright, together with its `interned_int_constants`
  bookkeeping.
* The **BV** half was live and is migrated: each canonical constant is
  declared with a fresh monotone value id *before* interning (the node
  is born marked; ids survive rebuilds via the symbol-level registry,
  so two different constants can never share one).  k literals now
  cost k marks, O(k) total.
* The old edges also fed `are_proven_disequal` and, through it, the
  equality-atom watch propagation (`(= x #x01)` forced false once `x`
  merges into `#x00`'s class).  Marks now feed the same paths: the
  proven-disequal test accepts differing class-value summaries, the
  merge-time atom re-test enqueues value-apart atoms, and a value-apart
  pair whose edge-explanation is absent propagates with an *empty*
  (tautological) justification – a level-0 fact, exactly what "two
  different ground constants" is.

Measured (release, k distinct BV constants under UF applications):

| k | edges (old) | marks (new) |
|---|---|---|
| 2000 | 4.75 s | 0.37 s |
| 4000 | 9.26 s | 0.64 s |

Corpus A/B on a 300-file random sample of the QF_BV/QF_ANIA extracts:
zero verdict mismatches, 3 wins / 1 loss / 296 ties.  Parity 100%.

Remaining gaps: BitVec large-arity `distinct`, unchanged (see below) –
still the only row of the original table left open.

## Attack 3: the order encoding over BitVec — correct, measured, no flip

The study's original conclusion predicted BitVec as the order encoding's
home turf: `bvule` is a total order (the whitelist passes), and every atom
is a bit-blasted gate circuit.  The encoder was built accordingly –
comparators as `bvule` atoms, mux pins as conditional BV equalities, the
chain as `bvult` atoms, pads as free bit-vectors (the pigeonhole
short-circuit guarantees `n ≤ 2^w`, hence `n2 = next_power_of_two(n) ≤
2^w` and the padded chain always fits the domain), plus an identity
phase-hint pass (each wire's bits pointed at its index so the identity
arrangement is the first descent).

**Correctness: complete.**  All polarities and edges agree with Z3:
free-variable `sat` (model verified pairwise-distinct), forced-equality
`unsat`, duplicate-argument `unsat`, negated-with-all-pinned-apart
`unsat`, the 32/33 boundary in both polarities, the exactly-full-domain
edge (`n=40, w=6 → n2 = 64 = 2^6`), and 200 randomized differential
trials (n ∈ {2..120}, w ∈ {4..32}, constants/compounds mixed in, both
polarities, forced equalities) — zero verdict disagreements.

**Performance: a wash.**  Release builds, old (pairwise) vs new (network):

| cell | pairwise | network |
|---|---|---|
| n=300 w=16 sat | 4.15 s | 3.80 s |
| n=300 w=16 unsat (explicit `= x1 x300`) | 0.055 s | 0.179 s |
| n=600 w=32 sat | 51.4 s | 42.1 s |
| n=2000 w=16 unsat (explicit) | 1.44 s | 0.99 s |
| n=2000 w=16 sat | timeout | timeout |
| n=600 w=10 sat (dense domain) | 35.6 s | 33.2 s |
| n=1000 w=11 sat (dense) | timeout | timeout |
| n=500 w=9 sat (dense) | 35.3 s | 34.7 s |

Differences are within the noise band `docs/BENCHMARKING.md` documents
(an RNG-seed change alone moves cost 7.31×).  No cell shows the decisive
win an encoding flip needs; the mid-n explicit-unsat cell actively
regresses (pairwise's lazy circuit for one `(= x_i x_j)` is trivial,
the network must derive the contradiction through its log² levels).

**Why the prediction failed – two architectural facts:**

1. **The BV circuits do not live in the main SAT core.**  `BvSolver`
   owns an *embedded* SAT instance, asserted into at theory-check time
   and solved in batches.  The order encoding's whole advantage –
   comparator decisions propagating through gates *during* the descent –
   is exactly what batching removes: gate propagation happens per theory
   check, not per decision.  (This is also why the identity phase hints
   inside the embedded instance could not rescue the n=2000 sat cell:
   the bottleneck is the interleaving, not the embedded search.)
2. **Pairwise circuits are built lazily per asserted atom.**  A pairwise
   `distinct` only pays for the equality circuits of atoms the search
   actually assigns; the C(n,2) blowup is *potential*, not eager.  The
   network, by contrast, needs every comparator of the chain wired for
   the encoding to mean anything.  At every reachable n both pay
   comparable eager costs.

**What would flip the verdict:** unify BV circuits into the main SAT
core (or give the embedded solver a per-decision propagation
interface).  Then comparators genuinely propagate mid-descent, the
identity phases guide the whole descent, and the network's O(n log²n)
shape should beat pairwise's on-demand C(n,2).  Until then, BitVec
stays pairwise for n > 32, exactly like Int/Real — for a different
reason: not a soundness gap, but the absence of a measurable win.

Code not landed (design lives here; the bitonic generator and 0-1
verification are reproduced in the Int/Real section above and in git
history of the experiment branch).

## Test evidence

`nixie-solver/tests/distinct_encoding.rs` (unchanged, 23 tests) plus the
`value_*` e-graph unit tests all green; full workspace suite green; Z3
parity 170/170 decisive, 0 disagreements; the Int/Real differential
observations above were re-verified against z3 4.16 verdict-for-verdict
(the only divergences were harness artifacts of `QF_UF` + Int sorts).
