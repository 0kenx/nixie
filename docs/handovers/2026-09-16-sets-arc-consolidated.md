# Handoff: the finite-sets arc — verdicts, models, and relations all landed

**Date:** 2026-09-16
**Landed by:** the sets arc, sessions of 2026-09-15/16 (commits `bced380b`,
`d4b72e2c`, `d832b82e`, `2540544a`, `1d46dfef`, `6ee0a8d8`, `4ade3b1e`,
`e27ec315` (the membership-congruence arc: four false-`sat` doors
closed, the join's value prints),
plus their doc commits)
**Predecessors:** `docs/handovers/2026-09-15-sets-cardinality-landed.md`
(the cardinality arc; its open chores are all closed), and
`docs/handovers/2026-09-15-sets-model-synthesis-landed.md` (this arc's
running log — the updates there are the detailed history; this file is the
consolidated state).

## Where things stand

The finite-set theory now covers **verdicts, models and relations**:

- **SMT-LIB surface**: `(Set X)` sorts; `set.union/inter/minus/member/
  subset/singleton/insert/card/complement/choose/is_empty/is_singleton`;
  `(as set.empty …)` / `(as set.universe …)`; Z3-classic bare aliases.
  Tuples: `(_ Tuple A B)` / `(Tuple A B)` / `(Relation A B)` sorts,
  `(tuple e…)`, `tuple.unit`, `(_ tuple.select i)`,
  `(_ tuple.update i t v)` with CVC5's bounds/type checks. Relations:
  `rel.join`, `rel.product`, `rel.transpose`, `rel.iden` with boundary
  validation and CVC5's unary-join rule.
- **Decision procedure**: `nixie-solver/src/solver/set_theory/` — the
  eager membership reduction plus the Venn-region/slack cardinality
  encoding, extended with the four relation operators (reference: CVC5's
  `theory_sets_rels.cpp`; `(A,B) ⨝ (B,C) : (A,C)` — the middle column is
  dropped). The join's witness splits are derived **before** cardinality
  so a final assert's split is counted in the same pass.
- **Models**: `nixie-solver/src/solver/set_model.rs` — synthesis verified
  before published (any definite mismatch rolls the sort back to the
  honest default). `SetView` is the one shared read-only evaluator behind
  `get-value`/`get-model` folding and the model-verification soundness
  gate. Sets print their values (`S = {1, 0, 2}`), tuples print as
  tuples, and rel compounds (transpose/product/iden) fold.
- **Tests**: 121/121 across five files — `finite_sets_cardinality` (40),
  `finite_sets_decision` (37), `finite_sets_sort_and_terms` (9),
  `finite_sets_model` (10), `finite_sets_relations` (25). Nothing
  ignored. Core lib 1820/1820, solver lib 450/450, clippy/fmt clean.
- **Parity**: re-run after every solving change; always 176 correct /
  1 inconclusive / 0 mismatch, z3 4.16.0, byte-identical to the tracked
  record (the corpus has no set problems).

## The soundness bugs found and closed on the way

Each of these answered `sat` (or printed a wrong model) before its fix;
each has a regression:

0. **Membership congruence was never stated for component-decided
   element equality** (`e27ec315`): `mk_eq` unfolds tuple-constructor
   equality componentwise (injectivity as a builder rewrite), so two
   ctor-spelled tuples never carry a syntactic `Eq` — their equality is
   decided at the *component* level — and SAT could commit the component
   equalities beside disagreeing membership atoms. Four doors, all
   answered `sat` (cvc5 1.3.4: `unsat` on every one): the join skolem
   middle pinned by an exact singleton; a user's `x = 3` at the join; a
   syntactic `t = (1,x)` at the join (congruence was opaque-sets-only,
   and a join's membership is forward-defined so base congruence does
   not propagate); and a join of two literal singletons (the
   `any_opaque` gate skipped the whole congruence block). Closed by the
   constructor-pair congruence pass in `set_theory::reduce` (antecedent
   = the componentwise conjunction, i.e. the dual of the injectivity
   rewrite), stated at opaque sets **and joins**, gated on needing
   either, filtered to pairs whose leaf equalities are committable
   (both sides in one group of the equality-adjacency closure — the
   closure is extended at the END of `reduce` because the singleton's
   `e ∈ {t} ↔ e = t` folds its own axiom to `true` in the builder: the
   surviving `Eq` nodes live inside the witness axioms), vacuous pairs
   skipped, fully-constant spellings first, budget 1024 with overflow
   raising `incomplete`. Regressions:
   `join_split_skolem_pinned_by_singleton_is_congruent`,
   `join_component_equality_is_congruent`,
   `join_syntactic_tuple_equality_is_congruent`,
   `join_of_literals_needs_congruence_too`, plus the mirrors
   `join_compose_syntactic_glue_still_refutes` (baseline behavior) and
   `join_component_equality_congruence_is_not_overconstrained`
   (asserts *not* `Unsat`; the shape honestly answers `Unknown` — the
   compose feedback crosses the pair budget).
1. **Equality never bound cardinality or choose** (`bced380b`): six
   false-sat classes (`S = T ∧ |S| = 5 ∧ |T| = 3`, `S = ∅ ∧ |S| ≥ 1`,
   EUF-derived `x = y` across `f x`/`f y`, asserted compound equality,
   `S = T ∧ choose(S) ≠ choose(T)`, the ite-choose identity). Fixed by
   mirroring Z3's `theory_finite_set_size::add_eq_axioms`.
2. **The join split was never counted** (`4ade3b1e`): the splits were
   pushed into the element lists keyed by `element_sort(derived)` — a
   *set's* element sort, `None` for a tuple — so the push silently never
   happened, and `(a,c) ∈ r ⨝ s` with both operands exactly pinned to a
   non-connecting pair answered `sat`. Key on the term's own sort, in a
   pre-pass before cardinality.
3. **`join_arities` returned decremented lengths** used as full ones
   (`4ade3b1e`): binary ⨝ binary built `(k)` and `(k,1,3)` — cross-sort
   elements no faithful model could value.
4. **The join's slack was unbounded above** (`2540544a`): `|r ⨝ s| = 2`
   with `|r| = |s| = 1` answered `sat`. Closed by `|r ⨝ s| ≤ |r|·|s|`.
5. **Two witnesses per disequality** (`6ee0a8d8`): the implicit pair
   direction flipped with survey order, minting `@set_ext_a_b` beside
   `@set_ext_b_a` with opposite xor orientations. Pairs are canonical
   now; tuple surjectivity axioms (`e = (sel₁ e, …, selₙ e)`) tie
   selector rebuilds to their elements; tuple ctor equality unfolds
   componentwise in `mk_eq` (injectivity as a builder rewrite).
6. **Counting-guard equalities escaped congruence for one pass**
   (`bced380b`): a same-pass re-survey closes the window.

## Open chores (none blocking)

1. ~~**The join's own `get-value` display still declines honestly**~~ —
   **CLOSED by `e27ec315`** (and the two residual layers closed by
   `518a3373`: the self-referential-pin fix and query-side composition —
   a query-only `(rel.join r s)` the assertions never mention now folds
   under `get-value` from the operands' verified values, as do
   transpose/product/iden; regressions
   `query_only_join_value_folds`, `query_only_transpose_and_product_fold`,
   `tuple_variable_member_model_prints`): the operand models print *and the join's own
   value folds* (`join_value_declines_honestly_today` was replaced by
   `join_value_prints`). The mechanism was model-side, not the datatype
   reconstruction the previous update suspected: the sweep's in-loop
   skolem mint freed the stale arithmetic default from the tuple-level
   `used` set — but that default can coincide with a genuine constant
   (`k = 2` where `(2,3)` is an element`), so the mint returned exactly
   that value back and the collision repair declined the whole sort.
   Every unpinned join skolem is now pre-minted against a
   **component-level** used set (seeded with every leaf of every resolved
   value) before the tuple sweep; a shared `minted` set guards the
   sweep's own branch against overwriting a pre-minted witness. The
   residual honest decline: SAT may commit disagreeing memberships for
   two *value-equal spellings* the compose rule never paired (a glued
   selector-spelling vs the folded constant tuple) — the rel synthesis
   rolls the join's entry back and `get-value` echoes; nothing wrong is
   ever printed. Closing that needs value-level closure in the compose
   pairing (pair by resolved value, not by term) — roadmap item 3.
2. **Known honest declines**, all documented in the roadmap below.

## Roadmap (value order)

1. **Bags** — **slice one landed** (`bedae910`): the SMT-LIB surface
   (`(Bag T)`, `(bag e n)`, `bag.union_max`/`union_disjoint`/`inter_min`/
   `difference_subtract`/`difference_remove`/`member`/`subbag`/`count`/
   `card`/`setof`, `(as bag.empty …)`), the twelve TermKinds, and the
   count reduction (every constraint → arithmetic over `bag.count`;
   extensional equality with `@bag_ext_*` witnesses; cardinality with a
   slack for *opaque* bags only — closed compounds get the exact sum, a
   differential-testing false-`sat` closed in flight). Verified against
   CVC5 1.3.4 on a 45-case battery (43 exact, 2 cvc5-timeouts refuted
   by one line of arithmetic). **Next slices**: bag-value model
   synthesis (a variable prints the `(as bag.empty …)` default today;
   assemble `bag.union_disjoint` of `(bag e n)` from the counts' values
   — the sets arc's model arc, step for step), `bag.count` query
   readback (the count terms are arith leaves the extractor doesn't
   read), then `bag.choose`/`bag.map`/`bag.filter`/`bag.fold`/… (honest
   parse-level rejections today).
2. **Synthesis reach**: intersection shapes beyond binary unions of
   opaque classes; uninterpreted element sorts (no mintable witness);
   complements over large finite sorts (> 1024, `MAX_UNIVERSE_ENUM`);
   pure product cardinality (a linear `|a×b|` via pairwise guards, or
   Z3-style unique values — currently the nonlinear rule gates to
   honest `unknown`).
3. **Value-level closure for the compose pairing** (the residual join
   display decline, see open chores): pair compose operands by resolved
   *value*, not by term, so two spellings of one tuple compose once and
   the committed atoms cannot disagree across them. The same machinery
   (a value-indexed operand map) would shrink the split/compose
   feedback population that `MAX_DERIVED_ELEMENTS = 24` currently caps
   — the cap degrades cross-pass growth honestly (`Unknown`) but the
   CVC5-shaped fix is lazy composition over member representatives
   (`computeMembersForBinOpRel`), not a budget.
4. **Remaining rel surface**: `rel.tclosure` (fixpoint or bounded
   unrolling), `rel.join_image`, `rel.group`, `rel.project`,
   `rel.table_join` — honest parse-level rejections today.
5. **Caps re-measurement** (`MAX_CONE_SETS=40`, `MAX_COUNT_ELEMENTS=24`,
   `MAX_JOIN_PAIRS=512`, `MAX_CONGRUENCE_PAIRS=1024`,
   `MAX_DERIVED_ELEMENTS=24`): the congruence web is now load-bearing —
   adversarial sat shapes with cardinality+join cost ~2.5× more search
   (10.2s → 25.1s on `join_witnesses_freely`'s second script; the
   satisfiable singleton+join mirror answers honest `Unknown` in ~6.5s
   where the pre-congruence build said `Sat` in ~5s). Measure against
   the TLA+ corpus once it runs green end-to-end (currently blocked on
   the wisas/recfun work, see other agents' handovers).

## Environment notes

- `precompile/` entries for this arc: `bced380b`, `d4b72e2c`,
  `d832b82e`, `2540544a`, `1d46dfef`, `6ee0a8d8`, `4ade3b1e`,
  `e27ec315`.
- Build with `CARGO_INCREMENTAL=0` (the handover's standing advice — a
  forgotten run left 5.5 GiB of incremental cache inside a 40 GiB
  debuginfo target) and keep big `CARGO_TARGET_DIR`s on `/media/data`,
  not `/tmp` (a full `--all-features` workspace test build measured
  132 GiB; `/` hit 100% and the linker died with SIGBUS mid-gate).
- Parallel agents are active (wisas/simplex, mbqi/constructor-tables,
  arithmetic arc). Before committing: `git reset -q`, stage only your
  files, `git status` twice; never stash.
- The shared disk hovers ~91%; prune `target/debug/deps` large stale
  artifacts before big builds and use `CARGO_INCREMENTAL=0`.
- Five workspace test timeouts (scope_rebase ×4, bv differential ×1)
  are pre-existing and owned by other agents — verified at the parent
  commits; don't chase them from a sets change.
- `Model::eval` folds `=` but not order comparisons (`>=`, `>`) over
  any theory — pre-existing general gap, noted in the roadmap of the
  model-synthesis handover; a cheap constant-folding arm fixes it for
  everyone.
