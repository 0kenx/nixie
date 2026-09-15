# Handoff: the finite-sets arc — verdicts, models, and relations all landed

**Date:** 2026-09-16
**Landed by:** the sets arc, sessions of 2026-09-15/16 (commits `bced380b`,
`d4b72e2c`, `d832b82e`, `2540544a`, `1d46dfef`, `6ee0a8d8`, `4ade3b1e`,
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

1. **The join's own `get-value` display still declines honestly**
   (pinned by `join_value_declines_honestly_today`, which flips loudly
   when fixed). The named next layer: the datatype reconstruction
   defaults tuple-sorted variables with constructors of the **wrong
   arity** (`(tuple 7)` inside a binary relation). The sort-sanity gates
   in `set_model.rs` contain it — nothing wrong is ever printed — but
   the display declines instead of synthesizing. Start in
   `model_builder.rs`'s datatype reconstruction (`ground_default_term`
   resolves the constructor correctly; the wrong-arity value comes from
   a different defaulting path — the debug trail in the 2026-09-16
   update of the predecessor handover has the exact terms).
2. **Known honest declines**, all documented in the roadmap below.

## Roadmap (value order)

1. **Bags**: `bag.count` pointwise identities; the cone/slack skeleton
   carries over with region *multiplicities*. Surface names: cvc5
   `smt2_state.cpp` (`bag.union_max`, `bag.difference_subtract`, …).
   AST needs `SortKind::Bag(SortId)` plus ~10 TermKinds — the compiler
   finds every exhaustive match, as it did for relations (~15 sites in
   core, ~10 in solver).
2. **Synthesis reach**: intersection shapes beyond binary unions of
   opaque classes; uninterpreted element sorts (no mintable witness);
   complements over large finite sorts (> 1024, `MAX_UNIVERSE_ENUM`);
   pure product cardinality (a linear `|a×b|` via pairwise guards, or
   Z3-style unique values — currently the nonlinear rule gates to
   honest `unknown`).
3. **Remaining rel surface**: `rel.tclosure` (fixpoint or bounded
   unrolling), `rel.join_image`, `rel.group`, `rel.project`,
   `rel.table_join` — honest parse-level rejections today.
4. **Caps re-measurement** (`MAX_CONE_SETS=40`, `MAX_COUNT_ELEMENTS=24`,
   `MAX_JOIN_PAIRS=512`): the join splits add elements to the counting
   lists, so the 24 cap gates more join problems than before — measure
   against the TLA+ corpus once it runs green end-to-end (currently
   blocked on the wisas/recfun work, see other agents' handovers).

## Environment notes

- `precompile/` entries for this arc: `bced380b`, `d4b72e2c`,
  `d832b82e`, `2540544a`, `1d46dfef`, `6ee0a8d8`, `4ade3b1e`.
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
