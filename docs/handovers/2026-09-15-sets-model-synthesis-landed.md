# Handoff: set model synthesis landed — next steps, open chores

**Date:** 2026-09-15
**Landed by:** the model-synthesis arc (commits `bced380b`, `d4b72e2c`, `d832b82e`)
**Predecessor:** `docs/handovers/2026-09-15-sets-cardinality-landed.md`
(whose open chores are now closed — see *Chores* below; its roadmap items 1
is done, 2–4 remain).

## What landed

### 1. A soundness fix first (`bced380b`)

While scoping the model work, six **false-`sat`** classes surfaced: the
cardinality encoding related the *memberships* of equal sets (the pair
machinery) but never their *sizes* or their `choose` applications. All of
these answered `sat` and are `unsat`:

```text
S = T  ∧  |S| = 5  ∧  |T| = 3        equal sets, unequal sizes
S = ∅  ∧  |S| ≥ 1                   constructor operand
x = y  ∧  |f x| = 5  ∧  |f y| = 3    EUF-derived equality (implicit pair)
S = {1} ∪ {2}  ∧  |S| = 5            asserted equality to a compound
S = T  ∧  choose(S) ≠ choose(T)      choose is a function symbol
c ∧ choose(ite c A B) ≠ choose(A)    the ite identity is never an atom
```

Fixes mirror Z3's `theory_finite_set_size::add_eq_axioms`: `a = b →
card(a) = card(b)` for every equality relation with both sides in the cone
(asserted equalities **and** implicit pairs — the cone's neighbour walk now
follows implicit pairs too), `a = b → choose(a) = choose(b)` over the
surveyed choose-term pairs, and `choose(ite c a b) = ite c (choose a)
(choose b)`. Eight regressions in `finite_sets_cardinality.rs`.

Also in that commit: the counting equations' de-duplication guards mint
element equalities one pass before the congruence block could see them;
the new same-pass re-survey closes that window (SAT could commit `k = 5`
while `k ∈ S` and `5 ∉ S` coexist — an unfaithful-model shape).

### 2. Set model synthesis (`d4b72e2c`, `d832b82e`)

Roadmap item 1: verdicts were correct but set-sorted variables printed the
factory default. New module `nixie-solver/src/solver/set_model.rs`:

- **Synthesis** (`Solver::extract_set_model`, called last in
  `build_model`): ground members read from the committed membership atoms;
  cardinality targets read from the arithmetic solver (directly, from the
  model entry, or through the `$p*` purification proxy — `set.card` is a
  foreign numeric leaf, see `purify_arith::PurifyState::proxy_of`);
  fresh elements minted per **equality class** of set terms (committed
  equality atoms + mutual subsets), propagated along committed subset
  edges; an intersection-sharing repair swaps private pool elements when
  a compound's target demands overlap (`|S|=|T|=2, |S∪T|=3` shares one).
  Elements the model left unconstrained are minted distinct, with a
  collision-repair pass (the arith pass defaults every free integer to 0;
  two defaulted-equal elements with disagreeing memberships are re-minted
  where unconstrained — if both values were pinned, the congruence axioms
  would have forced agreement, so disagreement proves a pure default).
- **Verified before published**: every cardinality target, committed
  equality/subset/membership atom and choose axiom is re-checked against
  the synthesized values; any definite mismatch rolls the whole sort back
  to unassigned (the honest pre-synthesis non-answer).
- **`SetView`**, the shared read-only evaluator used by both
  `Model::eval` (`get-value`/`get-model` folding — `set.member`/
  `set.card`/`set.subset`/`set.choose` fold to constants, set terms fold
  to canonical `set.union`-of-`set.singleton` values) and the
  model-verification soundness gate (now set-aware: set-sorted equality
  is extensional over values; the gate stays fail-open on `Undetermined`,
  so a declined synthesis changes nothing).
- Ten regressions in `nixie-solver/tests/finite_sets_model.rs`; 96/96
  across the four set test files.

Example: `|S| = 3 ∧ 1 ∈ S` now answers `sat` with
`S = (set.union (set.union (set.singleton 1) (set.singleton 0)) (set.singleton 2))`
and `(get-value ((set.card S)))` folds to `3`.

## Chores from the predecessor (all closed)

1. **Parity re-run** after `0682a6ed`/`8dbf0908`: done, z3 4.16.0 —
   176 correct / 1 inconclusive / 0 mismatch, byte-identical to the
   tracked `results.linux-x86_64.json` (no movement; the corpus has no
   set problems).
2. **`precompile/0682a6ed/`**: populated (worktree build, worktree
   deleted). `precompile/d4b72e2c/` holds the synthesis-arc binary.
3. **Workspace-wide `--all-features` suite**: run recorded in this arc
   (see the run log of 2026-09-15); known environment caveats below.
4. **nixie-math clippy failures**: fixed (dead stores and an unused
   closure in `ff_gb_scale_regression.rs` /
   `monomial_order_regressions.rs`, semantics unchanged).

## Environment notes

- Five test timeouts observed under load (4× `scope_rebase_tests`, 1×
  `bv_odd_width_blast_differential::odd_width_identity_pairs_hold`) are
  **pre-existing at `bced380b`** (verified in a throwaway worktree) and
  being repaired by a parallel agent (`/tmp/wt-repair` was actively
  running them). Machine load was 20–39 on 20 cores from parallel agents.
- `Model::eval` folds `=` but not order comparisons (`>=`, `>`) over any
  theory — `(>= x 3)` echoes for a pure integer `x` too. Pre-existing,
  general (not set-specific); a cheap constant-folding arm would fix it
  for everyone.

## Update 2026-09-15 (later): relations landed (`2540544a`)

Roadmap item 1 of the list below is **done**. Tuples are structural
single-constructor datatypes (`(_ Tuple A B)`, `(Tuple A B)`,
`(Relation A B)` sugar; `(tuple ...)`, `tuple.unit`,
`(_ tuple.select i)`, `(_ tuple.update i t v)`), and the four
`rel.*` operators reduce through the eager membership scheme
(`set_theory/mod.rs`; reference CVC5 `theory_sets_rels.cpp`):

- `t ∈ transpose(r) ⇔ rev(t) ∈ r` — `mk_tuple_select` folds over
  constructors, so `rev((1,2))` is the literal `(2,1)`.
- `(t,u) ∈ a×b ⇔ t ∈ a ∧ u ∈ b` — projections join the operands'
  element lists in the same pass (a pre-pass feeds derived elements
  before the definition loop).
- `(a,b) ∈ iden(s) ⇔ a ∈ s ∧ a = b`.
- Join: split (skolem per (element, join), like the disequality
  witnesses) + compose over ground pairs, capped at 512 with the
  honesty gate. Column arithmetic per CVC5's type rule:
  `(A,B) ⨝ (B,C) : (A,C)` — the middle column is dropped.
- Cardinality: `|transpose r| = |r|`, `|iden s| = |s|`,
  `|a×b| = |a|·|b|` (only when the product's support is not exact),
  and **`|r⨝s| ≤ |r|·|s|`** — the bound closed a false-`sat` class
  (`|J| = 2` with `|r| = |s| = 1` answered `sat`; `J` is determined).

Parity re-run after the change: z3 4.16.0, 176 correct / 1
inconclusive / 0 mismatch — byte-identical to the record (the corpus
has no relation problems). Known honest declines: pure product
cardinality over unconfined operands (nonlinear gate), rel compounds in
`get-value` echo (opaque relation variables synthesize fully —
`r = {(1,2), (3,4)}` prints as tuples). `precompile/2540544a/` cached.
A debug-only false alarm in the datatype model verifier was fixed
(tuples over Int/Bool are outside the pure-datatype fragment).

## Update 2026-09-15 (evening): rel compounds synthesize (`1d46dfef`)

The synthesis-reach item's rel half is done: transpose/product/iden
values now print and fold (`SetView` reads rel compounds through their
installed entries — one source of truth for `get-value`, the gate, and
nested reads); a cross-sort pass computes them after every sort's
opaque values land, verified against their cardinality targets with
rel-only rollback. Tuple-element component resolution makes committed
members like the join split `(1, k)` read as the constructor over
resolved (or freshly minted) components — both splits resolve through
the one skolem entry, so the middles meet. A card target on a rel
compound no longer rolls the operand's model back. The collision repair
learned that an undecided atom is not a conflict and that a *refuted*
counting guard pins nothing.

Still declining, pinned by a test: a **join's own value** echoes when
its split elements collide pinned-against-pinned through a shared
skolem (verdicts and operand models unaffected). Parity re-run:
176/1/0, z3 4.16.0, byte-identical. `precompile/1d46dfef/` cached.

## Update 2026-09-15 (night): witness canonicity + tuple surjectivity (`6ee0a8d8`)

Chasing the join's model decline three defects deep, each fixed at its
layer:

- **One witness per disequality**: the implicit opaque pairs are
  canonically ordered — the survey's discovery order flips as assertions
  accumulate, and a flipped pass minted a *second* witness
  (`@set_ext_a_b` beside `@set_ext_b_a`) with the opposite xor
  orientation. One unordered pair, one witness, stable across re-runs.
- **Tuple surjectivity**: every tuple-sorted element equals its selector
  rebuild — the constructor-surjectivity axiom the internally-declared
  tuple sorts never get from `declare-datatype`.
- **Skolem-faithful values**: the reduction's own existentials override
  their defaults (arith's zero, the datatype canonical tuple — which
  sometimes carries the wrong arity, now caught by sort-sanity gates
  that decline instead of printing an ill-sorted value) with fresh
  distinct witnesses, unless a committed-true equality pins them.

The join's own value still declines (the datatype default machinery's
wrong-arity constructors for tuple sorts are the next layer — see the
`tuple 7` in a binary relation from the debug trail); verdicts and all
other rel values unaffected. Two model tests were pinned against
witness-side drift (the xor satisfies on either side freely). Parity
re-run: 176/1/0, z3 4.16.0, byte-identical. `precompile/6ee0a8d8/`
cached.

## Roadmap (updated, value order)

1. **Bags**: `bag.count` pointwise identities; the cone/slack skeleton
   carries over with region *multiplicities*. Surface names: cvc5
   `smt2_state.cpp`. AST needs `SortKind::Bag(SortId)` plus ~10
   TermKinds.
2. **Synthesis reach**: the remaining honest declines are intersection
   shapes beyond binary unions of opaque classes (nested compounds with
   overlap targets), sets over uninterpreted element sorts (no mintable
   witness), complements over large finite sorts (> 1024 elements,
   `MAX_UNIVERSE_ENUM`), the join's own value (next layer: the datatype
   reconstruction defaults tuple-sorted vars with wrong-arity
   constructors — fix the default to respect the sort's own constructor),
   and pure product cardinality (a linear encoding of `|a×b|` via
   pairwise guards). Each extends naturally from the class/swap
   machinery in `set_model.rs`.
3. **Remaining rel surface**: `rel.tclosure` (needs a fixpoint or a
   bounded-unrolling scheme), `rel.join_image`, `rel.group`,
   `rel.project`, `rel.table_join` — all currently honest parse-level
   unknowns/rejections.
4. **Caps re-measurement** (`MAX_CONE_SETS=40`, `MAX_COUNT_ELEMENTS=24`,
   `MAX_JOIN_PAIRS=512`): once the TLA+ corpus runs green end-to-end,
   measure and tune.
