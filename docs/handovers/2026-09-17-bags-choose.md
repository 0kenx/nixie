# Handoff: the bags arc, part two — choose lands, two false-`sat` families closed under it, subbag queries fold

**Date:** 2026-09-17
**Landed by:** the bags arc continuation, session of 2026-09-17 (commits
`fd1f0595`, `d6940136`, `0e31151d`; binaries cached under
`precompile/<sha>/`)
**Predecessor:** `docs/handovers/2026-09-16-bags-arc.md` (its open
chores 1 and 3 are what this session executed; its roadmap for
`bag.map`/`filter`/`fold` remains open).

## Where things stand

The bags fragment now has **`bag.choose`** end to end — surface, builder
normalizations (CVC5's `CHOOSE_BAG_MAKE` fold), the member/congruence/
ite-unfolding axioms, count-driven model values for asserted chooses,
and query completion for query-only ones — plus **query-only
`bag.subbag` folding** from installed values. Along the way the session
found and closed **two pre-existing false-`sat` families** in the landed
reduction (they predate choose; probes on the pre-choose binary
`precompile/5c8bf7a8` reproduce them).

- **The ite hole** (`fd1f0595`): a bag-shaped `(ite c a b)` fell through
  `count_definition`'s catch-all to the *opaque* treatment — free
  nonnegative counts on a bag whose value the term determines.
  `x ≤ 0 ∧ count(1, ite(x>0, (1:2), (2:2))) = 1` answered `sat`
  (CVC5: `unsat`). Now `count(e, ite(c,a,b)) = ite(c, count(e,a),
  count(e,b))`, an ite over closed bags is *closed* (support walk +
  `bag_is_closed`), `|ite(c,a,b)| = ite(c,|a|,|b|)` exactly (the slack
  side had the same hole over opaque branches), and the catch-all was
  split: only `Var`/`Apply`/`Select` are opaque — anything else raises
  the honesty gate instead of trusting free counts.
- **The derived-equality congruence hole** (`fd1f0595`): `bag.count` and
  `bag.card` are functions of the bag *value*, but the purified encoding
  gives each term its own integer column with no tie across equalities
  the formula never wrote. `x = 0 ∧ count(1, f x) = 2 ∧ count(1, f 0) = 5`
  answered `sat` (EUF congruence `f x = f 0` never reached the columns);
  likewise `select`-over-`store` bags and cardinality through the slack.
  Fixed with a bag-pair congruence pass: `a = b → count(e,a) = count(e,b)`
  per element plus `a = b → |a| = |b|`, over opaque×opaque and
  opaque×constructor pairs only (the set theory's `implicit_pairs`
  eligibility — see the perf notes for why the filter is load-bearing).

## The choose slice (`d6940136`) — the decisions that matter

- **The member axiom is hybrid.** With a `bag.card` term already
  surveyed for `b`: the set theory's shape `count(choose(b),b) ≥ 1 ↔
  |b| ≥ 1` (this is what makes `|b| ≥ 1 ∧ count(choose(b),b) = 0`
  refute through the formula's own card). Without one: CVC5's
  disjunction `b = ∅ ∨ count ≥ 1` over the *equality atom* — **never a
  minted `bag.card`**. A card minted by the choose axiom joins the
  conjoined axioms, the model pass surveys it, and its barely-
  constrained slack column rolls perfectly good bags back to `∅`
  (`count(3,b) = 2 ∧ choose(b) = 3` printed `b = ∅` — fuzz-found). The
  minted emptiness atom also gets its forward zero-counts stated
  in-pass, because a single-assert script has no re-survey to state
  them (the one-pass gap).
- **Choose congruence and ite** mirror the set theory: `a = b →
  choose(a) = choose(b)` over surveyed choose pairs (budget 128), and
  `choose(ite c a b) = ite c (choose a) (choose b)`.
- **Models.** Assertion-side: a choose's value is picked from its bag's
  cells — *committed equalities first* (`committed_bool_model`, now
  `pub(super)`), else the first cell whose multiplicity equals the count
  column (the count **is** the multiplicity of the chosen value), else a
  fresh non-cell integer when the count is 0; a verification pass
  reconciles each pick against the installed cells and rolls the sort
  back on mismatch. Query-side: a query-only choose completes from the
  installed value before the count/member folds read it — CVC5 echoes
  these; we answer with a member and its multiplicity.
- **The minted-atom feedback loop is closed at the source.** The
  reduction's own equality atoms (pair congruence, choose emptiness) are
  re-surveyed by the next `assert` (axioms are conjoined onto the
  assertion), and each became an extensionality *witness* — the element
  list ballooned, and three-assert fuzz shapes went from instant to
  unfinishable. `Solver::bag_minted_eq_atoms` (persisted across asserts;
  pop-safe because entries only ever suppress and user-written
  re-assertions are exempt via `bag_user_eq_atoms`, collected from
  `certificate_assertions`) refuses them witnesses. With it, the
  union-rearrangement regression dropped 15s → 2.7s.
- **Differential result:** 10 hand shapes + 450 fuzz seeds vs CVC5
  1.3.4, **0 wrong verdicts**. 13/450 nixie timeouts on adversarial
  depth-2 random shapes (below).

## Subbag queries (`0e31151d`)

`(get-value ((bag.subbag A B)))` folds pointwise-≤ from installed
values; a side with no model entry folds when it is a closed ground
chain (`(bag 1 2)` is never installed — its value is itself) through a
shared `bag_cells_of_term` walker. `(bag.subbag b b)` folds to `true`
at parse, so that query prints `(true true)`.

## Open chores (in value order)

1. **`bag.map` / `bag.filter` / `bag.fold`** — unchanged from the
   predecessor handover; `define-fun`-ground substitution first, CVC5's
   `bag_solver.cpp` for the UF story.
2. **Choose/count perf on deep shapes** — the eager reduction emits
   933 axioms on a *three-assert* random formula (seed 25 of the
   campaign); 13/450 fuzz shapes take 34–90s where CVC5 needs <30s
   (honest answers, zero wrong verdicts). The cost is choose elements
   joining every identity/congruence product. First ideas if the corpus
   ever grows bags: skip count identities for choose elements over
   closed compounds whose support can't contain them; state element-pair
   congruence only over equality-connected elements (the set theory's
   `connected` walk); consider lazy choose axioms CVC5-style.
3. **`(assert x)` with non-Bool `x` answers `sat`** — pre-existing,
   found while testing (`(assert (bag.choose b))` degrades honestly to
   `unknown` via the encoder's gate, but a bare Int variable asserts as
   if Bool). CVC5 rejects at parse. The parser's `assert` should demand
   Bool — small fix, wrong owner to do it blind; whoever owns the
   parser surface should take it.
4. **`MAX_BAG_ELEMENTS = 24` / `MAX_BAG_PAIRS = 128` re-measurement**
   with the set caps, once the TLA+ corpus runs green.

## Environment notes

- **The disk filled to 100% twice again.** A `--all-features` workspace
  *test* build in a worktree reached **128 GiB** of target dir (debug +
  doc-tests + every feature × test targets). One worktree target +
  the primary's is more than the disk has. Build worktrees with
  `CARGO_TARGET_DIR` on `/media/data`, watch `df`, and delete the
  worktree the moment it stops being needed.
- **Corpus tests cannot run in worktrees**: `satcomp2024`/`smt-lib`/
  `satlib` are gitignored external data that exists only in the primary
  checkout — a worktree run reports ~60 `[corpus-missing]` failures
  that look like a regression and are not. Run the full suite in the
  primary.
- The session rode out two mid-edit states of the sat agent's
  `nixie-sat/src/solver/mod.rs` (their `EquivScratch` work) by building
  in a worktree at `main` and syncing back — the sanctioned move when
  the shared tree is transiently uncompilable.
- Fuzz harness for the choose fragment: `/tmp/bag_choose_fuzz.py`
  (regenerate from the predecessor's description: elements 0–3 + `x`,
  multiplicities −1..3, depth-2 bags, 2–4 asserts over
  count/member/subbag/equality/card/choose atoms, choose atoms in
  element position too). CVC5 1.3.4 at the usual nix store path; its
  timeouts on unknown-support card shapes are not counterexamples.
