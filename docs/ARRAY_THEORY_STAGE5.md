# Stage 5 design – incremental, indexed array theory (Z3 `theory_array_full` shape)

Companion to `ARRAY_THEORY_PLAN.md`.  This is the design for the stage that
actually shrinks the SAT search space on deep array goals (the `storecomm` /
`swap` invalid cases that sit at 3–5 s on `main`).

## The real Z3 model (not "no atoms")

Studying `../temp/z3/src/smt/theory_array_full.{h,cpp}` corrects the framing:
Z3's array theory **does** materialise axiom instances (lemmas), but:

1. **Indexed.**  Per array variable it keeps `var_data_full { m_maps, m_consts,
   m_as_arrays, m_parent_maps }` – the stores written into it, the constants it
   is equated to, and the **parents** (selects that read it, stores that build
   on it).  Axiom instantiation is a *lookup* in these maps, not a rescan of the
   formula.
2. **Event-driven.**  Instantiation fires on `merge_eh(v1,v2)` (two arrays
   became equal ⇒ their reads/writes must be reconciled now) and
   `relevant_eh(n)` (a select/store became relevant ⇒ its read-over-write axiom
   is added once).  Not "collect everything each round".
3. **Incremental.**  Lemmas are added as the search progresses; the SAT search
   continues (it does **not** backtrack to root and re-solve).  `can_propagate`
   / `propagate` are the theory hooks the context polls.

So the lever for nixie is **not** "avoid atoms" – it is "materialise only the
*relevant* atoms, found by index, added incrementally."  The current
`array_axioms.rs` rescan + round-based re-solve materialises far more (eager
full-chain unfold) and re-solves from root each round.  Both inflate the search.

## Target architecture for nixie

A persistent `ArrayTheory` owned by the `Solver` (not rebuilt per round),
mirroring `var_data_full`:

```
struct ArrayTheory {
    // array term -> the writes applied to it (store terms), in insertion order
    maps:    FxHashMap<TermId, Vec<TermId>>,
    // array term -> the selects that read it
    parents: FxHashMap<TermId, Vec<TermId>>,
    // push/pop scope trail
    scopes:  Vec<ArrayScopeMark>,
}
```

Populated as `select`/`store` terms are internalised (Stage 1 already records
them; this indexes them by array operand).  Scoped by the theory `push`/`pop`.

It reacts through the `TheoryManager`:

- **On EUF merge of two array terms** (`merge_eh`, nixie hook = after
  `euf.merge` of array-sorted nodes): for every select `select(a, k)` with `a`
  in the merged class, assert `select(a, k) = select(b, k)` for the partner `b`,
  and instantiate read-over-write for any store now reachable through the merge.
  This is congruence + read-over-write fired at merge time.
- **On relevance of a `select`/`store`** (`relevant_eh`, nixie hook = first time
  the term's SAT var is assigned): instantiate its read-over-write axiom once.
- Conflicts (a forced `select(store(a,i,v), i)` that the model pins ≠ `v`) are
  returned as theory conflict clauses from propagation / `final_check`.

The axiom instances are added **incrementally** – `solve_with_theory` must
*resume* the search (it currently resets `theory_processed = 0` each call,
`nixie-sat/.../search_ext.rs`, which forces the theory to be re-driven from the
trail and is why the round-based reset exists).

## Prerequisites (must land first, each independently sound)

### P1 – close the BV `assert_const` scoping leak

`rebase_theory_state` (`nixie-solver/.../mod.rs`) resets `bv` wholesale every
check because `BvSolver::assert_const` pins `x = c` as a **unit clause on the
BV solver's own SAT core** (`pin_bool_var` → `sat.add_clause([lit])`,
`nixie-theories/.../bv/solver.rs:523`), and that pinning is **not** wired into
the `Solver`'s user-level `push`/`pop` – only into `BvSolver`'s internal
`context_stack`.  So a `x = 5` pinned inside one search branch can outlive a
user `pop` and refute a later `(= x 6)`.  Until the pinning is tracked on the
`Solver` trail (a `TrailOp::BvPinned { term }` undone on `pop`, matching how
`Constraint::Eq` is trail-undone), incremental backtracking cannot be trusted
and the round-based reset cannot be removed.

### P2 – make `solve_with_theory` resumable

`solve_with_theory` (`nixie-sat/.../search_ext.rs:36`) initialises
`theory_processed = 0` on every call and re-drives the whole trail through the
theory.  For incremental lemma addition it must instead **persist** the
theory cursor across calls (resume from where the last call left off), so a
lemma added between calls is processed without re-asserting the trail.  This
is the SAT↔theory interface change; it touches the soundness-critical
theory-cursor invariant (`theory_processed.min(boundary)` on backtrack) and
must be verified against the 9.7k-test suite + parity.

## Implementation order (each step sound + verified on its own)

1. **Index structure** – `ArrayTheory { maps, parents }` populated from Stage 1
   records, scoped.  Pure bookkeeping (no propagation); unblocks lookup-based
   instantiation.  *Safe, no behaviour change.*
2. **P1 – BV `assert_const` trail tracking.**  Soundness fix; close the leak so
   `rebase_theory_state`'s BV reset can later be dropped.
3. **`merge_eh` congruence** – on EUF merge of array terms, propagate select
   congruence at observed indices via the index.  Additive to the lazy
   instantiator (fallback).  First real propagation.
4. **`relevant_eh` read-over-write** – instantiate a select/store's RoW axiom
   once, on first assignment, via the index (replaces the rescan).
5. **P2 – resumable `solve_with_theory`** – persist the theory cursor; add
   array lemmas incrementally.  *This is where the round-based re-solve is
   dropped.*
6. **Drop the round-based re-solve for cases the theory now covers** – keep it
   as a fallback.  This is where the deep-chain atom bloat disappears and the
   SAT goals speed up.

Steps 1–2 are safe and session-finishable; 3–4 are additive; 5–6 are the
soundness-critical interface change and the payoff.

## Guardrails (AGENTS.md)

- Every step keeps the lazy instantiator (`array_axioms.rs`) + concrete
  store-chain check (`check_array.rs`) as a fallback until the new path is
  proven complete on parity (163/0/5) + the 115-case false-SAT set (0 wrong) +
  the 6 cvc cases.
- No `z3`/`cvc5` linkage (`deny.toml`); the references are a specification.
- The SAT↔theory cursor change (step 5) is the highest-risk piece; it ships only
  after a dedicated test pass, and reverts cleanly if any suite regresses.

## Status

- Steps 1–6: not started.  Stage 1 bookkeeping (`array_select_terms` /
  `array_store_terms`) is in place (`f1c7fb1`) and feeds step 1.
