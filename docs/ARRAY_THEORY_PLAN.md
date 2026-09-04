# Incremental array theory – staged plan

## Goal

Replace the **round-based lazy array-axiom instantiation** in `nixie-solver/.../array_axioms.rs`
(collect structure ⇒ emit ground lemmas ⇒ `rebase_theory_state` + rebuild `TheoryManager` ⇒
`solve_with_theory` again from root, one or more times per `check`) with an **event-driven,
incremental array theory** integrated into the CDCL(T) loop, in the shape of Z3's
`theory_array_full`.

## Why

Profiling (`nixie-solver/.../mod.rs`, the array-refinement round) showed the per-round reset is
~1 µs and the per-round search restart is *warm* (`backtrack_to_root` leaves the SAT solver's
`phase` array intact). The cost of a deep `storecomm`/`swap` goal is therefore **the CDCL search
itself** over the atoms the lazy instantiator materialises (a depth-N store chain unfolds into
~N intermediate `select` atoms). An incremental theory reasons about reads/writes in a persistent
structure and propagates consequences on EUF events, so those atoms are never created – the
search space shrinks. Z3 solves the same goals in ~0.05 s.

Z3's `theory_array_full` is **itself axiom-instantiation-based**, but the instantiation is
*event-driven* (`merge_eh` when two array enodes merge, `relevant_eh` when a term becomes
relevant) and the lemmas are added *incrementally* (the SAT search continues, it does not
restart from root). That is the target shape.

## Reference

- `../temp/z3/src/smt/theory_array_full.{h,cpp}` – `internalize_term` (register store/select),
  `merge_eh(v1,v2)` (two arrays became equal ⇒ instantiate extensionality + congruence),
  `relevant_eh` (term became relevant ⇒ instantiate read-over-write), `instantiate_select_map_axiom`
  (the read-over-write axiom), `instantiate_default_*_axiom` (extensionality witnesses).
- `../temp/cvc5/src/theory/arrays/` – `array_info`, `inference_manager`, the persistent
  read/write tracking.

## Architecture (target)

An array theory owns, scoped by `push`/`pop`:
- the set of `store(base, idx, val)` terms and `select(array, idx)` terms internalised so far;
- for each array term, the writes applied to it (a parent/child map);
- the set of asserted array equalities/disequalities.

It reacts to two events from the TheoryManager:
- **EUF merge of two array-sorted terms** (Z3 `merge_eh`): if `a` and `b` merge, force
  `select(a, k) = select(b, k)` for every read index `k` on either, and (for a disequality
  `a ≠ b`) introduce an extensionality witness. This is *congruence + extensionality*, fired
  the moment the merge happens – not collected-and-re-solved.
- **Relevance of a `select`/`store`** (Z3 `relevant_eh`): instantiate the read-over-write axiom
  `select(store(base, idx, val), j) = ite(idx = j, val, select(base, j))` for that term, once.

Conflicts (e.g. a `select(store(a,i,v), i)` forced to differ from `v`) are reported as theory
conflict clauses during `final_check`/propagation, blocking the candidate model **inline**, so
no `rebase` + re-solve round is needed.

## Stages

Each stage is independently sound, tested (parity + the 115-case false-SAT set + the 6 cvc
cases), and committed on its own.

### Stage 1 – array term bookkeeping in TheoryManager (foundation, no behaviour change)

Register every internalised `store`/`select` term in an `ArrayState` on the TheoryManager,
keyed by term id, scoped with the existing theory `push`/`pop`. Add helpers to enumerate
`select(store(b,i,v), j)` shapes. **Pure bookkeeping** – no new propagation, no risk; unblocks
the later stages. Verify the 9.7k-test suite + parity still pass.

### Stage 2 – read-over-write as an inline `final_check` conflict detector

In `TheoryManager::final_check`, for each internalised `select(store(b,i,v), j)` where the
candidate model's EUF already decides `i = j` or `i ≠ j`, assert (via a theory conflict if
violated) `select = v` (when `i = j`) or `select = select(b, j)` (when `i ≠ j`). This catches
array-inconsistent candidate models in one `solve_with_theory` call instead of a round-based
re-solve, for the goals it covers. Kept **additive** to the lazy instantiator (which remains
the fallback) and gated behind `has_array_ops`.

### Stage 3 – extensionality + congruence on EUF merge (`merge_eh`)

Add an EUF merge callback (or scan merges in `final_check`): when two array terms merge,
propagate `select` congruence at observed indices; when a disequality `a ≠ b` is asserted,
introduce the extensionality witness. This is what decides the `storecomm` / `array_incompleteness1`
/ `storeinv` shapes inline.

### Stage 4 – incremental lemma addition (drop the round-based re-solve)

Once stages 2–3 produce conflicts inline, the array-axiom round in `check_core` becomes
unnecessary for the cases they cover. Remove it for those cases (keep it as a fallback). This
requires the array lemmas to be added **incrementally** – `solve_with_theory` must not reset
`theory_processed` to 0 per call and the theory solvers must unwind correctly on backtrack
(the `rebase_theory_state` comment names the leaks, e.g. BV `assert_const`, that must be fixed
first). This is the stage that delivers the search-space win for the deep SAT goals.

### Stage 5 – `on_assignment` propagation (full Z3 `assign_eh` shape)

Move read-over-write from `final_check` to `on_assignment`: propagate `select(store(b,i,v), j)`
the moment `i = j` / `i ≠ j` is decided, pruning the search mid-branch. Largest perf win,
largest risk; only after stages 1–4 are stable.

## Non-goals / guards

- **Soundness first.** Every stage keeps the existing lazy instantiator as a fallback until the
  new path is proven complete on the suite; a stage that cannot prove a goal it claims falls
  back rather than guessing.
- No `z3`/`cvc5` linkage (banned in `deny.toml`); the references above are a specification only.
- BV `assert_const` scoping and any other leak named in `rebase_theory_state` must be closed
  before stage 4 trusts incremental backtracking.

## Current status

- Stages 1–5: **not started**.
- The lazy instantiator (`array_axioms.rs`) + concrete store-chain decision procedure
  (`check_array.rs`) + select-over-ite axiom remain the active array machinery and are sound
  (parity 163/0/5; 115-case false-SAT set 0 wrong; 6 cvc cases match z3).
