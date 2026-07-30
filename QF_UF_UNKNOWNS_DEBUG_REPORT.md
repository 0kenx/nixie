# QF_UF explicit-`unknown`s — root cause found and fixed

Branch: working tree on top of `e0a1299`.  Clean (debug instrumentation reverted).

## Result

| | before | after |
|---|---|---|
| explicit `unknown` (z3=unsat) | **10** | **0** |
| of which → `unsat` (decisive, correct) | — | **9** |
| of which → `timeout` (honest, was spurious) | — | 1 (`PEQ/PEQ012_size6`) |
| decisive-wrong | 0 | **0** |

Validated on a 6 749-file QF_UF sample (all SEQ/QG-classification/PEQ
families + 250-file random sample, 12 s/file, vs z3 4.16):
**decisive-wrong 0, `unknown` 0.**

## Root cause

A CDCL(T) loop-invariant violation in `oxiz-sat::Solver::solve_with_theory`
(`oxiz-sat/src/solver/search_ext.rs`).

The inner theory loop handles a theory conflict by calling `learn_clause`,
which **enqueues the learned clause's asserting literal** (its propagation
reason is the new clause) but **does not itself run BCP**. The inner loop
only re-reads the trail through `theory.on_assignment` — never through the
watch lists — so the asserting literal's Boolean consequences sit unprocessed.

In the common case this is harmless: backtracking from a conflict leaves
unassigned variables, so `pick_branch_var` returns `Some`, the outer loop
iterates, and its top-of-loop `propagate` drains the pending work before
anything observes the trail.

**The bug:** when the asserting literal happens to *complete* the trail
(every variable now assigned), `pick_branch_var` returns `None` and
`final_check` runs **in the same iteration** — over a trail that still has
an unpropagated asserting literal (`prop_head < trail.len()`). A genuine
conflict hidden in that literal's watch list (e.g. an all-false original
clause it now falsifies) is missed, the theory reports `Sat`, and the
`trail_falsifies_live_clause` soundness backstop degrades the real `Unsat`
to a spurious `Unknown`. (`unknown` in 7 ms–5.9 s, all z3=unsat — exactly the
10-file signature.)

## Proof (SEQ032_size2, the 7 ms reproducer)

Tracing every trail assignment + every `propagate` step showed the final
trail of the spurious `Sat`:

```
clause 9 = [Lit(78), Lit(80), Lit(77)]   (original, correctly two-watched
                                          in watch[79] & watch[81])
  Lit(78) False  level 1  reason=Propagation(ClauseId(89))   <- theory-conflict asserting literal
  Lit(80) False  level 0  reason=Decision                   <- a learned unit
  Lit(77) False  level 0  reason=Propagation(ClauseId(32))
```

All three literals false → clause 9 is a conflict BCP must catch. The last
events before the verdict:

```
[prop] process lit=Lit(78)        <- decision at dl=2 propagated
[prop-exit] None (all processed)   <- prop_head == trail.len()
[final-check] entry prop_head=40 trail_len=41 pending=1 pend_lit=Some(Lit(79))
[final-check] Sat -> checking trail_falsifies   <- reached with 1 pending!
unknown
```

`ClauseId(89)` is a **theory-conflict learned clause**; `Lit(79)` (= ¬Lit(78),
the asserting literal) is the literal it enqueued. No `force_theory_unit` was
involved (this is not the empty-reason path), and the clause was correctly
watched — the defect is purely that `final_check` ran while the asserting
literal's watch list (`watch[79]`, which holds clause 9) was never traversed.
That traversal would have swapped the now-false watch to position 1, found no
non-false literal, and returned the conflict.

The other 9 reproducers (7× `QG-classification/qg5/gensys_*`,
`QG-classification/qg7/iso_icl_nogen_sk004`) all hit the identical path: an
original `(or (= t c0) …)` domain clause left all-false by an unpropagated
theory-conflict asserting literal.

## The fix

Restore the invariant that **decide / final-check only run at BCP fixpoint**.
After the inner theory loop, if it left pending Boolean propagation, re-enter
the outer loop so its top-of-loop `propagate` drains it first:

```rust
// BCP-fixpoint invariant before decide / final-check.
if self.trail.has_pending_propagation() {
    continue;
}
```

`has_pending_propagation()` is `O(1)` (`prop_head < trail.len()`); the
`continue` fires only in the rare full-trail-after-conflict case, so there is
no measurable search overhead. It can only *add* conflict detections (never
remove them), so it cannot introduce a wrong answer — only convert a spurious
`Sat` (→`Unknown`) into the real `Unsat`, or into continued search.

## Why not fix it inside the conflict arm?

The natural-looking fix — calling `propagate()` right after `learn_clause` in
the theory-conflict arm — re-opens conflict analysis inline and duplicates the
outer loop's conflict handling (analyze → backtrack → learn → restart). The
chosen one-line guard defers to the *existing* top-of-loop `propagate`, which
already does all of that correctly. It also covers any other future site that
might enqueue without BCP, not just the current conflict arm.

## Validation

- `SEQ032_size2` + the other 8 fast reproducers: `unknown` → **`unsat`**
  (matches z3).
- `PEQ/PEQ012_size6`: `unknown`(5.9 s) → `timeout` — oxiz now actually
  searches (the spurious-`Sat` shortcut is gone); z3 solves it in 3.1 s, so
  this is a pre-existing CDCL(T) performance gap on the PEQ/NEQ model-finding
  family, not the soundness bug. It joins the suite's ~140 honest timeouts.
- `cargo nextest run -p oxiz-sat`: **750/750 pass**.
- `cargo nextest run -p oxiz-solver`: 974 pass / 12 fail — the 12 failures are
  pre-existing WIP (strings / arrays / NIA / quantifiers / reset) and are
  **identical with and without this fix** (verified by reverting just
  `search_ext.rs`).
- 6 749-file QF_UF sample vs z3: **decisive-wrong 0**, `unknown` 0.

## Regression test

`oxiz-solver/tests/qf_uf_bcp_fixpoint_regression.rs` — runs `SEQ032_size2`
(the smallest reproducer) through `Context::execute_script` and asserts
`Unsat`. Verified to **fail without the fix** (returns `unknown`) and **pass
with it**.

## Files

- `oxiz-sat/src/solver/search_ext.rs` — the 1-line (+ comment) fix.
- `oxiz-solver/tests/qf_uf_bcp_fixpoint_regression.rs` — canary.
