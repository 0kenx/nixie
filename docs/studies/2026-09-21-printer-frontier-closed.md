# The printer frontier closed: the large nec-smt members print their residuals (2026-09-21)

**Date:** 2026-09-21. **Item:** the residual open item of the
`solve_eqs` arc — *"the five large non-foldable members hang in
`(simplify)`'s downstream substitute/printer on residuals z3 prints
fine"* (`2026-09-20-solve-eqs-guard-elimination.md`'s boundary
section).  With the fold landed and default-ON (refute-only), the
`(simplify)` command was the last surface where these members hung.

## The verdict

`(simplify …)` on every nec-smt member now **returns**: the foldable
ones to `false` (unchanged), the five large non-foldable ones to
**let-shared residuals in 0.26–4.5 s** (0.65–4.9 MB — z3's own
residuals on these are the same shape and scale), and the `sat`
member to its residual — **no hangs, no crashes, 0 wrong answers
across small+med+large** (11+1+1 folds all z3-verified `unsat`; every
other member's fold decision matches z3's).

The hang decomposed into **five stacked defects**, each found by
profiling or phase instrumentation after the previous layer cleared:

1. **The solve's interning flood** — `rw_are_equal`/`rw_are_distinct`
   probed via `mk_eq`, which INTERNS an `Eq` node per non-value probe
   (30 % `HashMap::insert` + 17 % rehash in the profile).  Fixed with
   the z3-faithful kind gate (z3's `are_equal` only decides value
   pairs; `mk_eq` stays on its constant-folding arms).
2. **The solve TREE vs the DAG** — the R5/R6 frame branch-outs
   re-descend shared sub-solves; the entry-level pair cache didn't
   cover them.  Fixed by threading the pair memo INTO the worklist
   (every intermediate `(ite, value)` pair resolved exactly once,
   manager-lifetime-valid: term ids are never reused and kinds are
   immutable — `gc` only prunes the intern table).  Plus an R7
   leaf-scan budget (8 192 nodes — R7 fires at every stalled level and
   an unbounded scan is quadratic on stalling chains).
3. **The ctx walk's native recursion** — two contracts added: the
   entry gate (input deeper than 512 — the assert path's proven
   envelope — returns unchanged) and a RECURSION budget threaded
   through the walk (the walk's depth is NOT the input's depth: the Eq
   arm's solve expands a shallow chain into a deep and/or form and
   re-enters on it; the `sat` member overflowed the main stack
   through exactly that).  Identity on exhaustion — sound degradation.
4. **`share_for_printing`'s quadratic binding loop** — each
   candidate's RHS went through `substitute`, which CLONES the growing
   `names` map per call (43 s on one member).  Fixed with
   `rebuild_children_with` (the substitution walk's exhaustive
   per-kind rebuild, factored out): a one-level child remap IS the
   full substitution under the children-first candidate order.  The
   final `text = format!("(let … {text})")` accumulation was likewise
   O(L²) — now a linear openings/body/closers assembly.
5. **THE ROOT CAUSE of the print explosion: the saturating sizes
   broke the topological order.**  `candidates.sort_by_key(size)`
   places a parent BEFORE its same-size child whenever both saturate
   at `usize::MAX` (every huge compound ties) — the child is not yet
   named when the parent's RHS is rebuilt, so the parent INLINES the
   child's whole subtree: measured **376 437 740 printed nodes** on
   one member (580 463 after the fix — 648×).  The fix is a post-order
   index tie-break (the DAG walk's Combine insertion order — a strict
   topological order).  Two supporting changes: the binding-candidate
   filter now also binds BIG single-reference compounds (tree ≥ 1 024
   — sharing alone let exponential single-ref spines explode an RHS),
   and `MAX_SHARED_BINDINGS` rose 1 000 → 100 000 (the binding count
   is DAG-linear; the old cap kept the SMALLEST candidates and dropped
   the biggest — exactly backwards for a bounded print; z3 uses 11 k+
   bindings on these members).

## Verification

* Workspace nextest `--all-features`: 12 108 run, 12 108 passed.
* **Armed parity** (z3 4.16.0): 177 benchmarks, **0 wrong-verdict
  pairs** (the standing single inconclusive unchanged).
* **Perf gate** (BASELINE `2269acc6`): **PASS — 1.000/1.000, wall
  0.99** (the simplifier is not on the DIMACS path).
* clippy/fmt/rustdoc clean.
* The nec-smt classes: small 11 folds + 24 residuals (0 timeouts —
  was 4 `print_file` timeouts + hangs); large 1 fold + 5 residuals
  (0 timeouts — was 6); med 1 fold + 14 residuals sampled (0
  timeouts).
* New regressions: `share_for_printing_tie_break_keeps_children_first`
  (a doubling chain whose sizes all saturate; WITHOUT the tie-break
  the test times out in the inline explosion — reproduces the bug),
  `ctx_simplify_recursion_budget_returns_instead_of_overflowing`
  (400 nested selects on a 1 MiB stack; the regression is the
  overflow).

## Traps this session

- **The CLI re-execs itself as a timeout supervisor** — a backgrounded
  "nixie" has a child "nixie"; `/proc/<pid>/task/<pid>/children`
  listing many pids means you grabbed a busy agent's tree.  Profile
  YOUR worker (match the binary path), or the samples are someone
  else's workload (one full profile here was another agent's print
  job).
- **Instrumentation can be the pathology**: a diagnostic
  `term_size` (non-saturating sum) panicked on overflow mid-loop and
  mimicked a hang; progress-print arms with modulo gaps hide the exact
  stuck iteration.  Measure, then REMOVE, then re-measure clean.
- `mk_and([t, t])` DEDUPS (the absorption) — building a sharing
  fixture needs `mk_add([t, t])`.
