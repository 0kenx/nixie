# Handoff: the bags arc, part three — `bag.map` and `bag.filter` land over unary functions

**Date:** 2026-09-17 (evening)
**Landed by:** the bags arc continuation (commit `98e8e773`; binary cached
under `precompile/98e8e773/`)
**Predecessors:** `docs/handovers/2026-09-16-bags-arc.md` (the fragment),
`docs/handovers/2026-09-17-bags-choose.md` (choose + the ite/congruence
fixes). This slice executes the remaining value item of part two's chore
list (`bag.map`/`bag.filter`; `bag.fold` stays rejected).

## What landed

`bag.map` and `bag.filter` end to end, for the fragment nixie's surface
can carry: a bare **unary function symbol** —

- a `define-fun` (the body is **inlined per element** by the reduction —
  exactly the parser's call-site substitution, so the reduction's images
  and the user's `(f x)` spellings are one hash-consed term), or
- a `declare-fun` (the image is an ordinary `Apply` the EUF layer owns;
  `(f 1) = 2` transfers into the map's counts through congruence).

Lambdas and function sorts do not exist in this surface (CVC5's own tests
are all `HO_ALL` + lambdas); non-unary or unknown names are honest parse
errors, and the parser intercepts `(bag.map f b)` in `open_named_head`
(the fp operators' rounding-mode pattern) because a function name is not
a term here.

The reduction:

- the **map images join the codomain element list** (inlined+folded, or
  EUF applies) — without them the codomain's list can be empty and the
  identities state nothing (the vacuity the support walk exists to
  prevent);
- `count(y, map f b) = Σ_x ite(f(x) = y, count(x, b), 0)` over
  **distinct-valued** domain elements (the cardinality sum's dedup
  guards); exact over a closed domain, and over an opaque one it carries
  a **nonnegative slack** — without the slack the encoding claimed the
  unknown support contributes nothing and `count(5, map f b) = 1` with no
  known preimage *refuted* (a false unsat, the worst class);
- `count(x, filter p b) = ite(p(x), count(x, b), 0)` — exact per element
  (filter only removes);
- `|map f b| = |b|` **exactly** (f is total: every copy maps to one copy)
  and `|filter p b| ≤ |b|`; map/filter of closed bags are closed.

The **builder deliberately does NOT** apply CVC5's make/⊎
normalizations: they mint `f(x)` applications, and for a *defined*
function that leaks an uninterpreted app the definition never constrains
(`count(2, map f (1:2)) = 0` with `f = *2` answered `sat`, CVC5:
`unsat`). The reduction owns the per-element work with the defs table
(`Solver::bag_fun_defs`, recorded by the Context on unary `define-fun`).

Models: map/filter values assemble from their counts; a **query-only**
map/filter (never asserted) completes from the domain's installed cells —
images folded per cell, merged by value, multiplicities summed — in the
same pre-fold sweep as query-only choose.

`set-logic` now resolves a `HO_`-prefixed name as its base logic (nixie
has no function sorts, so the prefix carries nothing extra to honor) —
this is what makes differential scripts both tools accept, since CVC5
gates function symbols-as-operator-arguments behind `HO_`.

## Verification

450 fuzz seeds vs CVC5 1.3.4 over the extended fragment (defined and
declared functions, map/filter nested in compounds, function-value
pins): **0 wrong verdicts**; 38 nixie timeouts (≈8%, the known
eager-reduction cost class — map/filter roughly double the identity
products) and 20 cvc5 timeouts (excluded by protocol). Two false-verdict
regressions found by hand probes during development are pinned in
`finite_bags_core.rs` (the builder's leaked apply; the missing
opaque-support slack). Suite **11944/11944**, clippy/fmt/doc clean,
Z3 parity 0 mismatches (176/177 decisive), perf gate PASS (1.000×
counters).

## Open chores (in value order)

1. **`bag.fold`** — still rejected. CVC5's reduction is a bounded
   quantifier over skolem families (`BAGS_FOLD_CARD`/`ELEMENTS`/
   `UNION_DISJOINT`/`COMBINE`, `bag_reduction.cpp`) — not compilable to
   the eager ground reduction; needs either a quantified axiom path or a
   CVC5-style lazy lemma scheme. `bag.all`/`bag.some` are filter
   equalities CVC5-side (`all p b ⇔ filter p b = b`,
   `some p b ⇔ filter p b ≠ ∅`) and could lower through the landed
   filter — a small slice if ever needed.
2. **Perf**: the ~8% timeout share on depth-2 random shapes (part two's
   chore 2, now bigger). Ideas stand: skip identities for elements a
   closed compound's support cannot contain; equality-connected-only
   element congruence; lazy map axioms.
3. **`(assert x)` with non-Bool `x`** answers `sat` — unchanged from
   part two's chore 3 (the parser owner's fix).
4. **Cap re-measurement** (`MAX_BAG_ELEMENTS`/`MAX_BAG_PAIRS`) —
   unchanged.

## Environment notes

- **The shared `target/` was cleaned mid-build twice** by parallel agents
  (a vanished release binary; a corrupted debug deps dir). The reliable
  pattern: keep a **private** `CARGO_TARGET_DIR` for verification runs
  and delete it after caching the binary. Disk is the recurring
  constraint: /media/data hit 99% and /tmp (the root disk) hit 100% —
  point `TMPDIR` at /media/data for fuzz campaigns, and delete
  worktree/target leftovers immediately.
- Two slow tests (`arith_incremental_matches_replay_fuzz`,
  `re_running_the_search_on_an_unchanged_goal_converges`) time out under
  3-agent parallel load while passing at `-j 8` — cap nextest concurrency
  when the machine is contended, and re-run suspects standalone before
  believing a failure.
- CVC5 1.3.4 rejects `(bag.map f b)` under every non-HO logic and errors
  (not warns) under `-q` when no `set-logic` was given — differential
  scripts want `(set-logic HO_ALL)` and stderr-free verdict reads.
