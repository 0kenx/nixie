# Handoff: Transcendental theory (δ-ICP) — next optimization targets

**Session:** 2026-09-22/23. **Landed:** `df8017a2` (the theory itself),
`8131ba44` (perf round). Binary: `precompile/8131ba44/nixie`. Benchmarks:
`bench/trans/` (20-goal corpus + `run_bench.sh`, honest z3 comparator),
results in `precompile/df8017a2/benchmark/trans/baseline.tsv` (before) and
`precompile/8131ba44/benchmark/trans/optimized.tsv` (after). Read
`docs/TRANS.md` first — the "Semantic decisions" section is the contract.

## Where things stand

20/20 corpus decided (13 delta-sat, 7 unsat), worst case 303 ms. Z3 4.16.0
decides 0/20 (`unknown` on everything it parses; no `exp`/`log`/`sqrt` on
Reals at all). So the remaining work is **self-improvement**, not
competition: widen what the fragment can decide, and kill the two slow
goals (t19 303 ms, t16 98 ms) plus the still-`unknown` classes below.

Diagnosing: set `NIXIE_TRANS_STATS=1` (per-goal counters via
`nixie_theories::trans::last_stats()`: node_props, constraint_props,
branches, conflicts, witness_tries) and `NIXIE_TRANS_DEBUG=1` (atoms,
assignments, ICP culprits). Both are env-gated, zero-cost when off.

## Ranked next targets

### 1. t19 class — first-split heuristic for periodic functions (303 ms)

`sin x = 0.5` on `[90,100]` (~3 periods). Current cost driver (from the
counters): the asin-contraction only fires once the argument window is
narrower than π/2, so the first ~6 bisections of a 10-wide box are *blind*
(no contraction, no conflict) and the deferred-sibling DFS re-propagates
from scratch after every one. Ideas, in order of expected payoff:

- **Monotone-segment first split**: when the branch var feeds a
  Sin/Cos node and the window spans ≥ π/2, split at the nearest
  critical point (`kπ`/`π/2+kπ`) instead of the midpoint — both halves
  land in monotone segments and the asin-contraction engages
  immediately. This is what dReal's pruning does implicitly via
  fixed-precision boxes; doing it explicitly should collapse t19 to
  ~1 ms.
- **Don't re-enqueue everything on `BranchInto`**: `restore()` + the
  full re-enqueue is O(N·fixpoint) per backtrack. A trail-based undo
  (record `(node, old_iv, old_deps)` per `tighten`, unwind to the
  branch mark) restores the *propagated* parent state and only needs to
  propagate the one changed variable. Cuts every deep search, not just
  periodic ones. (Careful: the current full re-enqueue exists because
  an earlier incremental version left the box inconsistent — write the
  trail as a proper undo log, and keep a debug-mode assertion that the
  re-propagated fixpoint matches the snapshot semantics on the corpus.)

### 2. t16 class — coupled-product goals (98 ms)

`x0·e^{−t} = 0.3` on boxes. Counters: ~2.3k node_props for a 20-node
problem — the fixpoint converges ulp-slowly through the
Mul→Exp→Log→Neg chain, and the exact witness (BigRational evaluation per
attempt) is not cheap. Ideas:

- **Fixpoint convergence check**: stop propagation when a full sweep
  narrows no bound by more than 2⁻⁵³ of scale instead of relying on the
  queue draining (ulp-creep chains keep the queue alive doing nothing).
- **Memoize the exact witness evaluation**: `evaluate_at_exact` re-walks
  the whole DAG per attempt; the transcendental `*_rational` enclosures
  dominate. Cache keyed on `(node, pinned-slot-values)` — midpoints
  repeat heavily across witness attempts.
- The `sin`/`cos` **rational enclosures** go through f64 range
  reduction (`trig_reduce_ifx` takes the f64 of the rational) — fine
  for |x| ≤ 2⁵⁰, but the f64 conversion of a BigRational point is one
  more rounding to audit. A rational-exact reduction (mod π/2 in
  Ifx arithmetic) would close the last theoretical gap.

### 3. Widen the decidable fragment (verdict wins, not speed)

Currently `unknown` (honest decline) for, in rough order of value:

- **`QF_UFRT`-style UF over Reals**: the decline is because congruence
  (`f x = f y` when `x = y`) is EUF semantics ICP doesn't carry. The
  cheap slice: Ackermannize ground UF applications (the corpus of
  `tactic/ackermann.rs` may already do this) before interning — ground
  congruence becomes plain equalities. This is exactly what the
  UF-in-trans regression test pins as declined today; flip it when done.
- **`distinct` over Reals** and **disequality pruning**: `Ne` never
  prunes. Point-disequality pruning is easy: when one side of the
  disequality becomes a point p, remove p from the other side by
  splitting (two children, p excluded on each). Rarely needed, but it
  turns `x ≠ 0 ∧ …` goals from flounder to decide.
- **Unbounded periodic refutations** (`sin²+cos²=0` over ℝ): needs
  periodicity reasoning (period folding: reduce x mod 2π once the box
  is wider than 2π, assert a witness-period bound). dReal also punts
  here, so this is optional polish — the honest `unknown` is defensible.

### 4. Integration depth (architecture, larger)

The dPLL(T) loop is whole-goal today (fresh SAT instance per check-sat,
no incremental assertions). If hybrid-systems users show up with
push/pop workflows, the pieces to reuse are: `TransBuild` (Tseitin over
arithmetic atoms) and the per-assignment compilation; the nixie-sat
instance already supports incremental `add_clause`. The expensive part
to preserve is `prepare_search`'s static memos — they're per-`TransProblem`,
and problems are rebuilt per assignment today.

### 5. Housekeeping (small)

- `TransOptions::max_branch_nodes`/`max_propagations` are not exposed
  as SMT-LIB options (`:trans-budget` style) — only `:delta` is. Wire
  them if users need to trade time for decisions.
- The corpus is hand-written; a dReal-benchmark import (their test
  suite has hybrid-ODE goals, e.g. `bouncing_ball`, `diode`) would be
  the natural scale-up. Compare against `dreal4` built from source —
  note `deny.toml` bans *linking* it, but running the binary as a
  differential oracle is the same pattern as the z3 parity suite.
- `sin_point_cached`'s thread-local cache is keyed on f64 bits; the
  exact-rational enclosures have **no** cache yet (see target 2).

## Traps recorded this session (do not re-learn)

- **Purification × δ**: never introduce a proxy variable + definition
  atom for a transcendental — per-atom δ-weakening doubles effective δ
  through the chain (the false-δ-sat class fixed in `8131ba44`).
  `is_arith_constructor` in `purify_arith.rs` is the gate; keep the
  six transcendental kinds in it.
- **Ulp-edge convergence**: outward-rounded f64 propagation saturates
  exactly ON the pruning bound. Any acceptance check tighter than the
  pruning bound (the exact witness is) needs the PRUNE_ULPS slack to
  have interior room. If you tighten PRUNE_ULPS=4, re-run t15/t16 —
  they are the canaries.
- **1-ulp branch loop**: never bisect an interval with
  `next_up(lo) >= hi` — the midpoint rounds to an endpoint and the
  second half equals the parent. `pick_branch_var` already skips them;
  any new branching site must too.
- **BranchInto semantics**: after `restore()`, the ENTIRE subtree is
  stale (the snapshot reset every node). The current code re-enqueues
  all nodes + constraints; an earlier "only the split var" version
  left the box inconsistent and floundered silently. Target 1's trail
  rewrite must preserve the re-propagation guarantee.
- The exact witness's `admissible_exact` bounds are stored per
  constraint at `add_constraint` time — do NOT re-derive them from an
  engine-side δ (they drifted once already: constraint-build δ vs
  engine-run δ differ in the d15 test).

## Verification bar for any change here

`cargo nextest run -p nixie-theories -E 'test(trans)'` (31) +
`cargo nextest run -p nixie-solver --test trans_delta_icp` (21) are the
fast canaries (the latter pins every verdict class: delta-sat, unsat,
honest-unknown, δ-option plumbing). Then the standard battery —
`cargo nextest run --workspace --all-features`, clippy/fmt/doc — plus
`./bench/trans/run_bench.sh precompile/8131ba44/nixie` to compare
against the recorded baseline (never re-run cells; add new corpus files
freely). The z3 parity suite and the perf gate must stay clean because
`purify_arith` is on the global assert path: any change there re-runs
both (`bench/z3_parity/run_parity.sh`, `bench/perf_gate/run_gate.sh`).
