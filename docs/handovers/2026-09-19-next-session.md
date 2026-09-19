# Handoff: the next session — where the tree stands, what's worth doing, how to verify

**Date:** 2026-09-19 (written at `e0bbb32e`)
**Read AGENTS.md first** — it is canonical. Then this file top to bottom.

## Where the tree stands (all landed, all verified at their landings)

Three arcs converged on main in the last two days:

1. **Bags (complete except fold/partition)** — the full SMT-LIB bags
   surface: make/union_max/union_disjoint/inter_min/both differences/
   member/subbag/count/card/setof/**choose**/**map**/**filter**/**
   all**/**some**, count-driven models, query folding. Handovers:
   `2026-09-16-bags-arc.md`, `2026-09-17-bags-choose.md`,
   `2026-09-17-bags-map-filter.md`, `2026-09-18-bags-all-some.md`
   (the last corrects an earlier false alarm — read its CORRECTION
   section before believing any "layout-dependent verdict" claim).
2. **The derivation stamps (resolved)** — row-level incremental bound
   propagation in the simplex, value-identical by proof: three stacked
   defects closed (family keying, sum-of-versions, first-writer-wins
   crossings), store-sequence bit-identity demonstrated (690 070/690 070),
   rehome 564 s → 34 s. `2026-09-18-derivation-stamps.md` + its
   RESOLVED addendum.
3. **The wide-LP exact-arithmetic build (the arith owner's)** — landed
   via `e0bbb32e`; their own final numbers: survey gap 113 → 47, suite
   11 970/11 970, gate counters 1.000. Their handoff:
   `docs/studies/2026-09-18-exact-arithmetic-wide-lp-handoff.md`, the
   arc memory `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
   (items 1–78; item 78 landed in `f4415a0e`).

Also landed by others while these ran: XOR/XNOR gate congruence in the
SAT core (bv_ILA at kissat parity), row-memory, honest-pace (a negative
result — "honest rows do not converge at any budget" — see
`3e07f340`'s study before touching row-honesty heuristics).

Perf-gate BASELINE is pinned at `e8b02064` (binary present).

## What's next, in value order

### 1. `bag.fold` — the last missing bag operator

The one honest parse-level rejection left
(`nixie-core/src/smtlib/parser/build.rs`'s reject arm). CVC5's
reduction is a bounded quantifier over skolem families
(`bag_reduction.cpp: reduceFoldOperator` — BAGS_FOLD_CARD/ELEMENTS/
UNION_DISJOINT/COMBINE) — not compilable to the eager ground
reduction. Two viable shapes:

- **Ground-instantiated**: for a CLOSED bag (support = the collected
  makes), fold is a finite sum over the known elements with
  multiplicities — same discipline as `bag.map`'s Σ-ite identity; the
  operand ordering question (fold is order-sensitive for non-AC f) is
  resolved by fixing any order over the ground support and stating
  permutation lemmas only when needed. Opaque bags: honest decline or
  the cardinality-slack trick — study CVC5 first.
- **define-fun ground bodies**: substitute the function inline per
  element exactly as `bag.map` does (`bag_apply_fun` in
  `nixie-solver/src/solver/bag_theory.rs` — the helper is already
  generic; fold needs an accumulator, not an image).

`bag.partition` needs tuples-of-bags output — likely stays rejected;
say so with a pointer.

Verification beyond the standard bar: extend
`/tmp`-regenerated fuzz (the bag generators are described in each
handover; CVC5 1.3.4 at the nix store path is the oracle; it CRASHES
on some `bag.some` shapes — treat `err:*Unhandled*` as inconclusive,
never evidence).

### 2. The latent delta-propagation invariant (arith owner's, small)

During the stamp debugging, a trajectory existed where the incremental
snap-delta update disagreed with exact evaluation by exactly 1/2
(`delta propagation mismatch`, the `debug_assert` in the pivot's
row-update loop — see the pre-RESOLVED section of
`2026-09-18-derivation-stamps.md` for the values). That trajectory no
longer exists under the landed semantics, but **the invariant's
exposure was trajectory-dependent, not the defect** — the incremental
update can disagree with `eval_expr` under some reachable state. Item
it in the wide-literal study: construct the minimal state (the old
stamp build's trajectory is gone; reason from the assert's condition —
`snap_delta` applied to a row whose OTHER nonbasics moved, or a base
assignment already stale) and either fix the propagation or prove the
invariant unreachable. The `debug_verify_invariant` machinery (item
60) is the right harness.

### 3. Bag perf on deep compounds (~8–10% timeout share)

Depth-2 random bag shapes still take 30–90 s where CVC5 needs <30 s
(honest answers, no wrongness — the 450-seed campaigns have 0
verdict disagreements). The ideas ledger is in
`2026-09-17-bags-map-filter.md`'s chore list. Measure FIRST per
`docs/BENCHMARKING.md` (heuristic-class change: matched null,
≥10 seeds). Only worth it if a corpus ever grows bags.

### 4. `(assert x)` with non-Bool `x` answers `sat`

Pre-existing parser leniency (`nixie-solver/src/solver/mod.rs`'s
Bool-const path). CVC5 rejects at parse. One-line-ish fix plus
regressions; coordinate — the parser surface is shared.

### 5. Cap re-measurement (`MAX_BAG_ELEMENTS`/`MAX_BAG_PAIRS`)

Only "once the TLA+ corpus runs green" (the standing condition in the
bags handovers). Check whether TLA+ is green before spending time.

## The verification bar (non-negotiable, from AGENTS.md)

```
cargo build --all-features
cargo nextest run --workspace --all-features
cargo clippy --all-features --all-targets -- -D warnings
cargo fmt --all -- --check
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features
./bench/z3_parity/run_parity.sh          # z3 4.16.0, record the version
bench/perf_gate/run_gate.sh              # BASELINE=e8b02064
```

For solver-touching work add the wide+mixed differentials
(`bench/differential/wide_fuzz.py`, `mixed_fuzz.py`, ≥3 fresh seeds
each; extend SHAPES, not seeds). **Scope to a worktree when the shared
tree is dirty or broken** — it has been both mid-session twice.

## Environment notes (hard-won, all recent)

- `/media/data` runs 90–100% full; the shared `target/` is ~100+ GB.
  Build with `CARGO_TARGET_DIR` on `/media/data`, `CARGO_INCREMENTAL=0`,
  delete the target when done. A disk-full build can produce a
  SILENTLY WRONG-VERDICT binary (the withdrawn "SAT false-unsat" of
  `2026-09-18-bags-all-some.md` was exactly this): **never trust or
  report a verdict from a binary built under disk pressure — rebuild
  clean and re-run before escalating.**
- Corpus tests cannot run in worktrees (gitignored external data lives
  only in the primary). Run the full suite in the primary.
- Slow tests (`scope_rebase`, the arith fuzz pair) time out under
  multi-agent load at full concurrency; cap `-j 8` and re-run suspects
  standalone before believing a failure.
- Main moves hourly. `git status` twice before staging; stage only
  your files; ff-merge from the primary. Other agents' worktrees are
  theirs — do not garbage-collect.
- The sat owner iterates in the primary's `nixie-sat/` (uncommitted
  edits are mid-flight; a landed compile error there once blocked the
  whole workspace — `fa0d59c9`'s one-line repair is the precedent:
  mechanical, unblocks everyone, their WIP merges over it).
- Binaries: after landing, `cp` your build to `precompile/<sha8>/nixie`.
  The cache is the shared build memory.
