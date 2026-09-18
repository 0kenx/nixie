# Handoff: the bags arc, part four — `bag.all`/`bag.some`, a core false-`sat` closed under them, and a **pre-existing layout-dependent false-`unsat` in the SAT core reported for its owner**

**Date:** 2026-09-18 (early hours)
**Landed by:** the bags arc continuation (commits `3b5c2721`, `a268baa6`;
binaries cached under `precompile/<sha>/`)
**Predecessors:** parts one–three (`2026-09-16-bags-arc.md`,
`2026-09-17-bags-choose.md`, `2026-09-17-bags-map-filter.md`).

## For the SAT owner — read this first

**Main currently answers a false `unsat` on a satisfiable SATCOMP instance,
and the verdict flips with unrelated binary-layout changes.**

```
f=satcomp2025/main_2025/1576e239e1c17939f24688a12fb10fae-6s299b685_Iter22.cnf
precompile/13173c88/nixie --dimacs $f   → sat   (3/3, pinned and unpinned)
git checkout 740c16bd && build → unsat (5/5)
same 740c16bd + unrelated nixie-core/solver source changes → sat   (3/3 + 3 seeds)
```

The `nixie-sat` source is byte-identical across the last two builds — the
verdict tracks the binary layout, which is the signature of latent
undefined behavior (uninitialized/stale scratch state — the window
`5c0c6844..740c16bd` contains the ELS/Tarlan epoch-stamped scratch and
the search-vs-inprocessing counter split). The perf gate catches it
(`GATE: FAIL (verdict mismatch — soundness)` on every current-main
binary; the same four instances: `nix-shell-env seed=1`,
`6s299b685_Iter22`, `x9-07092 seed=1`,
`circuit_48in64out_..._seed3.sanitized`, all base=sat cand=unsat). The
in-flight `nixie-sat/src/solver/congruence.rs` ITE-gate rework does not
fix this instance (a build with it still says `unsat`). Until fixed, no
landing on main can pass the perf gate honestly — attribute gate FAILs
accordingly, and pin the blame with the pristine-checkout A/B above.

## What landed

**`3b5c2721` — a core false `sat` in the numeric-argument purifier.**
`purify_numeric_uf_args` proxies numeric constants globally; a proxy
minted in a *later* assert left earlier assertions on the raw spelling —
`count(2, b)` in the first assert, `count(proxy, b)` later — two
arithmetic columns with no tie (counts are columns, not EUF closure
nodes; set member atoms get closure congruence, counts don't). The only
possible tie, the bag reduction's element-congruence axiom, was itself
rewritten by the same global substitution into a tautology and folded
away. Reproducer (order-dependent, six assert orders bisected):
`count(2,b)=1 ∧ count(2,filter p b)=0 ∧ (p 2)` answered `sat`, CVC5
`unsat`. Fix: the purifier's substitution shields bag element positions
(`TermManager::substitute_keeping` — the shield binds by filtering kept
keys out of the cloned context maps, because `resolved()` consults the
substitution before the cache). Found while testing `bag.some`; the
regression pins four assert orders.

**`a268baa6` — `bag.all`/`bag.some`**: CVC5's `ALL_FILTER`/`SOME_FILTER`
lowerings at parse time (`all p b ⇔ filter p b = b`, `some p b ⇔
filter p b ≠ ∅`), no new term kinds; predicate operands validated as
unary Bool-codomain functions; get-value folds bag-sorted equalities
from resolvable cells. 400 fuzz seeds vs CVC5, 0 wrong verdicts (59
cvc5 crashes/timeouts excluded — cvc5 itself dies with `Unhandled case
... bag.some` on some shapes).

## The fragment is now complete except fold/partition

Supported: sorts/`bag`/make, `union_max`/`union_disjoint`/`inter_min`/
`difference_subtract`/`difference_remove`/`member`/`subbag`/`count`/
`card`/`setof`/`choose`/`map`/`filter`/`all`/`some`, models and
query folding throughout. Still honest parse rejections:
`bag.fold` (needs CVC5's bounded-quantifier skolem-family scheme) and
`bag.partition` (tuple of bags).

## Open chores

1. **SAT owner's layout-dependent false unsat** (above) — gates every
   landing on main.
2. Perf: the ~8–10% timeout share on depth-2 random bag shapes (parts
   two/three's chore; ideas recorded there).
3. `(assert x)` with non-Bool `x` answers `sat` — the parser owner's.
4. Cap re-measurement — unchanged.

## Environment notes

- **A teammate's merge on the shared primary (`cd0430a5`) reset the
  working tree mid-session and wiped every uncommitted change — mine
  (this slice's first copy) and another agent's in-flight
  `nixie-sat` edit.** The AGENTS.md worktree discipline exists for
  exactly this; committed work survives, so commit early and often on
  the shared tree. The wiped slice was re-applied and re-verified
  (identical diff, fresh fuzz round).
- The perf gate's `taskset -c 0-7` is how the SAT bug first showed, but
  the bug is not affinity-dependent — it is per-build deterministic;
  A/B binaries, not run conditions, when attributing.
- Verification pattern that worked under three active agents: private
  `CARGO_TARGET_DIR` (deleted after caching the binary), scoped
  `cargo fmt -p`/`clippy -p` (a teammate's WIP file fails workspace
  lint), full-suite `-j 8` with standalone re-runs of any load-sensitive
  failure, and pristine-worktree A/B before believing any regression.
