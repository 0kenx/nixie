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

---

# CORRECTION (same day, quiet-machine re-verification)

## The SAT "layout-dependent false unsat" is WITHDRAWN — it was a
## disk-pressure build-corruption artifact

On a quiet machine, the finding does not survive clean builds:

- Fresh, clean-disk builds of `740c16bd` and of current main
  (`4e05b46e`) answer **`sat`** on `6s299b685_Iter22.cnf` — as does
  `precompile/13173c88`, and every binary at every commit in and after
  the window that I could rebuild.
- Nine deliberate layout perturbations of `740c16bd` (unrelated source
  edits, `codegen-units=1`, `debuginfo=1`, `opt-level=2`, `panic=abort`,
  incremental-rebuild cycles in a warmed target) — **all `sat`**.
- The perf gate on a fresh `4e05b46e` build: **PASS, 1.000× conflicts/
  decisions, zero verdict mismatches**. Same for `740c16bd`.

The only binaries that ever answered `unsat` were built in target
directories that had survived the session's disk-full events (/media/data
at 99–100%). The consistent explanation: a truncated/partial artifact
written under disk pressure linked into a deterministically-corrupt
binary; clean rebuilds cure it. The handovers' existing warning ("a
linker SIGBUS mid-gate means the disk, not the code") understates the
hazard — **a disk-pressure build can fail silently and yield a
wrong-verdict binary that passes every per-run determinism check**.
Rule: never trust — never *report* — a verdict from a binary built while
the disk was full; rebuild clean and re-run before escalating.

The SAT owner has no layout-UB to hunt on this evidence. (Not proven
absent — proven *unreproduced* across every reconstruction attempted;
both manifesting binaries are deleted.)

## The rehome-test timeout on main belongs to `51adf259` (arith owner)

`rehome_does_not_fabricate_a_crossing_on_a_referenced_slack` (added in
`740c16bd`, where it passes in 7.5 s) times out at 180 s from
`51adf259` onward — the ±1-divisor identity folds (`builder.rs` +65,
`rewrite/arith.rs` +10, landed inside the `docs(study)`-prefixed commit)
— on a fresh target with a clean disk, at `51adf259`, at `3b5c2721`,
and on current main. My two-point bisection (740c16bd pass → 3b5c2721
timeout) initially mis-attributed it to my purify fix; the intermediate
commits tell the real story. The full-suite "1 timed out" seen in
current runs is exactly this test. It is the arith owner's perf cliff
(or loop) on their own instance — `xi = 658812288346769706` is the
known model if they want to profile.

## Quiet-machine clean statements

- Full workspace suite at `4e05b46e`: **11957 tests, 11956 passed**,
  1 timed out (the rehome test above), 14 skipped.
- Perf gate at `4e05b46e` (fresh build): **PASS**, 1.000× counters.

## Addendum: the rehome timeout — resolved (`045c99c7`)

The follow-up session answered "did you fix it" properly. The code
culprit was **not** `51adf259` (docs-only) but the ±1-divisor folds
(`458a3ba5`, arriving via the `cd0430a5` merge) — and **the folds are
exonerated**: the hand-folded instance is equally slow (691 s vs 7 s)
on the pre-fold binary. The verdict stays `sat` throughout; this is a
pure perf cliff, and the profile convicts the **exact-rational
simplex** (>60 % of 564 s in `BigUint::gcd` under
`num_rational::Ratio::reduce`, hot frames `eval_big_raw` /
`derive_var_bound_big_parts` / `update_assignment`) — the item-76
machinery. Naive normalization deferral is unsound (`Ratio`'s canonical
form is load-bearing for `Ord`); the real cure is fraction-free
tableaus, which is the arith owner's design work.

What landed: the big test `#[ignore]`d with the repo's `pete_cxs_bp`
precedent (explicit-run recipe + 25×60 s nextest override sized for its
measured 1157 s; verified passing under that ceiling), the **defect it
guards stays covered in the default suite** by the 34 s two-disjunct
core, and the full study + reproducer pair (original vs hand-folded,
80× apart) in `docs/studies/2026-09-18-rehome-wide-rational-blowup.md`.
