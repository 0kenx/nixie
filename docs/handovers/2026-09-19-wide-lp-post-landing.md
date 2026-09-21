# Handoff: after the wide-LP build — what the exact channels opened, what the residual gap is made of, and the open arithmetic items (2026-09-19)

**Read `AGENTS.md` first — it is canonical.** The arc memory is
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`, items 1–84:
items 81–84 (landed as `e0bbb32e`, merged with the derivation-stamps and
item-78 sessions) are the wide-LP build this handoff succeeds. Where they
disagree, the guide wins. The tree-level session map is
`docs/handovers/2026-09-19-next-session.md` (read its environment notes);
this file is the arithmetic owner's successor to
`docs/studies/2026-09-18-exact-arithmetic-wide-lp-handoff.md`.

## Where the width walls stand (all landed, all gated)

The fixed-width channel is dissolved at every layer this arc mapped:

* **Bounds** are `BoundValue` (`Narrow(DeltaRational)` fast path /
  `Wide(Arc<BigDeltaRational>)`), every consumer comparing exactly.
* **Points** have a side store (`wide_points`) for nonbasics snapped past
  width; every exact reader consults it, `eval_expr` routes wide-point
  rows to exact evaluation, and the strengthened definitional invariant
  plus the delta-vs-reeval canary are the tripwires.
* **Assert entries** intern their rows exactly at the `i64::MIN` corner
  (`intern_exact_row` → rescale-or-capture); the sticky
  `unrepresentable_row_assert` decline is deleted.
* **Branching** derives exact floor/ceil at any width
  (`wide_floor_ceil_exact`) and asserts through `set_*_exact`;
  `find_fractional_int_var` resolves through the exact point read with
  the honest integrality test (integral real part AND no infinitesimal).
* **The model gate** evaluates exactly (`EvalVal::NumBig`): `-i64::MIN`,
  `2^63`-scale folds and comparisons certify or refute boundary models
  instead of conceding `Unrepresentable` (the nongenuine-block class).

Standing numbers on the fixed seeds (20261000–02 × 600, binary
`precompile/e0bbb32e/nixie`, z3 4.16.0): **gap 49** (46 SAT-side + 3
UNSAT-side; the build's own pre-merge measurement was 47 — the ±2 is
parallel-landing trajectory reshuffle), unknown 60, timeouts 11,
decisive 1 729. Baseline for any future attribution: this file's numbers.

## Superseded: the items-69–78 handoff's named project #1

`docs/handovers/2026-09-18-arithmetic-arc-items69-78-handoff.md` names
"dual-width branch bounds" (the A3 class) as the campaign's next slice.
**This build landed it** — items 81–84: exact branch bounds
(`wide_floor_ceil_exact`), the widened bound store, the honest
integrality test, and the exact publication channel. `Underivable` now
means only "no exact value at all" (a stale wide-row reference), not
"branch bounds leave `i64`". Its items 2+ (B&B budgets, wide-repair
NOCOL, the probe recipe) remain live and are folded into the residual
map below.

## The residual gap's shape (measured, this session)

Of the 49 survivors: **40 carry `div`/`mod` nesting under wide
constants**, 5 are plain-wide, 4 are div/mod-narrow. The width walls are
gone from the survivors — the residual is **search capacity over the
div/mod axiom feeds** (item 67's largest class, unchanged by this build).
Re-attribution is the next session's first hour: the item-67 technique
(env-gated tagged prints at every `TheoryResult::Unknown` return, every
bare `resource_limit = true`, and the statement-position top-level
`Unknown` returns in `nixie-solver/src/solver/mod.rs`) — the known
residual arms to distinguish: B&B node/depth budget, wide-repair NOCOL
(`find_wide_pivot_col` finds no eligible column), the LP pivot budget,
blocking downgrade with nongenuine blocks (the evaluator no longer
declines on *width* — `Unrepresentable` survives only for genuinely
unevaluable atoms, e.g. div-by-zero corners), and the MBQI/quantifier
classes.

## What's next, in value order

### 1. fi1 — the one unfulfilled prediction, still open

`docs/studies/assets/2026-09-17/false-unsat-fi1.smt2` answers honest
`unknown` (z3: `sat`) through the landed exact machinery. The original
handoff predicted the build would close it; it did not. The exact
bound/point/evaluator channels all exist now, so the remaining blocker
is findable: entry points are the item-53–55 probe set (verdict-site
backtrace, row-history logging, set-bound backtraces, exact row
validation at z3's model `xi = 658812288346769706, yi = 2^62`). Screen
first with the canaries the build landed (the `i64_min_*` and
`boundary_*` regressions) to confirm they stay green while you probe.

### 2. The latent delta-propagation invariant (cross-ref: the stamps session)

`docs/handovers/2026-09-19-next-session.md` item 2 asks for the minimal
construction where the pivot's incremental snap-delta update disagrees
with `eval_expr`. The wide-LP build added a *known* member of that family
and guarded it (rows referencing wide-point nonbasics skip the delta
loop, flag staleness — see the comment at the loop). The stamps session's
1/2-off trajectory is gone, but the invariant's exposure is
trajectory-dependent, not the defect: construct the minimal state or
prove it unreachable, in the wide-literal study, with
`debug_verify_invariant` as the harness.

### 3. The model-blocking unit-coverage debt

The exact evaluator retired the width-limit concession the blocking
fixtures leaned on; the re-scoped tests
(`nixie-solver/src/solver/model_blocking/tests.rs`,
`nixie-solver/tests/issue40_model_blocking.rs`) now pin certify-first-try
and direct-refutation contracts, so the **block-retry loop has no
deterministic unit fixture** (its coverage is the mixed fuzz, which
exercises it in the wild). Design a gate-only-refutation fixture: the
collision must be invisible to the tableau and the repairs — array/ite
congruence shapes are the candidates (the arithmetic shapes are all
certifiable-or-refutable exactly now). Document in the wide-literal
study when found.

### 4. `eval_linear`'s unchecked narrow accumulation

`nixie-solver/src/solver/model_eval.rs` (~line 743, the
congruence-equality candidate helper) still folds with bare `acc +=`,
`-`, `acc *=`. It is an optimization path (equality-derivation
candidates), so a wrap costs a wrong candidate, not a verdict — but it
is the same class the main evaluator's exact channel just retired. Fix
with checked-then-exact (mirror `combine_eager`'s shape) or gate it
declining on overflow.

### 5. item 76's bound-shadowing journal (design recorded, unlanded)

The widened bound store kept `set_lower_value`/`set_upper_value`'s
overwrite (never-weaken doc comment vs unconditional write — the
parallel arc's item 76). Z3's `lar_solver` answer is the per-variable
shadowing stack with journal-and-undo. Do NOT land a decline without
the journal (the pop-hole trap item 76 documents). With `BoundValue`,
the journal entries are bound clones as today — the widening changes
nothing structurally.

### 6. The ndir2 general gate (standing — RE-MEASURED 2026-09-21, verdict: keep-off)

`NIXIE_S6_NDIR2` stays default-off (items 50/61); the pinned form is
default-on. The revisit condition was met and executed
(`docs/studies/2026-09-21-ndir2-remeasured.md`, binary `fa30412c`):
the fi1 deflection wall DISSOLVED on the transformed tree (sat at
10/10 seeds armed), but the gate buys nothing on any current surface
(wide fuzz: zero wins, one seed mildly worse; the LIA mass 11/12
bit-identical) while its MBQI cadence cost persists (420 s cap vs
188 s default on the screening cell). Any future case for the general
gate needs NEW win evidence — the old deflection story is dead.

### 7. Hygiene: the generator's SHAPES lack the boundary literals

The arc's rule is "extend SHAPES, not seeds" — the wide/mixed fuzz
generators (`bench/differential/wide_fuzz.py`, `mixed_fuzz.py`) still
never emit strict bounds at the walls (`< -2^63`, `> i64::MAX` on real
vs int rows, `i64::MIN` corners). This build's regressions cover those
by hand; add the shapes so fresh seeds hunt them. Keep the z3-error
awareness (z3's QF_LRA front end rejects some wide literals — treat
`err:` output as non-evidence).

### 8. Cosmetic: exact-value spelling in `get-model`

Exact publication prints as `(* 1 -9223372036854775810)` (valid,
round-trips, `get-value` agrees). A rational spelling (`(/ n d)` kept
un-folded, or a decimal) would be prettier; low priority, model_fmt +
`mk_rdiv`'s reciprocal linearization are the sites.

## The verification bar (unchanged)

`cargo build --all-features`; the full suite (release acceptable under
disk pressure — document; the slow arith tests time out at nextest's
180 s cap under load: re-run suspects standalone before believing red);
doc tests; clippy/fmt/rustdoc clean; `./bench/z3_parity/run_parity.sh`
(z3 4.16.0, record it); wide+mixed fuzz ≥3 fresh seeds each;
`debug_panic_sweep.py` over the parity corpus; the perf gate
(BASELINE pinned at `e8b02064` at this writing — check the file); the
gap survey on the fixed seeds as the attribution delta:
`python3 bench/differential/gap_survey.py precompile/<sha>/nixie <dir> 600 20261000 20261001 20261002`.

## Process notes from this landing (condensed)

* The landing took three merges (derivation stamps, item-78, a docs tip)
  — main moved hourly. Merge in your worktree, re-verify the suite +
  parity + gate at each merge, ff from the primary only when it is
  clean and your files are disjoint from the dirty set. Re-verify any
  "red on main" reading against the current tip before believing it.
* Worktrees do not carry the untracked corpora — `[corpus-missing]`
  test failures there are the environment, not the code. Symlink
  `satcomp2024/ satcomp2025/ smt-lib/` from the primary into the
  worktree before running corpus tests.
* `nextest` single-test runs rebuild the LTO test binary (~10 min);
  prefer one full-suite run per merge cycle.
* A landed compile error once blocked the whole workspace
  (`congruence.rs`'s `String + &String` — repaired in `fa0d59c9` and
  again post-merge): mechanical unblock repairs are the precedent when
  a tip does not build `--all-features`.
* After landing: `cp` your binary to `precompile/<sha8>/nixie`. This
  build's is `precompile/e0bbb32e/`.

The one-sentence version: **the width walls are gone — bounds, points,
rows, branches and the model gate are exact where width demands it — the
residual gap is div/mod search capacity plus fi1, and the next dollar is
attribution first, then fi1's probe set.**
