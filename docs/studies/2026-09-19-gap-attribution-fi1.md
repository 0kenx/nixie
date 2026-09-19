# The post-wide-LP session: the residual gap re-attributed, fi1 decoded to the branch-walk class, the last evaluator wrap retired (2026-09-19)

Executes `docs/handovers/2026-09-19-wide-lp-post-landing.md`. The arc
memory is `2026-09-13-lia-wide-literal-arithmetic.md` (items 1–84 landed
at `e0bbb32e`; item 85 — the delta-propagation canary — landed in a
parallel session from the stamps handoff). Where this file and the arc
disagree, the arc wins.

## A. The residual gap, re-attributed (the handoff's item 2)

Method: the item-67 recipe — env-gated tagged prints
(`NIXIE_GAP_PROBE=1`) at every `TheoryResult::Unknown` return, every bare
`resource_limit = true` write, and every statement-position
`SolverResult::Unknown` return in `nixie-solver/src/solver/mod.rs`
(~75 tags), built at exactly `e0bbb32e` (the handoff's attribution
baseline; the probes print only at already-decided declines, so the
verdicts match the uninstrumented binary). `gap_survey.py` was extended
to capture the decline-site stderr alongside every gap member (landed).
Fixed seeds 20261000–02 × 600: **47 gap members** (44 SAT-side, 3
UNSAT-side) — the handoff's own ±2 note covers 49 → 47.

Last-tag attribution (the verdict-proximal decline; a member shows many
tags, only the exit site classifies):

| members | exit tag | arm |
|--------:|----------|-----|
| 27 (26 sat, 1 unsat) | `slv:conflict-limit-dropped` | theory resource exhaustion made sticky |
| 9 (8 sat, 1 unsat) | `slv:arith-atoms-need-theory` | the wide-const nonlinearity parse gate (item 32's class) |
| 5 (sat) | `slv:blocking-nongenuine` | item 64's residual (was 25 at item 67) |
| 3 (2 sat, 1 unsat) | `slv:bv-late-minting-budget` | div/mod atoms minting BV circuits (was 6) |
| 3 (sat) | `slv:qround-bigconst-uncertified` | certifier declines (was 22 at item 67 — the vocabulary + exact evaluator collapsed it) |

The dominant arm decoded one layer deeper — `conflict-limit-dropped` is
`theory_manager.resource_exhausted() || unjustified_conflict()` at a
`SatResult::Sat`, and the simplex's `resource_limit` flag is **sticky for
the instance's lifetime**: once any decline path sets it (NOCOL, pivot
cap, SOI), every later `Sat` candidate exits `Unknown` through this
gate. The members split by what set the flag:

* **7 NOCOL-storm members** — `find_wide_pivot_col` finds no eligible
  entering column, the wide classification declines, and this repeats
  per CDCL candidate: 38–4 098 storm fires per member (the counts cluster
  at 2^k·2−2 — the classification's bounded round loop, re-entered per
  candidate). Shapes: `div`/`mod` nesting under ±2^62 constants — the
  handoff's "search capacity over the div/mod axiom feeds", confirmed.
* **~20 B&B-depth members** — `lia:bnb-depth-budget`
  (`LIA_MAX_DEPTH = 4 096`) fires once, the theory declines, the CDCL
  keeps searching, the sticky flag ends it. Shapes: the same div/mod+wide
  family (the handoff's 40/49 measured shape matches these 27).

MBQI/quantifier classes: **zero** members (the generator is QF —
expected). LP pivot budget: 2 `make_feasible-pivot-cap` fires total
(noise). Item 67's map for comparison: Underivable 29 → 0 (the wide-LP
build retired it), blocking 25 → 5, big-const uncertified 22 → 3,
parse-gate 10 → 9, B&B budget 17 → 27 (the wall members migrated into
it), NOCOL 8 → 7, BV minting 6 → 3.

**Implication for the next campaign:** the residual is one machine —
per-check search capacity on div/mod-structured LIA at wide constants.
The candidate levers (all heuristic-class, all needing the
`docs/BENCHMARKING.md` matched-null discipline): NOCOL repair
eligibility (`find_wide_pivot_col`'s first-eligible-var rule), the B&B
branch-variable choice on ray-walking rows (see B below — the divergence
is structural, not budget), and cut power over rescaled div rows (also
B). Budget bumps alone are not the fix; the divergence makes depth
budgets irrelevant.

## B. fi1 — the honest `unknown` decoded to the branch-walk divergence class (the handoff's item 1)

`docs/studies/assets/2026-09-17/false-unsat-fi1.smt2` (z3 4.16.0:
`sat` at `xi = 5, yi = 2^62`; nixie: honest `unknown`). The item-53–55
canaries stay green (S6 audit silent, no debug-panic, the exact-channel
regressions green). A branch-trace probe (`NIXIE_FI1_PROBE=1`, in the
probe tree only) shows the mechanism, first B&B descent:

```
branch#0 var=16 <= -53   node depth=1
branch#1 var=5  <= 185 / >= 186   (both sides dead immediately)
branch#3 var=16 <= -54   node depth=3
branch#10 var=16 <= -55  ... var=16 <= -60 ... (one per node, forever)
```

* var 16 is the slack of the `/7` row (`v17 − v3 − 2v8 − 2v10 − 6v6 +
  12)/7` — the `div (−xi+5xi) 7` atom's channel. It is FREE (no atom
  bound of its own), so `close_free_vars_then_bnb`'s zero-split closes
  it `≤ −1`; the LP then re-optimizes it to a fractional value below
  every branch bound (`−53.5, −54.5, …`): **an unbounded ray the
  inequality branches prune nothing from** — each up-branch (`≥ −k`)
  conflicts immediately, each down-branch descends one more level. This
  is the same class the root integral dive patches (`y = 2a+1` walked
  `a := −1/2, −3/2, …`), but the dive runs only at the root and the
  post-dive candidates re-open the ray.
* The GMI cut layer cannot see the lattice: the `/7` row is a width
  rescale, and item 55 (correctly) marks a rescaled slack integer only
  when the rescaled row is itself an integral form — `1/7`-scaled
  coefficients never are. The mod-7 structure that makes the up-branches
  conflict is exactly what the cuts are barred from fabricating.
* Everything on the path is sound (the row validates at z3's model; the
  conflict reasons are the live bounds'); the blocker is pure search
  capacity — B&B diverges before the CDCL's trichotomy commitments can
  bound the slack, then the sticky resource flag (A) ends the run.

**Next entry points** (in promise order): (1) branch-variable selection
that detects the one-step-down-forever signature (var branched down at
depth d and again at d+1 with the sibling refuted — Z3's
`branch`/`bound` heuristics switch to the cut/eq-split arsenal there);
(2) the equal-bound case-split (`close_free_vars`'s `= 0 / = −1`
equalities) applied to FREE div slacks *at the atom level* — letting the
SAT core commit the trichotomy arm instead of the simplex-internal
zero-split; (3) cut forms that derive real divisibility lemmas from the
div/mod axiom rows (the Z3 `lia` `div/mod` axioms carry
`q = k·d + r, 0 ≤ r < d` as bounds on BOTH `q` and `r` — interning the
mod-slack's `[0,d)` window as a bound at intern time would bound var 16
the moment its inner vars are pinned). None are landed here: all are
heuristic-class changes requiring the matched-null bar.

## C. `eval_linear` made exact (the handoff's item 5) — LANDED

`nixie-solver/src/solver/model_eval.rs`'s congruence-equality candidate
helper folded with bare `Rational64` `+=`/`-`/`*=` — the last unchecked
narrow accumulation in the evaluator's periphery; a wrap pairs arguments
as "equal-valued" that are not (or splits an equal pair), feeding the
congruence blocker a wrong candidate. Now a `LinVal`
(`Narrow(Rational64)` fast path / `Wide(BigRational)`) mirrors
`combine_eager`'s checked-then-exact discipline: every op tries the
checked narrow fold, widens exactly on overflow, and comparison across
the width boundary is exact. `IntConst` leaves `i64` as exact `Wide`
values (never truncated, never `None`). Regression:
`eval_linear_folds_exact_beyond_narrow_width` pins `2^62 + 2^62`,
`(2^62+2^62)·2`, `−2^63 − 1` and a wide leaf exactly (the old folds
wrapped — in release silently).

## D. The boundary-literal generator SHAPES (the handoff's item 7) — LANDED

`wide_fuzz.py` and `mixed_fuzz.py` now emit the wall vocabulary the
hand-regressions cover, so fresh seeds hunt it continuously:
strict/weak bounds at `±2^63`-scale walls on Real vs Int rows
(`< i64::MIN` forces beyond-width witnesses — the exact publication
channel), the `i64::MIN` corner and first-beyond integers in the
constant pools, and spelled negation corners `(- 0 2^63-ish)` (z3's
QF_LRA front end still errors on some of these — `mixed_fuzz` now
normalizes that to `z3err` non-evidence exactly like `wide_fuzz`).
Smoke (100 instances each, seed 20262101/02, `e0bbb32e` binary): clean —
no verdict disagreements, no refuted models; wall literals appear in
~47% (mixed) / ~59% (wide) of instances. One pre-existing yield bug
fixed in passing: `wide_fuzz`'s f1-shape block applied `mod`/`div` to
REAL variables (ill-sorted — both solvers reject at parse and every such
instance was wasted); Real-sorted instances now get the `/` analogue of
the same nesting (unsat yield 23 → 37 on the smoke seed).

## E. The model-blocking gate-only-refutation fixture: the search came up empty (the handoff's item 4) — negative result

Twelve hand-designed candidates for a deterministic block-retry-succeeds
fixture (first candidate gate-refuted, retry certifies, `sat` with
`model_blocking_clauses ≥ 1`), driven at the unit surface with the
statistics visible: read-over-write and nested-store selects, ite over
stores, array equality, UF value clashes, UF congruent arguments,
Bool-argument applications, `mod`-argument applications, literal
`div`-by-zero corners, UF-disjunction escapes — **every one is either
certified on the first candidate, preempted by a repair path (array
axiom retraction, congruence-gap split, case-split lemmas), or refuted
directly by the theories; none pays a block**. The exact evaluator
retired the width-`Unrepresentable` class that the old fixtures leaned
on, and the surviving nongenuine `Unrepresentable` sources are thin
(`combine_eager`'s Sub fallback failing on non-numeric operands).
Conclusion: on the current tree the block-retry loop's *retry-succeeds*
path has no small deterministic shape — the repairs preempt exactly the
small collisions, and what remains is trajectory-dependent (the mixed
fuzz's in-the-wild coverage, plus the 5 survey members that exhaust
through nongenuine blocks). The unit debt stays open; the honest options
recorded for the next session: (a) accept fuzz-only coverage and pin the
loop's *contracts* instead (projection, budget, downgrade — already
pinned); (b) construct the fixture by asserting a candidate-breaking
polarity directly through the internal API (white-box: force the SAT
model to the colliding assignment), which tests the loop but not its
reachability.

## F. item 76's bound-shadowing journal: the design sharpened, deliberately not landed (the handoff's item 6)

Two facts sharpened past item 76/77's record:

1. **The pop behavior is already exact.** `set_lower_value`/
   `set_upper_value` push a full-clone `BoundUndo` per effective write,
   and under the simplex's LIFO scopes sequential restore IS the
   shadowing semantics: the pre-write live value equals the tightest
   still-alive bound at every restore point (induction over the write
   sequence). The "pop-hole" only opens for a DECLINE that leaves no
   trail entry — the trap item 76 documented.
2. **The unsound half is the live window, not the pop.** A weaker write
   arriving while a tighter bound is live *erases the tighter
   constraint's strength for as long as both are in scope* — the
   strictness-erase false-`sat` shape (a strict `slack ≤ −δ` overwritten
   by a weak `slack ≤ 0` lets the LP rest at exactly `0`). Item 77's
   guards closed the reachable writers; the exposure is future writers,
   which `NIXIE_BOUND_TRIPWIRE` watches.

The journal's actual job is therefore narrower than "fix the pop": it is
to make keep-the-tighter live (never-weaken, matching the doc comment)
*without losing the weaker write's reason set* — the displaced bound
must be journaled so (a) conflict explanation can still name the weaker
atom when the LP rests against it after the tighter pops, and (b) the
weaker write keeps a trail footprint. Per the handoff's own bar ("do NOT
land a decline without the journal"), and because this lands on the
hottest shared file mid-parallel-session, it stays unlanded; the design
above is the landing spec.

## G. A live FALSE `sat` found by the new SHAPES — the B&B leaf's re-solve-vs-scan vertex mismatch — FIXED at the root

The mixed differential's first fresh-seed run with the boundary SHAPES
(seed 20262113, instance 41) found a pre-existing wrong verdict
(reproduces on `precompile/e0bbb32e`):

```smt2
(set-logic QF_LIA)
(declare-const yi Int)
(assert (> (mod (+ (* -2 yi) 4611686018427387904) 4) 2))
```

z3: `unsat` (the expression is always 0 or 2 — the parity shape
`2·yi + 4·q = 2^62 − 3` has no integer point).  nixie: **`sat`**, publishing
`yi = −1` — a model violating its own assertion
(`mod(2^62 + 2, 4) = 2`, not `> 2`).

**The mechanism, decoded with the branch/leaf probes** (three layers,
one defect): `find_fractional_int_var` scans a node's integer variables
at the current (crude, post-pop) point and finds them all integral — but
the leaf's feasibility `simplex.check()` is a full `make_feasible` solve
that re-optimizes onto a **different vertex**, where `q = (div (−2y +
2^62) 4)` sits at `(2^62−1)/4` — fractional.  The leaf accepted on
feasibility alone (`Ok(()) ⇒ snapshot ⇒ Sat`), certifying the crude
point's integrality while snapshotting the re-solved vertex's values.
The model gate could not catch it downstream: the mod atom is a SETTLED
SAT polarity (the wrong feed is exactly what the search committed), and
the gate's settled-atom arm trusts committed polarities by design.  The
small-constant twins (`C = 12, 8, 100…`) answer correctly because the
div/mod case-equality rows land in the Diophantine/HNF layer, which
refutes the parity shape before any B&B leaf exists; the wide constant
(`2^62` exactly — `C = 2^62 ± 1` is genuinely `sat`) makes that layer
decline, exposing the leaf.

**The fix** (mirror of `try_eq_incumbent`'s existing discipline): the
B&B leaf re-scans integrality AT the re-solved vertex — a newly
fractional vertex branches there (the node loop continues with it), a
newly underivable one declines, only a still-integral vertex snapshots.
The integral dive's base case takes the same belt-and-braces re-scan
after its `state_feasible` probe (the probe's `crash_basis` re-derivation
replaces the very entries the scan read).  No correct `sat` is lost: a
re-solved vertex that is still integral accepts exactly as before; only
fractions that were being published as models now branch.  Regressions:
`bnb_leaf_rescan_rejects_post_resolve_fractional_vertex` and the
bounded twin, in `arith_wide_literal_regressions.rs`, pinning
never-`sat` on the exact reproducer.  The instance now answers honest
`unknown` (the wide-constant parity refutation is beyond this build's
Diophantine reach — a capacity item, not a soundness one).

Corollary recorded for the attribution (A): the "search capacity"
div/mod members are one `check()`-re-optimization away from this same
vertex-flip inside their searches — the leaf re-scan's extra branching
is the correct cost of not publishing fractional vertices.

## Verification (the bar, on the landing tree)

Workspace suite **11 974/11 974** on this build (pre-merge base) and
**11 987/11 987** after merging the then-current main (bag.fold, the
MBQI persistent-model rewrite, item 85's `NIXIE_DELTA_VERIFY` canary);
clippy/fmt/rustdoc clean (one pre-existing dead `if` in the wide-derivation
loop flagged by the new rust-1.96 `needless_ifs` lint was removed — main
landed the identical repair in parallel, merged); Z3 parity **100 %
correct, 0 disagreements** (z3 4.16.0, all logics); wide differential
3 × 300 + mixed differential 3 × 400 fresh seeds (20262120–25) on this
build and again (20262130–35) on the merged tree — **zero verdict
disagreements, zero refuted models** (the pre-fix tree's 20262113 run is
the false-`sat` find above); debug-panic sweep over the parity corpus
(177 files) — zero panics; perf gate **PASS** at counters 1.000/1.000,
wall 1.03 (BASELINE `2b0b4d54`).

**The fixed-seed gap survey re-baselines here** (a documented breakpoint,
not a regression): `gap_survey.py` imports `mixed_fuzz.py`'s generator
verbatim, and the boundary SHAPES change the seed→instance mapping — the
fixed seeds now measure the NEW corpus. Measured on the landing binary:
**150 gap members** (119 SAT-side, 31 UNSAT-side), of which **140 carry
the new wall literals** — dominated by the same div/mod+wide capacity
arms as the 47-member residual (the attribution in A carries over
mechanistically), now with the beyond-width-witness shapes amplified:
`(> x i64::MAX)`-class goals under nested div/mod are honest `unknown`s
where the exact publication channel still declines. Future attribution
runs re-baseline from this file's numbers; the old 47-member table stays
as the pre-SHAPES record.

## Process notes

* The attribution run doubles as the regression baseline check: the
  probe binary is verdict-identical to `precompile/e0bbb32e/nixie` (the
  tags print only at declines).
* `gap_survey.py`'s stderr capture is a keeper: re-attribution is now
  one command with `NIXIE_GAP_PROBE=1`, no probe rebuild needed beyond
  the tags themselves.
* The survey and the two fuzzers run 3-way parallel per seed comfortably
  on 20 cores alongside other agents' builds (~6 min per 600-instance
  seed).

## H. The wide-constant Hermite widening — the parity refutation restored end-to-end (the successor handoff's item 4)

The false-`sat` fix (G) left the exact reproducer an honest `unknown`:
the parity refutation `2y + 4q = 2^62 − 3` is *decidable*, but the
Diophantine layer's Hermite solve refused the system — `MAG_BOUND =
2^40` rejected the `i64`-range `IntEquation` constants at the first
substitution, so every wide-constant equality system was a `GiveUp`
degrading z3's `unsat` to `unknown`.

**The widening** (`lia/hnf.rs`): the blanket `2^40` is split by role.
`try_compute` keeps it (its outputs are `i64` matrices; test-only today).
`solve_integer_eq_system` runs under `MAG_BOUND_SOLVE = 2^63 − 1` — the
full `IntEquation` input domain — with the Euclid pair updates made
CHECKED (`checked_mul`/`checked_add`; the old unchecked form was
justified *by* the `2^40` bound, and that justification is now local to
each operation), and the substitution/consistency/witness accumulators
checked-only (exact within `i128`; a true overflow trips to `GiveUp`,
never a wrap). Entries leaving the bound still trip honestly (the
runaway-growth test pins the chained-Euclid shape), and out-of-bound
INITIAL entries are now simply computed exactly — a divisibility-
decidable row answers even with huge literals, strictly better than the
blanket refusal.

**Measured**: the exact reproducer answers `unsat` (z3 agrees); its
satisfiable twins (`2^62 ± 1`) stay `sat`. The fixed-seed survey drops
**150 → 104 members** — the 46 closed are almost entirely the UNSAT-side
parity class (31 → 3); the residual 104 is 101 SAT-side wall-literal
members, the beyond-width *witness* frontier (model construction, not
refutation) plus 3 stragglers. Timeouts 12 → 7. Gate PASS at counters
1.000/1.000 (wall 1.02); parity 100 % (z3 4.16.0); suite 12 009/12 009;
wide+mixed 3 × 300/400 fresh seeds (20262140–45) zero disagreements;
debug-panic sweep clean.

Unit pins: `solve_wide_constant_parity_refutes` (the `2^62` system,
infeasible core names the identity row), `solve_full_i64_domain_inputs`
(`i64::MIN`-range inputs; wide witnesses stay `Feasible` — the CALLER
narrows through `i64::try_from`), `solve_runaway_growth_still_gives_up`
(growth past `2^63` trips; the same shape a size class down decides).
The e2e regression re-pinned from never-`sat` to the exact `unsat`.
