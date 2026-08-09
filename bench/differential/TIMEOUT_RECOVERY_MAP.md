# Timeout-recovery opportunity map

Where the 145 main timeouts are recoverable from, after the validated re-score
(`VALIDATED_RESCORE.md`) and the UTVPI de-risk. This is a map of *what exists*
and *what gates it*, not a plan.

## The procedures already exist, unwired

main ships complete, tested theory procedures that are **not wired into the
solve path** (zero callers in `oxiz-solver`). Found by sweeping `pub mod`s with
no external references:

| module | lines | tests | scope | wired? |
|--------|------:|------:|-------|--------|
| `oxiz-theories/src/diff_logic` | 2,104 | 25 | pure difference logic (Bellman-Ford negative-cycle) — the literature-exact QF_IDL algorithm | **no** |
| `oxiz-theories/src/utvpi` | 1,917 | 33 | UTVPI (x±y ≤ c), generalizes difference logic | **no** |
| `oxiz-theories/src/nia_cdcl` | — | 4 | CDCL NIA search | yes, into `nlsat.rs:961` — yet QF_NIA is still 1/30 |

So QF_IDL has **two** unused, complete, tested decision procedures
(`diff_logic` for pure difference logic; `utvpi` for the broader fragment). QF_NIA
already invokes `nia_cdcl` and still fails — that is a separate
(effectiveness/gating) problem, not a wiring gap.

## The gate: CDCL(T) theory integration is the bottleneck, not missing procedures

The UTVPI de-risk settled *why* these stay unwired. Driving `utvpi` directly on
the confirmed-portable IDL instances showed qlock and the `queens_bench`
family are **Boolean combinations of IDL atoms**, not pure conjunctions:

- `qlock-4-10-7` body: `and`=3940, `or`=347, `not`=375, `=`=1169, `<=`=112.
- `super_queen30-1` body: one `and` of **1419 `(not (= …))` disequalities** + 30 `<=`.

A pre-check short-circuit (decide a pure conjunction upfront, like main's
`equality_transitivity_preprocess`) therefore **does not apply** — the
disequalities and disjunctions need the SAT layer to split them. Recovering
these means wiring `diff_logic`/`utvpi` as a **theory inside the CDCL(T) loop**
(SAT assigns the IDL atoms; the theory checks consistency), not a preprocessing
tactic.

That is exactly the layer this project has shown is unreliable: `bench_679` is a
CDCL(T) theory-dispatch gap (bvule atoms never reach `process_constraint` — 0
calls vs 2–45 for normal BV). Wiring any new theory there risks the same class
of dispatch bug. **The "bounded" framing does not survive the de-risk**: the IDL
recovery is a full theory-integration project in the codebase's demonstrated
weak area, not a one-mechanism port.

## What this means for the 145 timeouts

- **Recoverable in principle**: the IDL subset has the procedures
  (`diff_logic`/`utvpi`); they are complete and tested. The 7 confirmed
  oz-over-main IDL solves (qlock + 6 `queens_bench`) are real capability that
  main lacks the integration to use.
- **Gated by integration reliability**: until the CDCL(T) theory-dispatch layer
  is trustworthy (bench_679 fixed; a clean theory-wiring seam exists), wiring
  `diff_logic`/`utvpi` is high-risk. The leverage is in making that layer
  reliable *first* — it unblocks IDL *and* de-risks future theory work — rather
  than bolting one theory on and hoping the dispatch holds.
- **Not gated by v0.3.2**: none of this needs the upstream port. It is main's
  own unused code. This firms up the calibration: stop mining v0.3.2; the
  completeness work is main-side (wire main's procedures, fix main's dispatch).

## Suggested sequencing (informing the pivot)

1. **Fix `bench_679`'s dispatch gap** — it is the cheapest, most diagnostic CDCL(T)
   fix (atoms not reaching `process_constraint`) and proves the integration seam
   before any new theory is wired.
2. **Wire `diff_logic` for pure-difference-logic atoms in the CDCL(T) loop**
   (not a pre-check), gated by the asymmetric-trust rule from the review:
   negative-cycle → `unsat` (take it); `sat` → validate the model against the
   original assertions before reporting, else fall through. Reuse the
   model-verification machinery already in the harness/`Model::eval`.
3. Measure `trusted_total` before/after — the `queens_bench` sats only count if
   `diff_logic`'s model validates (oz's don't); the headline could be +1
   (qlock) not +7.

The QF_NIA cluster (1/30 for every build) is separate: `nia_cdcl` is already
wired and not helping, so that is an effectiveness investigation, not a wiring
gap.

## Addendum: the diff_logic chase on qlock (detection proven; propagation wall)

A full CDCL(T) wiring of `diff_logic` was built and driven to root-cause on
`qlock-4-10-7` (pure DL + Eq, 0 disequalities). Findings, so they are not
re-derived:

**Detection works.** Fed conservatively (genuine `x - y ◦ c` differences +
linearized equalities), maintained incrementally via `push`/`pop` at the CDCL
scopes, `diff_logic` **detects qlock's negative cycles**: 3 conflicts, each
returned as a valid `TheoryCheckResult::Conflict` clause of 2-3 literals
(`conflict_from_terms` builds them correctly; nothing is dropped). The
algorithmic core is sound and reaches CDCL.

**The wall: `oxiz-theories/src/diff_logic/solver.rs:258 propagate()` is a
stub.** It is gated on `config.propagate` and its body says "This is a
simplified version — full implementation would require tracking unasserted
constraints"; it does conflict detection only, **no theory propagation**.
Without propagation, CDCL+checker gets only the conflicts that happen to form
in the partial assignments it stumbles into — 3 in 60 s — and never converges
on qlock's Boolean structure. The refutation is *not dropped* (the clauses are
valid); it is too sparse to drive convergence. Landing qlock means implementing
theory propagation in `diff_logic` (track the unasserted DL atoms, derive
implied polarities from the Bellman-Ford shortest-path distances, feed them to
the SAT core as propagated literals) — substantial new algorithm code, not
wiring.

**Red herring, ruled out — do not re-chase:** `encode.rs`'s `TermKind::Let` arm
is a stub that ignores bindings, but it is **harmless for parsed SMT-LIB**: the
parser substitutes let-bound names in the body at
`oxiz-core/src/smtlib/parser/terms.rs:506`/`:1197` (symbol resolution), so by
the time `encode` sees the term the body already contains the binding values.
qlock's atoms ARE real 2-var differences (diff was fed ~17 k of them), not free
variables. (A synthetic `(let (...) (assert ...))` form — let *wrapping* a
command, non-standard — does mis-parse to `sat`, but that is malformed input,
not qlock's cause and not the standard `(assert (let ...))` form qlock uses.)

## CORRECTION: theory propagation IS plumbed (the real wall is diff_logic only)

A prior draft of this section claimed the CDCL(T) framework has no
theory-propagation path. That was wrong. Propagation is delivered by the
return value, not a separate callback method, and that channel is fully built
and exercised in production:

- oxiz-sat/src/solver/mod.rs:106 — TheoryCheckResult::Propagated(Vec<(Lit,
  SmallVec<[Lit; 8]>)>), literal plus reason clause.
- oxiz-sat/src/solver/search_ext.rs:120 and :307 — the mid-search and
  post-final_check paths match Propagated and install them soundly:
  unconditional facts (empty reason) become level-0 units via
  install_theory_units; reasoned ones become two-watched explanation clauses
  via add_theory_reason_clause + trail.assign_propagation (theory_processed
  clamped on backtrack).
- oxiz-solver/src/solver/theory_manager.rs:751 (derive_arith_propagations) and
  :2210 (ite-const axiom propagation) already return Propagated.

So the solver is CDCL(T) with working theory propagation, including
reason/level bookkeeping for conflict analysis. The only real wall is
**oxiz-theories/src/diff_logic/solver.rs:258 propagate() — a stub** (validates
distances, clears pending, returns empty). Landing qlock means implementing the
DL propagation rule there (track unasserted DL atoms; for each, check whether
the current shortest-path distances already imply its polarity — x - y ≤ c is
implied when dist[y] - dist[x] ≤ c — emitting the path edges as the reason) and
returning Propagated from process_constraint, copying derive_arith_propagations
as the template. One crate's algorithm plus a pattern that exists two files
over — not a multi-crate framework feature.

De-risk before wiring: standalone, check whether the DL propagation rule yields
a useful volume of implied literals on qlock's ~17k difference atoms. Useful
volume → wiring is a pattern-copy. Almost none → the sparseness is intrinsic to
qlock's encoding and qlock needs something else; worth knowing before building
the plumbing.


## De-risk result: DL propagation yields useful volume on qlock (wire it)

Standalone check of the DL propagation rule on qlock's 7,518 extracted
difference atoms (greedily-built consistent partial assignments; "atom
x-y<=c implied TRUE iff its negation y-x<=-c-1 conflicts", via diff_logic's
public `would_conflict`):

| consistent subset | unasserted | implied | % |
|------------------:|-----------:|--------:|---:|
| 40                | 7,478      | 500     | 7% |
| 60                | 7,458      | 1,029   | 14%|
| 80                | 7,438      | 1,331   | 18%|

Volume rises with subset size — exactly the dense pruning CDCL needs to
converge on a Boolean-structured DL theory. So the sparseness is NOT intrinsic
to qlock's encoding; wiring propagation is worth it.

Implementation path (pattern-copy, not a framework feature): the propagation
check belongs in `TheoryManager` (which holds the DL atom vocabulary via
`var_to_parsed_arith`), using `diff_logic`'s `would_conflict` for the
implication test, returning `TheoryCheckResult::Propagated` exactly like
`derive_arith_propagations` (theory_manager.rs:1000) — same channel
(search_ext.rs:120/307), same reason-lits construction, same statistics. The
open cost concern is O(unasserted-atoms) per check; if that is too slow it
needs diff_logic to expose single-source shortest-path bounds so the check is
O(1) per atom rather than a `would_conflict` recompute.

## SOUNDNESS CORRECTION: the de-risk's `would_conflict` is unsound as an implication test

The de-risk above greenlit wiring on the strength of "7-18% implied" measured
with `DiffLogicSolver::would_conflict`.  That test is **unsound** as an
implication oracle and over-counts by ~10x; the greenlight was partly built on
sand.  Re-derived and re-measured:

`would_conflict(x, y, c, strict)` reduces to `dist[x] - dist[y] <= c`, where
`dist` is the virtual-source Bellman-Ford distance.  That quantity is only a
**lower bound** on the true shortest path `d(y, x)` (the tightest derivable
bound on `x - y`), so it reports "implied" for bounds that are *not* entailed.
Decisive counter-example: a single asserted edge `a - b <= 5` gives
`dist[a] = dist[b] = 0`, which the test accepts as implying `a - b <= 3` —
false.  A controlled re-de-risk on qlock's 2,135 extracted DL atoms (consistent
partial assignments, sound all-pairs Bellman-Ford implication test) measured:

| consistent subset | unasserted | SOUND implied | unsound (`would_conflict`) |
|------------------:|-----------:|--------------:|---------------------------:|
| 40                | 2,095      | 1.5% (ineq) / 18.6% (incl. eq-TRUE) | 53.0% |
| 160               | 1,975      | 6.0% (ineq) / 55.7% (incl. eq-TRUE) | 68.9% |

The sound volume is real **only after including equality-TRUE propagation**
(transitive equality closure), which main does *not* currently theory-propagate
to CDCL (`propagate_equalities` shares EUF<->arith internally but returns
`Sat`/`Conflict`, never `Propagated`).  Pure *inequality* sound volume is
1-13%, rising with assignment density.  `would_conflict` is retained only for
its (sound) conflict-prediction use; its doc now warns it is not an implication
test.

## LANDED: sound `entailed_reason` / `sssp_from` primitive (diff_logic)

`oxiz-theories/src/diff_logic/solver.rs` now exposes the sound primitive the
chase identified as the single unblocked move:

- `sssp_from(src) -> Option<(dist, pred_edge)>` — real single-source shortest
  path from `src` over the asserted constraint edges (SPFA), with predecessor
  tracking.  This is the SOUND basis: the true `d(src, node)`, not the
  virtual-source difference.
- `entailed_from_sssp(xv, yv, c, strict, dist_from_y, pred_from_y)` — O(1)+path
  entailment test against a precomputed SSSP tree, for amortised propagation.
- `entailed_reason(x, y, c, strict)` — convenience wrapper.
- `get_diff_var(term)` — term->DiffVar lookup.

All sound (require the actual `d(y, x) <= c`), unit-tested (counter-example,
transitive chain, integer strict tightening, bidirectional equality).  **No
solver-path callers** — the primitive is landed and ready for a future sound
wiring; it does not affect any solve today.

## WIRING ATTEMPT (built, found 3 defects, reverted)

A full CDCL(T) wiring was built on top of the primitive (on-demand
`diff_theory_check` in `TheoryManager`, throttled in `on_assignment`,
reporting DL negative-cycle conflicts via `conflict_from_terms` AND
entailment propagations via `entailed_from_sssp`).  It found three defects,
each fixed; the third was not closeable and the wiring was reverted.

**qlock DID reach `unsat` — but only unsoundly.**  Reporting the DL
negative-cycle conflicts (handover rail #1) closed qlock-4-10-7 in ~0.06 s on
an early build.  That result was **unsound**: it relied on defect (1) below.
After fixing (1), the sound wiring needs **~192 s** on qlock (a timeout in the
10 s gate), so qlock-4-10-7 is **not** closed soundly within budget.

1. **Equality-constant feeding bug** (false refutations).  `feed_dl_atom` fed
   every equality as `x - y <= 0 ∧ y - x <= 0` (constant ZERO), ignoring the
   atom's parsed constant.  qlock has 713 difference-equalities with non-zero
   constant (`(= (- a b) k)`, k != 0); DLX1C0 / QF_UFIDL likewise.  Feeding the
   wrong constant manufactured spurious negative cycles → false `unsat` on
   SAT instances.  Fix: feed `x - y <= c ∧ y - x <= -c`.  (This fix is what
   turned qlock from 0.06 s to 192 s: the 0.06 s was the unsound run.)
2. **Bit-vector sort bug** (false refutations).  `encode.rs` stores `bvule`/
   `bvult` comparisons in `var_to_parsed_arith` as `Le`; the wiring mis-read
   them as integer difference edges → spurious cycles → false `unsat`/crash on
   `gryzzles.*` (QF_BV) and others.  Fix: gate to Int/Real-sorted operands only.
3. **Propagation unsound for DL-fragments-in-larger-formulas** (false `sat`).
   ISOLATED and verified.  `xs-08-20-3-2-4-5` (QF_UFLIA, z3=unsat) answered
   `sat` under the wiring; baseline answers timeout (sound).  Controlled tests:
     - period=1 (DL check every assignment): timeout (sound).
     - period=8 (throttled) + final-check conflict backstop: `sat` (unsound).
     - propagation DISABLED (conflict-only), period=8: timeout (sound).
     - Each individual propagation passes an independent re-derivation check
       (rebuild a DL graph from only its reason atoms; the reason re-derives
       the propagated literal), and the wrong-`sat` full assignment is itself
       DL-consistent (the final-check backstop finds no negative cycle).
   ROOT CAUSE: the 34 DL atoms in xs-08-20 are a *pure-DL fragment* (plain Int
   variables, not UF applications) embedded in a larger QF_UFLIA formula.  DL
   **conflicts** are always sound (a negative cycle is a pure arithmetic
   refutation in any theory combination).  DL **propagation** is sound only
   when DL is the COMPLETE theory for the formula: when the DL atoms are a
   fragment, propagation (even with individually-sound reasons) *steers the
   search* toward a DL-consistent-but-globally-inconsistent full assignment
   that the incomplete UF/arith final-check then accepts as `sat`.  Without
   propagation the search does not commit to that branch and times out.
   SOUND GATE: enable propagation only when every arithmetic atom is a DL
   atom (`dl_atoms.len() == var_to_parsed_arith.len()`), i.e. pure difference
   logic; otherwise conflict-only.

With (1)+(2) fixed AND propagation gated to pure-DL, the gate is SOUND (4
unsound = exactly the pre-existing known guards, zero regressions) and
NET-NEUTRAL (solved 125, agree 121 — identical to baseline).  The full-wiring's
apparent +4 solves (125->129) were on mixed UF+IDL formulas where propagation
is unsound; gating them out removes both the gains and the unsoundness, landing
at neutral.  qlock-4-10-7 still times out (192 s).  The whole `TheoryManager`
wiring was reverted (net-neutral, does not meet the qlock bar, adds complexity);
the sound primitive in `diff_logic` stays.

## What a sound, budget-closing wiring still needs

- A sound propagation gate is known (pure-DL only); the open problem is
  *completeness*: even sound, the on-demand rebuild + per-call all-pairs SSSP
  is too slow to densify conflicts enough for qlock (192 s vs 10 s budget).
  A budget-closing wiring likely needs *incremental* difference-logic
  maintenance (feed in `process_constraint`, push/pop at scopes — the chase's
  original design) with incremental shortest-path update (Cotton-Maler), not
  on-demand rebuild.  The landed `sssp_from`/`entailed_from_sssp` primitive is
  the right query layer for that.
- Note the asymmetry for future work: DL conflicts are safe to wire ungated
  (always sound); DL propagation must be gated to pure-DL (or made
  final-check-complete) or it manufactures wrong sats on mixed formulas.

## Incremental DL-as-primary experiment (built, 0 conflicts, reverted)

Hypothesis: arith's general simplex is the slow path on qlock; a Bellman-Ford
DL solver fed *incrementally* in `process_constraint` and checked *before*
`arith.check()` would catch difference-logic conflicts faster and close qlock.

Built it: `DiffLogicSolver` field on `Solver`, `&mut` to `TheoryManager`, fed in
`process_constraint`'s Lt/Le/Gt/Ge and Eq arms (correct eq-constant + plain-
operand + Int/Real gate), `push`/`pop` at theory scopes, `reset` at all 5 sites,
`trail.rs` destructure updated.  Per-atom `diff.check()` before `arith.check()`.

**Result: 0 DL conflicts on qlock, ever.** Instrumented feed+check trajectory
(fed=4000 in 12 s, dense graph: 4573 constraints / 176 vars) — `check()` AND an
independent all-pairs `sssp_from` scan both report **zero negative cycles** at
every partial assignment CDCL explores.  Yet arith (same difference constraints)
does find conflicts (that is how the sound on-demand version reached `unsat` in
~192 s).

**Root cause of the 0:** qlock's partial-assignment DL graphs are genuinely
consistent.  Its unsat requires the *full* assignment — or, equivalently, the
EUF-derived transitive equalities that arith receives via
`propagate_euf_equalities_to_arith` / `assert_explained_equality` but the DL
solver does not.  DL's own Bellman-Ford derives transitive difference bounds,
but only over the *directly asserted* atoms; it does not see the EUF congruence
merges arith gets.  So DL is complete only over its asserted fragment, and on
qlock that fragment stays feasible until the full assignment.

Reverted (the per-atom Bellman-Ford is pure overhead at 0 conflicts; net-
harmful).  The sound foundation (on-demand `diff_theory_check`, commit ebaf571)
stays.

**Next layer to close qlock via DL** (not done): feed EUF-derived equalities
into the DL graph too — i.e., when `propagate_euf_equalities_to_arith` asserts
`t1 = t2` to arith, also feed `t1 - t2 <= 0 ∧ t2 - t1 <= 0` to DL (when both are
plain Int/Real terms).  Then DL's graph would carry the same transitive
equalities arith has, and its Bellman-Ford would detect the same conflicts
faster.  This is the EUF×DL integration layer; unverified.

## z3/cvc5 reference + profiling: qlock's bottleneck is the CDCL search, not any theory procedure

Consulted the z3 and cvc5 source trees (`/media/data/proj/temp/{z3,cvc5}`) and z3's
runtime stats on qlock-4-10-7:

- z3 solves qlock in **0.04 s** via the standard **SMT tactic (CDCL + theory_arith)** —
  no difference-logic-specific tactic (its `diff_neq_tactic` targets a bounded
  `k<=x / x<=k / x-y!=k` fragment that qlock's equalities don't fit; `-v` shows
  restarts/decisions/clauses = the SMT engine).  cvc5 likewise has no dedicated DL
  solver (simplex only).
- z3's effort: **1265 decisions, 601 conflicts, 183 193 propagations (124 k binary),
  64 simplex pivots, 295 row-summations, 5 restarts.**  It is propagation-dominated
  with a tiny search and a nearly-free simplex.

Controlled experiments on oxiz (all reverted; foundation `diff_theory_check` stays):

| change | qlock (30 s cap) |
|--------|------------------|
| baseline (arith simplex) | timeout |
| + sound DL conflict+propagation (foundation) | ~192 s → unsat |
| + incremental DL as primary (feed every atom, check before simplex) | timeout |
| + raise arith-propagation gate (1024→20000) + run it mid-search | timeout |
| **skip `arith.check()` entirely in the Lt/Le/Gt/Ge arm** | **timeout** |

The last row is decisive: removing the simplex check entirely does not speed qlock
up, so `arith.check()` is **not** the bottleneck.  DL wiring, arith propagation,
and DL-primary all fail to converge in budget.  Combined with z3 converging in
1265 decisions / 0.04 s, the bottleneck is **oxiz's CDCL search efficiency itself**
on qlock's Boolean structure (branching / restarts / clause learning), not a missing
or slow theory procedure.

**Conclusion / redirect.**  The difference-logic procedure (the chase's focus) is
sound and correctly wired (it detects the same negative cycles arith does — verified
`CONFLICT_AGREE`), but it is **not** qlock's lever.  Closing qlock needs CDCL/search-
efficiency work in oxiz (the ~4800x per-search gap vs z3), which is a different
class of effort than theory wiring.  The sound DL primitive + on-demand check
(commits ebaf571 / e174b75) remain as a sound, net-neutral foundation usable by
future pure-DL tactics; they just do not close qlock.

## CDCL profiling on qlock (where the ~4800x gap lives)

Instrumented the search loop (decisions/conflicts/propagations/restarts + per-phase
time).  z3's qlock recipe for reference: **1265 decisions, 601 conflicts, 183 193
propagations, 5 restarts, 0.04 s** (propagation-dominated, tiny search).

oxiz on qlock (foundation build, 3 s samples):

| config | decisions/3s | conflicts/3s | propagations/3s | restarts | theory% |
|--------|-------------:|-------------:|----------------:|---------:|--------:|
| foundation (DL on-demand check) | 189 | 7 | 2 418 | 0 | 99% |
| DL check disabled | 7 448 | 480 | 12 836 | 4 | 96% |
| DL disabled + `arith.check()` disabled | 27 166 | 1 327 | 116 271 | 13 | 81% |

Findings:
- **The theory layer is 81-99% of runtime** on qlock (SAT propagate ~=0%).  The
  per-`on_assignment` theory work (EUF intern/merge + arith assert/check + the DL
  check) is ~100-200x slower per call than z3's theory.
- **The foundation's on-demand `diff_theory_check` is ~97% of theory time** — it
  rebuilds a fresh DL solver from the whole trail every Nth assignment (O(trail)
  per call).  Disabling it speeds the search **40x** (189->7448 decisions/3s) and
  restarts begin firing.
- **But disabling the DL check makes qlock STOP converging** (times out at 30s
  instead of the foundation's 192s -> unsat).  The DL check, though slow, supplies
  the pruning (DL conflicts/propagation) that lets CDCL converge.  So it is a
  trade-off, not pure harm: the foundation keeps it because 192s->unsat beats
  timeout.
- `arith.check()` is a further ~3.6x per-search cost (necessary — it supplies the
  conflicts; skipping it loses convergence).
- **The fundamental blocker**: even with theory maximally cheap (DL+arith.check
  off), oxiz does **46 013 decisions in 9s without converging** vs z3's 1265.
  oxiz's CDCL needs ~36x more decisions on qlock's Boolean structure (branching /
  clause-learning quality).

**What closing qlock actually needs** (all three, in priority order):
1. Cheap DL pruning: replace the on-demand rebuild with *incremental* DL
   maintenance + incremental SSSP (Cotton-Maler), so the pruning that drives
   convergence costs O(affected) not O(trail).  This is the single biggest win
   (the rebuild is 97% of theory time).
2. Cut the EUF+arith per-`on_assignment` cost (the residual 81-96%).
3. Improve CDCL decision efficiency (the 36x decision gap vs z3) — the deepest,
   least-localized issue.

The profiling instrumentation is not committed (stderr noise); re-apply the
`'search`-loop timed dump in `search_ext.rs` to reproduce.

## Landed improvements (two net-positive commits on top of the foundation)

The CDCL profiling above identified the on-demand `diff_theory_check` rebuild as
97% of theory time.  Replaced it with an *incremental* difference-logic solver:

1. **`e859a63` — incremental SSSP DL solver.** `DiffLogicSolver::add_leq_check`/
   `add_lt_check` use seeded SPFA (O(affected) per edge, maintaining cached
   distances) instead of full Bellman-Ford; fall back to full `check()` only on a
   detected cycle or after push/pop.  `DiffLogicSolver` is now a field on `Solver`
   (push/pop/reset threaded through all 5 reset sites + `trail.rs`), fed per atom
   via `diff_primary_conflict` (short-circuits arith.check for pure-DL), with a
   `final_check` conflict backstop.  3 new unit tests.  Gate: solved 125,
   agree_z3 **122 (+1 vs baseline 121)**, disagree 3.

2. **`7712714` — DL propagation via the incremental solver (no rebuild).**
   `derive_diff_propagations` queries the maintained `self.diff` (per-source
   `sssp_from`, per-call cache), gated to pure-DL.  Gate: solved **126 (+1)**,
   agree_z3 122, disagree 4 — all four disagreements are the known pre-existing
   guards (none QF_IDL/DL), so no new DL unsoundness.

Cumulative vs baseline (origin/main b7b6645): **solved 125→126, agree_z3
121→122**, soundness unchanged (only the known pre-existing disagrees).  These
are real completeness/accuracy gains from the DL work, stackable and
gate-verified.

**qlock-4-10-7 remains open.**  Its convergence is trajectory-fragile (~192 s
with the old on-demand propagation; timeout with the incremental conflict-only
build; does not converge in 120 s with the incremental propagation build).  The
blocker is oxiz's CDCL decision efficiency (z3 needs 1265 decisions on qlock;
oxiz needs 36x+ more, even with theory maximally cheap).  `theory_aware_branching`
is already on by default.  Closing qlock needs SAT-engine work (branching /
clause-learning quality / the per-`on_assignment` EUF+arith cost), which is the
next layer and a different class of effort than theory wiring.

## CDCL decision/branching profiling on qlock — deep conflicts (level ~140 vs z3's 2)

Instrumented conflict backtrack-level + learnt-clause size.  z3's qlock: ~2
decisions per conflict (shallow conflicts, aggressive learning).  oxiz (current
incremental-DL build, 3 s samples):

| t | decisions | conflicts | avg conflict level | avg clause size |
|--:|----------:|----------:|-------------------:|----------------:|
| 3 | 189 | 7  | **91**   | 3.0 |
| 9 | 502 | 21 | **140**  | 2.8 |

**oxiz's conflicts are at decision level ~140** (z3's are at ~2).  The learnt
clauses are short (good, ~3 lits) but learned at deep levels, so each conflict
backtracks only slightly and the search stays deep — it churns ~27 decisions
per conflict vs z3's ~2.  The theory detects the *same* conflicts as arith
(verified `CONFLICT_AGREE`); DL propagation fires (≈14 k propagations over 400
calls), but it is equality-focused and does not steer toward the shallow
*inequality*-bound conflicts the way z3's bound propagation does.

**Root cause = search guidance, not theory capability.**  z3's branching +
bound propagation reach qlock's DL-inconsistent combinations at decision level
~2; oxiz reaches them at ~140.  Closing qlock therefore needs CDCL-side work —
branching that prioritizes conflict-relevant (inequality) atoms, or theory
propagation that forces those bounds densely — neither of which the current
VSIDS + equality-DL-propagation provides.  This is the deepest, least-localized
remaining blocker and a different class of effort than the theory wiring that
already landed (+1 solve, +1 agree).

## Deepest root cause: oxiz's arith entailment is per-atom simplex probing, not incremental bounds

Option (b) — enable `derive_arith_propagations` (the existing arith bound
propagation) for qlock — produced **zero** propagations: it is called but
`comparison_entailed_reason` returns `None` for every atom (or is too expensive
to run densely).

Why: `ArithSolver::comparison_entailed_reason` is a *sound per-atom simplex
probe* — for each candidate atom it pushes the atom's negation, runs
`simplex.check()`, pops.  That is O(simplex-check) per atom, so a full pass over
qlock's ~3k atoms is ~3k simplex solves — exactly why the method is capped at
1024 atoms.  Enabling the cap for qlock makes each pass too slow to fire densely
(and at the sparse points it does fire, no atom is yet forced).  z3/cvc5 close
qlock via `arith-bound-prop` driven by **incremental bound tracking** (each
assertion tightens variable bounds in O(1); a cheap sweep infers implied bounds),
not per-atom re-solving.  oxiz's general simplex has no incremental bound layer,
so it cannot do the dense bound propagation that (a) supplies z3's 183k
propagations and (b) forces the shallow (level ~2) conflicts.

**This is the real qlock blocker**, and it reframes the whole chase: the
difference-logic procedure (`diff_logic`) was not the lever.  The DL work landed
sound, incremental, and net-positive (+1 solve, +1 agree), but qlock needs an
**incremental bound-tracking layer in the arithmetic solver** (or a dedicated
QF_IDL tactic with cheap bound propagation) — a major arithmetic-solver effort,
not theory wiring.  NOTE: that routing already exists — `derive_diff_propagations` queries
`DiffLogicSolver::entailed_from_sssp` (O(1) against the maintained distances)
and *does* fire densely on qlock (~14k propagations).  Yet qlock's conflicts stay
at level ~140.  So cheap DL bound propagation alone does NOT force the shallow
(level ~2) conflicts z3 gets.  The deepest remaining blocker is therefore the
**CDCL branching heuristic**: z3's branching reaches qlock's DL-inconsistent
combinations at decision level ~2; oxiz's reaches them at ~140, regardless of
how densely the theory propagates.  Closing qlock needs branching that
prioritizes conflict-relevant (inequality) atoms — a SAT-engine investigation,
not more theory wiring.

## Branching investigation: `theory_aware_branching` is a no-op; boosting theory atoms doesn't shallow conflicts

Read the decision path (`pick_branch_var`, `decide.rs`): cadical-style
VMTF/VSIDS with focused/stable modes, domain priority, optional external/LRB/CHB.
**`theory_aware_branching` is set `true` by default but is never passed to the
SAT solver nor consulted in `pick_branch_var`** — it is a no-op.  The only
theory influence on branching is encode-time `bump_decision_hint` (care-graph
atoms) and an `ite_table` activity bump; there is no mid-search theory-driven
branching.

Tested the obvious fix — boost every theory-atom var's VSIDS activity once before
search (prioritize theory atoms over qlock's 48 Bool vars).  qlock **still times
out**; the conflict level did not shallow.  So prioritizing theory atoms alone
does not break the deep-conflict (level ~140) dynamic.  The atoms that form
qlock's 2-3-literal neg-cycle conflicts get *assigned* at deep levels regardless
of activity — the deep-conflict behaviour is a property of oxiz's CDCL dynamics
on qlock's Boolean+DL structure, not a simple branching-order issue.

**Conclusion of the qlock chase.**  Across every layer — DL procedure (sound,
incremental, +1 solve/+1 agree landed), DL/arith conflict detection (redundant),
DL propagation (fires 14k, conflicts stay deep), arith bound-propagation (per-
atom simplex probe, finds nothing), CDCL branching (theory_aware_branching is a
no-op; theory-atom boost doesn't help) — qlock's closure is blocked by oxiz's
CDCL producing conflicts at decision level ~140 where z3 produces them at ~2.
This is a deep SAT-engine characteristic (conflict-depth / learning dynamics on
this formula class), not addressable by theory wiring.  The DL improvements that
landed are real and stand on their own.

## Conflict-depth root cause: qlock's theory conflicts are *diverse* — each involves a fresh (unfocused) atom

Instrumented `analyze_theory_conflict` (conflict.rs) to dump, per theory
conflict, the backtrack level and the VSIDS activity of the learnt-clause atoms:

| n | level | size | min_act | avg_act |
|--:|------:|-----:|--------:|--------:|
| 0 |  51 | 3 | **1.00** | 1.00 |
| 3 |  85 | 3 | **1.17** | 2.22 |
| 6 | 145 | 3 | **1.36** | 3.64 |
| 9 | 179 | 3 | **1.59** | 5.30 |

`min_act` stays ≈ 1.0 (VSIDS baseline — an atom never bumped before) across the
first 10 conflicts, even though `avg_act` rises (the repeated atoms do get
bumped).  **Every theory conflict involves at least one fresh, never-bumped
atom.**  That fresh atom is low-priority, so it is decided late (deep), and the
conflict only forms once it is finally assigned.  Theory conflicts DO VSIDS-bump
their atoms (`vsids.bump_batch`, conflict.rs:1067) — the problem is that qlock's
~3k atoms mean each conflict introduces yet another fresh atom, so the
branching can never focus on a small conflict-relevant set the way z3 does
(z3: 1265 decisions, level-~2 conflicts → focused).

**This is the conflict-depth root cause and it is fundamental**: qlock's
difference-logic unsat spreads its refutable combinations across many atoms, and
oxiz's CDCL produces diverse (non-focusing) theory conflicts as a result.  No
tweak tested changes it: chronological-backtracking off (assertion level itself
is deep), theory-atom activity boost, dense DL propagation (14k, equality-
focused).  Closing qlock needs the CDCL to *focus* — e.g. a learning-rate /
conflict-history heuristic that resists fresh-atom drift, or a dedicated QF_IDL
search that bounds the conflict atom set — a SAT-engine research problem, not
theory wiring.  The DL improvements that landed (+1 solve, +1 agree) are
unaffected and stand on their own.
