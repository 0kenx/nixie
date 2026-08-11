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

## z3 A/B proof: bound-propagation and simplification are NOT qlock's levers — it's CDCL + encoding

The preceding sections *inferred* that qlock's deep conflicts are a CDCL
characteristic, not a theory gap.  Traced against z3 4.16 (source at
`/media/data/proj/temp/z3`) to settle it definitively — and the
theory/simplification levers are now **disproven by direct A/B**, not just
inferred.

z3 solves qlock-4-10-7 in 0.04 s (unsat): 601 conflicts / 1265 decisions =
**2.1 decisions/conflict** (shallow).  Its arith theory is a bystander:
`:num-checks 1`, `:arith-conflicts ≈ 5` of ~600 — qlock is a *boolean-CDCL*
problem for z3.  Disabling the suspected levers one at a time:

| z3 config                                     | conflicts | decisions | dec/conflict |
|-----------------------------------------------|----------:|----------:|-------------:|
| baseline                                      |       601 |      1265 |         2.10 |
| `arith.propagation-mode=0` (bound-prop OFF)   |       544 |      1287 |         2.36 |
| elim-unconstrained + solve-eqs OFF            |       566 |      1096 |         1.94 |
| simplification OFF                            |       601 |      1265 |         2.10 |

Shallow conflicts survive **every** disabling.  Conclusions:

- **Bound propagation is not the lever** — the "needs an incremental bound
  layer" framing (`d4fdd30`) is disproven; do not pursue it for qlock.
- **Simplification / variable elimination is not the lever either.**
- The theory path is irrelevant to z3's win (theory check runs once).

This converts the "CDCL characteristic" conclusion from inference to **proof**:
the gap is on the SAT/encoding side.  The one concrete lead the trace surfaced
is **encoding size** — z3 internalizes qlock to **2896** bool vars; oxiz to
**4450** (+54%), with z3 emitting a binary-clause-heavy core
(`:mk-clause-binary 12799`) that gives BCP the power to conflict shallowly.
Combined with the fresh-atom conflict drift above, the actionable directions are
(a) an encoding audit to close the 2896-vs-4450 var gap, and (b) a CDCL
learning/focus heuristic that resists fresh-atom drift — both SAT-engine work,
neither theory.

(The `OXIZ_TRACE_DECISIONS` tracer, commit `37cf44d`, produced the oxiz-side
data — theory-assign 72% (DL, mean level ~147), theory-prop 0%, final-check 0%.
theory-prop 0% is structurally expected: a sound forward propagator derives only
entailed literals, which by definition cannot conflict — so it carries no
actionable signal, consistent with z3's theory being idle.)

## BCP-power measurement: encoding is not the deep-conflict cause either — it's CDCL dynamics

The encoding lead above (oxiz 4450 vs z3 2896 bool vars) suggested oxiz's
encoding might be BCP-poor.  Measured directly via the tracer's new
propagation count (commit `02490fc`): oxiz does **229 propagations/conflict**
on qlock vs z3's **305** — comparable (oxiz ~25% lower), not an order of
magnitude.  And z3 stays shallow (1.94 dec/conflict) even at 3550 vars with
elimination disabled.  So neither var count nor BCP power explains the gap.

This narrows the qlock blocker to **CDCL dynamics** alone: oxiz's
conflict-learning/branching fails to *focus* on qlock's structure (the
fresh-atom drift of `bf70532`), producing deep (~147), non-converging
conflicts where z3's converge shallowly.  The encoding audit is therefore
**deprioritized**; the lever is a CDCL focus/learning heuristic (resist
fresh-atom drift, or a conflict-depth-aware restart/learning policy), not
encoding and not theory.

## LRB/CHB prototype: neither resists qlock's fresh-atom drift

Switched the branching heuristic (cadical-style VMTF/VSIDS is the default) to
LRB (`use_lrb_branching=true`) then CHB (`use_chb_branching=true`) — the two
cadical heuristics designed to focus on productive variables and resist exactly
the fresh-atom drift identified above.  **Both still time out on qlock-4-10-7**
(30 s); the conflicts stay deep.  So no available branching heuristic in oxiz
(VMTF/VSIDS/LRB/CHB), nor disabling chronological backtracking, nor theory-atom
activity boosting, shallows qlock's theory conflicts.

**Final conclusion of the conflict-depth chase.**  qlock's deep (level ~140)
theory conflicts are robust to every CDCL-side intervention tested.  The
fresh-atom drift (each conflict introduces a never-bumped atom) is intrinsic to
how oxiz's CDCL(T) interacts with qlock's spread-out difference-logic unsat.
Closing qlock is not a config/heuristic toggle — it would need a structural
change (a dedicated QF_IDL decision procedure that doesn't rely on generic
CDCL(T) conflict-driven search, or a fundamentally different theory-propagation
strategy that pre-focuses the conflict atom set).  That is beyond theory wiring
or branching tuning.  The two net-positive DL improvements (+1 solve, +1 agree)
stand regardless.

## BREAKTHROUGH: the qlock "CDCL wall" was the branching heuristic — VSIDS solves qlock-4-10-7

The "deep SAT-engine characteristic / unfixable CDCL wall" conclusion
(`a409238`, `bf70532`) is **disproven**: it was the branching heuristic.
Systematic A/B across branching modes (made trivial by the committed
`OXIZ_TRACE_DECISIONS` tracer, `37cf44d`/`02490fc`):

| branching (oxiz config)        | qlock-4-10-7   | mean conflict level | qlock-4-10-10 level |
|--------------------------------|----------------|--------------------:|--------------------:|
| VMTF focused (current default) | timeout        |               ~147  |               ~147   |
| CHB                            | timeout        |               ~211  |               —      |
| **VSIDS**                      | **✅ unsat**    |              **36.6** |             106.8   |

**VSIDS solves the target instance** (exit 0) and shallows conflicts 147→37.
It is not a blanket cure (4-10-10/14/17 still time out, though VSIDS improves
them: 147→107), but the central blocker is broken.

**Root cause:** oxiz defaults to VMTF-focused (`enable_stabilize: true` +
`use_vmtf: true`), which *should* periodically switch to stable VSIDS
(cadical-style dual mode), but on qlock the baseline trace was **100% Vmtf** —
the stabilize switch (gated by `stabilize_base: 5000` ticks) never effectively
engages within the timeout.  z3/cadical lean on stable VSIDS, which is exactly
what fixes it.

**Caveats — do NOT blindly flip the default:** oxiz ships VMTF-focused for a
reason (avg/SATcomp performance); a blanket VSIDS flip could regress the
differential suite, and VSIDS doesn't fully close the gap (4-10-10 still ~107
vs z3's ~2).  Candidate fixes, in order of cheapness: (1) lower `stabilize_base`
(5000→~500) so stable VSIDS engages sooner — keeps the dual-mode design; (2)
per-logic VSIDS preference for QF_IDL/QF_LIA.  Both need differential-suite A/B
validation before landing.

## VSIDS A/B on the differential suite: NET REGRESSION — do not ship VSIDS as default

The VSIDS breakthrough above (`d703a32`) solves qlock-4-10-7, but only **slowly
(~58 s)**, and the differential-suite A/B (270-instance pinned sample,
`--timeout 10`, VMTF-default vs pure-VSIDS binaries) shows VSIDS is a **net
regression**:

| metric               | VMTF (default) | VSIDS   | delta |
|----------------------|---------------:|--------:|------:|
| solved               |            127 |     124 |   −3  |
| agree_z3             |            123 |     119 |   −4  |
| disagree_soundness   |              4 |       5 |  +1 ⚠️ |
| timeout_or_unknown   |            143 |     146 |  +3   |
| PAR-2                |        2969.24 | 2995.10 | +25.9 |

Per-instance trade: VSIDS **gains 2** (QF_AUFLIA/storecomm unsat ✓; QF_UFLIA/
mathsat xs-08-20-3-2-4-5 — but oxiz=sat vs z3=unsat, the new soundness
disagreement) and **loses 5** (QF_IDL/queens_bench, QF_UFIDL/RDS ×2, QF_UFLIA/
mathsat ×2).  Note qlock-4-10-7 is **not** in the 270-sample, so this is
VSIDS's effect on the *general* suite — and it **regresses other QF_IDL/UFIDL
instances** (queens_bench, RDS) even while it helps qlock-4-10-7.

**Conclusions:**
- Pure VSIDS is **ruled out** as a default (−3 solved, +1 soundness
  disagreement, worse PAR-2).
- VSIDS is **inconsistent within QF_IDL** (helps qlock-4-10-7, hurts
  queens_bench) — so per-logic VSIDS for QF_IDL is *not* obviously safe either.
- The new soundness disagreement (mathsat xs-08-20-3-2-4-5: oxiz sat, z3 unsat)
  needs model validation — likely a latent issue surfaced by the different
  search path, not a VSIDS-introduced unsoundness, but unconfirmed.
- The qlock-4-10-7 solve (58 s) is real but isolated and not worth the suite
  cost.  `stabilize_base` tuning (keeps dual-mode) is still untested and may
  avoid the regression, but VSIDS-pure is dead.

## mathsat xs-08-20-3-2-4-5 wrong-sat VALIDATED — it is the KNOWN xs_* QF_UFLIA bug, not VSIDS-introduced

The "+1 soundness disagreement" flagged in the VSIDS A/B above (`159596f`) is
**not a new or VSIDS-introduced unsoundness.**  Validated:

- `xs-08-20-3-2-4-5` (QF_UFLIA, mathsat/Wisa): oxiz **sat** (1.14 s, **zero
  conflicts**, no model, no honesty-gate trigger); z3 **unsat** (with proof);
  `:status unsat`.  Failure mode = QF_UFLIA encoding-completeness gap (immediate
  sat, no search).
- It is a **sibling of the already-pinned** `xs_8_13` (QF_UFLIA, in
  `known_unsound_regressions.rs`, `#[ignore]`d as a pre-existing main bug).
- `xs_8_13` itself wrong-sats under **both** VMTF and VSIDS → the bug is
  **branching-independent**; VSIDS merely reaches the sibling instance within
  the 10 s bench timeout (VMTF times out at 90 s on that specific file).

**Conclusion:** VSIDS introduces **no new soundness issue**.  The VSIDS A/B's
real cost is the perf regression (−3 solved / −4 agree / worse PAR-2), not
soundness.  `xs-08-20-3-2-4-5` can be added as a second guard for the existing
`xs_8_13` QF_UFLIA bug class if desired, but it is not a regression caused by
the branching change.

## QF_UFLIA false-SAT (xs_8_13 / xs-08-20-3-2-4-5): full root-cause trace — fix needs difference-bound machinery

Traced the `xs_*` QF_UFLIA wrong-sat to a precise mechanism.  **The fix is not a
patch**: it needs arithmetic machinery oxiz currently lacks (difference-bound
propagation or per-term LP optimization).  Trace below.

**Symptom.** oxiz answers `sat` (0 conflicts, no model, honesty-gate blind) on
`xs-08-20-3-2-4-5` / `xs_8_13` (QF_UFLIA, z3 unsat w/ proof, `:status unsat`).
A format-string counter: `arg1 = arg0 + 4*s_count(D) + 4*x_count(D)`,
`D = (fmt1-2)-fmt0`, with `s_count`/`x_count` `ite`-defined over indices `0..5`
and arithmetic forcing `s_count(D)+x_count(D) >= 5` (infeasible).  Adding an
**explicit** `(or (= D 0) … (= D 4))` makes oxiz say **unsat** (confirmed on the
let-expanded form).  So oxiz is complete *given* D's domain — it just never
*derives* D's domain.

**Why the existing fix is blind to it.** `refine_int_case_split`
(`int_case_split.rs`) already targets exactly this bug (its doc comment says so):
it collects integer UF-args (`collect_int_uf_args`), bounds them
(`compute_int_bounds`), and emits `(or (= t lo) … (= t hi))`.  But:

1. `compute_int_bounds` (line ~254) **only uses single-variable facts**
   (`parsed.terms.len() != 1` → skip) — a deliberate soundness guard ("multi-var
   equalities can pin a term to the candidate model's value → false-UNSAT on
   WiSA").  D is defined by the 3-var equality `D - fmt1 + fmt0 = -2`, so it is
   excluded.
2. Even *relaxing* that filter would not help: D's `{0..4}` range comes from a
   **bounded difference** `fmt1-fmt0 ∈ [2,6]`, where both `fmt0`/`fmt1` are
   individually free.  The per-variable interval fixpoint cannot derive a
   difference-bound (it needs one absolutely-bounded variable to start).
3. The **simplex doesn't have it either**: instrumented probe showed D's proxy
   *is* in `arith.term_to_var` (so it is registered), but the simplex has **no
   propagated bounds** for it — standard simplex bound propagation also cannot
   derive a bound on a free difference.  So querying the simplex (attempted via a
   `provable_int_bounds(term)` mirror of `value()`) returns `None`.

**The fix** therefore needs arithmetic machinery that derives D's `{0..4}` soundly:

- **(A) Per-term LP optimization** in the refinement: for each integer UF-arg
  with no propagated bound, run two simplex objective solves (min / max the term
  s.t. the asserted constraints) to get its implied integer range.  Correct but
  ~2 LP solves per candidate per refine round — budget-gate it.
- **(B) Difference-bound propagation** (Fourier–Motzkin eliminate `fmt0`/`fmt1`,
  or a difference-bound matrix) feeding `compute_int_bounds`.  Cheaper if the
  variable graph is sparse, more code.
- Either feeds the resulting `[lo,hi]` into the existing case-split emit, which
  then makes CDCL branch on D and the `unsat` falls out (as the manual-split test
  proved).

This is substantial, soundness-critical arithmetic-solver work (and must be
validated for the false-UNSAT the single-variable guard was protecting against),
not a localized patch.  The false-SAT remains open; `xs_8_13` stays `#[ignore]`d
and `xs-08-20-3-2-4-5` is a second instance of the same class.

## QF_UFLIA false-SAT FIXED — LP-optimization case-split (commit `8784060`)

The xs_* QF_UFLIA wrong-sat traced above is **fixed**.  Added
`ArithSolver::lp_int_bounds(term)`: minimize then maximize the term over the
simplex feasible region (`optimize_linexpr`, primal simplex / Bland's rule) to
get its exact LP-implied integer range `[ceil(min), floor(max)]`, mirroring z3's
`opt_solver::maximize_objective` bound-infer path.  `refine_int_case_split`
queries it as the fallback for UF-args the interval fixpoint cannot bound (the
bounded-difference case, e.g. `D = fmt1-fmt0-2 ∈ {0..4}`).

Sound: `[ceil(min), floor(max)]` is a superset of the true integer range, so the
case-split never excludes a reachable value — the false-UNSAT the single-
variable guard protected against cannot occur (and did not, in validation).

**Validated:**
- `xs_8_13` (QF_UFLIA): now **unsat** (was sat); its `known_unsound_regressions`
  guard un-ignored and **passes live**.
- Differential suite (270 inst, `--timeout 10`): `disagree_soundness` 4→**3**,
  `agree_z3` 123→**124**, `solved` 127 unchanged, PAR-2 flat (+3.3), **zero**
  new soundness disagreements (no false-UNSAT), **zero** solved losses.
- `xs-08-20-3-2-4-5` (larger sibling): now **timeout** instead of wrong-sat
  (soundness fixed; completeness on the largest instance is a separate goal).

This supersedes the "remains open / needs difference-bound machinery" note in
the trace above (`877acc3`) — option (A), per-term LP optimization, is what
landed.  Option (B) (difference-bound propagation) was not needed.

## Incremental bound propagation for vhard (QF_UFIDL) — built, SOUND on the DL family, gated; vhard7 still open

The handover's central premise was validated and refuted in part by direct
measurement.  Implementing the z3 `:arith-bound-prop` analogue for oxiz's
arithmetic solver.

**Premise validated.**  vhard7 is genuinely bound-prop-dependent (UNLIKE qlock,
where the prior chase proved bound-prop is not the lever).  z3 A/B on vhard7:

| z3 config | decisions | conflicts | arith-conflicts |
|-----------|----------:|----------:|----------------:|
| baseline | 1374 | 556 | 330 |
| `arith.propagation-mode=0` (bound-prop OFF) | 21770 | 2169 | 1788 |

Disabling bound-prop inflates z3's decisions 16× on vhard7 (the *opposite* of
qlock, where it barely moved).  oxiz's conflicts sit at decision level ~96 (max
327) vs z3's ~2; learnt clauses are short (mean 3.1) but learned deep.  So
forward-propagating forced arith atoms to CDCL at low levels is the right lever
for vhard7.

**What landed (env-gated `OXIZ_BOUND_PROP`, default off; SOUND).**

1. **Propagation-only single-variable bound tracker** in `ArithSolver`
   (`prop_lower`/`prop_upper` + undo trail, push/pop-scoped).  oxiz's simplex
   encodes every constraint as a *slack row* with the bound on the slack, so its
   `lower`/`upper` arrays carry **no** bound on the original variables — which
   defeats cheap bound propagation.  The tracker records the direct
   single-variable constant bound each `assert_le/ge/lt/gt` implies, plus
   `note_fixed_var` for **genuine** `term = constant` equalities only
   (`genuine_fixed_var`: rhs a numeric constant, lhs a non-constant Int/Real
   term).  Used for propagation only — never by `check()`/feasibility.

2. **`ArithSolver::derive_expr_bound_reasons`** — the cheap (`O(expr)`, no LP
   solve) Dutertre–de Oliveira bound derivation lifted to an arbitrary atom
   expression, reading the tracker (with a slack-derived fallback when
   `tighten`).  SOUND: a relaxation never tighter than the true bound, so any
   atom it forces is genuinely forced.

3. **`TheoryManager::derive_arith_bound_propagations`** — scans unassigned
   `Le/Lt/Ge/Gt` atoms (Eq excluded — the placeholder landmine), derives each
   expression bound, and emits forced polarities as `TheoryCheckResult::Propagated`
   via the existing eager-watched-clause install path.

**Two soundness bugs found & fixed during validation (z3-oracle + 270-instance
differential A/B):**

- **Constant-threshold bug.**  The force check initially passed the atom's RHS
  `constant` *into* the expression derivation and compared to `constant`,
  reading `e + c ◦ c` ≡ `e ◦ 0` instead of `e ◦ c`.  Correct only for `c == 0`
  atoms (why vhard7's `x > 0` ite-conditions appeared to work).  Produced
  false-UNSAT on every atom with a non-zero threshold (QF_LIA SMPT, etc.).
  Fixed: derive the bound on `e` (constant 0), compare to the threshold.

- **Derived-reason insufficiency on dense / UF-mixed logics.**  The tracker's
  single-atom bounds cannot summarize the multi-atom (EUF-congruence /
  tableau-derived) justifications the simplex's Farkas proof uses, so a
  derived-only reason clause can be over-strong.  Measured: 19–21 false-UNSAT
  disagreements on QF_LIA/UFLIA/ANIA.  **Crucially, 0 disagreements on
  QF_IDL/QF_UFIDL** (60-instance sample) — the derived reason is sound on the
  difference-logic family.  So the propagator is **gated to QF_IDL/QF_UFIDL**
  (`is_dl_family`), where it is sound, and disabled elsewhere.

**Soundness gate (270-instance differential, `--timeout 8`, baseline vs
`OXIZ_BOUND_PROP=1` vs `=tight`):**

| config | solved | agree_z3 | disagree_soundness |
|--------|-------:|---------:|-------------------:|
| baseline | 121 | 119 | 2 (pre-existing storecomm/bench_679) |
| `OXIZ_BOUND_PROP=1` (gated) | 121 | 119 | 2 (same pre-existing) |
| `OXIZ_BOUND_PROP=tight` (gated) | 115 | 113 | 2 (same; net-negative: O(tableau) cost) |

`OXIZ_BOUND_PROP=1` is **net-neutral on the suite and SOUND** (zero new
disagreements — the DL-family gate confines it to where the derived reason is
valid).  It closes **vhard4** (+1 vs baseline's vhard2-3); super_queen30-1 and
LamportBakery8 stay correctly `sat`.

**vhard7 remains open (soundly).**  The SOUND derived-reason propagator fires
(~750 propagations over the search, conflicts shallow 96→~80) but does not
converge in timeout.  Three reasons, in priority order:

1. **No transitive/recurrence bounds.**  The tracker holds only direct
   single-variable constant bounds.  vhard7's recurrence (`x1 = Sum(...)`)
   needs the bound on `x1` *derived through the tableau row* once `x0`/`Sum`
   are pinned.  `=tight` runs `Simplex::propagate_bounds` to add these, but it
   is net-negative (O(tableau) per assertion) and still does not close vhard7.
   Closing it needs the *incremental* bound layer (Dutertre–de Oliveira
   per-assert bound tightening, O(affected)) — the handover's part (A) proper —
   not the per-call `propagate_bounds`.
2. **Eager watched clauses lose pruning.**  A SOUND reason is necessarily
   larger (the complete Farkas antecedent set), so the eager
   `add_theory_reason_clause` materializes larger permanent clauses → less
   pruning → more conflicts.  This is exactly the eager-vs-lazy gap the
   handover's part (B) addresses: **lazy `Reason::Theory` propagation**
   (`trail.assign_theory` + on-demand explanation in `conflict.rs`'s
   `Reason::Theory` arm, currently a `break` stub).  Implementing part (B) is
   the single highest-leverage next step — it makes sound propagation cheap
   (no permanent clause) and is required for vhard7.
3. The unsound (constant-bug / ungated-derived-reason) variant closed vhard7-20
   in <0.3 s — *do not restore it*; the speed came from spurious propagations
   that happened to prune a genuinely-unsat formula.

**Net.**  A SOUND, env-gated incremental bound-propagation capability is landed
for the QF_IDL/QF_UFIDL family (closes vhard4, the first new vhard beyond
baseline's vhard2-3, with zero soundness regressions).  Closing vhard7 soundly
is gated on part (B) lazy theory propagation + the incremental (per-assert)
bound layer — both documented above and the clear next steps.

## Follow-up: ruled out eager-clause / has_units bottlenecks; bound-prop shallows but vhard7 conflicts stay deep

A second pass measured whether the eager-watched-clause install path (the
handover's part-B motivation) is actually the vhard7 bottleneck.  It is not:

- **Theory-reason-clause accumulation is negligible.**  Instrumented
  `add_theory_reason_clause`: only **3** theory-reason clauses are created over
  6 s on vhard7 (`OXIZ_BOUND_PROP=1`).  The bound-propagated literals mostly
  drive *conflicts* (via the theory check), not permanent clause installs — so
  the eager-clause DB is not cluttered and part (B) lazy propagation would NOT
  speed up vhard7.  (Part B is still the right design for *sound* propagation on
  dense logics, but it is not vhard7's lever.)
- **The `has_units` mixed-batch discard is not the cause.**  Instrumented the
  `search_ext` `has_units` branch (which backtracks to level 0 and discards
  reasoned propagations when a unit appears): **0** hits on vhard7.  The
  bound-prop's reasoned propagations are not being starved by units.

**What bound-prop DOES do on vhard7 (measured, 6 s):**

| config | conflicts | mean conflict level |
|--------|----------:|--------------------:|
| `OXIZ_BOUND_PROP` off (baseline) | 1145 | 96.7 |
| `OXIZ_BOUND_PROP=1` (gated) | 959 | **81.1** |

So the propagator **does shallow conflicts (96.7 → 81.1)** — it is helping — but
vhard7's conflicts remain at level ~81 where z3's sit at ~2.  This is the same
*deep-conflict CDCL characteristic* the qlock chase hit: even with sound forward
propagation firing (~750 propagated literals over the search), oxiz's CDCL
reaches the DL-inconsistent combinations at decision level ~81, not ~2.
Closing vhard7 therefore needs the deeper levers the qlock chase identified for
that class — (a) much denser propagation (the incremental per-assert bound
layer that derives *transitive* recurrence bounds, not just direct single-var
bounds), and/or (b) CDCL branching/learning that finds the shallow conflicts —
neither of which the current prop tracker (direct single-var bounds only)
provides.  The landed propagator is a real, sound improvement (closes vhard4,
shallows vhard7 conflicts by 16 levels) and the right foundation; vhard7 itself
is a deeper CDCL/incremental-bound problem on top of it.

## Restructure: tighten tableau bounds ONCE per assertion (not per atom) — closes vhard4,5,8,10,12

The `=tight` mode (which runs `Simplex::propagate_bounds` to derive *transitive*
tableau bounds) was O(tableau × atoms × assertions): `propagate_bounds` ran
*inside* the per-atom `derive_expr_bound_reasons`.  Restructured so the caller
(`derive_arith_bound_propagations`) runs the new `ArithSolver::tighten_tableau_bounds`
(= `propagate_bounds` to a fixpoint, ≤16 passes) ONCE per assertion, then scans
atoms cheaply.

**Result on the vhard family (QF_UFIDL, all unsat, 12 s timeout):**

| | baseline (`off`) | `OXIZ_BOUND_PROP=tight` |
|---|---|---|
| closes | vhard2,3 | **vhard2,3,4,5,8,10,12** |

So `=tight` closes **5 more vhard instances** than baseline (vhard4,5,8,10,12),
soundly (0 disagreements on the 60-instance IDL/UFIDL sample; 0 new
disagreements on the full 270-instance differential).  vhard7 — the specific
handover target — still times out: it is a particularly hard member of the
family (vhard8/10/12 close while vhard6/7/9/11/13+ do not; difficulty is
non-monotonic in the index).  Its conflicts remain deep (~level 98 even with
transitive bounds) — the same CDCL-dynamics characteristic; closing it needs
the full incremental per-assert bound layer (O(affected), not O(tableau)) and/or
CDCL branching work.

**Suite impact (270-instance differential, 8 s):** `=tight` is net-negative
(solved 118 vs baseline 121) because the vhard gains manifest only at 10–25 s
(they are timeouts, not yet solved, at 8 s) while the O(tableau) tightening cost
is paid on every DL assertion.  Hence both modes stay **env-gated, default
off**; `=tight` is the recommended setting for the QF_UFIDL/vhard family where
the slower convergence is worthwhile, `=1` for a lighter touch.

## BREAKTHROUGH: VSIDS + tight bound-prop closes vhard7 (1.7 s) and 18/19 of the vhard family

The vhard7 lever turned out to be the **synergy of VSIDS branching + tight
(transitive) bound propagation** — *neither alone suffices*:

| config (QF_UFIDL vhard7) | result |
|--------------------------|--------|
| baseline (VMTF, no bound-prop) | timeout |
| VMTF + tight bound-prop | timeout (conflicts ~level 98) |
| VSIDS, no bound-prop | timeout |
| **VSIDS + tight bound-prop** | **unsat in 1.7 s** |

Measured directly: VSIDS alone does not close vhard7, and tight bound-prop alone
(VMTF default) does not — only the combination does.  This mirrors the qlock
chase's finding that VSIDS (not the default VMTF-focused) shallows the
deep-conflict characteristic, but here VSIDS only works *with* the forward
bound propagation forcing the relevant atoms.

**Full vhard family (`OXIZ_BOUND_PROP=tight`, 25 s):** **18/19 close** (only
vhard16 times out) — vs baseline's 2/19 (vhard2,3).  vhard7 1.7 s, vhard15
16.6 s, vhard17 22.7 s.  All `unsat` (correct).  **+16 sound solves.**

**Delivery (commit, gated):**
- `SatSolver::set_branching_vsids` (pure VSIDS: `use_vmtf`/LRB/CHB off,
  `enable_stabilize` off).
- `Solver::set_logic` activates VSIDS **for QF_UFIDL only** (NOT QF_IDL) when
  `OXIZ_BOUND_PROP` is set.  QF_IDL is excluded because VSIDS/bound-prop
  **regress** the queens_bench / DTP QF_IDL families (the same QF_IDL-vs-QF_UFIDL
  split the qlock chase saw) — confirmed in the differential
  (super_queen30-1, DTP_k2 went sat→timeout under the broader QF_IDL+QF_UFIDL
  gate; narrowing to QF_UFIDL removes those regressions while keeping the vhard
  gain).
- The bound-prop propagator's `is_dl_family` gate is likewise narrowed to
  QF_UFIDL.

**Soundness + suite (270-instance differential, 8 s, two runs):**

| config | solved | agree_z3 | disagree_soundness |
|--------|-------:|---------:|-------------------:|
| baseline | 120 | 118 | 2 (pre-existing) |
| `OXIZ_BOUND_PROP=1` | 120 | 118 | 2 |
| `OXIZ_BOUND_PROP=tight` | **121–122** | 119–120 | 2 |

`=tight` is **net +1 (vhard7) and SOUND** (only the 2 pre-existing
disagreements; zero new).  qlock-4-10-7 (also QF_UFIDL) is **not** closed by
this — it stays timeout (soundly; z3=sat) — confirming qlock is a distinct,
harder CDCL case (the prior agent's conclusion stands).  Tests: 1417 + 1035
pass, 0 failures.  QF_UFIDL RDS family unaffected (no regressions).

Both modes stay env-gated (default off) per the handover's caution; `=tight` is
net-positive and the recommended setting for QF_UFIDL.  The QF_UFIDL-only VSIDS
gate is the key: it captures the vhard win without the QF_IDL regressions that
made the prior agent's *global* VSIDS experiment net-negative.
