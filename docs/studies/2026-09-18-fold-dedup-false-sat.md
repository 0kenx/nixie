# Post-fold exact-duplicate retire: a big measured win that exposes a latent false-SAT (2026-09-18, negative result + open lead)

Not landed.  The slice is measured **strongly positive on every metric the
corpus reports — and wrong**: it flips four UNSAT families to false `sat`
(33 of 300 powered cells).  Recorded here so the next session starts at
the forensics, not at the idea.

## The slice

The ELS fold's representative rewrite makes formerly-distinct clauses
identical (`(o2∨x)` and `(o1∨x)` both become `(o1∨x)` once `o1≡o2`
folds); bv_ILA's residual measured **60,602 exact duplicates**, cleaned
only by the next *scheduled* subsume round (46k at conflicts=2000).  The
prototype retires the second copy in-round — one hash probe per live
clause in the loop the fold already runs; sound on its face (subsumption
by an identical clause; the round is proof-gated; owners verified live at
round end; a live-reason guard added along the probe case-B shape).

## The measured effect (why it was tempting)

10-seed × 30-corpus powered run: conflicts geomean **0.8066**, solved
267 → 270, with b22 **0.164×**, b21 **0.257×**, s38584 0.449×,
5447072093nw 0.640×, bv_ILA 0.743× — and **33 verdict mismatches, every
one base=`unsat` → dedup=`sat`** on b21/b22/s38584/bv_ILA: false `sat`
on known-UNSAT instances.

## The forensics (b21, seed 1, `Solver::with_config(CaDiCaL preset)`)

Repro: `nixie-sat` example harness (load DIMACS, solve, verify every
original clause against the model).  The model is total, **exactly one**
violated original clause per false-sat (`#46302: (¬15955 ∨ 100)`), and:

- the violated clause is **never dedup-retired** (checked against the
  full 4,415-pair retire log);
- **both its variables are BVE-eliminated** (`var_eliminated` via
  `bve_def`; the ELS substitution map is *identity* for them — the ELS
  fold is not involved in their elimination);
- with fold rounds disabled (`NIXIE_SWEEP=0`) the build answers `unsat`;
  the base build answers `unsat` at 20 additional seeds and under
  `NIXIE_ELS_FORCE=1` / `NIXIE_FACTOR=0` / `NIXIE_INPROC_SCHED=0` —
  the hole is **exposed by the dedup's trajectory shift, not reached
  without it** in everything tried;
- a live-reason guard on the retire (the probe case-B shape) does **not**
  fix it — the dangling-reason theory is falsified.

## The open lead (next session's entry point)

A trajectory exists under which the **BVE model reconstruction assigns
eliminated variables inconsistently with an original clause** — one
violated clause, both its vars BVE-eliminated with identity ELS reps.
The dedup build is a *generator* for such trajectories (reproducible on
demand: b21 + seed 1 + the harness).  The audit should walk
`save_model`'s reconstruction of vars 15955/100 against their `bve_def`
snapshots on that repro — a latent defect there is reachable in
principle without the dedup (nothing but trajectory luck separates the
builds), which makes this a soundness lead, not a perf footnote.

The duplicate retire itself remains attractive (0.8066 geomean behind
it) — after the reconstruction audit either lands clean or the retire
needs to preserve whatever the reconstruction reads.

## Addendum (same day): the mechanism demonstrated; the walk hardened; the reference divergence named

Recreated the repro (worktree + the dedup retire + a model-checking
harness) and traced the extension walk (`NIXIE_WALK_TRACE`).  The exact
failure on b21/seed 1:

- `entry@559194` = witness `+100`, clause `(100 ∨ ¬15955)` — **the
  violated original clause itself**, correctly on the stack (BVE retired
  it with the pivot's witness when 100 was eliminated).  At walk time
  both literals are false → the walk flips 100 to true ✓.
- `entry@559189` = witness `−100`, clause `(¬100 ∨ ¬2990 ∨ ¬2382)` —
  five positions **earlier in the same elimination group**, opposite
  witness polarity (BVE pushes each retired clause with the pivot
  literal *that clause contains* — mixed polarities within one group are
  structural).  Under the then-current model (2990=T, 2382=T) every
  literal is false → the walk flips 100 **back to false** — re-falsifying
  the already-repaired `entry@559194`.  Under the upstream flips
  (15955's group at `576460` set 15955=T) the two demands are
  **contradictory**: no value of 100 satisfies both; the greedy walk
  oscillates — measured 64/64 repair passes without convergence.
- The wrongness cascades from upstream groups' flip decisions; the
  corner is a *shape* of the greedy walk, not a single bad entry.

**Cadical reference divergence (named, port attempted)**: cadical's
`External::extend` (extend.cpp) on a falsified entry flips **every
currently-false literal** of the clause, not only the witness.  The
naive port of that rule regressed catastrophically on the repro
(**13,762** violated clauses) — our push side differs from cadical's
somewhere upstream (what each mechanism pushes, per-elimination
grouping, or the base-value convention).  The next session's precise
task: diff the PUSH side against cadical's
`push_clause_on_extension_stack` callers per mechanism (BVE pivot
clauses, ELS equivalence implications, pure literals, probe promotions)
before touching the walk again.  The dedup remains the on-demand
trajectory generator for the corner.

**Landed**: a bounded (8-pass) fixpoint wrapper around the walk — repeat
the backward pass until a pass repairs nothing.  Bit-identical on
healthy trajectories by construction (pass 2 performs zero repairs when
the one-pass walk converged — verified conflicts-identical on the
five-instance gate band; suite 1080/1080; bv_ILA 15,144 = pin), and
strictly better on non-oscillating divergence; the oscillation corner
gives up at the bound (documented, unchanged).  Plus two `doc(hidden)`
audit accessors (`debug_ext_stack`, `debug_bve_def`).

Harness recipe (recreate as a `nixie-sat` example): load the DIMACS with
`ConfigPreset::CaDiCaL.config()`, `new_vars_bulk`, `add_clause_dimacs`
per clause, solve, then evaluate every original clause against
`model_value`; on violation print the clause, its vars'
`var_eliminated`, and the enclosing ext-stack entries mentioning each
var (split on `u32::MAX` sentinels; entry = `[witness, lits…]`).

## Addendum 2 (2026-09-18, the probe path): the 3-clause unsat core and the resolvent's lifecycle — this is verdict-level, not reconstruction-level

Following the "more violations = better probe" line: the witness-once
variant's 1,619 violated clauses (vs the stock walk's 1) exposed the
*whole* broken obligation set, and every one of its 61,281 unsatisfied
entries had `witval=false` (52,546 skipped by the rule + 8,735
repaired-then-flipped-back).  That enabled the decisive experiment:

**The consistency instance.**  Fix every never-eliminated variable to
the search's own model value (units), add one clause per extension
entry, hand to kissat: **UNSATISFIABLE**.  No consistent extension
exists — the folded formula's model does not extend to the original.
The search answered `sat` on a formula that *lost a constraint*: the
wrongness is equisatisfiability-level, not walk-level.

**The minimal unsat core (3 entry-clauses + the search's units):**

1. `(¬100 ∨ ¬2990 ∨ ¬2382)` — retired at 100's BVE elimination (witness −100)
2. `(100 ∨ ¬15955)` — the violated original clause itself (witness +100)
3. `(132 ∨ 15956 ∨ 15955 ∨ ¬2366)` — retired at 15955's elimination (witness 15955)

Derivation: the units fix 132=F, 15956=F, 2366=T, 2990=T, 2382=T → (3)
forces 15955=T → (2) forces 100=T → (1) forces 100=F.  Contradiction.

**The resolvent's lifecycle (watchdog-traced by clause id).**  The
soundness hinge is the resolvent of (1),(2) on 100:
`R = (¬2990 ∨ ¬2382 ∨ ¬15955)`.

- R **ADDED** by BVE as `ClauseId(260971)` at 100's elimination ✓
- R **shrunk** to `(¬2990 ∨ ¬15955)` (self-subsumption dropped ¬2382 —
  sound strengthening; the shrunken clause *implies* R) ✓
- 260971 **dedup-retired** (identical to live twin `213141` — the twin
  carries the constraint) ✓
- `213141` **retired via the fold's unit path**: ¬2990 became
  level-0-false, so `(¬2990 ∨ ¬15955)` reduced to the unit `¬15955`
  and was consumed — *sound in isolation* (the unit implies the clause)
- **No obligation containing {2990, 2382, 15955} or any subsumer of R
  exists anywhere on the stack** (verified: zero entries contain all
  three vars; zero clauses in the consistency dump subsume R).

Yet the obligations above ((3) in particular) contradict the unit
`¬15955` under the search's own fixed values — i.e. the elimination
chain, each step locally plausible, collectively dropped R's
constraint: the folded formula became strictly weaker and
*satisfiable*, the original is not.  b21 is UNSAT; the dedup
trajectory is only the generator — the base build carries the same
mechanism and is separated from a false `sat` by trajectory luck.

**Next session's entry point** (in measured order):
1. Audit the **shrink** of 260971 (which pass dropped ¬2382, with what
   justification clause — the shrink logs justifications for DRAT;
   replay them) and the **15955 elimination group** (entries 576406+
   in the trace): its resolvents should entail core entry (3)'s
   complement under the units — they don't; find which retired clause
   of 15955's group never received an obligation (the `213141`
   consumption path is the prime suspect: a clause consumed as a unit
   during the FOLD — between eliminations — while its *obligation
   duties* toward the extension stack had already been assumed by the
   elimination that retired its ancestors).
2. Repro: `model_check` harness + b21 + seed 1 + the dedup retire (the
   on-demand generator); the consistency-instance dumper and the
   triple watchdog are in the worktree patch set (not landed — the
   accessors `debug_ext_stack_and_model` + the `NIXIE_WATCH_TRIPLE`
   watchdogs; re-add per this addendum's recipe).
3. The stock build's fixpoint wrapper (landed) remains correct as far
   as it goes — this addendum supersedes the "reconstruction bug"
   framing: the walk cannot repair an obligation set that is
   unsatisfiable by construction.
