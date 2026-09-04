# Arithmetic negated-atom enforcement: two false-SAT holes mapped, fix attempt reverted (2026-08-21)

Status: **not fixed on main** — this records a root-cause map, a complete but
unlanded fix design, and the regression that forced the revert. All findings
verified on clean-HEAD worktree binaries (commit `3bfd6bf`).

## The bug class (pre-existing on main)

Several UNSAT instances answer `sat` because **theory atoms assigned their
negative polarity are not enforced against the final arithmetic model**:

| instance | logic | z3 | nixie (main) |
|---|---|---|---|
| `smt-lib/non-incremental/QF_UFIDL/pete/5s.smt2` (also cxs-bp, cxs-bp-ex, cxs-bp-safety) | QF_UFIDL | unsat (0.03s) | **sat** (0.8s) |
| `smt-lib/non-incremental/QF_ANIA/20190429-UltimateAutomizerSvcomp2019/avg40…TraceCheck_0.smt2` | QF_ANIA | unsat (3.8s) | **sat** (2.5s) |

Historical differential snapshots show these as *timeouts* — the false-SATs
became reachable when the search got fast enough to reach a bad full
assignment inside the 10 s cap.

### Hole A — negated `=` atoms never reach the arithmetic solver

`process_constraint` (theory_manager.rs) sends a **positive** `Eq` atom to
`arith.assert_eq` (tableau row), but a **negative** `Eq` atom (`(= a b)`
assigned false ⇒ a ≠ b) only asserts an EUF disequality (+ BV when
applicable). Nothing ever forces the *arithmetic* model to give the two
sides different values: `nelson_oppen_combine` propagates arith-entailed
equalities into EUF, but only when arithmetic *entails* the equality —
equal-by-accident model values (two free vars both at 3) never conflict with
the EUF diseq. Model-based combination only checks same-EUF-class ⇒ same
arith value, not the dual. Result: `sat` over a theory-inconsistent
assignment.

### Hole B — RETRACTED (scanner artifact) and superseded by the pin experiment

The originally reported "Hole B" (a negated `Le` atom, var 223, `-t ≤ 0`
assigned false with model `t = 1`) was a **misdiagnosis**: `var_to_parsed_arith`
carries a **`Le` placeholder for `Eq` atoms** (encode.rs stores it so the
positive polarity can assert both bounds), and the first scanner version
evaluated every parsed form as a comparison — misreading a negated `=` atom
(`t448 ≠ t456`, model 2 ≠ 3: **satisfied**) as a violated `≤`. With the
scanner fixed (comparison checks only for genuine `Lt/Le/Gt/Ge` constraints),
it reports **zero per-atom violations** on 5s's accepted assignment.

What actually characterizes the bug (z3-certified):

* nixie answered `sat` on 5s with model `pc0 = -1, dmem0 = -1, a1 = -1,
  ZERO = -2` (and **no UF interpretations** in the printed model);
* `F ∧ (= pc0 -1)` is **UNSAT** — the pinned constant *alone* refutes the
  formula (verified by minimization over the 4 pins: every proper subset is
  sat);
* every assigned atom is individually consistent with the theory model
  under nixie's opaque values for UF-application variables.

So the missing enforcement is **not** at the atom level: the formula entails
`pc0 ≠ -1` through a chain (pinned constant → ite-condition resolution →
equal-argument congruence on UF applications → a contradictory
equality/disequality), and nixie's final_check accepts an assignment that
breaks that chain — the negated-equality/congruence conflict is never
derived. This is Hole-A-shaped (negated `=` enforcement) but at the level of
*propagated/congruent* facts rather than asserted atoms: the operands whose
equality congruence forces are themselves UF results whose equality only the
combination loop can see.

## The fix attempt (reverted)

A complete `assert_diseq` for `ArithSolver` was implemented and validated at
the unit level (3 focused tests + a 400-case random brute-force oracle over
±5 grids, all passing):

* `assert_diseq(terms, rhs, reason)` records the constraint; `check()`
  enforces it via split-on-demand DFS: find the first diseq the current LP
  model violates → probe both split sides in scratch simplex scopes
  (integers: exact `≤ rhs-1 ∨ ≥ rhs+1`; reals: delta-strict `<`/`>`) →
  commit a feasible side in its own scope, flip on dead ends.
* Commit bookkeeping distinguishes **forced** sides (the other side refuted
  ⇒ the bound is a consequence of the atom; tight conflict cores may cite
  the atom) from **choice** sides (both feasible ⇒ any dead-end core citing
  it is not implied; fall back to the full asserted-atom core, justified by
  the exhausted DFS).
* All commits unwind at check exit; branch-and-bound's integral model is
  re-checked against the diseqs (the fractional LP value can hide a
  violation that every integral leaf has).
* Wired into the manager's negative-`Eq` and positive-`Diseq` arms (gated
  `!dl_pure`, see below). **With this wiring pete answered `unsat`**
  (correctly) until later enforcement fixes reshuffled the search trajectory
  (see the Hole B retraction below for what that residual failure is).

### Integration bugs found while landing it (all real, all with reproducers)

1. **Zombie disequalities across `reset()`**: `resync_theory_state` does
   `arith.reset()` + replay, but `reset()` did not clear the new
   `disequalities` vector — constraints of dead assignments survived into
   later rounds and over-constrained them (false `unsat` on
   `storeinv/swap_sf` sat-side tests; z3-verified the dead-end systems were
   genuinely unsat, proving the *state* was wrong, not the search).
   Lesson: **any new assertion vector added to a solver must be cleared in
   `reset()` and truncated in `ContextState`** — the replay re-feeds.
   The same replay also re-feeds every assigned atom per MBQI round →
   dedup `assert_diseq` on (form, rhs).
2. **Simplex `pop()` can restore a stale assignment with
   `assignment_current` still set**: `check()` snapshots the level *before*
   testing staleness, so a stale-at-snapshot-time assignment is restored
   verbatim; the next `check` skips `crash_basis` and `pivot`'s incremental
   delta propagation builds on inconsistent values (the
   `delta propagation mismatch` debug invariant fires; in release the
   assignment silently diverges). Fix (not landed): mark the assignment
   stale unconditionally on every pop — Dutertre–de Moura ("only bounds are
   backtrackable") promises exactly that. If this panic is ever seen on
   main, the fix is ready here.
3. **DL-purity cliff**: feeding a diseq on the pure-DL path called
   `break_dl_purity()` → qlock/queen (751-node DL graphs) degrade from
   1.8 s to timeout (simplex B&B over rows the dense core already decided;
   the pre-existing comment at the `!dl_pure` skip of
   `propagate_euf_equalities_to_arith` documents the same cliff). Gate the
   feeds on `!dl_pure`.

## Why it was reverted

The differential suite (270 pinned instances) flagged a NEW wrong answer:
`QF_UFLIA/wisas/xs_8_13.smt2` — `unsat` on main (correct, 6.4 s), `sat`
with the machinery (fast). With pete still false-SAT (per the then-believed
Hole B; per the corrected analysis below, the residual failure is the
combination-chain gap), the change was net-negative: it traded one pre-existing false-SAT for a
regression on a previously-correct family. Everything was reverted;
`git log` around `3bfd6bf` has the full implementation in the WIP if
resumed (or re-derive from this doc — the design above is complete).

## Diagnostic tooling (committed with this study's follow-up)

* **`NIXIE_SCAN_VIOL=1`** (debug builds): at `check_core`'s `Sat` exit, walk
  every assigned theory atom and print the first one the final theory model
  violates (`theory_manager/debug_scan.rs`; comparison checks only for
  genuine `Lt/Le/Gt/Ge` — see the module doc for the placeholder trap).
  Negative result is itself informative: it localizes the failure *below*
  the atom level.
* **Pin experiment** (external, z3): solve, take the model's constant
  assignments, check `F ∧ pins` with z3, then minimize the pin set. A
  refutable pin proves the `sat` verdict wrong without any internal
  instrumentation — this is what certified the 5s bug (`pc0 = -1` alone).
* **SMT2 dead-end dump** (from the reverted machinery work): at a DFS
  terminal dead end, dump equalities + bounds + diseqs as QF_LIA and ask
  z3 — distinguishes "search unsound" (z3: sat) from "state wrong" (z3:
  unsat ⇒ look for zombie/stale assertions).
* Bisect discipline: test in a `git worktree`, never stash/restore the
  shared tree; rebuild the harness binaries per commit.

## ROOT CAUSE (found 2026-08-21, follow-up session): non-convex combination incompleteness

The congruence-gap probe (`debug_scan_congruence_gaps`, committed with the
scanner) settles the mechanism on 5s's accepted assignment:

```
[cgap] PROPAGATION GAP: apps TermId(188) vs TermId(729) — args arith-equal
       in the model, EUF-distinct (merge never propagated)   [×4 more pairs]
```

`nelson_oppen_combine`'s arith→EUF direction only merges **entailed**
equalities (`entailed_equal_reason` = two scratch simplex proofs). When the
refutation requires merging two arguments that the arith model merely
*assigns* equal (not entails — e.g. two opaque UF-result variables the LP
happened to co-locate), the probe correctly declines, the merge never
commits, congruence never fires on the UF applications, and the negated-`=`
atom between the (would-be congruent) results never conflicts. The search
then reports `Sat` over an **arrangement that was never jointly checked** —
the textbook non-convex Nelson-Oppen gap. Per-atom scanning cannot see it
(each atom is individually consistent); the pin experiment certified it
(`F ∧ (= pc0 -1)` is unsat while the model pins `pc0 = -1`).

### Fix LANDED (2026-08-21, second follow-up): tentative-arrangement round

Implemented as designed (plus two additions the landing required), gated to
the validated `is_dl_family` (QF_UFIDL/UFIDL):

1. **`TheoryManager::arrange_model_equal_pairs`** (runs at the end of
   `model_based_combination`):
   * *Phase 1* — per-pair probes: for each model-equal, EUF-distinct pair of
     UF-argument interface terms (existing EUF nodes only — interning would
     perturb node order and flip unrelated verdicts), merge tentatively in a
     scope.  A direct EUF conflict proves `C ⊢ x ≠ y` (core minus the
     tentative edge's tag; the tag is collision-checked against
     `derived_reasons`): assert that derived disequality scoped, with `C`
     recorded as its justification, and request a split atom for the pair.
   * *Phase 2* — full arrangement: accumulate up to 32 merges in one scope;
     a direct conflict (pete: congruence vs a negated `=` on the results)
     requests atoms for the merged superset.  If no direct conflict, a
     **cross-theory check** (`arrangement_cross_check_arith`) groups
     arith-valued shared terms by their merged EUF class, asserts the
     class-disagreement equalities into a scoped tableau and lets
     `arith.check` refute (the wisas shape: congruence over merged args
     collapses `format`-apps whose pinned constants disagree only in
     arithmetic).
2. **`Solver::refine_arrangement_splits`** — on a `Sat`, drain the requests,
   `mk_eq` + `encode_depth` each pair (cvc5 `ensureLiteral`; preferred
   positive phase) and re-solve through the existing block/case-split
   restart loop (theories reset, fresh manager).  The refutation rests on
   search facts, so no clause may be asserted — only the branching dimension
   is added; a true polarity merges through `process_constraint` and the
   conflict becomes an ordinary learned clause.

**Results**: the entire pete family flips to correct `unsat` (5s, cxs-bp,
cxs-bp-ex, cxs-bp-safety, cxs-bp-ex-inp-safety — and 6stage-flush, a
previous timeout).  Differential: **0 new unsound**; the only remaining
disagreement is the pre-existing QF_ANIA avg40 (different family — the round
is gated off there).  Regression tests:
`nixie-solver/tests/arrangement_round_regressions.rs` (+ fixture).

**The wisas lesson (verified twice now)**: QF_UFLIA/wisas/xs_8_13 flips
between correct `unsat` and false `sat` across *search configurations*
(ab-vmtf/ab-vsids experiment snapshots: `sat`; ab-fixed: `unsat`) — the same
hole class reachable by trajectory.  The first ungated landing flipped it
(debug AND release).  Two measurement traps recorded: (1) *debug vs release
builds can disagree on these instances* — always compare release-vs-release
(HEAD debug answered wisas `sat` while HEAD release said `unsat`);
(2) a change that derives nothing on an instance can still perturb it via
node-creation order — the round now skips pairs without existing EUF nodes.
With the `is_dl_family` gate wisas keeps main's verdict.

### Original fix-shape sketch (superseded by the landing above)

Tentative-arrangement round at `final_check`:

1. Collect the model-equal candidate pairs the cgap probe finds (interface
   terms that are UF arguments, grouped by arith value — the existing
   `by_val` machinery already builds this set).
2. Tentatively merge them in EUF **inside a scope** (EUF needs push/pop or a
   rebuild-on-exit; today only `reset()`+replay exists — the cheap route is
   snapshotting the merge list and unmerging is NOT sound in general, so a
   scoped EUF or a replay is required).
3. If EUF conflicts under the tentative arrangement, the assignment implies
   `¬(x₁=y₁ ∧ … ∧ xₖ=yₖ)` over the merged pairs — learn that **interface
   disjunction lemma** as a clause over the pairs' `(= x_i y_i)` SAT atoms
   (encodable whenever the pairs are formula atoms, which the pete family's
   `(= app1 app2)` atoms are; pairs without a SAT variable cannot be
   learned — skip them, staying incomplete-but-sound there).
4. Drop the tentative merges and continue the search. Iterate.

Sound because the lemma is a logical consequence of the (refuted) tentative
conjunction; incomplete only for pairs lacking SAT atoms.

The reverted `assert_diseq` machinery is complementary, not sufficient: it
enforces negated-`=` atoms *inside* arithmetic once operands are interned,
but the pete refutation needs the arrangement merge FIRST (congruence over
equal args) to make the negated-`=` fire — which is why wiring it flipped
pete only along some trajectories.

## Remaining steps

1. ~~Land the arrangement round~~ **done** - see "Fix LANDED" above
   (commit `8db2f3c`): entire pete family -> correct `unsat`, differential
   0 new unsound.
2. QF_ANIA avg40 - **FIXED (2026-08-21, fourth follow-up): two lazy-lemma
   gaps in the array theory**.  The single-pin diagnosis led to minimal
   probes that isolated two independent missing axioms:
   * **Constant-function arrays**: `((as const S) v)` parses as a qualified
     `Apply` (`(as const)`) - an opaque array term unless recognized.  Even
     the fully ground `(select ((as const (Array Int Int)) 162) 7)` was
     free.  Fix: `collect_array_structure` records const-array terms
     (name `(as const)`, array-sorted, one arg) and
     `instantiate_array_axioms` asserts one UNIT per observed read:
     `select((as const S) v, i) = v` (z3 folds this in the rewriter -
     `mk_select`'s `is_const`; the unit is the lazy-lemma equivalent).
   * **select-over-select (RMW heaps)**: `select(select(A, j), i)` where A
     stores at j - the Ultimate heap-update shape
     `store(mem, base, store(select(mem, base), off, v))`.  The outer
     read's array operand is itself a read; nothing resolved it.  Fix: a
     select-over-select arm in `build_read_over_write` resolves the inner
     read through A's FULL (aliased) store chain and, on a store index
     SYNTACTICALLY equal to the read index, twins the outer read to
     `select(value, i)` guarded only by the alias equalities.
   Result: avg40+pin now grinds toward the refutation instead of answering
   `sat`; at the differential's 10 s cap it is an honest TIMEOUT
   (wrong-sat -> timeout).  **Differential: disagree(soundness)=0 for the
   first time** (162/163 solved; avg40 is the one loss).
   Perf follow-up (NOT landed): deep RMW chains resolve one memory level
   per refinement round; the twin reads re-seed the round machinery and the
   instance stream never saturates (measured 0 -> 373 -> 997 -> 1659 over
   four rounds; avg40 needs >1000 s).  Two tautology-drop optimizations
   landed (ELSE clauses whose disjunction contains a syntactically-true
   `index = ki` literal are dropped instead of materialised - the
   materialised twin is what re-seeds); the remaining growth is via the
   upward-closure / witness paths.  The proper fix is z3-style EAGER chain
   reduction in a rewriter (compose `select(mem_N, base)` down the whole
   alias chain at internalization), a separate piece of work.
   **floppy2 lesson**: the first version ALSO materialised the
   differing-index ELSE rows; on satisfiable QF_ANIA goals that churn never
   saturates, the honesty gate fires and correct `sat` answers became
   `unknown` (4-7 floppy2 instances, sat 2.6 s -> unknown).  The landed
   version fires ONLY on the syntactic match (incomplete for
   differing-index arrangements - as before the fix - instead of
   completeness-with-timeouts on the sat side).

3. wisas-class inputs (QF_UFLIA): **RESOLVED 2026-08-21 (fifth follow-up,
   and rebuilt on the reference architecture in the sixth)**.  The fifth
   follow-up removed a wall-clock gate that made verdicts load-dependent
   (same binary: 7x`sat`/1x`unsat` on `xs_8_13`; forced arms 5x`sat` at
   budget 0 vs 5x`unsat` at budget inf).  The sixth follow-up then replaced
   "always run the reactive round" with the z3/cvc5 architecture after
   reading both references:
   * **z3 `smt/arith_eq_adapter.cpp`**: interface-equality triangle lemmas
     (`eq <-> le and ge` via `mk_th_axiom`) internalized DURING the search
     on deductive triggers (`new_eq_eh`/`new_diseq_eh` = enode merges,
     `restart_eh` = base-level pairs), trail-scoped (`already_processed`
     + trail object), phase-guided (`try_true_first`), relevancy-gated.
     No post-hoc round, no budget of any kind.
   * **cvc5 `theory/arith/equality_solver.cpp`**: (dis)equalities flow as
     propagations through the shared equality engine (distributed mode).
   * **cvc5 `theory/arith/branch_and_bound.cpp`**: split lemmas
     (`(= v i) v (v < i) v (v > i)`, `ensureLiteral` + `preferPhase(true)`,
     via the inference manager) asserted mid-search at a DEDUCTIVE trigger
     (fractional LP value) — violated at the trigger, so no restart.
   Nixie now mirrors this split:
   * **Eager half** (`assert_eager_int_case_splits`, called after
     `pre_encode_care_graph_atoms`): enumeration lemmas for int-sorted UF
     arguments whose finite range the level-0 interval fixpoint derives
     (the same soundness basis as before), asserted BEFORE the search,
     with `set_preferred_phase(lit, true)` on every `(= t k)` literal
     (z3 `try_true_first` / cvc5 `preferPhase` port).  CDCL pins values
     from conflict #1; no candidate is reached without the branching
     dimension for this class.
   * **Reactive half** (`refine_int_case_split`, kept): fires at a
     theory-consistent candidate for ranges ONLY the LP fallback can see
     (it needs the base-scoped simplex, empty pre-search — measured:
     fixpoint-only leaves `xs_8_13` `sat`).  The trigger is deductive
     (candidate + finite range from asserted facts), cvc5-B&B-class; the
     reset-and-re-solve is INHERENT to enumeration lemmas (unlike a B&B
     split at a fractional point, an enumeration clause is *satisfied* by
     the candidate, so it cannot invalidate it mid-search).  Deterministic
     caps only (one round, 32 terms, width <= 8) — the gate the user
     asked for: deductive, load-independent, thread-safe.
   Results: `xs_8_13` deterministic `unsat`; app12/bench_315 26.0s ->
   12.8s (eager lemmas replaced its reactive reset); differential 162
   solved / 0 disagreements with both app12 files back (bench_134
   timeout->sat 9.0s, bench_315 timeout->unsat 10.8s at the 10s cap under
   parallel load); pete + wisas families clean.  The wisas lesson's
   "trajectory-dependent" verdicts were the clock, not chaos.
