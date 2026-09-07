# BV-Circuit Unification, Option A Stage 1: circuits in the main CDCL core

**Date:** 2026-09-07
**Handover:** `docs/handovers/2026-09-07-bv-unification.md` (this note is the
stage-1 landing report).
**Baseline:** `precompile/30c049c` (Sep 2026, main).

**Verdict:** landed.  The unified path is real and measured: on mixed
UF+BV goals the `distinct`-over-BV cells flip from **timeout to solved**
(n=300 w=16: timeout → 6.7 s; n=500 w=16: timeout → 21.5 s; n=100 w=8:
50 s → 0.15 s), with zero verdict mismatches over the calibration cells, a
300-file random QF_BV corpus sample, and the Z3 parity suite (169/169
decisive).  Digging for the unified path's soundness also surfaced and fixed
a **pre-existing incremental false-`unsat`** on the baseline itself
(`EufSolver` value-apart propagation pinned conditional facts as permanent
level-0 units; see §4).

## 1. What landed

**The architecture seam.**  `BvSolver` gains a *build target* abstraction
(`nixie-theories/src/bv/solver.rs`): `build_with(sat, f)` parks the embedded
SAT instance for the duration of `f` and repoints every `new_var`/
`add_clause`/const-bit the gate constructors perform at the **caller's**
core.  The memo tables (`term_to_bv`, `ult_cache`, `bool_node`) persist
across windows, so a *unified generation* accumulates main-core-var entries
and the embedded instance stays dormant (`Theory::check`/`push`/`pop`/
`get_model`/`notify_equality` are guarded no-ops; `enter_unified`/
`exit_unified` give the generation a clean var-space slate).

**The link pass** (`nixie-solver/src/solver/bv_unified.rs`).  At assertion
time, after `emit_assertion_clauses` has minted every atom's main var, the
pass bit-blasts each BV-sorted sub-term and each BV atom's defining circuit
into the main core and ties the atom var to the circuit output with two
clauses (`atom <=> circuit`).  A sweep of `var_to_constraint` additionally
links the pairwise atoms a large `distinct` mints.  From then on the atom's
semantics are ordinary clauses: deciding it propagates bits natively during
the descent, conflicts are learned by the main CDCL engine over its own
literals (the "native bit learning" option of the handover's staged plan –
sound because the circuit clauses are a definitional extension), and the
theory manager skips the embedded assert+check round-trip for linked atoms.

**Gates** (all-or-nothing per *generation*; any failure ends the generation
by wiping the var-space tables, which parks everything on the lazy path):
no quantifiers, no arrays, no `Apply` with a BV-sorted result (congruence
merges have no clause form), no user scopes, not certified/proof mode, not
ring-dominated-with-arith-relaxation (the dispatch's own routing), not the
all-blastable fragment (the eager pure-BV dispatch owns that; unification
would blast every file twice), and a 200 k *distinct-term + atom* budget
(n=2000 `distinct` ⇒ ~2 M pair atoms ⇒ lazy).  Kill switch:
`NIXIE_BV_UNIFIED=0`.  Trace: `NIXIE_BV_UNIFIED_TRACE=1`.

**Honesty gate.**  A BV atom the manager sees assigned without a link is
recorded; a `Sat` exit with unlinked atoms builds the missing circuits and
re-searches (bounded rounds, `Unknown` at budget exhaustion).  Rescoping:
the rebase sites and the in-search `resync_theory_state` reset only the
embedded-path state while a generation lives (a full `Theory::reset` there
was the first bug found – see §3), keeping the memo truthful against the
permanent base-scope clauses.  Model reads route through an adopted main-core
snapshot (`adopt_model_snapshot`), so `get_value*`/`model_bv_values`/the
debug circuit-verification net work unchanged.

**Not unified (deliberately, stage 2+):** scope-journalled memo retraction
for incremental sessions past a `push`; the order-encoding rebuild (the
handover's flip condition 2 is now unblocked – see §5); CEGAR unification;
native bit-learning policy (deletion/DRAT implications of auxiliary vars).

## 2. Measurements (release, this tree vs `precompile/30c049c`)

Distinct-over-BV, *mixed* goal (one Bool-result UF atom forces the general
path; the pure-BV forms stay with the eager dispatch, unchanged):

| cell | baseline | unified | lazy (same build, flag off) |
|---|---|---|---|
| n=100 w=8 sat | 50.3 s | **0.15 s** | ~50 s |
| n=300 w=16 sat | timeout | **6.7 s** | timeout |
| n=500 w=16 sat | timeout | **21.5 s** | timeout |
| n=600 w=32 sat | timeout | timeout | timeout |
| n=300 w=16 unsat (explicit `=`) | 0.05 s | 2.3 s | 0.05 s |

The flag-off column is the controlled comparison: identical binary,
identical everything except the unification – the wins are the architecture,
not trajectory luck.  Main-core tick counts confirm the mechanism the
campaign predicted: baseline/lazy show 0–1 main-core *decisions* (the work
hidden in per-check embedded solves), unified shows the whole search in the
main core (e.g. 52 185 decisions at n=100 w=8).  The mid-n unsat cell pays
the eager C(n,2) link cost (45 k pair circuits at n=300) – bounded, and the
encoding-shape decision that removes it is exactly flip condition 2.

Mixed UF(Bool)+BV random cells (50 files, sat+unsat): every file
sub-0.11 s in every mode, verdicts identical – the unified path is not a
regression on ordinary small mixed goals.

Corpus A/B, 300-file random sample of `smt-lib/non-incremental/QF_BV`
(seed 42, list committed alongside this note's raw data in the worktree
scratch): **zero verdict mismatches**, 1 old-timeout solved by the new
build, 0 new timeouts.  Repeat runs of the apparent wall-time losses
(sage/spear families) on a quiet machine show them to be load noise
(`bin_libsmbsharemodes_vc6063`: 0.857 s vs 0.849 s over 3 runs each) – those
files run the dispatch path, which this change does not touch.  Per
`docs/BENCHMARKING.md`, wall was not treated as primary evidence anywhere.

Z3 parity (`bench/z3_parity/run_parity.sh`, z3 4.16.0): **170 total,
169 correct, 0 wrong, 1 inconclusive – 100 % parity over decisive
comparisons** (matches the recorded baseline).

Test suite: 10 617 passed / 3 timed out under parallel-suite load – each of
the three passes standalone (38 s / 101 s / 157 s; two of them are marked
SLOW pre-change).  New battery: `nixie-solver/tests/bv_unified_regressions.rs`
(12 tests, green under both `NIXIE_BV_UNIFIED=1` and `=0`).

## 3. Bugs found on the way (each with its reproduction in the battery)

1. **`resync_theory_state` killed generations mid-search.**  The manager's
   in-search resync called the full `Theory::reset` on the BV solver, which
   `exit_unified`s the generation inside the theory while the owning
   `Solver` still believes it is active, wipes the memo, and makes the next
   link pass re-blast fresh duplicate circuits besides the surviving ones
   (false `unsat` on any second check with a BV assertion).  Fixed: the
   resync (and every round boundary) resets only the embedded-path state
   while a generation lives.
2. **Encode-time free vectors could land in the wrong instance.**  The
   theory-variable walk `new_bv`s BV leaves at encode time; on the first
   assertion of a generation that ran *before* the generation decision.
   `enter_unified` therefore wipes the var-space tables on entry (the
   orphaned embedded free vectors are harmless), and the two encode-time
   `new_bv` sites route through a unified-aware helper.
3. Both of the above were found by `mixed_int_bv_uf_multicheck_stays_sat`
   failing in the full suite – the landmine list's "keep digging" advice in
   action: the first plausible cause (the link pass) was not the cause.

## 4. The pre-existing soundness bug the campaign surfaced (fixed here)

`TheoryManager::forced_eq_lit` treated every value-apart pair as
tautologically apart: when `try_explain_diseq` found no disequality edge, it
fabricated an **empty justification**, and `install_theory_units` then
stored that conditional fact as a *permanent level-0 unit clause*.  But a
class only *acquires* a value summary when one of its members merges with a
value-carrying ground constant – typically under an **assigned equality
atom**.  A first `check-sat`'s branch choice (`(or (= v c1) (= v c2))` with
the model picking `c1`) therefore pinned `¬(= v c2)` at level 0 forever, and
a later `(assert (= v c2))` was falsely refuted.  Reproduced on the
untouched baseline binary (`precompile/30c049c`): `sat, unsat` for a
`sat, sat` goal – in the **lazy** architecture, no unification involved.

Fix: `EufSolver::try_explain_value_apart` explains the apartness through
each class's value-*carrier* merge proofs (`try_explain_equality(node,
carrier)`), which is empty exactly in the born-ground case (two different
ground constants – the handover's value-mark contract preserved, its
`value_*` e-graph tests all green) and cites the establishing atoms
otherwise, so the propagation is reasoned, level-aware, and retractable.
`bv_branch_pin_other_branch_stays_sat` is the regression test; the
refutation direction (`bv_forced_branch_then_other_is_unsat`,
`bv_value_apart_refutation_still_works`) pins the fix against both
over-reach and loss.

## 5. Where this leaves the handover's flip conditions

1. *QF_BV corpus geomean ≥ 1.15×*: **not the right metric for stage 1** –
   the stage's gates intentionally leave the all-blastable fragment (the bulk
   of QF_BV) on the untouched eager dispatch, and the corpus A/B shows
   exactly that (zero mismatches, no systematic change).  The unified
   path's measured wins are on *mixed* goals; a corpus-level QF_BV geomean
   flip belongs to stage 2 (order encoding / dispatch unification).
2. *Order encoding*: **unblocked.**  Comparator decisions now propagate
   mid-descent in the main core; the network's O(n log² n) shape vs
   pairwise's eager C(n,2) link cost is the next measurable question
   (n=300 unsat cell above is its first data point: pairwise-link costs
   2.3 s where the lazy single-pair circuit cost 0.05 s).
3. *No regression on the ite/bvsmod/wide-const/signed battery and `value_*`
   tests*: **green** (12/12 new battery tests under both modes, full
   workspace suite green, value-mark e-graph tests green).

## 6. Artifacts

- Raw calibration committed alongside this note:
  `docs/studies/data/2026-09-07-bv-unification-stage1-{qfbv-sample.txt,cells.json}`
  (the corpus sample is fixed at seed 42 – never re-sample it).
- Binary cached at `precompile/<landing-sha>/nixie`.
