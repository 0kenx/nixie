# The LIA branch channel: built, measured, gated off — the per-LP churn is the binding constraint

**Date:** 2026-09-20 (the "close the gaps for real" session).
**Landed:** the complete CDCL-visible branch channel, **default off**
(`NIXIE_LIA_BRANCH=1` opts in).  Default-off is measured **bit-identical**
on every solved LIA cell (32/32 cells, conflicts equal).  Full bar: 12 070
tests, parity 176/177 with 0 disagreements, gate 1.000, clippy/fmt clean.

## What was built

The `2026-09-20-lia-branch-channel-design.md` map, implemented end to end:

- **`ArithSolver`**: `pending_branch: Option<(TermId, i64)>` published at
  the fractional point when armed (`arm_branch_channel`); `take_pending_branch`
  drains; cleared per check.  When a split is published, the internal B&B
  runs under a **pivot-denominated budget** (`LIA_ARMED_MAX_PIVOTS`,
  per-instance `Simplex::pivots_total` counter — the process-global diag
  counters would cross-contaminate parallel tests) and skips the integral
  dive (the dive costs a full LP re-feasibilization per level and runs
  before the first node is counted).
- **`Solver::check_core_solving`**: the `resource_exhausted` Sat arm, before
  declaring `Unknown`, drains the request and asserts the **valid clause**
  `(<= t k) ∨ (>= t k+1)` (integral-split theorem) via the int-case-split
  atom pattern (`encode_depth(.., 0)` + `sat.add_clause`), then restarts
  the round (the colocated-split restart verbatim: root, theories reset,
  manager rebuilt — the SAT core keeps its learned clauses, so CDCL owns
  the branch tree with warm restarts).  Dedup on `(term, k)`, round cap
  2 000.
- The `Conflict`-channel alternative (returning the split as an
  asserting lemma through `analyze_theory_asserting_lemma`) was verified
  to exist and handle two-unassigned-literal clauses — the reset-restart
  shape was chosen instead for its established precedent.

## The measurement that gates it

Armed (always-on), on the standing LIA cells: **31/32 bit-identical**,
one regression — `v20_problem__019` `sat → timeout`: its solve needs
more internal pivots than the armed budget, and the split round-trips it
gets instead cost more than the internal search they replaced.

On the CAV target family (`problem__022`/`011`): the channel fires
(emission observed), but **never completes a round-trip** — the per-LP
degenerate churn (the pivot-storm addendum's ~2 s per post-cut
re-feasibilization) is spent *inside every theory check*, before the
split can reach CDCL; measured ~8 bnb nodes in 15 s.  The channel fixes
the tree, not the per-LP cost; **the LP-cost layer (fraction-free rows)
is the prerequisite**, after which arming is a one-line flip plus the
matched-null campaign the trajectory shift deserves.

## The arming gate

`NIXIE_LIA_BRANCH=1` (OnceLock-cached — the env-probe rule).  Default
off = the historical search exactly (the 32/32 bit-identical check is
the evidence).  This preserves the machinery for the post-fraction-free
session without shipping an armed trajectory shift that trades a
measured solve for unmeasured theory.

## Probe notes for the follow-up

- The emission site is `lia_cuts_then_bnb`'s tail; the drain is the
  `resource_exhausted` arm in `check_core_solving`.
- The free-vars path (`close_free_vars_then_bnb`) bypasses the emission —
  instances there keep the historical behavior even when armed.
- `problem__022` at 60 s: emission fires, no round-trip completes.
- The wide-literal bnb pins PASS armed (the channel solves that instance
  through split rounds — noted as the one observed armed-path solve).
