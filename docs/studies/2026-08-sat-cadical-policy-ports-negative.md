# Two CDCL heuristic ports screened against matched nulls: both dead

Date: 2026-08-22. Continuation of [`2026-08-sat-speed-vs-cadical.md`](2026-08-sat-speed-vs-cadical.md),
which identified the 2–20× gap vs CaDiCaL as search-trajectory (conflict-count)
differences and listed four candidate causes. The top two candidates were
implemented behind study switches and run through the
[`docs/BENCHMARKING.md`](../BENCHMARKING.md) protocol (≥10 seeds/cell,
common-random-number pairing via `Solver::set_random_seed`, deterministic
metric = conflicts-to-verdict, treatment/matched-null ratio). **Both failed
the null comparison.** The switches stay in the tree (`doc(hidden)`, env-gated,
default-off) so the studies can be reproduced; no default behavior changed —
verified by bit-identical trajectories on the tracking instances.

## Study 1: mode-gated heuristic bumping (cadical `bump_variable`)

`OXIZ_BUMP_MODE_GATE=1`: conflict bumps reach only the active mode's
structure — VSIDS scores in stable, VMTF queue in focused — instead of the
historical double maintenance. `OXIZ_BUMP_MODE_GATE_NULL=1`: same structural
change, but stable-mode score bumps go to *random* variables of the same
count (scrambled signal).

Single-seed screening was promising on two instances and the full 10-seed
screen killed it:

| instance | base | treat | null | T/N |
|---|---|---|---|---|
| constraints_17 (SAT) | 28,176 | 21,282 | 46,647 | **0.456** |
| crn_11_99_u (UNSAT) | 93,134 | 95,859 | 122,672 | 0.781 |
| qwh.50.1250 (SAT) | 95,147 | 111,129 | 135,068 | 0.823 |
| summle_X4044 (SAT) | 104,832 | 119,710 | 102,047 | 1.173 |
| frb65-12-2 (SAT) | 423,828 | 546,220 | 465,249 | 1.174 |
| stable-300 (SAT) | 929,883 | 823,985 | 431,532 | **1.909** |

(The first three rows are from the reduce study's shared screening below;
mode-gate rows: see git history of this file for the 4-instance screen —
constraints_17 0.49, mrpp 0.58, but 6s167-opt 1.18 *null-better* and mrpp
1.11 worse than baseline.) Verdict: heterogeneous chaos with no consistent
treatment/null separation → dropped.

## Study 2: cadical `reduce.cpp` port (schedule + glue/used retention)

`OXIZ_CADICAL_REDUCE=1`: reduction scheduled like CaDiCaL (first at conflict
300, then `25·√conflicts` apart, ×log₁₀(irr/1e4) above 1e5 irredundant),
selection by `(glue desc, size desc)` over non-reason learned clauses after
tier protection (glue≤2 && used>0; glue≤6 && used≥30), deleting the worst
75%. Replaces the fixed-12000-conflict tier-percentage reduce.
`OXIZ_CADICAL_REDUCE_NULL=1`: identical trigger points and deletion counts,
clauses chosen uniformly at random (partial Fisher–Yates).

12 instances × 10 seeds × 3 arms, median conflicts:

| instance | fam | base | treat | null | T/N |
|---|---|---|---|---|---|
| 6s167-opt | UNSAT | 125,828 | 123,708 | 127,562 | 0.970 |
| crn_11_99_u | UNSAT | 93,134 | 95,859 | 122,672 | **0.781** |
| constraints_17 | SAT | 28,176 | 21,282 | 46,647 | **0.456** |
| mrpp_4x4#12 | UNSAT | 287,065 | 300,531 | 301,156 | 0.998 |
| qwh.50.1250 | SAT | 95,147 | 111,129 | 135,068 | 0.823 |
| summle_X4044 | SAT | 104,832 | 119,710 | 102,047 | 1.173 |
| stable-300 | SAT | 929,883 | 823,985 | 431,532 | **1.909** |
| frb65-12-2 | SAT | 423,828 | 546,220 | 465,249 | 1.174 |
| si2-b03m-m800-03 | SAT | 42,320 | 42,849 | 43,905 | 0.976 |
| Break_unsat_06_07 | UNSAT | 32,990 | 34,196 | 34,977 | 0.978 |
| g2-ak128boothbg2msisc | SAT | TO×3 arms @60 s | — | — | — |
| barman-pfile06-022 | UNSAT | 1,267 | 1,200 | 1,190 | 1.008 |

T/N geomean: UNSAT 0.943, SAT ≈0.99 (excluding the all-timeout instance).
Verdict per the rule "ratio ≤ 1 ⇒ nothing": **dropped as a default change.**

Notable observations for whoever revisits clause-db management here:

* On `stable-300`, *random* deletion at cadical trigger points beats
  glue-ranked deletion by ~2× (median over 10 seeds) and beats both the
  baseline schedule and the treatment. Either that instance rewards raw DB
  churn (fresh clauses) rather than retention quality, or the used-stamp /
  LBD signals are misinformative there. One instance is not a policy, but it
  is a lead: the retention *signal*, not just the schedule, may be wrong.
* The treatment's two clear wins (constraints_17 0.456, crn_11 0.781) show
  the early-first-reduction schedule does matter on some families; any
  future attempt should start there and hunt for the interaction that makes
  stable-300/frb65 pay for it.
* Seed sensitivity dwarfs everything: baseline mrpp alone swings
  159k→460k conflicts across seeds (≈2.9×); single-seed A/B numbers on such
  instances are worthless (reconfirmed live twice during this study).

## What was NOT ported (recorded omission)

cadical's satisfied-clause sweep + falsified-literal removal at reduce time
(`collect.cpp`) was deliberately left out to isolate schedule+retention; its
absence is one candidate explanation for the neutral result. Also unported:
`propagate_out_of_order_units`. Both would need their own controlled pass.

## Soundness / regression status

All runs across both studies produced identical verdicts per instance across
arms and seeds (no arm ever flipped SAT/UNSAT). Full workspace suite,
clippy/fmt/doc, and the Z3 parity suite (168/168 correct, 0 wrong) clean on
the commit carrying these switches. Default-path trajectory preservation
re-verified post-commit (`170039/550301/19369185` on 6s167-opt).

## Remaining candidates from the original list

* mid-search vivification cadence (cadical vivified 1126 clauses on
  6s167-opt where oxiz vivifies only pre-search);
* OTFS during analysis (880 events on the same instance);
* tick-accounting correction (still gated behind its own study).

Given two consecutive kills under proper controls, the prior that "porting
individual cadical policies onto this codebase transfers CaDiCaL's search
power" should be treated as weak. The alternative hypothesis — that the gap
comes from an interacting *system* property (e.g., phase/target handling
during stabilization, or EVSIDS ordering dynamics in long stable phases)
rather than from any single policy — now has more support than any specific
policy hypothesis tested so far.
