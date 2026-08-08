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
