# Elimination first-parent preparation: registered census and cost screen

The [mark-cleanup repair](2026-09-08-elimination-mark-cleanup.md) is on main
as `e15d0bf`. The remaining hypothesis is that consecutive resolution pairs
repeatedly prepare the same first parent even when the preceding pair was
tautological and changed no clause or assignment. Reusing that preparation
could remove literal scans, buffer pushes and mark/unmark stores while
preserving every pair, resolvent, proof event and budget decision.

The cached si2 profiles after the absolute-cursor repair attribute roughly
11% of cycles to `elim_round`; the resolution helper is inlined into it.
Those samples do not isolate this opportunity. The older g2-slp resolution
profile is not evidence of a current gain on the user's anchors.

## Stage A: one observation run

Instrument the existing scalar path behind a dedicated compile-time feature.
Count every resolution call, first/second-parent literal inspection,
first-parent marked literal and second-parent resolvent append. A row is one
first-parent occurrence in `elim_resolvents_bounded`. Reset eligibility at
each row boundary. A first-parent preparation is reusable only when the
preceding examined pair in that same row was tautological. Missing/deleted
second parents skipped by the caller have no effects and do not break the
interval. Every non-tautological helper outcome ends eligibility, including
ordinary collected resolvents; this intentionally uses a conservative scope.

Report first-parent inspection and marked-prefix agreement on each eligible
reuse. Counter overflow is an error, never silently saturated or wrapped.
Counters are observations only: they must not enter solver decisions. Their
instrumented runtime is not a performance metric.

Run **si2-b03m-m800-03 only**, seed 0, MAXC=40000, CPU 10, CaDiCaL preset,
ordinary release optimization, `NIXIE_SWEEP=0`, model output enabled and other
study overrides cleared. Use the committed observer binary, a 300-second
emergency timeout, and the result store. No repeated cells. Check the SAT
model independently and require complete stdout identity with the cached
scalar si2 output (`490756d`, sparse-word-subsumption record
`e45297cb1743dd83`). That older control is an output oracle only; no new
performance comparison is made against it.

Advance to a prototype only if all identity/accounting checks pass, at least
1,000 resolution calls were observed, reusable first-parent inspections are
at least **50% of all first-parent inspections**, and at least **25% of all
resolution literal inspections** (first plus second parent). These are
component opportunity gates, not a claim of whole-solve savings.

## Stage B: at most four cost cells, conditional on Stage A

If the census passes, implement reuse with an explicit row lifetime. Leave
the ordinary helper's cleanup contract intact; clear retained marks before
every effect and before leaving a row, including all early returns. Preserve
parent order and literal order. Compare batched and scalar state/proofs on
small formulas, including satisfied/deleted parents, units, both strengthening
directions, tautologies, clause-bound exits and row changes.

First run clean scalar `e15d0bf` then the committed candidate on si2 with the
same settings. Stop unless whole-process user instructions are non-increasing,
cycles/conflict is at most **0.95**, and full output is identical. Only after
that pass run circuit candidate then scalar at the same seed/cap. Final
advancement requires geometric-mean cycles/conflict <= **0.95**, instructions
<= **1.00**, neither cycle ratio > **1.03**, and all identity/model checks.
Require one active PMU and >=99.9% event scheduling coverage. Wall time is
secondary. Do not tune the batch policy on these measurements.

This is at most **five new solver runs** including the observation, stopping
after one if Stage A fails or three if the first cost pair fails. Reuse
existing cells if any exact identity already exists. A successful screen
still needs broader qualification and every workspace/soundness gate before
a production landing. Archive a rejected implementation and commit its
finding to main. The goal remains the mode-matched Kissat throughput gap.
