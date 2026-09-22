# CP domain-exclusion witness reuse

Pre-registration, 2026-09-22, before producer edits or performance cells.
Baseline is main 345ecfec, including bounds and model-evaluation reuse.
The diagnostic profile of the preceding optimized binary attributes 18% of
the larger sparse schedule to `CpModel::explain`; finding a positive domain
premise repeatedly scans the full reason list and each domain's indicators.
Confirm that target on the current baseline before editing the producer.

Candidate: retain the position of a fixed positive indicator while constructing
the callback's existing immutable domain/reason snapshot. For exactly-one
exclusions, use that position and the already known domain to construct the
same witness. Independently check every certificate with the unchanged checker.
Keep every consequence, premise, first constraint witness, callback event and
search decision unchanged. Conflicts keep the existing witness search. The
index is local to one callback; no state crosses a push/pop or model boundary.
Invalid hints fail closed. No heuristic, propagation rule or budget changes.

The exact old computation is the control; require byte-identical driver
transcripts, including reasons/certificates and solver search counters. Add
exhaustive comparison with the existing witness search, and run independent
CP semantic/proof oracles. Reject any mismatch. This is a producer-only
engineering change, not a policy needing a randomized matched null.

Use the unchanged `reference.py` grid and build profile: seven families,
4x4 and 8x16, ordinary/certified, two scoped rounds, pinned CPU 0, whole-process
user instructions with >=99% PMU coverage. External reference is installed
Z3 4.16.0; reuse its matching df564313 cells (seeds 0..19) without rerunning.
Use ten selection seeds 0..9 and ten confirmation seeds 10..19, paired across
Nixie revisions. The latter are fresh to this candidate, not new corpus data.
Freeze committed binaries before measuring; retain manifests, locks, hashes,
profiles and immutable benchstore records. Wall time is diagnostic only.

Go bar: ordinary and certified instruction geomeans <=0.95 of the current
baseline, no family >1.05, with the same result on confirmation seeds. Report
Nixie/Z3 separately from current/previous Nixie, baseline distributions,
per-family/size ratios and solved-at-cap. Retain callback diagnostics on the
existing 8x8/32x16 grid; no callback family may regress >5%. These are SAT
admission/integration microbenchmarks, not hard packing/UNSAT or a general
solver speed claim. Z3 model checking runs outside its measured process;
Nixie's model/certificate checking is included. Keep all certification gates.

Complete release-mode AGENTS.md verification, Z3 parity and the perf landing
gate before landing. Record negative experiments rather than dropping them.

## Second stage, before its edits or measurements

The first candidate 0bb2d4f6 has identical transcripts but selection ratios
0.9629 ordinary / 0.9637 certified: neutral and below the go bar. Keep it as
an ablation, not a standalone performance success. Its profile still shows
domain construction/filtering prominently. Inspection finds two redundant
operations: unknown indicators scan the current BigInt domain for membership,
and domain reconstruction clones values which it discards when a true
indicator fixes that domain.

Use the same snapshot's fixed-premise flag to answer membership for an unknown
indicator: with validated unique values and a valid snapshot, it is excluded
exactly when a different indicator is fixed true. Continue all global trials
in their original order, even for such excluded candidates. During snapshot
construction, borrow the fixed value and stop cloning alternatives once one
is seen; materialize the same final domain. Check snapshot identity against
an independent reconstruction for every partial assignment, including invalid
states. No scheduling rule or explanation change. The full candidate must
meet the original go bar against 345ecfec; report the 0bb2d4f6 ablation too.
Confirmation seeds 10..19 remain unmeasured for either candidate.
