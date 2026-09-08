# Elimination first-parent preparation: census below the registered gate

**Verdict:** stop after the single registered observation. Reusable
first-parent inspections were **48.29%**, below the required **50%**.
The independent model check and scalar-output identity passed. No throughput
prototype or cost comparison was run; this is not a measured speedup or
regression. The registration below is unchanged.

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

## Observation result: do not advance

Observer source commit `ba5602f800fd532152807669bc19eac540973363` is based
on the registration commit `691b53b` and contains only the feature-gated
census, its tests and the one-cell runner. The ordinary solver remains the
fixed scalar implementation from `e15d0bf`. The observer binary SHA-256 is
`e82ef09034b06beeb3d901c629d676bbb5f8e4279a192c7f7702bc5b54b9abd7`;
rebuilding from the clean committed source produced the identical binary.

The sole measurement is si2, seed 0, the registered 40,000-conflict cap and
CPU 10, with sweep disabled. It returned SAT after **39,246 conflicts**,
182,307 decisions and 960,337 propagations. Every original CNF clause was
checked against its emitted model. Complete stdout matches the cached
`490756d` output byte for byte, with SHA-256
`c25ba0a9a391a198ca92943e0e5f07eab463efa505980699e3245d712173d30f`.
This uses the cached output only as a correctness/trajectory oracle.

The ten elimination rounds reported:

| Observation | Count |
|---|---:|
| First-parent rows | 25,576 |
| Resolution calls | 558,406 |
| First-parent literal inspections | 4,202,661 |
| Second-parent literal inspections | 2,871,855 |
| First-parent marked literals | 3,642,829 |
| Second-parent resolvent appends | 2,030,174 |
| Tautological pairs | 255,845 |
| Same-parent pairs following a tautology in the same row | 250,787 |
| Reusable first-parent inspections | 2,029,374 |
| Reusable first-parent marks | 1,782,621 |

Reusable inspections are **48.2878%** of first-parent inspections and
**28.6857%** of all 7,074,516 resolution literal inspections. The total-work
fraction clears its 25% gate; the first-parent fraction misses its 50% gate.
All round-level resolution-call accounting checks and every credited
preparation's inspection/prefix agreement check passed.

The conservative scope loses reuse after all 302,561 non-tautological
outcomes, as registered, even where an ordinary collected resolvent has no
immediate effect. That boundary leaves too little observed reuse to pass
the agreed gate. Do not lower the threshold, select later rounds, or try
another seed to rescue this result. Broader reuse across non-tautological
outcomes would be a different design with additional mutation/proof lifetime
obligations; this observation does not qualify it. It also does not estimate
the whole-solve instruction or cycle saving from this literal-scan fraction.

The observer passed all **1,003 SAT tests** (one existing skip), including
seven new accounting/coverage tests and the 19,683-case resolution
truth-table regression. SAT all-feature/all-target Clippy with warnings
denied, workspace formatting, and the ordinary release observer build also
passed. The observer is archived rather than added to production; no solving
code changes land with this result, and no full-workspace qualification is
claimed for it.

Record **`22045fa22e9f7331`**, configuration hash `721f929960f13064`, lives
under `precompile/ba5602f/benchmark/runs/elimination-parent-reuse/`.
`precompile/ba5602f/benchmark/elimination-parent-reuse/` preserves the raw
stdout/stderr, started/completed markers, manifest, summary, qualification
logs and source/binary identity. The captured nextest pass listing is
partially truncated; its successful final summary is retained. The adjacent
`source.bundle` and `source.patch` preserve the complete observer and runner;
the verified bundle requires `691b53b`. The unused experiment worktree and
branch are removed after recording this result. Stage B's four cost cells
were not run.
