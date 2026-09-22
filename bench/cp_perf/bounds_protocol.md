# CP scheduling bounds reuse, with Z3 performance reference

Pre-registration, 2026-09-22, before performance cells or producer changes.
Baseline source df564313 includes the previous borrowed-trial optimization.
A diagnostic profile of its unchanged CP producer in cached b1c8f0ab attributes
about 91% of samples to cumulative feasibility; repeated min/max domain scans
are prominent. Confirm the target against the newly built baseline too.

Candidate: reuse exact domain extrema lazily within one callback. Borrow the
immutable domain snapshot; singleton trials bypass the cache and never update
it. Keep visits, first witnesses, consequences, explanations, BigInt arithmetic,
proof checking and solver search policies identical. No cross-callback cache.
The old producer is the exact-computation control, not a heuristic placebo.
Reject any changed Nixie transcript or correctness oracle result.

Primary requested external reference: installed Z3 4.16.0, native SMT-LIB QF_LIA
with finite Int start domains, Boolean presences and exact cumulative load
checks at every task start. Starts/ends are half open. Every Z3 model is checked
independently using Python arbitrary-precision integers, including domains,
presence assumptions, shared conditions and capacity. No Unknown/timeout is a
solved or agreeing result. Record model validation failures and stop.

Reference grid: the existing public CP driver, seven families (unknown,
present, absent, shared, blocked, wide, sparse), 4x4 and 8x16 task/domain shapes,
ordinary and certified Nixie, two push/check/pop rounds. Z3 performs the same
rounds and returns its start/presence assignments. All cases have explicit SAT
witnesses; this is admission/integration cost, not hard packing or UNSAT search.
CP callback diagnostics retain the existing 8x8/32x16 grid.

Ten selection seeds 0..9, reserve 10..19 for confirmation. Rotate value order
and set solver seeds for both engines. Pin CPU 0; primary metric is complete
process user instructions via perf stat, require unscaled/non-multiplexed
coverage >=99%. Includes Nixie's construction, all solver and checker work,
output/destruction; Z3 includes parsing, solving and model extraction. Python
Z3-model validation is outside the measured process and reported explicitly.
Wall time is diagnostic on this loaded host. Outer cap 120 s, never policy.

Reuse immutable benchstore cells. Configs include hashes of the driver and
reference harness; Z3 version/binary hash identify the reference. Its git
field identifies the benchmark-driving Nixie revision, not Z3's source Git
commit (as in the existing heap reference studies). Cache binaries before
measurement; never benchmark a mutable cargo target.

Report Nixie/Z3 instruction geomeans by family, shape and ordinary/certified
mode, plus current/previous Nixie ratios with exact output identity. Show
baseline per-cell distributions and solved-at-cap. Go bar: callback geomean
<=0.90, no callback family >1.05, and neither ordinary nor certified geomean
>1.05 vs current Nixie; require >5% end-to-end gain or the documented inert
component-gain/neutral-system corollary. Confirm on fresh seeds. Do not claim
whole-solver speed or compare callbacks directly with Z3. Record negative
results; finish all AGENTS.md gates, land main and clean up.

## Pre-registered second stage: model replay evaluation reuse

The selection results for bounds alone are callback ratio 0.8309 and ordinary
end-to-end ratio 0.9670 (neutral). The larger sparse-case profile attributes
most samples to model evaluation. Inspection shows the independent model gate
re-evaluates watched atoms in statement checks and repeated consequences.
Before measuring a second candidate, freeze merged bounds-only c6e4d9c3 as an
ablation control. Reuse only Boolean results concretely evaluated in the current
model-validation invocation; never use SAT phases or callback fixations as a
source of truth. Retain every statement and certificate check, vocabulary guard,
callback event and consequence order. No persistent cache or evaluator rewrite.
False and undetermined results must still fail closed. Check changed models,
negated/formula watches, false reasons and unregistered certificates explicitly.

Use the same reference/diagnostic grids and unchanged driver/harness. Compare
second-stage candidate against c6e4d9c3 for isolation and df564313 for the full
change (disclose intervening unrelated theory fixes). Reserve seeds 10..19 for
final confirmation; select no policy or threshold from these data. Require
identical Nixie transcripts and >5% ordinary/certified instruction reduction
without a >5% family regression. Run the ignored model-certification canary in
addition to all normal gates because this stage touches model validation.
