# Inline the existing trail assignment core

## Registration

The cached baseline assembly still calls `Trail::assign` at both propagation
assignment sites (`3dd6e` and `3e188`), despite the cold
growth split's intention to inline the routine. Promote its existing inline
hint to `inline(always)`. This changes no source-level operation or data
representation. Growth remains cold and out of line. Reference Kissat
`fastassign.h` and CaDiCaL's propagation assign helpers inline assignment.

Screen break and circuit at seed 0 using cached `0263862` release baseline,
CPU 10, the existing complete-work PMU protocol. Exact output/model identity
is required. If promising, use seeds 1–3 on break, crn, circuit, and si2 plus
j3037 seed 1; reuse baseline/reference cells, honoring the user's reduced
run count. Instructions are primary with cycle confirmation. Performance
claim bar: confirmation geomean cycles at most 0.95, instructions at most
1.00, no input above 1.05 cycles. Full workspace gates, SAT differentials
and fresh available-Z3 parity are required before source landing.

## Verdict: rejected at the two-cell screen

Outputs remain byte-identical. Instructions T/B: break 0.9966, circuit
0.9985. Cycles T/B: 1.0172 and 1.0461. The annotation does not establish
a useful cycle saving; it was removed without a confirmation sweep.
These two cells do not isolate the cause of the cycle movement or establish
a multi-seed regression. Patch, binary and records are archived under
`precompile/1d217a2/benchmark/`.
