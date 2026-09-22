# Binary extension-field performance study

The pre-registered workload, controls, counter-coverage argument, acceptance
bar, and run-once protocol are in `bench/ff_extension_perf/README.md`.
Production baseline is `df564313`; the benchmark-only commit adds no solver
changes. CPU instructions, not elapsed time, are the primary metric.

## Preflight finding, before measured cells

Untimed functional checks validate all 13 generated cases at seed zero.
The initial budget probe used a depth-64 shared square/add expression over
F256; it produced no verdict within the external 120-second safety cap.
A short sampled profile of that running process concentrated on one tight
loop, but the cached release executable is stripped, so that sample does
not identify a source-level cause. Preserve it as diagnostic evidence,
not a completed performance cell or an instruction ratio.

The measured budget probe is fixed at depth 16, which returns Unknown.
The depth-64 input is retained as a separate diagnostic and must be
investigated with a symbol-enabled build. No measurement or benchmark cell
was rerun; these were functional checks without cost collection.

## Results

All 130 baseline cells (13 cases x seeds 0..9) completed and were checked
by the independent harness. Baseline records belong to benchmark-only
`a2698f3c`, whose production code and release CLI are identical to `df564313`.

The symbol-enabled diagnostic identifies `track_theory_vars` as the deep
DAG bottleneck: its FF compound arms omitted the scope-journalled memo used
by other compounds. A depth-n shared square/add chain was revisited once per
path (exponential), before the bounded FF evaluator could run. The sampled
stack profile lost samples under IO load and is used only for source-level
identification, not cost percentages. A separate zero-loss instruction
profile (410 samples) also identifies BigUint shift/XOR and allocation in
the binary evaluator as material costs.

Before collecting treatment cells, the candidate is fixed to two changes:
use the existing scope-journalled memo for FF compounds, setting the honesty
flag before a memo hit; and use checked u32 operands/u64 intermediates for
degree <=32 shift-and-reduce multiplication. Coefficient-loop budget charges
remain identical, including multiplication by zero. Wide fields retain the
original BigUint loop. No variable/child/enumeration order changes and no
heuristic policy are introduced. The acceptance bar and workload matrix are
unchanged. The depth-64 diagnostic will additionally become a regression;
no capped baseline is converted into a made-up speed ratio.

Paired instruction results and final verification are pending.
