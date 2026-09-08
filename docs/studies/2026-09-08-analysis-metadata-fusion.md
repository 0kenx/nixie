# Conflict-analysis metadata fusion: registered cost screen

The target is ordinary Nixie's cost per conflict. The user's `6333f83`
mode-matched panel still shows substantial wall time per conflict even on
instances with similar or fewer conflicts than Kissat. Solver tick totals
are not interchangeable with hardware cycles or with each other's counters.
This experiment changes the implementation of existing bookkeeping, with
exact search identity required; it introduces no search policy.

## Implementation and null

First-UIP resolution repeatedly fetches the same clause to increment usage,
read/promote its tier, check low glue, add activity and finally walk literals.
Replace that sequence with one validated header read, combined metadata writes,
and the ensuing literal view. Preserve the original-clause no-op, deleted
header behavior, saturating usage byte, Local/Mid/Core transition order,
unmodified flag bits, exact f32 addition, reduction recency/histogram updates,
and LRAT antecedent order. The clause-traffic observer must still see the
pre-update state. Keep the scalar sequence as a test-only oracle.

Baseline/null is the committed ordinary solver including the arena repair
landed with this registration. Pin its actual SHA and release binary hash in
the records before running anything. The candidate adds only the fusion and
its tests. Neither arm uses the rejected grouped watcher representation.
Both are built from clean committed sources with the same lockfile, compiler
and release settings. No dirty-tree binary is admissible.

This is an engineering comparison: the null does identical semantic work on
an identical trajectory. Any discrepancy in clauses, proof, model, counters
or observed state is a failed correctness gate, not evidence of a heuristic
benefit. Exhaust all usage/flag encodings and glue boundaries against the
original update sequence, compare explicit per-clause state in paired solves,
and independently check small SAT models and UNSAT LRAT proofs.

## Four fixed cells, no tuning

Use circuit_48in64out and j3037_10_mdd_bm1 from `satcomp2024/bench`, whose exact
content hashes are already recorded in the recent throughput studies. Run
baseline and candidate once each, seed 0, at 40,000 conflicts, CPU 10, CaDiCaL
preset, ordinary release features, `NIXIE_SWEEP=0`, model output enabled.
All other study overrides are cleared. Order: circuit baseline, circuit
candidate, j3037 candidate, j3037 baseline. Reuse an existing exact cell if
present; record each new cell once in `precompile/<sha>/benchmark/runs/`.
A 300-second emergency timeout cannot become a policy input or a repeat.

Measure whole-process user instructions as the primary complete-work counter;
report user cycles/conflict, branch misses, conflicts, verdict and secondary
wall time. Require one active PMU, at least 99.9% scheduling coverage, and
byte-identical solver stdout in each pair. A conflict-budget `Unknown` is a
prefix-cost observation, never a solved or independently verified verdict.

Advance only if geometric-mean instructions and cycles/conflict ratios are
both at most **0.95**, neither individual ratio exceeds **1.03**, and all
identity/correctness gates pass. Otherwise record the finding and stop this
candidate without tuning or repeated cells. Four cells are a rejection screen,
not a broad performance claim or a substitute for a multi-seed heuristic
study. A positive screen still requires all repository correctness gates and
fresh SMT differential parity before production landing.
