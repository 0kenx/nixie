# Eager watch normalization throughput experiment

## Registration

Baseline is `0263862` (solver source unchanged through `2bd403c`). The user
requested closing the Kissat gap while reducing the number of runs. Reuse
the completed mode-matched baseline cells; do not repeat reference runs.

Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp` compute the other
watched literal with the XOR of the watched pair and the falsified literal.
Apply that identity in Nixie, then **always** store the normalized pair
before testing satisfaction. This differs from the rejected on-demand
normalization: the final literal order remains exactly the old conditional
swap's order on every visit, including both satisfied paths. No heuristic,
watch order, counter, proof, or assignment change is intended.

Screen seed 0 on `break_unsat_06_07` and `circuit_48in64out` using cached
release baselines, the existing full-invocation PMU runner, and CPU 10. Stop
on trajectory divergence or an obvious cycle regression. If promising,
confirm on seeds 1–3 for break, crn, circuit, and si2 (12 new cells, cached
baselines), with j3037 seed 1 as a larger held-out workload. No ten-seed
sweep: this is the user's reduced-run scope. Report the small sample and
the restricted panel explicitly. Primary metric is instructions; require
cycle confirmation. A landing needs at least 5% lower geometric-mean cycles
on the confirmation panel, non-increasing instructions, and no input over
5% worse. Do not generalize this to the full competition corpus.

Before landing solver code, require exact diagnostic/model identity on
paired cells, focused tests of both watch orientations and all visit exits,
SAT differential/model checks, full workspace verification, and fresh Z3
parity using the available version. A rejected screen is recorded here.

## Verdict: rejected at the two-cell screen

Both outputs were byte-identical to baseline, including the checked circuit
SAT model. Instructions fell 1.33% / 1.19% and branch misses fell 14.56% /
14.05% on break / circuit, respectively, but cycles rose 5.65% / 23.67%.
The unconditional writes do not establish lower hardware cost. This is a
rejection screen, not a multi-seed regression estimate or an attribution
of the cycle increase. The candidate was removed; no confirmation sweep
was launched. Do not repeat eager XOR normalization solely to eliminate
the orientation branch. Archived patch, binary and PMU records are under
`precompile/2bd403c/benchmark/`.
