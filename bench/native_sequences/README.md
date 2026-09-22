# Native sequence performance versus Z3

Pre-registered on 2026-09-22 before executing the corpus. This compares the
landed Nixie `3a42cb2d` binary with installed Z3 4.16.0. It changes no solver
or search policy, so a heuristic treatment/matched-null experiment does not
apply. Do not interpret a cross-solver comparison as an optimization study.

Run `python3 bench/native_sequences/perf.py`. Defaults: CPU 6, six-second
external supervision cap, ten requested seeds (0–9), alternating solver
order. The complete manifest is written before measurements. Every cell is
saved immediately under `precompile/3a42cb2d7e7b3f8612a6b2d9abe760616919d133/
benchmark/native-sequences-z3-perf/` and reused on subsequent invocations.
`--summarize-only` reads those records without executing solver cells.

Primary metric: whole-process retired user instructions, measured with
`taskset -c 6 perf stat -x, -e cpu_core/instructions/u`. This covers startup,
parsing, shape materialization, scalar solving, independent model validation,
and result printing, including dynamically linked user libraries. Kernel
instructions are excluded. Accept only one numeric counter at 100% enabled;
no multiplexed/scaled measurements or retries. Counts are a hardware work
proxy with small process/allocator variability, not exact abstract ticks.
Wall time is secondary and includes perf launch overhead and machine load.

Report solved counts, failures/Unknown/timeouts, and per-case ten-seed
min/median/max instructions. Ratios use only pairs with both expected decisive
verdicts and valid counters; report excluded cases explicitly. No timeout or
Unknown is a cheap solve. No speedup claim follows from a wall-time ratio.
Fixed launch cost may dominate these deliberately small obligations. Report
size scaling, and do not extrapolate to arbitrary TLA specifications.

Corpus: append length, queue tail read, split/rejoin disequality, and history
element constraints at lengths 8, 32, 128, 512; empty, concat disequality,
nested congruence; three unsupported-fragment probes. These are identical
native SMT inputs for both solvers. `seq.update` is excluded because this Z3
version does not implement that operator; the semantics differential suite
separately tests its reference-definition translation.

Expected answers have direct mathematical arguments: append adds one;
tail position n−2 is original position n−1; splitting at n/2 and rejoining
recovers a length-n sequence; history `[0,...,n−1]` is a witness. Extraction
at the end is empty. Distinct a=0,b=1 witnesses concat disequality; equality
of a,b implies equality of nested singletons. For the unsupported probes,
symbolic append is the same length identity, a constant-seven length-eight
sequence with i=0 witnesses symbolic read, and empty a,b witness the word
equation. A disagreement stops the runner immediately after recording it.

No solver proof checking is claimed here. Nixie's SAT path independently
validates its models; native UNSAT proof export is unsupported. Thus raw
records intentionally use `nixie-sequence-perf/1`, alongside the canonical
store, rather than falsely setting benchstore's mandatory
`verified_model_or_proof=true` field. Identity includes host, binary hash,
revision, input hash, seed, CPU, event and cap. The run-once/reuse protocol
still applies; raw errors and rejected counts survive for audit.

Seed caveat identified before measurement: `Solver::set_random_seed` seeds
the outer SAT state, while `check_sequences` constructs its child with only
`self.config.clone()`. It does not propagate that SAT RNG state. Consequently
ten requested Nixie seeds are repeated measurements of the current default
child search, not ten independently seeded native search trajectories. Z3
receives all ten seed options. No tuning or reseeding fix is part of this
benchmark. This limitation must remain in the result interpretation.
