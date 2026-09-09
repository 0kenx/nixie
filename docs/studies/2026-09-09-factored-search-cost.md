# Remaining search cost on the fixed factored circuit

Registered before measurement. The exact relation transformer already has a
checked 700-group, sixfold literal-storage reduction and a verified SAT
model on this input. Its [feasibility study](2026-09-08-relation-factorization.md)
left substantial search cost and explicitly identified that cost as the next
target. This study profiles that fixed representation; it does not select a
new encoding, change solver policy, or claim a factorization speedup.

The preliminary source audit checked occurrence rebuilding. Forward
subsumption builds its index in candidate-size order, while elimination
connects original clauses in clause-ID order and mutates their occurrence
lists during each round. Sharing those indexes is not a simple removal of
duplicate work. Watch rebuilds also reset ordering visible to later search.
The older capacity-persistence experiment already rejected allocator-count
arguments. No new occurrence implementation is justified by those facts
alone; first measure the remaining cost on the reduced representation.

## One profile, then at most one traffic observation

Use committed solver source `1f3f316`, the lockfile retained with that
commit, portable release optimization, and the repository's `perf` profile
(release optimization plus debug information and retained symbols). Cache
the new binary and remove its build worktree. Reuse
`precompile/f033bfa/benchmark/relation-factorization-feasibility/circuit.factored.cnf`;
do not transform the input or rerun old controls or Kissat.

The sole initial solver invocation uses CPU 10, seed 1, CaDiCaL preset,
MAXC=10000000, sweep disabled, model printing enabled, and a 300-second
emergency timeout. Clear other study overrides. Record user-space cycles
with a fixed period of 500003 and DWARF call stacks, using the CPU's atom
PMU. Pin outside perf. Retain raw data, symbols/binary identity, flat and
inclusive reports, exact commands, stdout/stderr and completion status.
Outer perf stat counts whole-invocation user instructions/cycles and event
coverage; these totals include the recording process and are explicitly
**not ordinary solver cost measurements**. They must not be compared with
unprofiled controls. Transformation and certificate auditing are outside
this fixed-input search diagnostic.

Require at least 10000 cycle samples, no lost samples, one active PMU,
at least 99.9% counter scheduling coverage, and an independently checked
SAT model on both the factored and original CNFs. An Unknown, timeout,
invalid model or inadequate profile rejects the completed-solve diagnosis;
retain it without rerunning the cell. Compare printed search counters with
the old feasibility record as historical context, not as a causal comparison.

If inclusive propagation accounts for at least 50% of sampled user cycles,
run exactly one existing `clause-traffic` observer from the same committed
source, with stride 16 and otherwise identical settings. It must have
byte-identical complete stdout and independently verified models. Require
at least 1000 sampled clause-epoch rows and complete accounting without
observer limit/overflow errors. Its instrumented runtime is not a cost
measurement. Report visits, payload accesses and scanned literals by
original/learned origin and clause width; the existing 4096-conflict epochs
give an early/late breakdown.

The next implementation target follows these prespecified diagnostic rules:

- If propagation is below 50%, target the largest non-propagation component
  only if its inclusive share is at least 10%; otherwise retain the diffuse
  profile without proposing a small local optimization.
- If propagation dominates and original five-literal clauses contribute at
  least 40% of sampled propagation payload accesses plus tail scans, study
  an engine specialized for the fixed factored representation.
- If that original-clause gate fails but learned clauses contribute at
  least 50% of the same work, target the learned-clause path instead.
- Otherwise the representation-specific hypothesis does not advance.

These are opportunity gates, not predicted savings or a default-flip gate.
The traffic counts are an unweighted work proxy and must not be converted
directly into cycle savings. One input and one seed cannot establish a
general improvement. Any behavior-changing prototype still requires a
sound matched null and the seed protocol; a trajectory-preserving prototype
needs an independently registered cost screen. This step uses at most two
new solver runs, recorded once in the result store, and lands its diagnosis
and next target on main.
