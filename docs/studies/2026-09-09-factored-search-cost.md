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
original/learned status, and learned-clause width. The existing collector
aggregates original clauses across widths and epochs; only learned rows
support a width or early/late breakdown. This capability correction was
recorded before either solver invocation. Total original work is therefore
only an upper bound on original five-literal work.

The next implementation target follows these prespecified diagnostic rules:

- If propagation is below 50%, target the largest non-propagation component
  only if its inclusive share is at least 10%; otherwise retain the diffuse
  profile without proposing a small local optimization.
- The representation-specific engine needs original five-literal clauses
  to contribute at least 40% of sampled propagation payload accesses plus
  tail scans. If even total original work is below 40%, reject that gate.
  A larger aggregate does not establish a pass; it requires a subsequent
  width-resolved observation before that engine can advance.
- If the representation-specific gate fails or remains unestablished but
  learned clauses contribute at least 50% of the same work, target the
  learned-clause path instead.
- Otherwise the representation-specific hypothesis does not advance.

These are opportunity gates, not predicted savings or a default-flip gate.
The traffic counts are an unweighted work proxy and must not be converted
directly into cycle savings. One input and one seed cannot establish a
general improvement. Any behavior-changing prototype still requires a
sound matched null and the seed protocol; a trajectory-preserving prototype
needs an independently registered cost screen. This step uses at most two
new solver runs, recorded once in the result store, and lands its diagnosis
and next target on main.

## Result: measurement rejected; second invocation cancelled

Exactly **one new solver invocation** ran. It returned SAT with **91833
conflicts**, 315010 decisions and 8369710 propagations. Independent checks
accepted its model against both the fixed factored CNF and the original CNF.
Its complete stdout is byte-identical to the retained feasibility solve
(`87eb5896119b2e0d389bd7495929722291351a3889509b1c549dab3c593814c4`).
This confirms the observed search counters and witness at the new committed
source; it does not measure a speedup.

The profile **fails the preregistered quality gate**:

| Check | Observed | Verdict |
|---|---:|---|
| At least 10000 cycle samples | 13323 | pass |
| No lost samples | 589, reported through 207 lost-record chunks | fail |
| One active PMU in outer stat | nonzero `cpu_atom` and `cpu_core` events | fail |
| At least 99.9% event scheduling coverage | `cpu_atom` reported 99.00% | fail |
| Both SAT model checks | accepted | pass |

The raw stream also contains **6562 throttle** and 6563 unthrottle records.
The host's `perf_event_max_sample_rate` was 2000 when inspected after the
run. The fixed period of 500003 cycles, an 8192-byte stack per sample and
the default recording buffer did not produce a complete profile on this
host. `perf report` shows implausible caller addresses such as `0x1f` and
does not reconstruct the full solve stack. The binary does contain frame
description entries covering `main`, `propagate` and `subsume_round`, so
missing unwind tables alone is not an established explanation. The exact
cause of the caller reconstruction and outer-PMU contamination remains
unresolved; neither is evidence that the solver itself migrated CPUs.

For transparency, the surviving samples assign 59.70% self / 59.72%
inclusive to propagation and 12.31% to `subsume_round`. **These incomplete
samples do not pass the 50% opportunity gate.** They must not be used to
select the representation engine or learned-clause path. No traffic observer
ran, no new implementation target advanced, and no solver source changed.
This is an inconclusive diagnostic, not a negative result for either engine.

Before another separately registered solver measurement, qualify the
profiler on a synthetic workload: verify workload and recorder affinity
separately, avoid treating nested-recorder counters as solver counters,
respect the actual sampling-rate limit, size the recording buffer, and check
loss/throttling plus unwind validity. Check the measurement chain before
consuming another solver cell. Do not rerun this cell or lower its gates.

## Retained evidence and cleanup

Raw evidence lives under
`precompile/1f3f316/benchmark/factored-search-cost/`: the manifest, one-shot
runner, build identities/logs, immediate start/completion markers, stdout,
stderr, outer counters, original `profile.data`, complete flat/inclusive
reports, raw structural counts, and `profile.rejected.json` /
`profile-diagnosis.json`. The rejection explicitly records
`counter_coverage_verified: false`. It is deliberately outside accepted
`nixie-bench-record/1` records: that schema requires verified counter
coverage, which this invocation cannot claim. The retained completion
marker prevents the runner from executing the solver again; the false
diagnosis gate prevents the conditional traffic invocation. `benchstore
missing` does not represent rejected cells and must not be used to retry
this study.

The symbols build is cached as `precompile/1f3f316/stats_solve-perf`
(`f5d833270d667551f90f0fec7a399302060e0e2c754ae834cf1e669fba89bb19`),
and the unused traffic build as `stats_solve-traffic`
(`8509f71c724203c86e918884b735269983d1be77e62f395332a91a13708315d3`).
Both use Rust 1.96.0 and the committed lockfile; exact settings are in the
build identity. The temporary build worktree was removed before measurement.
Interrupted/duplicate offline report dumps and Python cache files were
removed after retaining the raw data and complete reports.

Validation for this documentation-only result consisted of the two CNF
model checks, stdout identity, binary/input hashes and the raw profile
quality audit. No additional solver tests or parity runs were consumed;
the source remains the fully qualified `1f3f316` repair.
