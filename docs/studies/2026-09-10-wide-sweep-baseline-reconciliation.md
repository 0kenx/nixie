# Reconcile the wider sweep with the e6d1ddda benchmark

## Registration and source audit

The user pointed out that the eight-input kernel sweep is slower than
`/tmp/opencode/mini_bench_3arm_e6d1ddda.jsonl`. The historical Nixie / Kissat
wall geomean is 2.2930, compared with the archived candidate's 2.5869 in the
new sweep. These are different measurement sessions, and their Nixie search
counters differ on seven of eight nontrivial inputs. NoL changes from
1727396 to 6362065 conflicts; constraints from 40004 to 87007. This cannot
be explained by timing interference alone.

The entire `nixie-sat` Git tree at e6d1ddda091800444398d9bcaa05b2051456f905
and the sweep control fd01d0b596d4640ab63e4b126bd62595d1c24016 is identical:
`a3c6c5b0662ac46b7b15317694d7b91c279c9956`. Their root Cargo.toml,
Cargo.lock and .cargo configuration also have no diff. Some nixie-core
source differs, so this does not assert whole-binary identity. The historical
JSONL lacks a binary hash, Nixie command/environment, seed and CPU affinity;
do not invent those fields. Retained Kissat logs identify 4.0.4 / 8af8e56
and the requested disabled-pass options.

Nixie's sweeping pass defaults **on** in both revisions; the wider sweep
explicitly set `NIXIE_SWEEP=0` in both Nixie arms. Definition extraction
defaults off, so its explicit zero is not itself a default-mode difference.
Explicit seed zero maps to the same initial RNG state as an omitted seed.
The leading hypothesis is a sweep-mode mismatch. Calling the previous
control simply "production" hid this distinction: it was production code
under a deliberately sweep-disabled configuration, not the default setup.

Use exactly two missing diagnostic cells, constraints followed by noL, on
the existing qualified fd01d0b binary SHA256
8c18517990b8e9aad3273fc0acd354362599c806ce6f9a596e231d98851bacde.
Retain the wider sweep's exact hashed inputs, CPU 15, seed 0, CaDiCaL preset,
MAXC=10000000, PRINT_MODEL=1, NIXIE_DEFINITIONS=0, cleared study knobs,
portable release, warm input/binary, grouped whole-process user PMU counters,
GNU time 1.10 and anonymous tmpfs output. Change only NIXIE_SWEEP to 1.
Keep the 300-second emergency cap and the existing quality/idle guards.
Search the canonical store before starting; reuse existing cells and do not
retry. No new old-revision build, reference run, candidate run, seed or
parameter search is authorized by this registration.

Compare every historical Nixie stdout/stderr diagnostic line against the
new solve, excluding the newly requested DIMACS model and measurement footer.
Independently check both new SAT models on the original CNFs. Exact equality
would establish that the sweep-enabled production code reproduces the
historical printed trajectories on the two major outliers. It would not
recover the missing historical environment or prove mode equality on all
eight inputs. A mismatch leaves the hypothesis unresolved; report it rather
than trying more configurations. Hardware counts and wall are retained for
reuse, but this is a configuration diagnosis, not a new heuristic claim or
a measurement of sweeping's general benefit. No matched-null or seed panel
is needed to answer the narrow trajectory-reproduction question.

Retain the supplied JSONL as historical evidence with its original metadata
limitations. Correct the wider study's default-mode implication and record
the actual findings. The rejected kernel remains rejected. Future kernel
studies may retain a sweep-disabled diagnostic, but the user's headline
comparison must explicitly state and match the intended Nixie mode.

## Result: both historical trajectories reproduced

Both registered sweep-enabled checks completed and reproduced **every
historical diagnostic line exactly**, including walk work, conflicts,
decisions, propagations, restarts, learned/deleted clauses, LBD, backtracks,
scheduling ticks, stabilization, subsumption, BVE, substitutions and units.
Both new SAT models independently satisfy their original CNFs. This
confirms the sweep-mode explanation for the search-work difference on the
two largest apparent regressions, using the same frozen production binary
as the wider study. No old revision was rebuilt and no solver source changed.

| Input | Historical e6d1ddda conflicts | Production sweep off | Production sweep on, new |
| --- | ---: | ---: | ---: |
| noL | 1,727,396 | 6,362,065 | 1,727,396 |
| constraints | 40,004 | 87,007 | 40,004 |

NoL's historical/new sweep-enabled propagation count is 70174865 and
scheduled tick count is 415246670. Constraints reproduces 6060215
propagations and 43247552 ticks. These exact diagnostic matches identify
the workload independently of machine timing. They do not recover the
historical binary hash or environment, or demonstrate that every unprinted
internal state and event matches.

| Input | Historical wall | Production sweep off | Rejected candidate sweep off | Production sweep on, new |
| --- | ---: | ---: | ---: | ---: |
| noL | 43.511 s | 220.87 s* | 196.33 s | 50.99 s |
| constraints | 5.761 s | 19.41 s | 25.14 s | 10.01 s |

*The old wider-sweep noL control failed the off-CPU quality gate; it remains
excluded from qualified wall comparisons. Both new captures have 100% PMU
coverage, zero major faults, less than 0.5% off CPU and unchanged audited
constrained sleepers. Their raw hardware counts are:

| Input | Instructions | Cycles | Peak RSS, KiB | Canonical record |
| --- | ---: | ---: | ---: | --- |
| constraints | 53,147,102,832 | 45,156,742,562 | 94,888 | 14d6f38d3c5c5cb9 |
| noL | 389,171,744,416 | 231,268,638,827 | 57,360 | 36990e8006fa9aac |

**The remaining historical timing difference is unresolved.** Even with
the printed trajectories reproduced, noL is 17.2% slower and constraints
73.8% slower than the supplied historical observations. The historical
JSONL has no binary/build hash, CPU affinity, user time or PMU counts, so
these differences cannot distinguish execution-code regression from build,
core placement, frequency, allocator layout and shared-host interference.
Do not claim that restoring sweeping has recovered the old wall performance,
or dismiss the remaining difference as proven noise. Conversely, the
4.51x/4.36x candidate-to-historical wall ratios from the prior table are not
measurements of a like-configured implementation regression.

The earlier kernel rejection is unaffected: its candidate and production
arms both had sweeping disabled and identical printed trajectories. Its
fresh qualified pairs were 7.87% slower in wall geomean. However, neither
that study's control nor its candidate represented Nixie's default mode.
The historical panel's 2.2930 Nixie/Kissat wall geomean and the candidate's
2.5869 therefore cannot be used as a version-to-version trend. The historical
file alone also does not establish which mode is generally best. No new
policy choice follows from these two diagnostics.

## Reporting correction and retained evidence

The [wider study](2026-09-10-long-list-wide-sweep.md) now starts with an
explicit mode correction. For the user's continuing comparison, use Nixie's
default sweeping setting and retain the requested Kissat options; identify
both modes in the manifest and headline. A sweep-disabled propagation
diagnostic may still be useful, but cannot silently replace that comparison.
Reject or separately label cross-run joins with different effective modes,
and require exact workload checks before calling a change an execution-only
gain or regression. Do not manufacture a new eight-input default-mode
geomean by combining these two checks with six sweep-disabled cells.

The [supplied JSONL](assets/2026-09-10-e6d1ddda-historical-mini-bench.jsonl)
is preserved verbatim, including its Z3 rows as provenance only; this
investigation uses Nixie and Kissat. The
[reconciliation audit](assets/2026-09-10-wide-sweep-baseline-reconciliation-audit.json)
retains source/binary/input hashes, both canonical identities and raw metrics,
the exact historical/new diagnostic comparisons and harness hashes. New
records are under `precompile/fd01d0b/benchmark/runs/sweep-mode-reconciliation/`;
the runner, manifest, two starts/completions and historical copies are under
`precompile/fd01d0b/sweep-reconciliation/`. No cells were repeated. This
documentation correction needs no new solver build or workspace/parity
qualification; it claims no production implementation change.
