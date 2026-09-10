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
