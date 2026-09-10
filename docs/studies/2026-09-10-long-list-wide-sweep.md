# Wider sweep of the long-list assignment kernel

## Registration

The user requested a wider sweep after the two-input rejection recorded in
[the kernel study](2026-09-10-long-list-internal-assignment.md). Extend the
same archived binary 7842303bd99e90b95612a8f6402d29f3ed1a848d to the eight
nontrivial inputs in the original comparison. This new request authorizes
the extension beyond the earlier stop rule. It does not erase the observed
j3037 regression or establish a new post-hoc promotion threshold.

Freeze the source, compiler, lock, configuration and binary. Candidate SHA256:
e19abe8cad03a79d9e02661a9ab0d49c9d5d57ac93056a7e5501d9d1dcb84f47.
Use qualified production fd01d0b596d4640ab63e4b126bd62595d1c24016, binary
8c18517990b8e9aad3273fc0acd354362599c806ce6f9a596e231d98851bacde.
The later production ledger commit has byte-identical ordinary executable
text, as established by its qualification audit. No rebuild or source edit.

Panel: break_unsat_06_07, noL_11_14, crn_11_99_u, summle_x4044,
j3037_10_mdd_bm1, circuit_48in64out, constraints_17_0.4_1 and
si2-b03m-m800-03. Use the existing fixture/competition CNFs by exact hash,
including the existing sanitized circuit/constraints files. Exclude the
zero-conflict sat_simple startup smoke from aggregates. Seed 0 only;
this is a trajectory-preserving implementation screen, not a heuristic trial.

All Nixie cells use CaDiCaL preset, MAXC=10000000, PRINT_MODEL=1,
NIXIE_SWEEP=0 and NIXIE_DEFINITIONS=0, with other study environment knobs
cleared. CPU 15 Atom, portable release, warm input/binary, anonymous tmpfs
output, GNU time 1.10 and grouped user cycles/instructions/branches/misses.
300-second emergency cap, including noL's full trajectory rather than a
shortened prefix. Run one cell at a time and no owned builds during timing.
Require >=99.9% PMU coverage, zero major faults, <=5% off CPU and unchanged
audited constrained sleepers. Report quality failures without replacement
runs; incomplete cells cannot enter complete-solve cost geomeans.

Reuse candidate crn 2963f46b6fbec7b5 and j3037 61e1dc00d8f1cb07. Reuse
production crn 0840cab28aa276cb, j3037 0ec1f4bfcfe8f5f9 and summle
02d916e9af5fe4da. Fill only six missing candidate and five missing control
cells. When both arms are missing, alternate control/candidate order across
the predetermined panel order (break, circuit, constraints, si2, noL), with
summle first using its cached control. Do not stop the sweep on a performance
regression. Any result/model/trajectory disagreement stops inference and
requires a correctness investigation before proceeding.

Keep Kissat as the performance target: use available 4.0.4 source 8af8e56,
binary 5c91c37e4bcab56c71e304d610e303e239ab1de9809de409fe012d1d73d34fa4,
with --probe=0 --preprocess=0 --factor=0 --substitute=0 --sweep=0 --vivify=0
--transitive=0 --backbone=0 --congruence=0, seed 0 and the same caps/CPU.
Reuse j3037 45a3c8f2e3057841, circuit dffd0cb6beb45f5f and si2
c3bb0064cbaa9d2d. The latter two supply wall context only, without hardware
instruction/cycle counters; do not invent those counters or rerun the cells
to add them. Fill the five missing Kissat cells once. Total new cost budget:
16 cells, with eight existing cells reused. No new profile, seed search,
candidate variant or threshold tuning in this extension.

Use the existing long-list-internal-assignment benchstore cell identities
for new matching cells; do not rename a suite/config to repeat a prior run.
Retain a manifest, reuse map, every start/completion, raw output and canonical
record under precompile. Compare Nixie stdout byte-for-byte, including every
reported search counter and model. Independently verify each SAT model
against its input CNF; unchecked UNSAT remains unknown/unverified in storage.

Report per-input instructions, cycles, wall and conflicts, candidate/control
ratios, complete-panel and newly measured-input geomeans separately, wins and
regressions, completed/verified counts, and wall ratios against Kissat. Split
freshly paired results from comparisons against older cached runs. Shared
host load and older controls limit wall attribution; no broad statistical
claim follows from one seed or this selected panel. Existing source-level
cost diagnoses still apply to the unchanged binary. Preserve the prior
rejection and record whether broader evidence supports or contradicts its
generality. Any later production promotion still requires full qualification.
