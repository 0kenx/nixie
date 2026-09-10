# Wider sweep of the long-list assignment kernel

**Scope correction:** both Nixie arms below explicitly disable sweeping with
`NIXIE_SWEEP=0`; "production" identifies the production binary under that
configuration. Nixie's default is sweeping enabled. These results must not
be presented as a continuation of the user's e6d1ddda benchmark
without reconciling the changed search trajectories. See the
[historical-baseline reconciliation](2026-09-10-wide-sweep-baseline-reconciliation.md).
The kernel rejection within this study's fixed configuration still stands.

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

## Completed sweep: retain the rejection

The wider evidence does not support promoting this kernel. It retires 3.50%
fewer instructions across all eight inputs, but the four fresh pairs that
pass the timing-quality gate are 7.87% slower in wall geomean and use 8.13%
more cycles. None of those four improves wall: break is flat at the timer's
resolution; circuit, constraints and si2 regress. The apparent improvement
in the aggregate containing older controls comes from crn and especially
summle. This is a once-only implementation screen, not a statistically
established population effect.

Exactly 16 new cost cells completed and eight existing cells were reused.
There were no solver retries, replacement controls, new profiles, variants,
builds or shortened noL prefixes. All 24 cells completed within the cap.
Each arm reports five SAT and three UNSAT results. All 15 SAT models were
independently checked against every original CNF clause. The nine UNSAT
results have no independently checked proof and remain unknown/unverified
in canonical storage. All eight Nixie candidate/control stdout streams are
byte-identical, including every printed counter and complete model. No
production source is changed or promoted; the earlier scoped qualification
is not presented as full workspace qualification.

### Per-input cost

Times are whole-process seconds. `C/P` means candidate / production, so
smaller is better. Cycles and instructions are grouped user-mode hardware
counters, not the solver's scheduling ticks. The
[derived audit](assets/2026-09-10-long-list-wide-sweep-audit.json) retains
absolute counts, identities, quality fields and aggregation membership.

| Input | Production wall | Candidate wall | Kissat wall | C/P instructions | C/P cycles | C/P wall |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| break | 0.82 | 0.82 | 0.41 | 0.9576 | 1.0052 | 1.0000 |
| noL | 220.87* | 196.33 | 16.69 | 0.9528 | 0.9427* | 0.8889* |
| crn | 1.44 | 1.30 | 0.68 | 0.9398 | 0.9007 | 0.9028 |
| summle | 4.97 | 2.94 | 1.88 | 0.9803 | 0.5965 | 0.5915 |
| j3037 | 36.13 | 37.66 | 18.04 | 0.9460 | 1.0431 | 1.0423 |
| circuit | 7.44 | 7.57 | 5.55 | 0.9406 | 1.0159 | 1.0175 |
| constraints | 19.41 | 25.14 | 4.63 | 1.0221 | 1.2995 | 1.2952 |
| si2 | 2.19 | 2.25 | 1.22 | 0.9836 | 1.0302 | 1.0274 |

*The noL production run spent 5.302% off CPU, exceeding the registered 5%
gate. Its wall and cycle comparisons are retained as raw observations but
excluded from qualified aggregates. Its instruction count remains usable:
the solve completed with 100% counter coverage, zero major faults and the
same printed trajectory as the candidate. It was not rerun. The candidate's
off-CPU fraction was 0.606%. All other cells pass their timing checks, and
all 16 new captures have 100% PMU coverage, zero major faults and unchanged
audited constrained sleepers. These checks do not exclude interference from
other runnable work or shared caches and memory bandwidth.

Production crn, summle and j3037 controls are cached from September 9;
their candidates were measured on September 10. Candidate crn/j3037 and
Kissat j3037/circuit/si2 were already available before this extension.
Kissat circuit/si2 have cached wall and search counters but no hardware
instruction/cycle capture. The other five Nixie pairs were freshly paired
in the registered alternating order, without intervening owned builds.

| Cohort | C/P instructions (n) | C/P cycles (n) | C/P wall (n) |
| --- | ---: | ---: | ---: |
| Entire eight-input panel | 0.9650 (8) | 0.9627 (7) | 0.9604 (7) |
| Six added candidate inputs | 0.9725 (6) | 0.9600 (5) | 0.9566 (5) |
| Five fresh Nixie pairs | 0.9709 (5) | 1.0813 (4) | 1.0787 (4) |
| Three comparisons against cached production | 0.9552 (3) | 0.8245 (3) | 0.8226 (3) |

Every entry is a geometric mean of per-input ratios; `n` is the number
included for that metric. The six added inputs exclude crn/j3037; the five
fresh pairs additionally exclude summle. The raw all-eight wall ratio would
be 0.9512, but includes the failed-quality noL control and is not a qualified
result. Across seven qualified pairs there are two apparent wall gains,
one flat result and four regressions. Both apparent gains use older
controls. In particular, summle's 40.85% wall reduction accompanies only a
1.97% instruction reduction. This observation cannot establish a 41% kernel
speedup from a single noncontemporaneous comparison. The mixed-panel 3.96%
wall reduction is also within the methodology's neutral band.

### Kissat remains the target

On the **same seven inputs** with qualified wall for all three arms,
production / Kissat is 2.1695 and candidate / Kissat is 2.0836. That apparent
4% improvement has the cached-control limitation above; it is not a landed
improvement. Candidate / Kissat across all eight qualified reference pairs
is 2.5869, including the full noL outlier. Do not compare that eight-input
number to the seven-input production ratio, or directly to an earlier
six-input headline. On the common six inputs with hardware instructions,
production / Kissat is 3.1653 and candidate / Kissat is 3.0578. On the common
five with qualified cycles, those ratios are 2.5116 and 2.3597.

The candidate changes execution cost without changing Nixie's printed
search work. Therefore its cost ratios against production are also its
cost-per-conflict and cost-per-propagation ratios. Across solvers, the work
counts differ:

| Input | Nixie conflicts, both arms | Kissat conflicts | Nixie propagations, both arms | Kissat propagations |
| --- | ---: | ---: | ---: | ---: |
| break | 28,619 | 28,289 | 4,071,874 | 3,640,748 |
| noL | 6,362,065 | 794,536 | 255,078,463 | 33,208,368 |
| crn | 87,939 | 71,192 | 3,817,687 | 4,238,393 |
| summle | 19,333 | 19,709 | 32,793,359 | 40,986,169 |
| j3037 | 330,565 | 286,784 | 323,390,316 | 218,808,022 |
| circuit | 162,529 | 277,061 | 17,162,958 | 16,013,560 |
| constraints | 87,007 | 21,955 | 11,659,552 | 3,749,535 |
| si2 | 39,246 | 51,823 | 960,337 | 1,164,987 |

The eight-input Nixie / Kissat geomeans are 1.4535 for conflicts and 1.4964
for printed propagations. NoL alone performs about eight times as many
conflicts and 7.68 times as many propagations; constraints performs 3.96
and 3.11 times as many. The smaller panel's near-equal propagation totals
do not extend to this complete panel. Execution remains an essential target,
but whole-process wall divided by a legacy propagation counter also includes
inprocessing and other work, and is not an isolated BCP cost measurement.

### What the added regressions tell us

Constraints is the strongest new counterexample: instructions increase
2.21%, cycles 29.95% and wall 29.52%. Retired branches fall 1.64%, branch
misses fall 0.61%, and peak RSS falls from 109468 to 96864 KiB. Cycles per
instruction increase 27.14%; cycles per user second differ by only 0.44%.
Thus fewer branches, fewer misses and lower peak memory do not price the
critical path. This is consistent with added dependencies or stalls, but
these aggregate counters cannot identify the exact cause. Allocation timing
and layout are also possible contributors; they are not established by RSS.

Circuit and si2 similarly retire fewer instructions but use more cycles;
their cycles-per-instruction ratios rise 8.01% and 4.74%, respectively.
The broad instruction reduction therefore does not justify treating the
remaining machine cost as an incidental detail. Break is an additional
neutral example: 4.24% fewer instructions, essentially unchanged wall and
slightly more cycles. Avoid selecting a runtime threshold from the observed
winners or treating this kernel as universally cheaper.

The prior assembly diagnosis remains the concrete implementation lead:
fixed-domain reservation, view setup and callback gates are repeated per
nonempty list, while internal assignment state introduces dependent arena
and value-base reloads in the scanning loop. The narrow boundary reduced
individual frames but did not remove those loads. No new profile was taken;
the earlier throttled capture still cannot establish cycle shares. The next
distinct implementation should amortize setup across a propagation session
while keeping the scanning boundary narrow, and isolate assignment-only
metadata if needed to keep hot bases live. It must demonstrate removal of
the identified setup and reloads in assembly before a new cost screen.
Include constraints as a required regression case alongside crn and j3037.
Neither repeating this exact kernel nor sweeping inline annotations follows
from these results.

### Result retention and checks

The derived audit contains exact source/binary/input/output hashes, the
fixed new-cell order, fresh/cached membership, all 24 record IDs, raw counts
and explicit aggregation masks. Canonical records remain under
`precompile/<source>/benchmark/runs/long-list-internal-assignment/`; raw
captures remain in each source's benchmark cache. The frozen runner, input
manifest, reuse map, start/completion log and read-only report are retained
under `precompile/7842303/wide-sweep/`, with their hashes in the audit.
These are reusable cost cells, not permission to run them again.

Validation rechecked the canonical schema, record identities, binary/input
hashes, every SAT model, eight stdout comparisons and aggregate masks. No
solver code changed during the extension, so no build, full workspace suite
or new Z3 parity claim is attached to this documentation-only result. The
production performance gap remains open.
