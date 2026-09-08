# Exact sparse-word subsumption: registered cost screen

The target is cycles per conflict, including inprocessing charged to the whole
solve. Existing profiles attribute 13.2% of si2-b03m time to subsumption. This
experiment replaces repeated signed-byte membership checks on dense connected
clauses with exact sparse 64-bit literal masks. It changes no search policy.

## Mechanism and invariants

Group literal codes by `code >> 6`. For each connected-clause word, subtract
the candidate's positive-literal mask. Zero missing bits means inclusion;
exactly one missing bit across the entire clause permits strengthening only
if its complement is present. Otherwise the check fails. Complementary codes
differ in their low bit, so they share a word. This implements the existing
scalar check and CaDiCaL `src/subsume.cpp:subsume_check` semantics exactly.

Pack only clauses with at least four literals per distinct word. Two u64s
store each word index and mask, so this fixed threshold does not expand the
literal payload. Repeated variables (either polarity, including duplicates)
fall back to the scalar path to preserve its multiplicity behavior. Candidate
mask updates must reproduce signed marks' last-write behavior on opposite
polarities. Sparse clauses and unrepresentable optional-cache offsets also
use the original matcher.

Build masks only upon connection, after any strengthening. Already connected
clauses are not rewritten during this round; check arena liveness before
using a row. Preserve schedule sorting and ties, occurrence order, budget
increments and stopping points, binary processing, dirty-set/RNG updates,
proof events, and scratch-buffer lifetimes. Debug builds compare every packed
match against the scalar result. Tests also compare explicit clause payloads
and metadata, models and proof transcripts; a database's abbreviated Debug
output is not a state oracle.

## Static evidence, before solver runs

A scan of original clauses of length 3 through 100 counts exact word groups:

| input | literals | words | eligible literals | eligible words |
|---|---:|---:|---:|---:|
| si2-b03m | 5,958,086 | 792,532 | 5,914,871 | 778,844 |
| circuit | 1,344,000 | 582,480 | 94,080 | 23,280 |
| j3037 | 88,328 | 72,174 | 0 | 0 |

These are input counts, not dynamic work or a speedup estimate. The target
is si2; circuit guards sparse-case overhead. j3037 gets no new cost cell.
Input SHA-256 values:

- si2: `8e24efbf17294a0fe9a2f7681d5cbb615f7f3417cc04258debb6c2ee498192ee`
- circuit: `d3338c04e29f5c8b7e75686fa30fd9927babb7b34b9f7c87785397662f59d8e2`
- j3037: `7672cb34e4b32cf83292630f1155b7e564bdcf4b2eedd60f7f25cf59b4b5bcc7`

## At most four new cells, no tuning

Use a clean committed control based on main `a43ee41`, and its direct
descendant containing only this implementation/tests. Pin both source and
binary hashes. Build both with the same compiler, lockfile, release profile
and ordinary features. Explicitly set `NIXIE_SWEEP=0` in both arms because
main now defaults sweep on. Clear all other study overrides.

First run si2 scalar then packed, seed 0, MAXC=40000, CPU 10, CaDiCaL preset,
model output enabled. Measure whole-process user instructions, user cycles
per conflict, branches/misses, conflicts, verdict and secondary wall time.
Require one active PMU with at least 99.9% scheduling coverage. Store every
cell once in the canonical result store; reuse exact existing cells. A
300-second emergency timeout is not a policy input or permission to rerun.

Stop immediately unless both si2 instruction and cycles/conflict treatment
/ scalar ratios are at most **0.95**, with byte-identical complete stdout.
Only on passing run circuit packed then scalar with the same settings;
neither circuit cost ratio may exceed **1.03**. Any trajectory discrepancy
fails the engineering comparison. No density-threshold or inline tuning
after seeing these cells. Budget Unknown is an unsolved prefix observation,
not an independently verified answer. Report solved-at-cap for each pair.

This is a small rejection screen, not a broad or multi-seed performance
claim. Positive production landing additionally requires full workspace
build, nextest, doc tests, clippy, formatting, docs and fresh Z3 parity.
Failure archives the candidate source and records the finding on main.
