# Subsumption rejection hints

## Registration

The earlier sparse-word and variable-signature filters did not qualify.
This successor uses one literal already examined by the scalar matcher,
with no mask construction or candidate bitmap. The connected occurrence
stores its clause ID and a rejection hint, initially the first clause
literal. After validating clause liveness and incrementing the original
pair budget, an absent hint rejects the pair. Otherwise run the original
signed-mark matcher; remember the first absent literal it encounters.
A second complemented occurrence still fails through the original loop.

The hint remains a literal of that connected clause. Each schedule ID is
visited once; connection follows strengthening. Later iterations can
promote a connected subsumer but only delete or strengthen their own
candidate. No propagation runs inside this pass. Therefore connected
literal membership cannot change before the occurrence lists are discarded.
Keep a debug membership assertion, and preserve liveness checks, budget
increments and stopping points, all literal/occurrence order, dirty sets,
RNG, proof events, and the existing scratch lifetime. CaDiCaL's
`src/subsume.cpp:subsume_check` rotates a failed literal into the clause's
first slot; this experiment keeps its hint outside the arena so Nixie's
observable clause order is unchanged. No unsafe code or solver heuristic.

Use committed main `f1096e3` (the concurrent sweep revert) as the source base.
The registration-only descendant is the exact engineering control; its
direct code descendant is treatment. Pin source, binary, compiler,
lockfile and ordinary release build settings. Explicit `NIXIE_SWEEP=0` in
both arms; clear other study overrides. Record additional defaults from
this revision. No new Kissat runs; its cached mode-matched results remain
the reference gap, not the trajectory-matched control.

At most four new cost cells: si2-b03m scalar then hint, seed 0, MAXC=40000,
CPU 10, model output enabled. Whole-invocation user instructions are primary;
user cycles/conflict are the advancement metric. Require one active PMU
and at least 99.9% coverage. Record once in `subsumption-rejection-hint`
under `precompile/<sha>/benchmark/`; preserve every raw result. A 300-second
emergency timeout is not a solver policy. Require identical complete
stdout and independently checked SAT models. Unknown is a prefix, not a
verified verdict.

Advance to circuit (hint then scalar, identical settings) only if si2
cycles/conflict T/C <= 0.95 and instructions T/C <= 1.00. After both pairs,
require geomean cycles/conflict <= 0.95, geomean instructions <= 1.00,
and neither circuit ratio above 1.03. No hint initialization, capacity,
inline or threshold tuning after observing results. This small screen can
reject, not establish a broad performance win. Report solved-at-cap.

Before cost runs: exhaustive matcher equivalence including duplicates,
opposite polarities, repeated comparisons, and single/multiple flips;
paired real rounds including strengthening, budgets, schedules and proofs;
all SAT tests, clippy and fmt; ordinary committed release builds. A source
landing additionally requires all workspace build/test/doc-test/clippy/fmt/
doc gates and fresh Z3 differential parity. Failure archives the prototype
and lands the finding only.

## Result: rejected after two cost cells

The exact control is **`19d4d47a04b37c4e1e98f3a508d713fd9da06ec6`**,
binary SHA-256
`3cb1f6e64843d5730867d34e2f1264dd14adba2ee2b0654a70876f9fd5887883`.
The direct-descendant prototype is
**`e31fd7cb53758f9de68a88c3e24ed1286a34d406`**, binary SHA-256
`c841f1e07c34a5672c13f2bdc6250bce959ed08277e60d93d89e5ae377f082e9`.
Both were built from clean committed source with Rust 1.96.0 / LLVM 22.1.2,
ordinary release features and identical lockfile
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Kitten definition extraction defaults off in this revision; sweep was
explicitly disabled. Source and binary identities remain pinned independently
of concurrent main history changes.

Only the registered first pair ran: si2-b03m, seed 0, 40,000-conflict cap,
CPU 10, full model output. Both completed SAT at **39,246 conflicts**.
Complete stdout, including every printed counter and model, is identical;
both SAT models were checked independently against the original CNF.
Solved-at-cap is **1/1 in each arm**.

| metric | scalar | rejection hint | treatment / control |
|---|---:|---:|---:|
| user instructions | 27,371,385,294 | 27,244,786,323 | **0.995375** |
| user cycles | 9,493,066,795 | 9,333,998,615 | **0.983244** |
| cycles / conflict | 241,886.23 | 237,833.12 | **0.983244** |
| branches | 6,510,354,574 | 6,459,906,844 | 0.992251 |
| branch misses | 41,983,836 | 41,356,750 | 0.985064 |

Secondary wall times were 2.271 s and 2.220 s. Each run used one active
`cpu_atom` PMU with 100% event coverage. No own build or test overlapped
measurement. The shared host had other work (the pre-run snapshot is
archived); this single pair does not establish a general cycle effect or
statistical neutrality.

The measured instruction decrease is **0.46%**, and the cycle/conflict
decrease is **1.68%**, below the registered 5% advancement gate. **No circuit
runs, repetitions, or hint/capacity tuning followed.** The kernel's complete
cost includes larger occurrence entries, the extra mark read, hint updates,
allocation and fallback scans. This screen does not separate hint hit rate
from those costs; it establishes that this concrete implementation does not
qualify. Do not retry this same rejection-hint design on these observations.
A successor needs dynamic evidence of substantially more removable work.

## Verification and disposition

All **1,013 SAT tests passed**, with one existing skip. Four new tests cover
**503,820** repeated matcher comparisons including duplicates and complementary
pairs; hint updates and single/multiple flips; paired real rounds with
strengthening, connection, budget exits and repeated rounds; and 24 generated
formulas with exhaustive truth-table classification, checked SAT models and
independently checked UNSAT LRAT proofs. Paired comparisons include explicit
clause literal order and metadata, trail, watches, BIG, statistics, dirty sets,
elimination marks, final models and proof transcripts. Debug builds assert
hint membership and compare every actual hint result with scalar checking.

The focused tests also passed in separate full-schedule and recency/hot-connect
processes. All-target/all-feature SAT clippy, workspace formatting and committed
release builds passed. The cost gate failed, so no full workspace or SMT parity
qualification is claimed and **no prototype solver code lands on main**.

Canonical records: control **`b5af28e0b5de204b`**, treatment
**`117280be33c764ff`**. Complete stdout SHA-256:
`c25ba0a9a391a198ca92943e0e5f07eab463efa505980699e3245d712173d30f`.
Both records, raw stdout/stderr/PMU data and completion markers are under
`precompile/<sha>/benchmark/subsumption-rejection-hint/`, with canonical schema
records under `benchmark/runs/subsumption-rejection-hint/`. The candidate cache
also retains the conditional manifest, verified summary, build/test logs,
source identities and verified source bundle/patch including the runner.
The temporary experiment checkout and branches are removed after this finding
lands. This result does not close the Kissat throughput gap.
