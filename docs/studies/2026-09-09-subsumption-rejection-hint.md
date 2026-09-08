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
