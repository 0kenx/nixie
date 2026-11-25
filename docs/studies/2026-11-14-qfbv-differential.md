# QF_BV differential scan (2026-11-14, HEAD `257669e2`)

**Method:** stratified 165-instance sample over 10 QF_BV families, 10 s cap,
serialized (nixie vs z3 4.16.0).

## Overall: near parity

**nixie 138/165 vs z3 149/165, zero wrong verdicts.**  Five families at full
parity (sage, MCMPC, Noetzli, stp_samples, uclid); spear 19/20 vs 20/20;
bruttomesso 19/20 vs 18/20 (a win).

## Gap families

| family | nixie | z3 | shape |
|---|---|---|---|
| 20210219-Sydr | 10/15 (13/15 @15s) | 15/15 | XOR/AND-heavy DSE predicates; 2–5× slower, boundary class |
| asp | 2/15 (3/15 @15s) | 6/15 (7/15) | the DL/asp problems bit-blasted; gryzzles.8-as-BV: nixie 12.4 s vs z3 0.5 s |
| Sage2 | 8/15 (9/15) | 10/15 | mixed |

## Root cause on the asp class: the CDCL(T) wrapper, not the encoding

gryzzles-as-BV counters: nixie 17.7k conflicts / 16.6M propagations ≈
**700 µs/conflict vs z3's ~100 µs** – moderate conflict-efficiency gap
(z3: 9.5k conflicts) amplified ~7× by per-conflict cost.  SIGPROF profile:
SAT propagation only 12 %; ~62 % in `EufSolver::merge →
congruence::propagate → diseq_pair_counts.contains_key` (the atom-watch
loop's hash probe per watched equality per merge – BV gate equalities
become thousands of EUF atoms).  Blasted SMT input pays the full theory
callback machinery; z3 blasts once and runs a lean SAT core.

## Landed from this scan (`d32e9010`)

The watch-loop diseq probe is now gated on the merged root carrying any
disequality watch (array probe; a pair-count hit implies a watched live
diseq, so an empty list makes the hash hit impossible).  Equivalent-work
– counters bit-identical on gryzzles-BV/sydr/peq/coilist/vlsat/wisa;
sydr_2856 0.795×, peq 0.946×, others neutral.  **Honest family verdict:
no solve-count flip at matched 15 s caps** (asp 3→3, Sydr 13→13, Sage2
9→8 with one boundary wobble) – the class gap stays architectural.

## Lean-BV path LANDED (`19101c14`)

The precondition implemented for the pure case: problems declaring
exactly `QF_BV` (no UF/array symbols can exist) skip the EUF
interning+merge+congruence walk for BV-sorted equality atoms – their
bit-blast comparators decide them completely.  Gated on the declared
logic string; mixed/UF/missing-logic inputs keep full EUF, so
congruence-dependent completeness is untouched elsewhere.

Measured: **142/165 on the same stratified sample (was 138/165), zero
wrong verdicts** – Sydr 10→13, asp 2→3, spear 19→20; gryzzles-as-BV
13.2 s → 7.5 s (1.76×).  Solver suite 3102 (420 BV tests), full
workspace 12 800, parity 171/0/6, perf gate PASS.  The remaining
class gap (asp/Sage2 vs z3) is the residual per-literal callback cost
on the general CDCL(T) loop – a fully lean blast-and-solve path would
require eager blasting + a solver-level bypass, which stays recorded as
the larger architectural item.

## Lean-BV v2 (`70782b57`)

The residual CDCL(T) profile (post-v1) showed three more redundant-EUF
spots, all now gated on the same `bv_pure` invariant: Bool-sorted Eq
atoms (both polarities – the blast decides iff), the Distinct-negative
equality merge, and `intern_arith_shared_terms` (its UF/select-congruence
purpose cannot exist in QF_BV; its operand interning produced the
`add_proof_edge` SmallVec-spill churn at 87 % of callback time).
gryzzles-as-BV: 13.2 s → **5.3 s (2.5× cumulative)**; the 165-sample
holds 142/165 with zero wrong verdicts.  The remaining ~10 s-cap misses
are search-shaped (the unified layer's `entailed_equal` merges – its
real word-level reasoning – are deliberately untouched), so further
gains on this class need either the eager dispatch to take over
no-elim goals (a routing decision with its own measured regressions)
or the fully lean blast-and-solve path.

## Routing re-evaluation (post-v2): the unified decision CONFIRMED

Lean-BV made the general path cheaper, so the stage-4 routing (no-elim
pure-BV goals stay unified; only elim-uncnstr takeovers go eager) was
re-measured with the full sample via the built-in A/B arm
(`NIXIE_BV_DISPATCH_UNIFIED=0`): **unified 138/165 vs eager 123/165,
zero verdict differences**.  The instance-level eager wins
(gryzzles-as-BV 3.0 s vs 6.0 s, predicate_2856 9.5 s vs 17.7 s) are
real but family-scale losses dominate (bruttomesso 18→12, spear 19→14,
asp 3→1, Sage2 8→7, Sydr 11→10, MCMPC 15→14; uclid alone gains 14→15).
The routing stands.

The deeper finding: z3's ALWAYS-eager qfbv pipeline solves BBB-32 in
0.03 s where nixie's eager path needs 27 s (unified: 5 s) – the eager
pipeline's PREPROCESSING (solve-eqs / simplification before blasting,
Z3's `tacas07` collapsing power) is the actual gap, not the routing.
Recorded as the concrete work item for this class.

## BBB-32 diagnosis (the eager pipeline's real gap)

The 27 s eager run on `tacas07/BBB-32` (z3: 0.03 s) is NOT
preprocessing – `NIXIE_PRE_TRACE` shows every stage under 1 ms with
`solve_eqs plain=0` (the goal is ONE giant equivalence assertion, a
circuit miter).  The time is the blast + SAT over a miter whose two
sides z3 collapses structurally (rewriting / gate-level structural
sharing reduces it to constant `true`).  Work item: blast-level
structural hashing (shared Boolean gate nodes across the circuit, the
AIG discipline) and/or a stronger simplify pass before blasting – the
`bitblast_advanced` module's AIG machinery is the natural base.

## Precondition for the class gap

A lean blast-and-solve path for pure-BV inputs (blast eagerly, run the
DIMACS fast-path SAT core without per-literal theory callbacks) – the
same lean-vs-wrapped split the CNF leg already has.  Recorded as the
next architectural item alongside theory_i_arith-class arith.
