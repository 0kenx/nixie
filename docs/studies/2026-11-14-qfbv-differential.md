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
**700 µs/conflict vs z3's ~100 µs** — moderate conflict-efficiency gap
(z3: 9.5k conflicts) amplified ~7× by per-conflict cost.  SIGPROF profile:
SAT propagation only 12 %; ~62 % in `EufSolver::merge →
congruence::propagate → diseq_pair_counts.contains_key` (the atom-watch
loop's hash probe per watched equality per merge — BV gate equalities
become thousands of EUF atoms).  Blasted SMT input pays the full theory
callback machinery; z3 blasts once and runs a lean SAT core.

## Landed from this scan (`d32e9010`)

The watch-loop diseq probe is now gated on the merged root carrying any
disequality watch (array probe; a pair-count hit implies a watched live
diseq, so an empty list makes the hash hit impossible).  Equivalent-work
— counters bit-identical on gryzzles-BV/sydr/peq/coilist/vlsat/wisa;
sydr_2856 0.795×, peq 0.946×, others neutral.  **Honest family verdict:
no solve-count flip at matched 15 s caps** (asp 3→3, Sydr 13→13, Sage2
9→8 with one boundary wobble) — the class gap stays architectural.

## Precondition for the class gap

A lean blast-and-solve path for pure-BV inputs (blast eagerly, run the
DIMACS fast-path SAT core without per-literal theory callbacks) — the
same lean-vs-wrapped split the CNF leg already has.  Recorded as the
next architectural item alongside theory_i_arith-class arith.
