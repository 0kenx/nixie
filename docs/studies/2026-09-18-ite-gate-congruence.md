# ITE gate congruence: the missing 46K gates of the bv_ILA family (2026-09-18)

The SAT-side perf handover's open item 1a (`bv_ILA` 41.7× wall vs kissat,
"trail-reuse + phase quality" hypothesis) turned out to be neither: the
instance is cracked by **kissat's gate-congruence closure**, and nixie's port
of it was missing the ITE gates entirely — 46,213 of the 82,214 gates kissat
extracts on this file (57% of variables), feeding 50,931 merged equivalent
variables (35%) and 108,484 gate-subsumed clauses before search starts.

## Diagnosis chain (every layer measured)

1. **bv_ILA anatomy**: nixie 405,848 conflicts vs kissat 9,465, verdicts
   agree (UNSAT). `kissat --verbose=2` section reports:
   `congruence-1: 28471 AND + 7530 XOR + 46213 ITE gates; merged 50931
   equivalent variables 35.34%; subsumed 108484 clauses 44%`.
2. **nixie's `solver/congruence.rs`** (pre-change): AND (ternary +
   two binary implications) and XOR (4-clause pattern) gates only. Its
   first-scan line on bv_ILA: `gates=29946` — roughly kissat's AND count,
   no ITE.
3. **Where the fold actually fires under the default config**: the ELS
   round (`substitute_equivalent_literals_round`) is config-off in the
   CaDiCaL preset; the rounds that DO run are triggered by the SAT sweep
   (`kitten_sweep_enabled()` is default-ON — the doc comments claiming
   "inert unless NIXIE_SWEEP=1" are stale), which calls the ELS round
   whenever it proves equivalences. Gate congruence rides inside that
   round (`augment_big_with_gate_congruence`). On bv_ILA the pre-search
   sweep round found 38 equivalences → fold ran → `els=7247`
   substitutions total — vs kissat's 51K. The equivalence *supply* was
   the gap, not the fold machinery.

## The landing

`detect_gates` gains the kissat `extract_ite_gates_with_base_clause` shape:
an ITE gate `o ↔ (c ? t : e)` is recorded when its four defining clauses
`(¬o∨¬c∨t), (¬o∨c∨e), (o∨¬c∨¬t), (o∨c∨¬e)` are all present. The scan walks
each ternary clause as the C-form base with a positive output candidate
(every ITE definition has a positive-output presentation — the four clauses
of `o ↔ f` are those of `¬o ↔ ¬f` with roles swapped), verifies the A-form
by hash lookup, and discovers the else-literal by walking a CSR index of
ternary clauses by literal over the (o, cond) pair, verifying the B-form.
The closure (`SignedUf` fixpoint) merges on the canonical presentation of
each gate's function:

- `(c ? t : e) ≡ (¬c ? e : t)` — then/else **swapped** with the cond flip;
- complement: `¬(c ? t : e) = (c ? ¬t : ¬e) = (¬c ? ¬e : ¬t)` — here all
  three negated;
- trivial `c ? t : t` proves `o ≡ t` outright (direct union, and the
  `then` literal is named in the class materialization — its equivalence
  is otherwise lost to the fold);
- `c ? t : ¬t` is left to the XOR arm (kissat parity).

Four merge rules over the canonical-triple table (same function; same
complement; and the two cross rules — my positive triple as someone's
complement, my complement as someone's positive). Without rule 4 the
complementary pairs collide in only one scan order.

## The three bugs the verification stack caught (each now pinned by a test)

1. **Canonicalization polarity** (first prototype): I canonicalized the
   swap branch to `(¬c, ¬e, ¬t)` — negating all three, which is the
   *complement's* swap form, a different function. Result: a false UNSAT
   on `6s299b685_Iter22` (kissat: SAT, exit 10) at 6 conflicts — caught by
   the differential fuzzer + kissat disagreement, root-caused by dumping
   the claimed equivalence classes and kissat-checking each pair
   (`F ∧ ¬(a↔b)` must be UNSAT; five pairs came back SAT). The fix is the
   swap-vs-complement distinction above. Regression:
   `ite_false_unsat_regression_complement_vs_plain_presentation`.
2. **Missing mirror rule**: complement merges fired only in one scan
   order (rules 1–3 above). Regression: the same test's scan-order
   variants.
3. **Class materialization keying**: both polarities of every output are
   named so complementary classes have ≥2 members — but each literal must
   be keyed by its **own** union-find root. Keying by `find(out)` mixed a
   class with its mirror, and the consecutive-chaining then asserted
   `¬o1 ≡ o2` false equivalences — a *second* false UNSAT on Iter22 (3
   conflicts), again caught by the class checker (5/5 bogus pairs).
   Fix: `classes[uf.find(lit)]`. Note this bug produced 59,491 "classes"
   on bv_ILA and a 0-conflict refutation — landing on the correct UNSAT
   verdict **by luck**; the conflict-count collapse it showed was
   bogus-merge inflation, not real inference.

## Soundness evidence

- `nixie-sat/tests/ite_gate_congruence_regressions.rs`: 7 black-box tests
  (congruent twins, complement twins as negation, swap presentation,
  trivial gate, the Iter22 shape with model validation, distinct gates do
  not fold, XOR-shaped ITE).
- Differential fuzz vs a clean-HEAD base build + kissat tiebreak:
  ~4,700 structured instances (gate-structured generators: ITE/AND/XOR
  mixes, congruent and complementary twins, chained gates, phase-transition
  random 3-SAT at sizes 150–320 vars so the ELS rounds actually fire):
  **0 verdict disagreements**; the only flags were base-timeout →
  candidate-solves (kissat confirms the candidate's verdict).
- Equivalence-class audit on the two sensitive instances: every claimed
  pair kissat-verified (`bv_ILA`: 38,558 pairs / 0 bogus; `Iter22`: 52/0).
- Full workspace nextest (11,955 pass; the one timeout is another agent's
  in-flight arithmetic test, unrelated), clippy/fmt/doc clean (my crates),
  Z3 parity 177 / 0 mismatches / 1 inconclusive (baseline).

**A meta-find worth flagging**: the shared `target/release/nixie` binary
produced a false UNSAT on two fuzz seeds where every clean-HEAD build
(nixie-sat identical, other crates at both cf80a806 and HEAD) answers
correctly — the stale-shared-binary trap from the handover, now seen
producing a wrong verdict, not just wrong perf numbers. Never use a shared
`target/` binary as a differential base; rebuild from a worktree.

## Effect (default config, deterministic counters)

| instance | base conflicts | candidate | ratio |
|---|---|---|---|
| bv_ILA_Piccolo_JALR | 405,848 | 302,978 | **0.75** |
| 6s299b685_Iter22 | 4,034 | 1,464 | **0.36** |
| b21 | 216,109 | 157,666 | **0.73** |
| s38584 | 16,138 | 15,159 | 0.94 |
| Carry_Bits / SCPC / x9 / frb35 / circuit | — | — | **1.000 (bit-identical)** |

The bit-identical band is the point: under the default config the pass
fires only inside already-scheduled ELS rounds, so formulas without
congruent ITE structure keep byte-identical trajectories. Perf gate at
GATE_SEEDS=10: conflicts geomean **0.984**, wall 0.93, PASS.

Powered 10-seed × 30-instance corpus run: `precompile/<sha>/benchmark/
ite-power/` (recorded by the landing).

## What is still open (the named next slices, in measured order)

1. **The fold trigger, not the extraction, is now the bottleneck.** With
   `NIXIE_ELS_FORCE=1` the closure produces 38,536 *valid* merged classes
   on bv_ILA — but under the default config those merges only land when
   the sweep happens to trigger an ELS round, and mostly late (els=19,210
   by conflicts=4000, then trickle). kissat runs congruence inside its
   probe schedule and applies merges immediately (its `merge_literals`
   adds real binary clauses + learns units on clashing classes). Arming
   an unconditional congruence round (density-gated — the
   `2026-09-06-els-gate-density-study` knob exists) is the next slice;
   naive always-on ELS forcing measured a wall tax on fold-empty
   instances (the 2026-09-05 study's result reproduces: identical
   conflicts, +60% wall on a hard random instance).
2. **Gate-based subsumption** (kissat subsumed 108,484 clauses = 44% of
   tried on bv_ILA) — separate machinery, big BVE-cost reduction on this
   family (the 36M-resolution phase-1 elim would shrink with it).
3. **n-ary AND/XOR gates** (kissat arity defaults: AND ≤ 1M, XOR ≤ 4) —
   nixie's arms are arity-2; on bv_ILA the ternary-only restriction
   measured roughly at parity (29,946 found vs kissat's 36K), so this is
   lower priority than 1–2.
4. **Congruence during probing**: kissat's probe→congruence interleave
   derives hyper-binaries that complete half-encoded gates before
   extraction; our extraction only sees complete 4-clause patterns.

## Powered experiment (10 seeds × 30-instance standing corpus, 60 s cap)

`precompile/1fd5b96f/benchmark/ite-power/power.tsv` (600 runs, both-censored
cells recorded and skipped for further seeds):

- **0 verdict mismatches** over all cells.
- solved-at-cap: 234 = 234 (unchanged).
- Conflicts geomean over the 14 instances with paired cells: **0.9915**;
  per-family seed-averaged: b21 0.941, Iter22 0.964, s38584 0.974, the
  inert band exactly 1.000, worst cell b22 1.005 (noise).
- bv_ILA solves in ~100 s on this machine and cap-censors at 60 s in both
  arms; its evidence remains the deterministic single-trajectory numbers
  above (405,848 → 302,978 conflicts, verdict-consistent).

The seed-averaged per-family ratios (e.g. b21 0.941 vs the seed-1 0.73)
are the honest numbers — per-seed spreads on these instances are wide,
exactly the CDCL-chaos caveat; the aggregate claim is "no regression,
targeted improvement, soundness-clean", not a headline speedup. The big
remaining win on this family needs the fold-trigger slice below.

Perf-gate BASELINE re-pinned to this landing (1fd5b96f) — deliberate
heuristic landing, conflicts moved 0.984 at GATE_SEEDS=10.
