# FSM synthesis performance: Nixie's lazy graph reduction vs Z3's eager encoding

**Date:** 2026-09-22 · **Nixie:** this landing (witness certificates) ·
**Z3:** 4.16.0 · **Tooling:** `bench/fsm_perf/` (`gen.py` + `run.sh`),
reproducible with a fixed seed.

## Question

MonoSAT-style FSM constraints (fixed NFA, guarded transitions, constant-word
acceptance reified as atoms; synthesis = guard search over positive and
negative word examples) have two possible implementations in an SMT
context: a **lazy** theory integration (Nixie: product graphs + the
explained graph propagator with path/cut lemmas) and an **eager** encoding
(plain SMT-LIB formulas — the only option in Z3/cvc5, which have no FSM
theory). Which wins where?

## Two findings from one campaign

1. **A false sat in the script surface.** The verdict-agreement canary
   caught a second `fsm.accepts` after an `(assert ...)` being silently
   unregistered (fixed with epoch-based incremental registration; pinned
   by `nixie-solver/tests/fsm_script_lifecycle.rs`). All numbers below
   are from the fixed binary.
2. **The first measurement was 96% certificate checking.** Profiling
   (`perf record`, instruction-sampled) showed the recompute-based graph
   certificate checker — an O(V·E) closure per emitted consequence
   inside the CDCL loop — dominating solves (4394 M vs 186 M
   instructions with checking disabled on one instance). The
   certificates were redesigned to **witness form**: the propagator
   attaches the structure its search already produced (a path walk, a
   cut's closed vertex set, a cycle, a topological order) and checking
   is linear in the witness. Two witness bugs were caught by the suites
   during the redesign — a walk emitted in reverse order, and a global
   atom/negation premise partition that misfiled terms when one model
   uses `g` and `¬g` as guards (a term being one edge's atom and
   another's negation) — both now pinned by regressions.

## Methodology (and a measurement trap)

**Instances** (`gen.py`, seed 20260922): synthesis-shaped — a candidate
automaton over alphabet {0,1} with three guarded candidate transitions per
(state, symbol) — stay / advance / jump — plus epsilon advances on even
states; two accepting states; 2 positive + 2 negative random words. Grid:
states {8,16,32,64} × word length {10,40,80}, 3 reps each, plus 6 short
UNSAT canaries (the same word demanded accepted and rejected). 42 pairs.
**Encodings:** Nixie files use the `declare-fsm`/`fsm.*` surface; Z3 files
use the standard exact eager encoding (layered one-hot reachability with
bounded epsilon relaxation; guard variables shared by name).

**Metric:** `perf stat -e cpu_core/instructions/u` with **both solvers
pinned to one P-core** (`taskset`). This machine is a hybrid P/E-cluster
CPU where *unpinned* instruction counts are inflated by load-dependent
per-cluster PMU scaling — identical binaries measured 6× apart across
runs, and A/A "stability" of the inflated counter was ±2%. Pinned to the
core-cluster event, A/A repeats agree to **1e-6**. (Wall time is a
footnote only: ambient load average 35–100 from parallel agents.)
Verdict agreement is a soundness canary: any mismatch aborts.

## Results (pinned instruction-count geomean, nixie/z3; < 1 = nixie cheaper)

| family | n | nixie/z3 | | family | n | nixie/z3 |
|---|---|---:|---|---|---|---:|
| s8_w10 | 3 | **0.30** | | s32_w10 | 3 | **0.18** |
| s8_w40 | 3 | **0.14** | | s32_w4 (unsat) | 3 | **0.025** |
| s8_w80 | 3 | **0.20** | | s32_w40 | 3 | **0.11** |
| s16_w10 | 3 | **0.23** | | s32_w80 | 3 | **0.12** |
| s16_w4 (unsat) | 3 | 1.46 | | s64_w10 (unsat) | 3 | **0.006** |
| s16_w40 | 3 | **0.10** | | s64_w40 | 3 | **0.10** |
| s16_w80 | 3 | **0.18** | | s64_w80 | 3 | **0.10** |
| | | | | **TOTAL** | 42 | **0.123** |

42/42 verdicts agree. Representative absolutes: s64_w80_r0 ≈ 2.0 G
(nixie) vs 21 G (z3); the s64_w10 unsat family refutes in ~13–30 M
instructions vs z3's 5+ G.

## Reading

- **After witness certificates, the lazy reduction wins essentially
  everywhere on this workload class**: 3–170× cheaper per family, total
  geomean 8× (0.123). Cuts refute contradictions without touching the
  unrolled encoding's inference chain; paths witness acceptance with a
  handful of literals while Z3 grinds the full biconditional system.
- The single losing family (s16_w4, 1.46×) is the tiniest canary —
  fixed setup costs dominate both sides there.
- Before the witness redesign, the same grid measured **1.34 total**
  (certificate-dominated): the earlier "eager encoding wins large
  products" conclusion was an artifact of checking cost, not of the
  reduction. The propagator's own per-event O(V+E) maintenance is now
  the next ceiling, visible only at the largest products (s64_w80
  still does ~2 G instructions of graph maintenance for a ~0.5 s
  solve).

## Limitations

- One eager encoding (the standard exact one); no hand tuning on
  either side beyond defaults.
- Synthesis-shaped only; pure-acceptance queries with pinned guards are
  trivial for both and not measured.
- Same-word double reification is pathological for any encoding
  (canaries kept short by design).
- The hybrid-PMU inflation trap documented above: any future
  instruction-count benchmark on this machine must pin and use the
  cluster-scoped event, or it will measure noise.

## Follow-ups

1. The propagator's per-event O(V+E) scans are the remaining ceiling —
   incremental (Ramalingam–Reps) reachability and layer sharing across
   words of one automaton.
2. `-conflict-min-cut`-style smaller cut explanations would compound the
   refutation advantage.
3. cvc5 as a third column when available on this machine.
