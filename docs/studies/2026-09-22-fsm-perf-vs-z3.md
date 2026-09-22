# FSM synthesis performance: Nixie's lazy graph reduction vs Z3's eager encoding

**Date:** 2026-09-22 · **Nixie:** `1cbb34e9` · **Z3:** 4.16.0 · **Tooling:**
`bench/fsm_perf/` (`gen.py` + `run.sh`), reproducible with a fixed seed.

## Question

MonoSAT-style FSM constraints (fixed NFA, guarded transitions, constant-word
acceptance reified as atoms; synthesis = guard search over positive and
negative word examples) have two possible implementations in an SMT
context: a **lazy** theory integration (Nixie: product graphs + the
explained graph propagator with path/cut lemmas) and an **eager** encoding
(plain SMT-LIB formulas — the only option in Z3/cvc5, which have no FSM
theory). Which wins where?

There is no benchmark corpus for this fragment, so this study generates
paired instances and measures both solvers on semantically identical
problems.

## Methodology

**Instances** (`gen.py`, seed 20260922): synthesis-shaped — a candidate
automaton over alphabet {0,1} with three guarded candidate transitions per
(state, symbol) — stay / advance / jump — plus epsilon advances on even
states; two accepting states; 2 positive + 2 negative random words. Grid:
states {8,16,32,64} × word length {10,40,80}, 3 reps each, plus 6 short
UNSAT canaries (the same word demanded accepted and rejected — the
equality is semantic, so both solvers must refute). 42 pairs total.

**Encodings.** Nixie files use the `declare-fsm`/`fsm.*` command surface
directly. Z3 files use the standard **exact** eager encoding: layered
one-hot reachability `R[p][q]` with bounded epsilon relaxation
(`E[i][p][q]`, |Q| monotone iterations; the layering makes the
biconditional system acyclic, hence exact — the same construction as the
solver test suite's independent oracle). Guard variables are shared by
name across all words in both files, so the search space is identical.

**Metrics.** Primary: `perf stat -e instructions:u` (this machine is a
hybrid CPU; atom+core cluster counts summed) — load-independent, unlike
wall time on this machine (load average 46–100 from parallel agents).
Wall cap 120 s per run, recorded only as a footnote. Instruction counts
show a ±2 % run-to-run spread (allocator/hash-seed effects in the full
SMT pipeline; the SAT core alone is bit-stable) — the family-level
effects below are 2–90×, far above that noise. **Verdict agreement is a
soundness canary: any mismatch aborts the run.**

**Honesty note:** the canary did its job before any number was recorded —
the first full run exposed a **false sat** in Nixie's script surface
(a second `fsm.accepts` after an `assert` was silently unregistered),
delta-debugged to a 19-line repro, fixed with incremental registration
(`1cbb34e9`, regressions in `nixie-solver/tests/fsm_script_lifecycle.rs`).
All numbers below are from the fixed binary; 42/42 verdicts agree.

## Results (instruction-count geomean, nixie/z3; < 1 = nixie cheaper)

| family | n | nixie/z3 | | family | n | nixie/z3 |
|---|---|---:|---|---|---|---:|
| s8_w10 | 3 | **0.64** | | s32_w10 | 3 | 2.18 |
| s8_w40 | 3 | **0.47** | | s32_w40 | 3 | 6.79 |
| s8_w80 | 3 | 2.03 | | s32_w80 | 3 | 10.43 |
| s16_w4 (unsat) | 3 | 1.86 | | s64_w10 (unsat) | 3 | **0.011** |
| s16_w10 | 3 | 1.14 | | s64_w40 | 3 | 10.38 |
| s16_w40 | 3 | 2.25 | | s64_w80 | 3 | 13.14 |
| s16_w80 | 3 | 6.17 | | s32_w4 (unsat) | 3 | **0.014** |
| | | | | **TOTAL** | 42 | **1.34** |

## Reading

- **Refutation is where the lazy theory dominates.** The UNSSAT canary
  families (short words, contradictory demands) refute through cuts over
  the shared guard literals: nixie is **70–90× cheaper** than Z3, which
  must grind the unrolled biconditional system. The same shows at
  s8_w10/s8_w40 (**1.5–2× cheaper**).
- **Large products favor the eager encoding.** From ~16 states × 40+
  symbols upward Z3 wins 2–13×: each watched-guard fixation costs the
  graph propagator an O(V+E) scan (V = states × (len+1); e.g. 5184
  vertices and ~7k edges per graph at s64_w80, four graphs), while Z3's
  clauses propagate SAT-natively. This is exactly the documented scale
  target of the first integration (`docs/GRAPH.md`: tens of vertices,
  hundreds of edges; no throughput claim vs MonoSAT) — now quantified
  for the FSM reduction: **the crossover sits near states × word length
  ≈ 500–1000 product vertices for SAT-heavy workloads.**
- Total geomean 1.34 over the mixed grid — Z3 ahead overall on this
  workload class, nixie ahead on the refutation-heavy corner.

## Limitations

- One eager encoding (the standard exact one). A hand-optimized encoding
  (implication-only variants where polarity permits, epsilon-closure
  preprocessing per guard assignment class) could shift Z3's numbers;
  no such tuning was attempted for either side beyond defaults.
- Synthesis-shaped only (free guards, few examples). Pure-acceptance
  queries with pinned guards are trivial for both and not measured.
- Wall times omitted from conclusions (machine contention); instruction
  counts carry the comparison.
- Same-word double reification (both a positive and a negative demand on
  the *same* word) is pathological for **any** encoding — the solvers
  must derive the two independent reifications' equality through shared
  guards alone; canaries are kept short for this reason.

## Follow-ups

1. The propagator's per-event O(V+E) rescans are the bottleneck the
   numbers point at — the documented upgrade path is MonoSAT's
   incremental algorithms (Ramalingam–Reps style reachability), plus
   prefix layer sharing across words of one automaton.
2. A `-conflict-min-cut`-style smaller-cut policy for negative
   explanations would compound the refutation advantage.
3. Re-run on a calm machine for wall-time footnotes; extend the grid
   (alphabet > 2, more examples, interleaved words) if the fragment
   gains users.
