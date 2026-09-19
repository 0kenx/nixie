# The SMT standing table's gap, attributed (QF_LIA −22, QF_BV −3)

**Date:** 2026-09-19. **Input:** the first `bench/smt_perf` snapshot
(z3 4.16.0, nixie `7e5075db`, 60 instances/family, 10 s cap).  Every
loss was reproduced and attributed to a mechanism; this is the map for
the owning arcs.  Nothing here is landed solver behavior — the
deliverable is the diagnosis, the repros, and the fix routes.

## QF_LIA: 32/60 vs z3's 54/60 — two mechanisms, one family cluster

22 losses = 13 timeouts + 9 `unknown`, and **17 of the 22 are
`nec-smt`** (8 timeouts + 9 unknowns); the rest are singles.

### 1. The nec-smt `unknown`s: the deep-encoding class (9 instances)

Repro: `nec-smt/large/checkpass/prp-43-49.smt2` — `unknown` in 0.7 s
with **0 decisions, 0 conflicts** (the solver never searched).

Mechanism: the file's assertion is one giant `let`/`ite`/`=`/`not`
tree nesting **2537 deep** (paren depth; spine composition ≈ 1188
`ite`, 878 `=`, 417 `not` levels), while `ENCODE_DEPTH_LIMIT = 512`
(`solver/mod.rs`).  The depth guard trips at assert time and the
verdict is an instant, spurious `Unknown` — exactly the class the
guard's own comments fixed for bit-vector ops (the
`subtree_exceeds_encode_depth` BV-terminal change recovered 51 corpus
files).  z3 decides these (several at 0 conflicts — its preprocessor
folds them).

Fix route: the Bool/Int-`ite` and `=` arms of `encode_depth_uncached`
are *genuinely recursive* (they recurse into all three ite branches —
unlike the BV mint-and-stop set), so the terminal-class fix does not
apply; the honest fix is the explicit-stack conversion of the Tseitin
encoder (the AGENTS.md stack rule; ~970 lines, 32 recursive sites) or
a flattening pre-pass for ite/eq spines.  Large, hot-path — its own
session.

### 2. The CAV/SMPT timeouts: integer reasoning + simplex blowup

Repro: `CAV_2009_benchmarks/smt/45-vars/problem__022.smt2` (56 lines,
45 vars) — z3: `sat` with `arith-branch 1, arith-dio-calls 1`;
nixie: no verdict in 60 s.

Mechanism, proven in two steps:
- `--conflict-limit 1` never returns in 30 s → the spin produces **no
  SAT conflict at all** — it is inside the theory layer.
- `-t 5` fires exactly at 5 s → the spin is in the deadline-checked
  region (the search's theory callbacks), not encoding.
- `perf` (dev build): ~100 % of samples in `num_rational::Ratio::
  reduce` → BigInt `gcd`/`shr_assign` on multi-limb integers —
  **simplex rational blowup**: coefficients growing exponentially so
  every tableaux op pays a giant GCD.

And the decisive contrast: z3's counter shows **`arith-dio-calls 1`**
— it decides the goal in its Diophantine (equation) solver.  These
problems are equality-heavy integer goals; nixie has no DIO-style
integer solver, so they fall to branch-and-bound over a simplex whose
rationals explode.  Two owning-arc items: the DIO/integer-reasoning
gap and the coefficient-width blowup guard (a bit-width tripwire that
declines the check honestly instead of grinding — `crash_basis`/
`resource_limit` are the existing hooks).

## QF_BV: 50/60 vs 53/60 — the algebraic-identity class (4 instances)

All four losses are z3-`unsat/sat`-at-**0-conflicts** on
multiplier-identity problems (`2017-BuchwaldFried/counterexample.*`,
`Sage2/bench_16217`, `sage/app{7,12}`): z3's rewriter folds the
multiplier distributivity identities outright; nixie bit-blasts the
circuits and grinds (repro: the 291-line BuchwaldFried instance — no
verdict in 20 s).  This is the *wienand distributivity* class the
pure-BV dispatch's own comments name ("the wienand identity folds to
`false` and refutes on the spot" — the SOM/poly-identity rewriting
route); the dispatch's preprocessor covers some shapes, these four
are uncovered.

## The near-miss datum (decisive for prioritization)

All 28 QF_LIA non-solves were re-run at a 35 s cap (3.5× the table's):
**zero** flip to solved.  The gap is *categorical*, not
constant-factor — no amount of percentage-level LIA speedup moves this
table; only the mechanism fixes above do.  (Conversely: the both-solved
median conflict ratio of 1.0 says the mechanisms, once fixed, land on a
solver already competitive per conflict.)

## The standing verdict

The solved-count gap is *not* general slowness — on the both-solved
set the conflict ratio's median is **1.0**.  The gap is concentrated,
mechanism-attributed, and each mechanism has a named owner route
above.  Re-run `bench/smt_perf/run_perf.sh` after any of them lands.
