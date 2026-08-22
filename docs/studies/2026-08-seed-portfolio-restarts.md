# Seed-portfolio restarts: measured variance, the mechanism, and two measurement traps (2026-08-22)

## Question

The 94-file CaDiCaL differential's timeout residue (8 files: oxiz TO where
cadical solves at 4–23 s) is worth more than any constant factor.  Two
candidate levers (user proposal): (1) an alternate-preset fallback after a
no-progress budget, (2) kissat-style restart-with-a-different-PRNG-seed
after budget exhaustion ("trivially sound, exploits the measured variance").

Reference reading first: kissat (`../temp/kissat/src`) has no
restart-with-new-seed inside one solve — it alternates FOCUSED/STABLE
*phases* with per-mode tiers/schedules (`search.c`) and exposes a per-solve
`seed` option (`options.h`).  The portfolio-restart is therefore our own
construction on top of kissat's seed vocabulary.  z3/cvc5 analogues
(`arith_eq_adapter`, arith `EqualitySolver`/`BranchAndBound`) address theory
combination, not SAT seed variance, and were covered by the earlier
case-split rebuild.

## Measured: seed variance on the residue is large (deterministic counts)

`set_random_seed` did not exist at measurement time, so arms were injected
via a temporary raw-state patch (see the caveat below).  Cost metric:
instructions-to-verdict, PMU `cpu_core/instructions`, CPU-pinned,
`target-prof` release build with symbols.  Cells show verdict + G =
1e9 instructions; `TO` = wall-capped at 200–400 s under external load
(those cells mean "≥ that many", not a hard cost).

| file | default | s0 | s1 | s2 | s3 | s4 | s5–8 |
|---|---|---|---|---|---|---|---|
| x9-09054 | S 524 | **S 64** | **S 153** | TO | S 401 | TO | — |
| rbsat-v760 | S 519 | S 635 | TO | TO | TO | **S 328** | s8: **S 88** |
| crypto1-seed102 | TO(>1.7T) | TO | TO | TO | TO | **S 506** | TO |
| noL-11-14 | S 437 | TO | TO | TO | TO | TO | — |
| worker_550 | TO | TO | TO | TO | TO | TO | — |
| circuit_64in64out | TO | TO | TO | TO | TO | TO | — |

Same file, same binary: 64G vs 524G vs >1.7T across RNG states.  Seed-solve
probability at ≤650G: x9-09054 4/6, rbsat 4/9, crypto1 1/9, worker_550 0/6,
circuit64 0/6.

**Caveat (raw-state arms).**  The temporary patch assigned the seed
*directly* as xorshift64 state.  Raw seed `0` is the xorshift fixed point —
that arm ran with randomization effectively *off* (a deterministic
no-random-polarity config), and small raw seeds are weakly spread.  The
landed API mixes seeds through splitmix64 (`seed_to_rng_state`), so the
*specific* arm numbers above correspond to raw states, not to
`set_random_seed(k)`.  The finding that survives: order-of-magnitude seed
variance exists on this residue and a default-first chain converts real
timeouts.  Re-measure the arm table with the mixed API before tuning any
production seed list.

## Correction (2026-08-22, post-landing re-measure with the landed API)

The first mixed-API re-measure reported seeds 0-4 bit-identical to default
on x9-09054/rbsat and nearly invalidated the raw-state finding.  That was a
**harness bug**: the portfolio refactor folded the single-seed knob into
`SEEDS=` while the measurement script still set `SEED=` (silently dead),
so every "seeded" arm ran the default seed.  Diagnosis path worth keeping:
a `rand_calls` counter (temporary instrumentation, since reverted) showed
`decision_polarity` itself is invoked (1.53M calls per 600k conflicts) and
`rand_bool` fires (1.55M hits) — the RNG surface is live; identical
*counts* across arms was the tell that the seed never reached the solver.

Re-measured correctly (`SEEDS=`, quiet machine, instructions-to-verdict):

* x9-09054: default 525G; `SEEDS=1` reaches 600k-conflict cap with only
  1.43M decisions (vs default's 1.53M at the same cap); `SEEDS=4` SOLVES
  at 403k conflicts (~2/3 of default's 1.32M).  Chain @500k arms: 655G
  over 4 arms — default's own trajectory is already the good one at full
  budget, so a default-first chain with generous arms pays ~25% overhead
  vs plain default *when default eventually solves*; the chain wins when
  the budget is capped below default's requirement.
* rbsat: default 519G; chain @500k arms SOLVES in 375G over 3 arms
  (~1.4x faster than default) — rotation genuinely pays here.
* crypto1: still TO >1.7T on default; the raw-state matrix solved it at
  506G on one arm — re-screen its arm list under `SEEDS=` before relying
  on that cell.

Operational summary: `SEEDS=default,0,1,2,3,4 ARM_CONFLICTS=<~60% of the
budget you would otherwise give default>` is the shape that converts
timeouts at bounded budgets; single-seed `default` remains best when the
budget is unlimited and default's trajectory happens to solve.

## The mechanism (landed)

* `Solver::set_random_seed` now records the configured state in a
  `rng_seed` field and `reset()` restores it — previously `reset()` stomped
  back to the built-in constant, so a user seed survived only until the
  first reset and every randomized decision silently reverted to the
  default trajectory mid-portfolio (found while wiring this; the fix is a
  behaviour bug fix for any existing `set_random_seed` user).
* `cnf_solve` gained `SEEDS=<comma list>` (`default` keeps the built-in
  stream) and `ARM_CONFLICTS=<n>`: each arm is a **full solve restart**
  (fresh solver over the same clauses) with its own seed and a per-arm
  conflict budget.  `Unsat`/`Sat` from any arm is a real verdict and returns
  immediately (SAT verdicts are seed-independent facts); only budget
  exhaustion advances.  Deterministic: arm list and budgets are counters,
  never wall-clock.  `max_conflicts()` getter added for budget composition.

## Chain arithmetic (from the measured arm costs)

With a default-first chain at 2M-conflict arms (~128G per exhausted arm):

| file | chain cost | flips |
|---|---|---|
| x9-09054 | 128G + 64G (s0 solves) ≈ 192G ≈ 17 s quiet | **even the 25 s cap** |
| rbsat | 9 × 130G + 88G (s8) ≈ 1.26T ≈ 115 s | ≥ 2 min budgets |
| crypto1 | 5 × ~500G (s4) ≈ 2.5T ≈ 230 s | ≥ 4 min budgets |

Baseline: all three TO at any budget below ~1.7T.  These projections use
the raw-state arm table — re-measure with mixed seeds before shipping a
seed list.

## What the residue actually is (per-file diagnosis)

* worker_550: cadical solves with **511 conflicts / 299k decisions**
  (585 decisions per conflict) — a decision-quality pattern we do not
  reproduce at any seed (0/6).  Branching-heuristic work, not seeds.
* circuit_64in64out: cadical subsumes 54% of clauses, strengthens 34%,
  vivifies 19.9k mid-search — inprocessing amplitude we do not run.
* crypto1: inprocessing-heavy too, plus raw throughput.
* noL/x9-08075/FmlaEquivChain solve on the default path in 47–60 s quiet —
  constant-factor work (the watch-arena/BCP items) is what fits them under
  a 25 s cap.

## The two traps this study hit (again)

1. **Wall-clock caps under external load produced a false negative
   verdict.**  The first seed screen (5 seeds × 6 files, 75–90 s wall caps,
   machine at load 6–12) reported 29/30 TO and "no seed headroom".  The
   deterministic re-measure found 2–3 of those files solve at 64–328G on
   specific seeds (rbsat even solves on the default seed in 46 s quiet).
   Same class as the wisas wall-clock-gate bug: verdicts as a function of
   load.  Every "TO" in a screening table must be an instruction cap, not a
   wall cap, on a shared machine.
2. **CPU pinning starves under load 23 — and the load was our own orphans.**
   `taskset -c 6` + `perf stat` runs TO'd at 900 s for a ~190G chain.
   Post-mortem (2026-08-22 morning): 14 orphaned `cnf_solve` instances from
   the previous day's timed-out screens (the `timeout` wrappers died, the
   children survived; one running since 03:57, several pinning ~4 GB each)
   were the bulk of that load — my own measurement contamination, not
   "other agents' work".  All killed; load fell 73 -> 17 within seconds.
   Two habits recorded: (a) always `pgrep cnf_solve` before trusting a
   quiet-machine claim, (b) screening harnesses must use
   `subprocess.run(timeout=...)` with process-group kill (`start_new_session`
   + `os.killpg`), not a bare shell `timeout` that can orphan children.

Also inconclusive (wall-capped, never re-measured): the alternate-schedule
screen (`RESTART=luby INTERVAL=512`, `STABLE=0`, full inprocessing stack)
reported 15/15 TO — under the same load contamination, so treat it as
unknown, not dead.

## Status of the other items in the plan

* Flat watch arena (~5–7%), unchecked trail reads in propagate,
  conflict-scratch reuse: **deferred** — the load window blocked honest
  identical-trajectory verification; `#![deny(unsafe_code)]` additionally
  rules out the raw-pointer trail cache (documented in
  `sat-elimination-port.md`).  Re-attempt on a quiet machine.
* Mid-search vivification cadence, OTFS-in-analysis: priors unchanged
  (four null-killed ports); the circuit64 diagnosis above is the argument
  for screening vivify cadence cheaply when quiet time exists.
