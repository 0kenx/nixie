# Experiment: how much headroom does CaDiCaL's rephase round-robin actually have?

Run on a patched copy of CaDiCaL 3.0.1 (`../temp/cadical` is a read-only reference; the study
used a private copy — see *Reproducing*). **~1 530 solver runs**: 648 for Part 1, ~730 for the
Part 2 rollout, ~140 for the interval sweep. Paths are relative to the repository root.

Design context: [`2026-08-rl-phase-selection-design.md`](2026-08-rl-phase-selection-design.md).
Methodology this established: [`../BENCHMARKING.md`](../BENCHMARKING.md).

## Setup

**Patch 1 — scriptable rephase actions** (`src/rephase.cpp`). `CADICAL_REPHASE_SCRIPT`
overrides the built-in round-robin at boundary *i* with `script[i]`, where
`O`=original `I`=inverted `F`=flipping `R`=random `B`=best `W`=walk, and `.`/past-end falls
back to the built-in schedule. This turns the schedule into a controllable decision variable.

**Patch 2 — honest cost metric** (`src/stats.cpp`). CaDiCaL's printed `ticks`
(= searchticks + inprobeticks) and `propagations` both **exclude local-search work**, so any
schedule using `W` looks artificially cheap. Added `ORACLECOST` = `totalticks + ticks.walk`.
All results below use this walk-inclusive, deterministic counter — not wall clock, which was
contaminated by a concurrent `rustc` build on the box.

**Validation.** Unscripted, the patched binary reproduces the reference binary's counters
exactly (13547 conflicts / 72319 decisions / 1415463 propagations / 4 rephases on `c7552`);
only per-second rates differ. `DEF` (no `--seed`) matches `--seed=0` on 18/18 instances.

**Instances.** 18 from `satcomp2025/main_easy_mid`, screened to those CaDiCaL solves in
<60 s *and* that reach ≥3 rephase boundaries. 8 SAT / 10 UNSAT, 0.1 s–45 s, 3–57 boundaries.

**Policies (12).** `DEF` (built-in round-robin), 6 constant-action, 5 fixed random schedules.

## Result 1 — the built-in round-robin is the best single fixed policy

| policy | cost | solved | vs DEF |
|---|---|---|---|
| **DEF** | **15892 M** | **18/18** | — |
| allW | 52056 M | 17/18 | +228% |
| rnd4 | 22703 M | 18/18 | +43% |
| allO | 101057 M | 16/18 | +536% |
| allB | 159552 M | 14/18 | +904% |

Every constant action and every random schedule is worse in aggregate. CaDiCaL's design is
vindicated: the *diversity* of the round-robin is what makes it robust. Committing to any
single action is catastrophic (`allB` fails 4 instances outright).

## Result 2 — the hindsight oracle looks like 2.05×…

Per-instance virtual best over the 12 policies: **7757 M vs 15892 M = 2.05× cheaper**
(median 1.62×, geomean 2.44×, max 22.9×). `DEF` was optimal on only **2/18** instances.

Taken alone this reads as a large headroom result. It is not.

## Result 3 — …but the noise floor is 7.31×

Same solver, same schedule, **only the RNG seed changed** (12 seeds):

| | aggregate cost |
|---|---|
| seed 0 (the default) | **15 892 M** ← luckiest of 12 |
| seed 13 | 17 006 M |
| seed 3 | 22 294 M |
| median seed | 28 684 M |
| seed 2 | 116 230 M |

**min→max spread = 7.31×.** Changing nothing at all moves the baseline more than three times
as much as the entire policy oracle gap. And Experiment A's baseline (seed 0) happens to be
the single luckiest seed in the sample.

The virtual-best-over-*seeds* gap (2.26×) is **larger** than the virtual-best-over-*policies*
gap (2.05×) — and the seed is a *conservative* perturbation here, because
`shuffle_scores`/`shuffle_queue` sit behind a `marked_failed` guard and several instances
showed a seed gap of exactly 1.00× (seed had literally zero effect).

## Result 4 — the ranking is not pure chaos, but it does not transfer

Replicating all 12 policies at seed 42:

| | value | chance |
|---|---|---|
| argmin agreement across seeds | 5/18 = 28% | 8% |
| best@seed0 in top-3 @seed42 | 13/18 = 72% | 25% |
| mean Spearman ρ | **+0.469** | 0 |

So a real systematic component exists. But held-out transfer is unstable:

| | geomean | median | improved | regressed |
|---|---|---|---|---|
| train seed0 → test seed42 | 1.35× | 1.15× | 12/18 | 4/18 |
| train seed42 → test seed0 | **0.93×** | 1.06× | 10/18 | 8/18 |

One direction gains 35%, the other **loses** 7%. Choosing the best *fixed* policy on seed 42
and applying it at seed 0 costs **0.44×** — a 56% regression. That is overfitting to chaos.

The asymmetry has a mechanical cause: `DEF` costs 15 892 M at seed 0 but 30 928 M at seed 42,
so "gains" measured against the seed-42 baseline are mostly the baseline being unlucky.

## Result 5 — the trap that manufactures fake wins

`allO`, `allB` etc. are **seed-invariant**: forcing a constant action means `rephase_random`
and `walk` never fire, so the RNG is never consulted. Observed directly — `allO` costs are
bit-identical across seeds (1401/1401, 1728/1728, 1591/1591), while `DEF` on the same
instances swings 3018→9786.

> Comparing a deterministic policy against a stochastic baseline at a single seed is a biased
> comparison that systematically favours the policy. A learned phase policy evaluated in
> greedy mode has exactly this property.

Across all 36 (instance, seed) cells `allO` is in fact **2.8× worse** than `DEF` on geomean
(wins 16/36) — the opposite of what the single-seed table suggested.

## Result 6 — what a valid experiment costs

Within-instance sd of log cost across seeds: **0.52** mean. Strongly bimodal — some instances
are effectively deterministic (`x9-06068` 1.0×, `c7552` 1.1×, `AProVE07-21` 1.2× max/min),
others are wild (`fsf-300-354` **203×**, `case17` 49×, `DS-ST` 28×).

Runs needed for 80% power at α=0.05:

| effect to detect | unpaired | with common-random-numbers pairing |
|---|---|---|
| 5% | ~1 791 | ~224 |
| 10% | ~470 | ~59 |
| 20% | ~129 | ~17 |

---

# Part 2 — the per-boundary greedy rollout (E1 proper)

**Patch 3 — matched null control** (`rephase.cpp`). Script characters `0`–`5` select
`rephase_random` under six distinct nonces. All six are the *same semantic action* and rewrite
the entire phase array, so they perturb the trajectory exactly as hard as swapping O/I/F/B, but
carry zero heuristic content. Verified distinct: on `AProVE07-21` the six span 35.0 M–83.3 M.

**Method.** Bertsekas rollout: at boundary *k*, hold 0..*k*−1 fixed, try every branch at *k*
with the built-in schedule continuing afterwards, keep the cheapest, advance. Unlike Experiment
A's hindsight virtual-best this is an *achievable* policy, and it is the strongest thing any
per-boundary state-aware selector could imitate. 10 instances, ≤10 steps, both branch sets,
~730 runs.

## Result 7 — the rollout looks like a big win

| | geomean vs DEF | median |
|---|---|---|
| ACTION rollout {O,I,F,R,B,W} | **2.56×** | 2.02× |
| NULL rollout {0..5} | 1.34× | 1.20× |
| **ACTION / NULL** | **1.91×** | ACTION wins 9/10 |

Read alone, this says per-boundary action selection carries real signal — the opposite of
Experiment A. Three checks say otherwise.

## Result 8 — 80% of the gain is trajectory overfitting

Replaying each discovered prefix under a fresh seed:

| | geomean |
|---|---|
| gain at the seed it was optimised on | **2.56×** |
| gain at a fresh seed | **1.20×**  (kept 5/10) |

Individual inversions are severe: `x9-07092` 7.29× → **0.19×**; `battleship` 12.45× → **0.45×**.

## Result 9 — the advantage lives exactly where it cannot generalise

Correlating the ACTION-over-NULL advantage against each instance's seed-noise (sd of log cost
over 12 seeds):

**Pearson r = +0.84**

| instance class | n | ACTION/NULL |
|---|---|---|
| seed-**stable** (sd < 0.2) | 6 | **1.13×** |
| seed-**noisy** (sd ≥ 0.2) | 4 | **4.24×** |

On instances where the search is stable — precisely where a genuine heuristic signal would show
up cleanly — choosing the right action beats choosing a meaningless one by 13%. The impressive
numbers come only from chaotic instances, where hindsight optimisation is mining variance.

Encouragingly, on stable instances the (smaller) gains *do* transfer: `AProVE07-21` 1.76× →
1.79×, `c7552` 1.05× → 1.01×, `SCPC-500-13` 1.18× → 1.23×. But its NULL rollout also scored
1.53× on `AProVE07-21` — so even there, most of the transferable gain is "perturb at these
moments", not "perturb this way".

## Result 10 — the decisive per-decision measurement

Cost spread between the best and worst branch, measured at each individual rephase boundary:

| branch set | median spread | geomean | n |
|---|---|---|---|
| six genuinely different actions | **1.40×** | 2.19× | 51 |
| six *identical* randomisations | **1.52×** | 2.36× | 68 |

**Choosing among six semantically identical randomisations produces more cost spread than
choosing among six genuinely different rephase actions.** At the decision point the variance is
chaos, not action semantics. This is the cleanest single number in the study.

Consistently, the greedy-chosen sequences show no pattern — `WF`, `FORF`, `W`, `IB`, `FOIBBF`,
`WI`, `IBRW`, `BORBWIFBFW`, `OORIBWBFOF` — with near-uniform action frequency
(B 12, W 10, F 10, O 7, I 7, R 5). That is the signature of `argmin` over six noisy draws. Real
signal would concentrate (e.g. "B in stable mode").

## Result 11 — the timing knob is no better

I hypothesised from Result 10 that value might lie in rephase *timing* rather than *content*.
Sweeping `--rephaseint` ∈ {125…8000} (default 1000) over 10 instances × 2 seeds:

| | gain vs default |
|---|---|
| best global interval, seed 0 | 1.14× (=8000) |
| best global interval, seed 42 | 1.07× (=4000) |
| tuned on seed 0 → evaluated seed 42, per-instance | **1.07×** (6/10 improved) |
| tuned on seed 0 → evaluated seed 42, single global | **1.04×** |

Below the noise floor, so **not** a detectable effect on this sample (the power analysis demands
~470 unpaired runs for 10%). The only thing worth carrying forward is a weakly consistent
*direction*: both seeds prefer intervals longer than the default 1000. The timing hypothesis is
not supported.

## What this does and does not establish

**Establishes:**
1. The measurement noise floor (7.31× aggregate, sd(log)=0.52 per instance) dwarfs the effect
   size being chased. The report's target — "≥3% PAR-2 reduction" — is roughly two orders of
   magnitude below the noise on a suite this size.
2. Instance-level selection over fixed rephase policies does **not** transfer across an
   irrelevant perturbation. The 2.05× oracle is not attainable.
3. Seed-invariance of deterministic policies is a live bias that will manufacture fake wins.
4. CaDiCaL's round-robin is genuinely well chosen: no fixed alternative beats it.

5. **The rephase action-selection decision point does not carry learnable signal.** Established
   by a matched null control at three levels: per-decision spread (null ≥ action), transfer
   (2.56× → 1.20×), and the r=+0.84 coupling between apparent advantage and instance chaos.
6. Neither does the rephase *interval*.

**Does not establish:** that phase handling in general is a dead end. Specifically untested:
per-*variable* phase policies (the A4/NeuroBack-style intervention), one-shot pre-search phase
initialisation, and target-phase mechanisms absent from Nixie entirely. Those are different
decision points with different noise properties. What is ruled out is the specific action space
the design doc recommended starting from — CaDiCaL's six rephase actions.

## Consequences for the design

- **Every advancement gate in the design doc needs revising.** They were written assuming
  effects are measurable on a few hundred instances at one seed. They are not.
- **Common-random-numbers pairing is mandatory**, not optional — it cuts required runs ~8×.
- **Report seed distributions, never single-seed points.** Minimum ~10 seeds per cell.
- **Include seed-only controls in every comparison**, at matched perturbation strength.
- **The oracle study (E1) must be re-scoped**: run it per-boundary with multiple seeds, and
  compare its oracle against a seed-perturbation oracle of matched strength. If the per-boundary
  oracle does not clear the seed oracle, the project should stop — same logic as before, but now
  with a calibrated noise floor to measure against.
- **Prefer seed-insensitive instances for development** (`c7552`, `AProVE07-21`, `SCPC-500-*`,
  `div-mitern172` all have max/min < 1.6×). Signal is visible there at a fraction of the cost.

## Verdict

**Do not build the restart-level RL selector over rephase actions.** It was the design doc's
recommended starting point (architecture A1); the data says the decision point it targets is
chaos-dominated. A policy trained there would learn noise, and the proposed evaluation protocol
could not have detected the difference.

What survives, in priority order:

1. **A0 — baseline completion.** Nixie still lacks CaDiCaL's `target` phase array, per-backtrack
   `update_target_and_best`, and a real rephase schedule (`rephase_interval: 0` today). This is
   a fidelity gap, justified independently of any learning, and unaffected by these results.
2. **The measurement infrastructure.** The patched CaDiCaL, the deterministic walk-inclusive
   cost counter, the matched-null methodology, and the noise-floor calibration are reusable for
   *any* future heuristic claim in this repo — learned or hand-written.
3. **A3 — the search-posture classifier** (replacing Z3's `m_trail.size() > 0.50*m_trail_avg`).
   Untouched by this study; it is a different decision point with a genuinely one-feature
   incumbent.
4. **A4 — per-variable phase policies.** Also untouched, and the intervention with actual
   published support (NeuroBack). Note its decision point is per-variable, where averaging over
   ~10⁵ decisions may suppress exactly the chaos that sank the per-boundary study.

**Methodological rule to carry forward:** every future heuristic comparison in this repo should
ship with a matched null — a variant that changes nothing semantically but perturbs the search
equally hard. Without it, a 2× measurement means nothing.

## Reproducing

The harness lived in an ephemeral session scratchpad and is **not** checked in — the reference
solvers under `../temp/` are read-only, so the study ran against a private copy. To rebuild it,
copy `../temp/cadical` (`src/`, `build/`, `makefile`, `configure`, `scripts/`, `VERSION`)
somewhere writable and apply three small patches. `make cadical` in `build/` rebuilds
incrementally.

**Patch 1 — `src/rephase.cpp`, scriptable actions.** In `rephase()`, after
`count = lim.rephased[stable]++` and the `single` computation, initialise `char type = 0` and
read `getenv("CADICAL_REPHASE_SCRIPT")`. Index it by `stats.rephased.total - 1`; map
`O/I/F/R/B/W` onto `rephase_original/_inverted/_flipping/_random/_best/_walk`; treat `.` and
past-end as fall-through. Guard the existing schedule chain behind `if (type) {} else if (…)`.

**Patch 2 — `src/rephase.cpp`, matched null.** Add a file-static `nixie_rephase_nonce`; in
`rephase_random()` mix it into the `Random` state (`random += nonce * 7919`). In the script
dispatch, map characters `'0'..'5'` to `rephase_random()` under nonces 1..6.

**Patch 3 — `src/stats.cpp`, honest cost metric.** CaDiCaL's `totalticks` is
`searchticks + inprobeticks` and excludes `stats.ticks.walk`, so walk-heavy schedules look
artificially cheap. Emit `totalticks + stats.ticks.walk` to stderr under a
`CADICAL_ORACLE_COST` env guard.

**Validation before trusting any result:** with no env vars set, the patched binary must
reproduce the reference binary's counters exactly (on `c7552`: 13547 conflicts, 72319 decisions,
1415463 propagations, 4 rephases), and `DEFAULT` must equal `--seed=0`. Both held, 18/18.

Driver: a caching runner keyed on `(instance, script, timelimit, extra_args)` over a
10-worker thread pool, parsing `^s `, `^c conflicts:`, `^c rephased:`, and the `ORACLECOST`
line. Instances: `satcomp2025/main_easy_mid`, screened to those solved in <60 s that reach ≥3
rephase boundaries.

See [`../BENCHMARKING.md`](../BENCHMARKING.md) for the methodology this study established.
