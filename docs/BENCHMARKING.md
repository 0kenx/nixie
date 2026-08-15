# Measuring Heuristic Changes in OxiZ

How to tell whether a search-heuristic change actually helped. This is a **methodology**
document, not an API guide — for API pitfalls see [`PITFALLS.md`](PITFALLS.md).

It applies to any change that alters the *path* the search takes without altering the answer:
branching, phase/polarity, restarts, rephasing, clause deletion, inprocessing schedules,
stabilization, cache and tier policies, and every learned or auto-tuned variant of these.

It does **not** apply to soundness changes. A wrong answer is a bug at n=1; no statistics
required. See `AGENTS.md`.

---

## 1. The core problem: CDCL is chaotic

A CDCL solver is a chaotic dynamical system. Perturb it anywhere and the trajectory diverges —
different conflicts, different learned clauses, different everything downstream. So what you
measure after a change is always two things added together:

```
observed effect  =  the idea's merit  +  trajectory reshuffling
```

The second term is not small. Measured on this repo's own benchmarks (18 instances from
`satcomp2025/main_easy_mid`, CaDiCaL 3.0.1 as the reference implementation):

| perturbation | aggregate cost swing |
|---|---|
| **changing only the RNG seed** (identical solver, identical schedule) | **7.31×** |
| the entire effect being hunted (rephase policy selection) | 2.05× |

Per-instance the noise is strongly bimodal — some instances are effectively deterministic
(`c7552` 1.1× max/min across 12 seeds), others are wild (`fsf-300-354` **203×**, `case17` 49×).
Mean within-instance sd of log cost: **0.52**.

A 2× improvement and a 2× coincidence are indistinguishable without a control.

---

## 2. The rule: every heuristic comparison ships with a matched null

A **null** is a placebo — a change that perturbs the search but contains no useful information.
It answers: *what would I have measured if my idea were worthless?*

**Matched** is the load-bearing word. The null must perturb the search **as hard as** the real
change, differing **only** in the semantic content you claim is doing the work. Magnitude,
timing, frequency, code path, determinism, and number of choices all held equal.

The reported quantity then stops being *treatment vs baseline* and becomes:

```
treatment effect / matched-null effect
```

**If that ratio is ≤ 1 you have nothing**, however good the raw number looked.

### Constructing one

Ask what your change *physically does*, then build something that does the identical physical
thing with the meaning scrambled.

| change under test | matched null |
|---|---|
| new restart policy | same restart *count* and interval distribution, trigger points chosen arbitrarily |
| new phase/rephase action | same phase-array rewrite, but content randomised |
| new clause-deletion heuristic | delete the same number of clauses, chosen by a scrambled score |
| new branching order | same score distribution, permuted across variables |
| any learned model | permute the weights, or shuffle the training labels — preserves the output distribution, severs the input→output mapping |

The last row is the general ML form: keep the marginal output distribution identical, destroy
the relationship to the input. If the model still "wins", it was never using its input.

### Three ways the match gets broken

1. **Null too weak.** A control that barely perturbs makes any real change look good. Real
   example: reseeding CaDiCaL's RNG does *nothing* on some instances, because
   `shuffle_scores`/`shuffle_queue` sit behind a `marked_failed` guard and `opts.randec`
   defaults off. Several instances showed exactly 1.00× seed spread. Always verify the null
   actually moves the cost before trusting it.

2. **Unequal selection opportunities.** If your method takes `argmin` over *k* candidates, the
   null must also take `argmin` over *k* candidates. Best-of-6 beats a single draw on variance
   alone, regardless of merit.

3. **Determinism asymmetry** (see §4).

---

## 3. Cost metrics: deterministic, and actually complete

**Never use wall-clock time as the primary metric**, and never as a policy *input*. Other work
on the machine contaminates it, and a time-dependent solver is nondeterministic — which breaks
`bench/z3_parity/run_parity.sh`, bug reproduction, and differential fuzzing.

Use tick/propagation counters. But **verify the counter covers all the work you changed.**
CaDiCaL's printed `ticks` (`searchticks + inprobeticks`) and `propagations` both *exclude*
local-search work, so any schedule using the `walk` rephase action looks artificially cheap on
either metric. That is a silent ~6% understatement that biases toward walk-heavy policies.

Report wall-clock separately, measured on a quiet machine, as a sanity check that the
deterministic proxy tracks reality.

---

## 4. The determinism trap

Constant/deterministic policies never consult the RNG, so they are **seed-invariant**. Measured
directly: forcing a constant rephase action gave bit-identical costs across seeds
(1401/1401, 1728/1728, 1591/1591) while the default schedule swung 3018 → 9786 on the same
instance.

Comparing a deterministic policy against a stochastic baseline **at a single seed** compares a
fixed point against one draw from a distribution — and you happened to draw the baseline's
value. In the case above, the constant policy looked like a winner at seed 0 but was **2.8×
worse** than the default across all 36 (instance, seed) cells.

> A learned policy evaluated in greedy mode has exactly this property. Its baseline does not.

Mitigation: report the baseline as a *distribution* over ≥10 seeds, never a point.

---

## 5. Statistical power: what a valid experiment costs

From the measured noise (sd of log cost = 0.52), runs needed for 80% power at α = 0.05:

| effect to detect | unpaired | with common-random-numbers pairing |
|---|---|---|
| 5% | ~1 791 | ~224 |
| 10% | ~470 | ~59 |
| 20% | ~129 | ~17 |

Consequences:

- **Common-random-numbers pairing is mandatory, not optional** — same instances, same seeds,
  same order across arms. It cuts required runs ~8×.
- A "3% PAR-2 improvement" claim on a few hundred single-seed runs is **unfalsifiable**. Do not
  make it, and do not accept it.
- Prefer seed-insensitive instances during development (`c7552`, `AProVE07-21`, `SCPC-500-*`,
  `div-mitern172` all have max/min < 1.6×). Signal is visible there at a fraction of the cost.
- Report per-family results, never aggregate-only. Report SAT and UNSAT separately —
  `satlib/RND3SAT/UUF*` is entirely unsatisfiable and makes a good negative control.

---

## 6. Hindsight oracles are not achievable policies

A per-instance or per-decision "virtual best" selected with hindsight is an **upper bound**, not
a result. It capitalises on chaos. Always validate by replaying the discovered configuration
under a **fresh seed**.

Worked example from the rephase study — a Bertsekas rollout choosing the best action at each
rephase boundary:

| | geomean gain |
|---|---|
| at the seed it was optimised on | **2.56×** |
| replayed at a fresh seed | **1.20×** (kept 5/10) |

Individual inversions were severe: 7.29× → 0.19×, 12.45× → 0.45×. **80% of the apparent gain
was fitted to one trajectory.**

A useful diagnostic: correlate the apparent advantage against per-instance seed-noise. In that
study, Pearson r = **+0.84** — the "signal" lived almost entirely on chaotic instances. On
seed-stable instances the advantage over the matched null was 1.13×; on noisy ones, 4.24×. When
your effect appears only where measurement is least reliable, it is measurement, not effect.

Another diagnostic: if a selection method has real signal, its choices **concentrate**. Choices
distributed near-uniformly over the action set are the signature of `argmin` over noisy draws.

---

## 7. Checklist

Before claiming a heuristic change helped:

- [ ] Primary metric is deterministic, and verified to include *all* work the change affects
- [ ] Matched null defined, and verified to actually perturb the search
- [ ] Null has equal perturbation magnitude and equal selection opportunities
- [ ] Reported as treatment / null, not treatment / baseline
- [ ] ≥10 seeds per cell; baseline reported as a distribution
- [ ] Common-random-numbers pairing across arms
- [ ] Effect size checked against the power table in §5
- [ ] Any hindsight-selected configuration replayed at a fresh seed
- [ ] Per-family and SAT/UNSAT breakdowns reported
- [ ] Wall-clock confirmed on a quiet machine
- [ ] `./bench/z3_parity/run_parity.sh` clean (soundness is unaffected by any of the above)

---

## 8. Case study: rephase action selection (2026-08)

Full write-up: [`studies/2026-08-rephase-action-selection.md`](studies/2026-08-rephase-action-selection.md).
All numbers in this document come from it. ~1 530 solver runs on an instrumented copy of
CaDiCaL 3.0.1.

**Question.** CaDiCaL's `rephase()` picks from six actions (`original`, `inverted`, `flipping`,
`random`, `best`, `walk`) via a hardcoded round-robin on a counter — it observes nothing about
the instance or search state. Z3's `do_rephase()` is the same shape. Is that fixed schedule
leaving value on the table, i.e. is it worth learning?

**Treatment.** A per-boundary greedy (Bertsekas) rollout choosing the best of the six real
actions at each rephase boundary.

**Matched null.** The same rollout over six variants of `rephase_random` under different RNG
nonces — same operation (full phase-array rewrite), same magnitude, same 6-way branching, zero
heuristic content.

**Outcome — the controls caught two real but meaningless measurements:**

| headline measurement | matched control | verdict |
|---|---|---|
| 2.05× headroom from instance-level policy selection | seed-only oracle **2.26×** | null larger |
| 2.56× from per-boundary action selection | fresh-seed replay **1.20×** | 80% was overfit |
| per-boundary spread across 6 *different* actions: 1.40× | across 6 *identical* ones: **1.52×** | null larger |

The last row is the decisive one: choosing among six semantically identical randomisations
produced *more* cost spread than choosing among six genuinely different actions. At that
decision point the variance is chaos, not action semantics.

**Conclusion.** The rephase action-selection decision point carries no learnable signal, and a
planned restart-level RL selector was cancelled on this evidence. Untouched by the study, and
still open: per-*variable* phase policies, one-shot pre-search phase initialisation, and the
`target` phase array that OxiZ still lacks entirely (see the study's *Verdict* section).
