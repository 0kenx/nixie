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
- [ ] Go/no-go metrics and falsification criteria written down **before** running (§10)
- [ ] Ladder position stated: telemetry / shadow / flag-gated — no default flip without passing gates (§10)
- [ ] Baseline arm is the strongest relevant existing path (plus reference solver where one exists), not a strawman (§10)
- [ ] Every raw run recorded with `benchstore.py`; existing cells reused, never re-run (§9)

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

---

## 9. The result store: run once, reuse everywhere

A disciplined experiment needs ≥10 seeds × N instances × ≥3 arms (treatment, matched null,
strongest baseline). Re-measuring a baseline or null arm for every new study wastes machine-days
and invites quiet top-ups at mismatched settings. So every run is recorded **once**, on disk, and
reused by every later experiment that needs that exact cell.

### Layout

Results live in the same per-machine, gitignored tree as the precompiled binaries
(`AGENTS.md` → *Git: precompile binary cache*):

```
precompile/<sha-short>/benchmark/runs/<suite>/<instance>__<inst8>__<config>__s<seed>.json
```

- One JSON file per `(instance × config × seed)` run — `oxiz-bench-record/1` schema.
- **Per machine. Never committed. Never compared across different `host.id`s.**
- A measurement's identity is its **join key**:
  `(host.id, git sha, binary sha256, suite, instance sha256, config id, seed)`.
  The file name carries the human-readable projection; `record_id` is the first 16 hex of the
  join-key hash.

### Required record fields

| field | discipline it enforces |
|---|---|
| `host.id`, `cpu`, `os` | cross-host comparisons are invalid; tooling refuses to mix hosts by default |
| `git.sha_long/sha_short/dirty` | dirty-tree runs are excluded from reuse unless explicitly requested |
| `binary.sha256` | pins the exact binary, not just the commit |
| `instance.name/sha256/family/sat_expected` | content-addressed instances; family = per-family reporting |
| `config.id`, `flags`, `cmdline` | reproducible arm definition |
| `arm.role`: `treatment\|null\|baseline\|reference` | matched-null protocol is part of the data, not prose |
| `metrics.primary {name, value}` | deterministic counter only |
| `metrics.counter_coverage_verified: true` | §3's completeness check is mandatory to record at all |
| `wall_clock_s` | optional sanity value; rejected as primary metric |
| `verdict.answer`, `verified_model_or_proof` | a non-`unknown` verdict must have been model-checked or proof-checked |

### Tooling: `bench/suite/scripts/benchstore.py`

```bash
BENCH=bench/suite/scripts/benchstore.py
$BENCH record run.json                        # validate + file into precompile/<sha>/benchmark/
$BENCH locate --suite satcomp25 --instance fs.cnf --host $HOST   # find cached cells
$BENCH missing manifest.json                  # cells of a planned experiment not yet in the store
$BENCH verify                                 # revalidate all records (path + record_id + schema)
```

Experiment protocol:

1. Write the manifest (`suite`, `host`, `instances` × `configs` × `seeds`) **and** the §10
   pre-registration before running anything.
2. `$BENCH missing manifest.json` → run exactly those cells, with the target sha's precompiled
   binary.
3. `record` each run immediately after it finishes.
4. Compare arms by joining stored records on `(instance sha256, config id, seed)` — common-random-
   number pairing holds by construction.

Rules:

- **Never re-run an existing cell to get a nicer number.** That is cherry-picking with extra
  steps. If a measurement must genuinely be superseded (wrong config, broken counter), delete the
  old record explicitly in the write-up and say why.
- Results are attributable to committed trees only: `dirty` records do not participate in reuse.

## 10. Discipline from the 2026-08 reviews

Distilled from [`2026-08-established-research-candidates.md`](2026-08-established-research-candidates.md)
(§*Common implementation gate*, §*Reference-parity backlog*) and
[`2026-08-novel-research-agenda.md`](2026-08-novel-research-agenda.md) (§*Cross-cutting research
protocol*, every proposal's *First experiment*/*Falsification*). Sections 1–8 above say how to
measure; these rules say how an experiment is allowed to proceed.

1. **Escalation ladder.** Every heuristic idea climbs
   `telemetry/oracle study → shadow mode → flag-gated matched-null A/B → default flip`.
   No behaviour change before the previous gate passes with pre-registered exit criteria. All eight
   novel-agenda proposals start instrumentation-only for exactly this reason; four local policy
   ports died at the null without ever touching default behaviour — which was the system working.
2. **Pre-register falsification.** Write the go/no-go metrics and the falsification criteria into
   the study doc *before* running. Post-hoc metrics migrate toward whatever moved. Intermediate
   proxies are not success: "a stronger relaxation violation by itself is not success"; "a reduced
   pivot count is insufficient if row work or coefficient growth increases".
3. **Strongest-baseline rule.** The baseline arm is the strongest relevant existing OxiZ path, and
   where a reference implementation exists (CaDiCaL/Kissat/Z3), the treatment is also compared
   against it. Beating a weakened arm proves nothing.
4. **Tick-accounting changes are schedule changes.** They alter budgets globally and therefore
   need their own matched-null study before being classed as "engineering" improvements.
5. **Never tune isolated policies against PAR-2 or wall-clock.** Explicit non-priority in the
   established-candidates doc, for the §3 determinism reasons plus the measured null-beating of
   four recent wall-clock-tuned experiments.
6. **Complete fallback or no merge.** Any new mechanism degrades to the trusted path or returns
   `Unknown`; exhaustion never fabricates a consequence, a model, or an answer.
7. **Negative results land in `docs/studies/`.** Already `AGENTS.md` policy; a cancelled idea with
   a recorded verdict is a finished step.
