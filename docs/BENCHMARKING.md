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

### Cost is not score: report both

A geomean tick ratio answers *“is the search cheaper?”*. A competition — and this repo's
standing table — scores `P(solve < T)`: the fraction of instances that finish inside a
fixed cap. Under the heavy tail measured in §5 those two objectives come apart, and a
change can be flat on one while moving the other in either direction.

**Report both**, always: the paired geomean ratio against the matched null, *and* the
change in solved-at-cap over the same paired runs. It is the same data, joined the same
way, at no extra machine cost. §11 says why the second number sometimes disagrees with
the first, and when to believe it.

### The neutrality band: ±5%

A geomean effect within **±5%** is **neutral** — reported as neutral, never as a win or a
loss.

The band is a *practical-significance* threshold, not a confidence interval. Paired
deterministic counters (e.g. instructions-to-verdict under trajectory identity) repeat nearly
bit-exactly, so a 3% shift is usually real — and still not actionable: an effect that small
does not justify added complexity, a new maintenance surface, or soundness-adjacent risk,
and it sits inside the day-to-day trajectory reshuffle of unrelated changes landing next to
it. Effects at or beyond the band need the full §2/§5 machinery (matched null, seeds,
families) before they mean anything at all.

Corollaries:

- A pre-registered go bar (e.g. ≥ 1.02×) is legitimate: it prices the change's complexity.
  Landing *inside* the band while failing the bar is a neutral outcome, not a "regression" —
  the write-up must say "neutral, below the pre-registered bar", not "slower".
- Conversely, a within-band *end-to-end* effect is never, by itself, a reason to land a
  change — **with one landing corollary**: a component-level effect **above** the band paired
  with a **neutral** end-to-end result is landable when the component improvement is measured
  real and the landing adds **no new risk — verified as inert (or measured) on every path
  that executes the component, not merely on the presets you benchmarked**.  A SAT-core
  change is an SMT-path change whenever the embedded CDCL(T) core executes it (the SMT
  default runs inprocessing): the trie-vivify landing answered "no new risk" from the
  DIMACS presets alone, and a trajectory-crossed false-SAT surfaced on `pete/cxs-bp`
  (`studies/2026-08-trie-vivify.md`, reverted).  The end-to-end neutrality certifies the
  absence of a *measured system cost*; it says nothing about paths the measurement did not
  cover, and the component win compounds only where the component actually gains share
  later.  Any landing that touches shared solver code ships with a fresh SMT differential
  at the landing commit.
- **Enablement rule (2026-08-25, direction)**: the statistical bar above governs *claims
  of improvement* (win/loss language, "N% faster").  It is not the bar for deciding
  whether a **sound-by-construction mechanism runs by default**.  A change may be enabled
  by default when (a) its soundness is an argument, not a measurement — every unsafe
  interaction is excluded structurally, and (b) screening shows **no obvious regress**:
  a full differential at the new default with **0 verdict disagreements** and a solved
  count not worse than the previous default.  Default flips under this rule still ship
  with the fresh differential and parity from (b); if the later multi-seed A/B shows the
  default was the wrong call, the revert is a one-line flip, not a measurement program.
  (First application: freeze-set collapse, `studies/2026-08-freeze-set-collapse.md` —
  +3 solved / 0 lost / 0 disagreements at default-on.)
- The band applies to *measured* geomeans from paired, deterministic, complete-work metrics.
  Unpaired or single-seed numbers may not borrow it to claim neutrality: establish the
  measurement's own noise first (§4, §5).

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
- [ ] Geomean within ±5% reported as **neutral** (§3 band) — no win/loss language, no landing or reverting on it alone
- [ ] Any hindsight-selected configuration replayed at a fresh seed
- [ ] Per-family and SAT/UNSAT breakdowns reported
- [ ] Solved-at-cap reported alongside the geomean ratio, over the same paired runs (§3, §11)
- [ ] Reference arms present for SAT-side work: **kissat** (goal) and cadical (parity) (§12)
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
precompile/<sha-short>/benchmark/runs/<suite>/<instance>__<inst8>__c<cfghex16>__s<seed>.json
```

- One JSON file per `(instance × config × seed)` run — `oxiz-bench-record/1` schema.
- **Config identity is content-addressed.** The `c<cfghex16>` segment is
  `sha256(canonical flags)[:16]`; `config.id` is a human label only. Two arms with different
  labels but identical flags are **the same cell** (recorded once); any behavioural difference
  must appear in `flags`, or it does not exist. Flags are flat scalars or flat scalar lists
  (list order is significant); nested objects and non-finite floats are rejected so the
  canonical form stays well-defined.
- **Per machine. Never committed. Never compared across different `host.id`s.**
- A measurement's identity is its **join key**:
  `(host.id, git sha, binary sha256, suite, instance sha256, config-hash, seed)`.
  The file name carries the human-readable projection; `record_id` is the first 16 hex of the
  join-key hash.

### Required record fields

| field | discipline it enforces |
|---|---|
| `host.id`, `cpu`, `os` | cross-host comparisons are invalid; tooling refuses to mix hosts by default |
| `git.sha_long/sha_short/dirty` | dirty-tree runs are excluded from reuse unless explicitly requested |
| `binary.sha256` | pins the exact binary, not just the commit |
| `instance.name/sha256/family/sat_expected` | content-addressed instances; family = per-family reporting |
| `config.flags` | content-addressed arm identity (`config_hash` = sha256 of canonical flags); the only place a behavioural difference may live |
| `config.id`, `cmdline` | human label and reproduction aid; **not** part of identity |
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
$BENCH locate --suite satcomp25 --any-host --flags '{"vivify": true}'   # exact flag-set match
$BENCH missing manifest.json                  # cells of a planned experiment not yet in the store
$BENCH verify                                 # revalidate all records (path + ids + schema)
```

Manifest configs are either bare labels (empty flags) or `{id, flags}` objects, so flag
combos are expressed directly:

```json
{
  "suite": "satcomp25", "host": "devbox",
  "configs": [
    "default",
    {"id": "vivify-on",  "flags": {"vivify": true, "vivify_budget_tier": 2}},
    {"id": "vivify-null","flags": {"vivify": true, "vivify_budget_tier": 2, "scramble_order": true}}
  ],
  "seeds": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
  "instances": [{"name": "fs.cnf", "path": "satcomp2025/main_easy_mid/fs.cnf"}]
}
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
   where a reference implementation exists the treatment is also compared against it. Beating a
   weakened arm proves nothing — and beating a *superseded* reference proves less than it looks
   (§12). For SAT-side work the reference arms are **kissat** (the goal) and cadical (the parity
   source); for SMT, `z3`.
4. **Tick-accounting changes are schedule changes.** They alter budgets globally and therefore
   need their own matched-null study before being classed as "engineering" improvements.
5. **Never tune isolated policies against PAR-2 or wall-clock.** Explicit non-priority in the
   established-candidates doc, for the §3 determinism reasons plus the measured null-beating of
   four recent wall-clock-tuned experiments.
6. **Complete fallback or no merge.** Any new mechanism degrades to the trusted path or returns
   `Unknown`; exhaustion never fabricates a consequence, a model, or an answer.
7. **Negative results land in `docs/studies/`.** Already `AGENTS.md` policy; a cancelled idea with
   a recorded verdict is a finished step.

---

## 11. The scoring objective: survival at the cap, and variance as a resource

Added 2026-09-01. Sections 1–8 treat the heavy tail measured in §5 purely as an obstacle
to measurement. It is also a property of the solver, and the two facts have different
consequences.

### 11.1 Geomean cost and solved-at-cap are different objectives

Recall the measured distribution: sd of log cost **0.52**, per-instance seed spread from
1.1× (`c7552`) to **203×** (`fsf-300-354`). A distribution that wide means:

- A change that shifts probability mass across the cap on a handful of tail instances
  **scores**, while barely moving a geomean dominated by the well-behaved middle.
- A change that cheapens instances already solved in 2 s moves the geomean and **scores
  nothing**.

Both appear as "an x% geomean effect". So the ±5% neutrality band in §3 governs *cost*
claims; it is not a verdict on *score*. A change inside the band with a real, paired,
repeatable solved-at-cap gain is a legitimate landing candidate — reported honestly as
"cost-neutral, +N solved at cap", never as "N% faster".

The converse guard matters more, because it is the easier mistake: **a solved-at-cap
gain of a few files is well inside the noise of a 261-file table.** Two runs of the same
binary at different seeds routinely differ by several files (see the standing-gap study's
own load-margin erratum, where the 60 s 6-way cap turned two ~51 s solves into TOs).
Treat solved-at-cap exactly like any other measurement: paired, ≥10 seeds, matched null,
per-family. The flip *list* is the evidence, not the flip *count* — a change that gains 6
and loses 4 has produced a reshuffle, not an improvement, unless the gains concentrate
somewhere the mechanism predicts.

### 11.2 When behind, variance is worth buying

This follows from the same distribution and is the non-obvious half.

Competition score is `P(cost < T)` per instance. If your expected cost on a class of
instances is above the cap and the opponent's is below it, **reducing your variance
lowers your score and increasing it raises your score** — the trailing player wants a
wider distribution, because only the lucky tail crosses the line. This is the standard
trailing-team result from optimal-stopping and portfolio theory, and it applies to the
17 residual files in the standing table more or less exactly.

Practical consequences for study design:

- A mean-neutral, variance-**increasing** change is not automatically worthless. Score it
  on the survival function, not the geomean, and say which regime it is aimed at.
- Symmetrically, a variance-**reducing** change (determinising a policy, removing a
  randomised action) can be geomean-positive and score-negative on the classes where we
  are behind. The stable-mode `RANDPOL` landing is the counter-example worth remembering:
  removing randomness there was **+16 standing files**, because on those instances we
  were *not* behind on expectation — the randomness was destroying a working descent.
  Both directions are real; which one applies is an empirical question about where the
  class's cost distribution sits relative to the cap, and that is measurable before the
  change is built.
- State the regime in the pre-registration (§10.2): *"this change targets instances whose
  median cost is above/below the cap"*. A change evaluated in the wrong regime will be
  scored by a statistic that cannot see it.

### 11.3 Oracle-agreement: a metric that is not chaotic

§5's power table (~1 791 unpaired runs for a 5% effect) is the reason most ideas here are
never evaluated. Where a **ground-truth answer for the decision under test** can be
obtained offline, the runtime metric can be bypassed entirely.

The worked instance already exists in this repo. `Solver::set_phase_hint` (the phase
oracle from the standing-gap study) seeds the saved/target/best arrays with a known model;
on `worker_550` that produced **sat with 0 conflicts, 28 987 decisions, pure descent**.
That experiment establishes that for the model-finding loss class, the *correct decision
is known*. So a candidate phase source can be scored by **agreement with the oracle
phases** — a per-instance, near-deterministic quantity needing no seeds, no matched null,
and no cap.

Generalised: any instance solvable twice yields an oracle for some decision — the model
(correct polarity), the final proof's clause usage (which learned clauses mattered), the
minimised core (which assumptions mattered). Screening candidate heuristics on
oracle-agreement costs a fraction of a runtime A/B and has no chaos term.

Two rules keep this honest:

- Oracle-agreement is a **screening** metric, not a result. It ranks candidates cheaply;
  the survivor still climbs the §10.1 ladder and still needs the full matched-null A/B
  before a default flip. A heuristic that agrees with the oracle and still loses at the
  cap has been falsified, not vindicated.
- The oracle is hindsight (§6). Agreement measured on the instance the oracle came from
  is an upper bound; report agreement on **held-out** instances whose oracles were not
  used to build the heuristic.

---

## 12. The reference bar: kissat is the goal, cadical is the parity source

Added 2026-09-01. Every standing SAT measurement in this repo to date used **CaDiCaL** as
the reference — most recently 145 vs 162 on the 261-file table
([`studies/2026-08-satcomp-standing-gap.md`](studies/2026-08-satcomp-standing-gap.md)).
That choice is correct for one purpose and wrong for the other, and the two were conflated.

**CaDiCaL is the parity source.** It is the implementation this SAT core is ported from;
its counters are the ones our instrumentation is matched against; a differential conflict
count against it is the most sensitive signal available for a port bug, and it caught one
(the inverted shrink-fallback direction). Keep it.

**CaDiCaL is not the bar.** Recent SAT Competition main tracks are won by kissat and its
derivatives, so "close to CaDiCaL" systematically understates the distance to a medal.
A standing table measured only against CaDiCaL can be improved to parity and still be far
from competitive.

From 2026-09, SAT-side benchmarking carries **two reference arms**:

| arm | binary | role |
|---|---|---|
| **goal** | `../temp/kissat/build/kissat` (4.0.4) | the bar. Every standing table reports oxiz / kissat / cadical. |
| **parity** | `../temp/cadical/build/cadical` | port fidelity; differential counters; matched instrumentation |

Both are recorded with `arm.role: reference` in the result store (§9), so a reference cell
is measured once per `(host, instance, seed)` and reused like any other.

### Building the reference

The binary is built in the sibling reference tree, mirroring the existing
`../temp/cadical/build/cadical`. No reference source is modified:

```bash
cd ../temp/kissat && ./configure && make -j8      # -> ../temp/kissat/build/kissat
../temp/kissat/build/kissat --version             # 4.0.4
```

Invocation for benchmarking:

```bash
kissat -q --time=<cap> <file.cnf>     # verdict only; exit 10 = sat, 20 = unsat
kissat --statistics <file.cnf>        # deterministic counters
```

### Counter completeness (§3) applies, differently

§3's warning — CaDiCaL's printed `ticks` is `searchticks + inprobeticks` and silently
excludes local search — has a kissat analogue that is easier to get wrong. kissat splits
its deterministic work across **at least seven** counters:

```
search_ticks  probing_ticks  factor_ticks  kitten_ticks
backbone_ticks  substitute_ticks  transitive_ticks
```

Measured on `constraints_17_0.4_1`: `search_ticks` 230.9 M, `probing_ticks` 40.8 M,
`factor_ticks` 19.9 M, `kitten_ticks` 3.2 M, the remaining three 2.3 M — so
**`search_ticks` alone is 78% of the summed total on that instance**, and the shortfall is
largest exactly on the instances where kissat's inprocessing is doing the winning. Sum the counters, or compare on a metric whose
coverage has been verified on the instance at hand
(`metrics.counter_coverage_verified` is a required record field for this reason).

Two of those counters name inprocessing components OxiZ does not have — `factor_ticks`
(structured factoring/BVA) and `kitten_ticks` (the embedded sub-solver used for sweeping).
Where a kissat comparison shows a large gap, check first whether the gap lives in a
component we simply do not run; that is a different (and cheaper) finding than a decision-
quality deficit.

### What to re-measure

The standing table is the repo's headline number, and it currently has no kissat column.
Re-running it is a mechanical, well-defined job that produces the first honest statement
of the actual competitive gap — recorded as a follow-up in
[`2026-08-novel-research-agenda.md`](2026-08-novel-research-agenda.md) §*2026-09 addendum*.
Until it exists, no document in this repo should describe the SAT core's standing in
competition terms.
