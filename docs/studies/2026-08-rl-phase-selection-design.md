# RL Phase Selection for Nixie's CDCL Core — Design

> **Status: architecture A1 was cancelled.** The experiment this design proposed was run, and
> the rephase action-selection decision point it targets carries no learnable signal. See
> [`2026-08-rephase-action-selection.md`](2026-08-rephase-action-selection.md) for the data and
> the verdict, including which parts of this design survive (A0 baseline completion, A3, A4).
> Retained because the knob inventory in §1 and the reference-solver survey are still accurate
> and useful.

Grounded in the actual code: `nixie-sat/src/`, `../temp/cadical/src/`, `../temp/z3/src/sat/`,
`../temp/cvc5/src/`. Every claim below cites a file:line that was read. **All paths are
relative to the repository root**, not to this file's location.

---

## 0. Findings that change the framing

### 0.1 The decision point worth learning is *rephase action selection*, not "which phase heuristic"

The preliminary report proposes a four-action menu `{PS, LSIDS, MIX, FLIP}` chosen at restart
boundaries. That is a synthesized action space. A better one already exists in the reference
solvers, and it is *demonstrably un-tuned*.

CaDiCaL `rephase.cpp` selects from six actions — `original`, `inverted`, `flipping`, `random`,
`best`, `walk` — via a hardcoded round-robin on a counter:

```
single && !walk :  count % 8   → (inverted, best, flipping, best, random, best, original, best)
single &&  walk :  count % 12  → (…, walk interleaved every third)
stable && !walk :  original, inverted, then (count-2) % 4
!stable         :  flipping, then (count-1) % 4
```

The selector input is `count`, `stable`, and two compile-time options. **It observes nothing
about the instance or the search state.** Z3 is the same shape but weaker — `do_rephase()`
(`sat_solver.cpp:3022`) switches on `m_rephase.count % 4` for `PS_BASIC_CACHING`.

A fixed round-robin over six actions, chosen with zero state input, in the hottest research area
of modern SAT solving, is exactly the kind of decision a small policy should be able to beat.
The report's action space has to *rediscover* phase saving; this one starts from a schedule that
is already known to work and asks only "reorder it adaptively".

**Recommendation: replace the round-robin, not phase saving.**

### 0.2 Nixie already contains most of the action space — as dead code

| Module | Contents | Wired into `solver/`? |
|---|---|---|
| `rephasing.rs` | `RephasingManager`, 7 strategies (Original/Inverted/Random/False/True/Best/Walk), geometric interval | **No** — `pub use` in `lib.rs:*` only |
| `target_phase.rs` | `TargetPhaseSelector`, `PhaseMode{Saved,Target,Random}`, confidence decay, `on_conflict_literal`, `on_learned_clause` | **No** |
| `local_search.rs` | walk / WalkSAT | **No** |
| `ml_branching.rs` | `MLBranching`, online RL-flavoured branching | **No** |
| `agility.rs` | `AgilityTracker` — phase-flip rate, the canonical phase feature | **No** |
| `smoothed_lbd.rs`, `stabilization.rs`, `autotuning.rs` | assorted | check individually |

The *live* rephase is eight lines inline in `solver/decide.rs:443-459`, alternating
restore-best / global-invert, gated on `self.stable` — and it is **off by default**
(`rephase_interval: 0`, `solver/mod.rs:374`).

Consequence: a large fraction of "build the action space" is really "wire up and validate
existing modules", and those modules have never been exercised by the search, so they are
presumed-broken until tested.

### 0.3 Nixie is missing the target-phase array — the biggest SAT-side phase mechanism

| Phase array | CaDiCaL (`phases.hpp`) | Nixie |
|---|---|---|
| `saved` | ✅ | ✅ `phase: Vec<bool>` (`mod.rs:624`) |
| `best` | ✅ | ✅ `best_phase` (`mod.rs:641`) — but see below |
| `target` | ✅ | ❌ **missing** |
| `forced` | ✅ (`opts.forcephase`) | ~ `deterministic_phase: Vec<Option<bool>>` (theory-only) |
| `prev` | ✅ (local search) | ❌ |

Two fidelity gaps beyond the missing array:

1. **Update frequency.** CaDiCaL calls `update_target_and_best()` from *every* `backtrack()`
   (`backtrack.cpp:84`), keyed on `no_conflict_until`. Nixie updates `best_phase` only inside
   `restart()` (`decide.rs:422-429`) and only by scanning the whole trail. Between restarts,
   the best trail is invisible.
2. **Reset semantics.** CaDiCaL resets `target_assigned = 0` on every rephase, and
   `best_assigned = 0` only when the rephase was `'B'` (`backtrack.cpp:51-57`). Target is
   short-horizon, best is long-horizon. Nixie collapses both into one array with one horizon.

`decide_phase()` (`decide.cpp:120`) consults, in order:
`force_saved_phase → forced → initial(if forcephase) → target(if stable) → saved → initial`.
Nixie's `decision_polarity()` (`mod.rs:1491`) consults:
`deterministic → random(2%) → saved ^ inverted`.

**This must be closed before any RL experiment.** Otherwise the policy learns to compensate for
a missing baseline mechanism, and the result won't transfer or replicate.

### 0.4 Crate dependency direction blocks the obvious architecture

`nixie-ml` depends on `nixie-sat` (`nixie-ml/Cargo.toml:14`), not the reverse. A policy living in
`nixie-ml` cannot be called from the search loop except through a trait object owned by
`nixie-sat`.

There is a precedent — `external_branching: Option<BoxedBranchingHeuristic>`
(`solver/mod.rs:290`) — but **do not copy its shape**. `pick_branch_var` builds a fresh
`Vec<Var>` of *all* unassigned variables plus a parallel `Vec<f64>` of scores on **every
decision** (`decide.rs:41-45`). That is O(n) allocation per decision. It is unusable for
anything on the hot path and is itself worth flagging as a performance bug.

Also relevant: `nixie-sat` is `no_std`-capable (`nixie-core` with `default-features = false`,
`libm` dependency). Any policy that ships inside `nixie-sat` must be `no_std` + `libm`, no `std::`
float intrinsics.

### 0.5 `Solver` is not `Clone`

There is no `#[derive(Clone)]` or `impl Clone` for `Solver`. Counterfactual rollouts (the
decisive cheap experiment, §4.2) therefore need **deterministic replay**, not state cloning:
the solver's only randomness is a seeded xorshift64 (`rng_state`, `seed_to_rng_state`
`decide.rs:584`), so `(instance, seed, scripted action prefix)` reproduces a run exactly.
Replay is O(prefix) per rollout but requires zero new unsafe state-snapshot machinery. Take it.

### 0.6 Determinism is a hard constraint the report violates

The report puts CPU time in the state features ("Recent work rates … per decision"), and its
cost function uses `Δt_t`. **Wall-clock time must never enter the policy's state.** A
time-dependent policy makes the solver nondeterministic, which breaks:
- `bench/z3_parity/run_parity.sh` (the soundness canary — AGENTS.md),
- reproducing any bug report,
- the differential fuzzing that this codebase relies on.

Time may appear in the *offline* reward. The *online* state must be built from tick counters.
Nixie already tracks per-mode ticks (`ticks_focused`, `ticks_stable`, `mod.rs:669-670`), which is
CaDiCaL's `stats.ticks.search` — a deterministic proxy for time. Use those.

### 0.7 Soundness posture (state this explicitly, it is a real advantage here)

Phase selection is **soundness-neutral by construction**: it only reorders the search. Under
AGENTS.md's rules this is one of the few places a learned component is admissible at all. The
invariant to assert and test:

> The policy may only write `phase[]` and select among phase *sources*. It must never write
> `deterministic_phase`, never assign a variable, never add or drop a clause, and never
> influence conflict analysis or backtrack level.

`set_preferred_phase` (`mod.rs:1449`) currently writes **both** `phase` and `best_phase`. That
coupling means a theory phase hint silently corrupts the best-phase record. Worth fixing
independently, and the policy must not go through that path.

### 0.8 Benchmarks are already in-repo

| Path | Count | Note |
|---|---|---|
| `satlib/RND3SAT/UUF*` | ~3100 | **all UNSAT** (UUF = uniform unsat). Poor phase-policy training set, excellent negative control. |
| `satcomp2025/main_easy_mid` | 308 | mixed, `.cnf` + `.cnf.xz` |
| `satcomp2024/bench` | 108 | mixed |

No harder / later set is present. §5.1 addresses the split.

---

## 1. Knob inventory

### 1A. Live in Nixie today

Phase-proper:

| Knob | Location | Default | Note |
|---|---|---|---|
| `random_polarity_prob` | `mod.rs:193,348` | `0.02` | Random phase on 2% of *every* decision. CaDiCaL has no such knob (its `randec` randomizes the *variable*, not the phase). Z3 has `PS_RANDOM` as a global mode. This is an Nixie invention — **ablate it**, it may be pure noise injection. |
| `rephase_interval` | `mod.rs:268,374` | `0` (**off**) | Restarts between phase inversions |
| `phase_inverted` | `mod.rs:636` | — | Global XOR on saved phase |
| `phase[]` | `mod.rs:624` | — | Saved phase; written in `backtrack_with_phase_saving` (`decide.rs:233`) |
| `best_phase[]`, `best_trail_size` | `mod.rs:641-644` | — | Updated only at restart |
| `deterministic_phase[]` | `mod.rs:631` | — | Theory-supplied, bypasses randomization + inversion |
| `enable_lucky` | `mod.rs:286,378` | `true` | CaDiCaL `opts.lucky` |
| `set_preferred_phase` / `set_deterministic_phase` | `mod.rs:1449,1482` | — | Theory API |

Adjacent knobs that co-determine phase effectiveness (must be frozen across arms):

| Knob | Default |
|---|---|
| `enable_stabilize`, `stabilize_base`, `focused_luby_cap`, `luby_cap` | `true`, `5000`, `16`, `64` |
| `use_vmtf`, `focused_vmtf`, `use_chb_branching`, `use_lrb_branching` | `true`, `true`, `false`, `false` |
| `restart_strategy`, `restart_interval`, `restart_multiplier` | `Luby`, `100`, `1.5` |
| `reuse_trail` | `true` |
| `enable_chronological_backtrack`, `chrono_backtrack_threshold` | `true`, `100` |
| `var_decay`, `clause_decay` | `0.95`, `0.999` |
| `enable_inprocessing`, `inprocessing_interval` | `false`, `5000` |
| `enable_equiv_substitution`, `enable_bve` | `false`, `false` |

`enable_chronological_backtrack` deserves special note: Shaw & Meel's LSIDS result is
specifically about the phase-saving/chrono-backtracking interaction, and Nixie has chrono
**on by default**. It also already tracks `chrono_backtracks` / `non_chrono_backtracks`
(`mod.rs:418-419`) — a ready-made feature.

### 1B. Present but unwired (free action space / free features)

`RephasingManager` (7 strategies), `TargetPhaseSelector` (`PhaseMode`, confidence,
`on_learned_clause`), `AgilityTracker` (phase-flip rate), `local_search` (walk),
`MLBranching`. Each needs validation before use — none has ever run inside the search.

### 1C. In CaDiCaL, absent from Nixie

**Phase arrays / selection**
- `phases.target` + `opts.target` (0/1/2, 2 = stable-only)
- `phases.forced` + `opts.forcephase` — force initial phase globally
- `phases.prev` — pre-walk snapshot
- `opts.phase` — initial phase polarity (Nixie hardcodes `false` via `unwrap_or(false)`)
- `force_saved_phase` flag (`decide.cpp:126`)
- `opts.stubbornIOfocused` — periodic I/O phase forcing in focused mode

**Rephase scheduling**
- `opts.rephase` 0/1/2 (2 = stable-only, and then measured in `stats.stabconflicts` not
  `stats.conflicts` — `rephase.cpp:29-31`)
- `opts.rephaseint` with **arithmetic** growth `delta = rephaseint * (total + 1)`
  (Nixie's dead `RephasingManager` uses *geometric* `×1.1` — divergence from reference)
- `lim.rephased[stable]` — **separate action counters per mode**
- `shuffle_scores()` / `shuffle_queue()` fired at the *end* of every rephase
  (`rephase.cpp` tail) — coupling between rephase and branching order that Nixie lacks entirely
- `opts.shuffle`, `shufflequeue`, `shufflescores`, `shufflerandom`

**Walk / local search**
- `opts.walk`, `walkeffort` (80‰), `walkmineff`, `walkmaxeff` (1e7), `walknonstable`,
  `walkredundant`, `walkfullocc`, `warmup`

**Random decisions** (variable, not phase — but a confounder to control)
- `opts.randec`, `randeclength`, `randecint`, `randecstable`, `randecfocused`
  (`decide.cpp:39-100`); note length scales as `randeclength * log(count+10)`

**Other**
- `opts.score`, `scorefactor` (950‰)
- `luckyearly`, `luckylate`, `luckyassumptions`
- `reducetarget`, tier-based clause management (`tier.cpp`)

### 1D. In Z3, absent from Nixie

- **`phase_selection` enum as first-class config** (`sat_config.h:26`): `PS_ALWAYS_TRUE`,
  `PS_ALWAYS_FALSE`, `PS_BASIC_CACHING`, `PS_SAT_CACHING`, `PS_LOCAL_SEARCH`, `PS_FROZEN`,
  `PS_RANDOM`. `guess()` at `sat_solver.cpp:1720`.
- **Two-phase search state** `m_search_state ∈ {s_sat, s_unsat}` with
  `m_search_sat_conflicts` / `m_search_unsat_conflicts` budgets, `m_search_next_toggle`
  (`sat_solver.cpp:2018-2022`). `PS_SAT_CACHING` picks `m_phase` in UNSAT-mode and
  `m_best_phase` in SAT-mode (`1734-1738`).
- **The toggle condition is a hand-tuned single-feature classifier** (`sat_solver.cpp:2982`):
  ```cpp
  return (m_phase_counter >= m_search_next_toggle) &&
         (m_search_state == s_sat || m_trail.size() > 0.50*m_trail_avg);
  ```
  A learned replacement for *this predicate* is one of the highest-value, lowest-risk targets
  in the whole design (see architecture A3).
- On toggle: `std::swap(m_fast_glue_backup, m_fast_glue_avg)` + slow (`2994-2995`) — Nixie has
  the analogue (`glue_current`/`glue_saved` swap, `decide.rs:390`) but keyed to stable/focused,
  not to a SAT/UNSAT posture.
- `m_phase_sticky`, `m_rephase_base` (`sat_config.h:92-93`)
- `m_ext->get_phase(next)` — theory phase override, checked *before* the mode switch

### 1E. In CVC5, absent from Nixie

CVC5 is thin on phase *heuristics* but rich on **theory-driven phase**, which matters because
Nixie is a CDCL(T) solver:

- `PropEngine::preferPhase(TNode, bool)` (`prop/prop_engine.cpp:375`) — soft hint
- `requirePhase` (`prop/theory_proxy.cpp:380-398`) — **hard** requirement returned alongside the
  decision literal; `cdclt_propagator.cpp:340` honours it. Nixie's `deterministic_phase` is the
  soft version; there is no hard version.
- MiniSat `polarity` vector with a **sticky bit**: `polarity[v] = int(b) | 0x2`
  (`prop/minisat/core/Solver.h:793`) — one array encodes both "preferred" and "must always".
  Cheaper than Nixie's `Vec<Option<bool>>`.
- `phase_saving` level 0/1/2 (`Solver.h:345`) — limited vs full phase saving
- Justification heuristic (`decision/justification_strategy.cpp`) — derives *both* variable and
  polarity from formula structure. A structural phase prior, and a strong non-learned baseline
  that the report does not consider.
- `decisionMode` option; `--random-freq` (`prop_options.toml:26`, default 0.0 — note CVC5
  defaults random decisions **off**, unlike Nixie's 0.02)

---

## 2. Candidate architectures

### A0 — Baseline completion (prerequisite, not optional)

Wire target phases and a real rephase schedule to CaDiCaL fidelity:
- add `target_phase: Vec<bool>` + `target_assigned: usize`
- call `update_target_and_best()` from `backtrack_with_phase_saving`, keyed on a
  `no_conflict_until` counter, with CaDiCaL's reset semantics
- consult target in `decision_polarity` when `stable`
- implement the six rephase actions against the real solver state; fix
  `RephasingManager`'s geometric interval to CaDiCaL's arithmetic `rephaseint * (total+1)`
- separate per-mode action counters (`lim.rephased[stable]`)
- turn `rephase_interval` on

Deliverable: a solver whose phase machinery is a faithful CaDiCaL port. **This is the control
arm.** Any RL result measured against the current `rephase_interval: 0` solver is measuring A0,
not the policy.

### A1 — Contextual bandit over rephase actions ⭐ recommended first

- **When**: at each rephase boundary (~10³–10⁴ conflicts apart, arithmetic growth). Far rarer
  than the report's restart boundary; overhead is unmeasurable by construction.
- **Action**: `{Original, Inverted, Flipping, Random, Best, Target, Walk}` (7)
- **State**: ~24 O(1) tick-based counters (§3)
- **Model**: 24→32→16→7 MLP + scalar critic (1,413 params, as the report computes) — or start
  with linear/LinUCB, which is auditable and may suffice
- **Baseline to beat**: CaDiCaL's round-robin, *not* phase saving

Rationale: the intervention is 1000× rarer than per-decision, the action space is
pre-validated by two production solvers, and the incumbent selector uses no state at all.

### A2 — Semi-MDP actor-critic at rephase boundary

A1 plus credit assignment across the episode (PPO / A2C, γ over rephase epochs). Only after A1
shows the bandit's myopic reward correlates with end-to-end cost. Risk: rephase epochs number
in the tens per instance — very few decisions per episode, so variance dominates. Mitigate with
the counterfactual dataset from E1 as a warm start.

### A3 — Learned search-posture classifier ⭐ highest value/risk ratio

Replace Z3's `m_trail.size() > 0.50 * m_trail_avg` and/or Nixie's tick-threshold
`check_stabilize` (`decide.rs:370`) with a small learned binary classifier over the same
feature vector. Outputs SAT-posture vs UNSAT-posture, which then selects the phase *source*
(`best`/`target` vs `saved`) exactly as Z3's `PS_SAT_CACHING` does.

Why this is attractive: the incumbent is a literal one-feature hand-tuned threshold with a
magic `0.50`. Beating a one-feature threshold with a 24-feature model is a much softer target
than beating a well-tuned round-robin, and it is directly interpretable ("the policy learned
that trail-height ratio matters less than LBD dispersion on family X").

### A4 — Gated per-variable binary policy (second stage)

Only after A1/A3 clear the gates. Query for the first K ∈ {32,64,128} decisions after a
rephase; `phase[]` everywhere else. 16→32→1 MLP (577 params). Feature per variable: saved
phase, target agreement, best agreement, VSIDS percentile, assignment age, flip count,
occurrence ratio. Output: follow-saved vs flip (so the network defaults to phase saving at
zero output).

Note: this is where the report's LSIDS action belongs — as a *feature* (signed literal
activity margin), not an action. Nixie has no signed literal activity; adding it is a
prerequisite and a standalone hand-engineered baseline worth measuring on its own (H0b).

### A5 — Per-decision GNN — rejected

`decision_polarity` is on the hot path, called once per decision from two sites
(`mod.rs:2332`, `search_ext.rs:315`). Inference there cannot pay for itself, and it confounds
with variable selection. Agrees with the report.

### Code placement

Two paths, both needed:

- **Training/research path**: a new `PhasePolicy` trait in `nixie-sat/src/solver/heuristic.rs`,
  `Option<Box<dyn PhasePolicy>>` in `SolverConfig`, implemented in `nixie-ml`. Respects the
  dependency direction. **Design the callback to take a `&PhaseFeatures` struct of scalars and
  return an enum** — never a `Vec` of candidates. Do not repeat `BranchingHeuristic::select`'s
  O(n)-alloc-per-call mistake.
- **Shipping path**: weights baked into `nixie-sat` as a `const [[f32; N]; M]`, behind a cargo
  feature, `no_std` + `libm`. No file I/O, no allocation, no `std` floats.

---

## 3. State features (tick-based, deterministic, all O(1))

All available from existing counters; none requires a scan. Clip + normalize with
**training-split-only** statistics.

| Group | Features | Source |
|---|---|---|
| Scale | log(num_vars), log(#clauses), log(#learnt), log(trail size) | `num_vars`, `learned_clause_ids` |
| Progress | rephase index, restart index, stabphase index, `stable` flag | `rephase_count`, `stats.restarts`, `stabphases`, `stable` |
| Work rates | Δticks, Δdecisions, Δpropagations, Δconflicts per epoch; propagations/conflict; decisions/conflict | `ticks_focused/stable`, `SolverStats`, `propagations_per_conflict()` |
| Clause quality | `lbd_ema_fast`, `lbd_ema_slow`, their ratio, `glue_current.fast/slow`, avg_lbd | `mod.rs:692-694`, `restart_model.rs:63` |
| Backtracking | chrono ratio, mean backtrack depth, non-chrono count | `chrono_backtrack_ratio()` |
| **Phase-specific** | `best_trail_size / num_vars`, target-vs-saved agreement rate, best-vs-saved agreement rate, **agility** (phase-flip rate), phase-saving reuse rate | `best_trail_size`; `AgilityTracker` (needs wiring); new counters |
| Trail | current trail size / trail EMA (Z3's toggle feature) | needs a trail EMA — Z3 `m_trail_avg` |

The three highlighted phase-specific features (agreement rates + agility) are the ones most
likely to carry the signal, and **none exists today**. `AgilityTracker` is written but unwired.
Wiring it is cheap and is independently useful.

**Excluded on principle**: wall-clock time, memory, anything non-reproducible.

---

## 4. Hypotheses and experiments

Ordered so that each cheap experiment can kill the expensive ones downstream.

### H0 — Baseline gap (must run first)
*Claim*: Nixie's phase machinery is materially behind CaDiCaL's; closing it (A0) produces a gain
independent of any learning.
*Predicts*: target phases + real rephase schedule improves PAR-2 on `satcomp2025/main_easy_mid`.
*Kill*: none — this runs regardless. It defines the control arm.
*Sub-hypothesis H0b*: signed-literal-activity (LSIDS) as a hand-engineered phase heuristic beats
A0. If LSIDS alone captures the gain, the RL work targets a smaller residual.

**E0** — Implement A0. Measure: solved count, PAR-2, conflicts, decisions, on all three in-repo
suites, ≥5 seeds. Also implement the no-op policy-call control (a `PhasePolicy` that returns the
round-robin action) and measure its overhead — this is the zero point for every later
overhead claim.

### H1 — Schedule signal exists (the decisive experiment)
*Claim*: an oracle that picks the best rephase action at each boundary substantially beats the
round-robin.
*Predicts*: oracle PAR-2 ≪ round-robin PAR-2.
*Kill*: **if the oracle gap is small, stop the entire project.** No policy can beat its own
oracle. This is the single most important experiment and it requires no ML at all.

**E1 — Counterfactual rollout study.** For each instance and each rephase boundary *i*:
- replay deterministically to boundary *i* with the reference action prefix
  (`(instance, seed, prefix)` reproduces exactly — §0.5),
- for each of the 7 actions, continue for a fixed **tick** budget,
- record work-to-next-N-conflicts and trail-height achieved.

Yields three things at once: (a) the H1 oracle gap, (b) a supervised warm-start dataset,
(c) the (features → best action) table for H2. Cost is ~7× a normal run per prefix, bounded by
capping boundaries per instance. **Budget the engineering for deterministic replay before
anything else** — it is the load-bearing tool.

### H2 — The oracle action is predictable from O(1) state
*Claim*: a classifier on the §3 features predicts E1's oracle action above the marginal-class rate.
*Predicts*: held-out accuracy > majority-class baseline by a clear margin; permutation
importance identifies which features carry it.
*Kill*: if a gradient-boosted tree on the full feature set cannot beat majority-class offline,
an online 1.4k-param MLP will not either. Stop, or go back and find better features.

**E2** — Offline supervised study on E1's dataset. Fit (i) majority class, (ii) logistic
regression, (iii) GBT, (iv) the target MLP. Report accuracy, and — more importantly — *regret*:
expected work under the predicted action vs oracle vs round-robin.

### H3 — Learned selector beats the fixed schedule end-to-end
*Predicts*: reproducible solved-count increase **or** ≥3% PAR-2 reduction vs A0 on two
family-disjoint held-out sets.

**E3** — Static schedule sweep first (cheap, no ML): permutations of the round-robin, per-mode
variants, action-frequency reweighting. This bounds how much of any gain is "a better fixed
schedule" rather than "state-awareness". **E4** — LinUCB/contextual bandit online. **E5** — MLP
policy warm-started from E2, fine-tuned with PPO. Evaluate greedy, exploration off.

### H4 — Attribution: the gain is state-awareness, not perturbation
*Claim*: the learned policy beats a random selector over the same action set at the same
call frequency.
*Kill*: if random-action-selection matches the policy, the effect is diversification, not
learning. This is NeuroCore's documented negative result and the most likely failure mode.

**E6** — Controls at identical call frequency: round-robin, uniform-random selector,
frequency-matched fixed period, no-op call. Plus an ablation removing the phase-specific
features (agility, agreement rates) to test that the signal lives where we think it does.

### H5 — SAT/UNSAT asymmetry
*Claim*: gains concentrate on satisfiable instances.
*Predicts*: near-zero effect on `satlib/RND3SAT/UUF*` (all UNSAT — §0.8), positive on the SAT
portion of the competition sets.
*Value*: `UUF*` is a ready-made 3100-instance negative control. If the policy "improves" UUF,
suspect a measurement bug.

### H6 — Transfer
*Claim*: the policy does not regress on any held-out family.
**E7** — Group by normalized CNF hash + generator + provenance; train on satcomp2024 + satlib,
lock satcomp2025 for final test. **Note**: `main_easy_mid` is by name the easy/mid slice; a
harder held-out slice must be sourced. Report per-family, never aggregate-only.

### H7 — Residual per-variable signal (gate to A4)
Only after H3+H4 pass. Sweep K including K=0.

### H8 — Posture classifier (A3, can run in parallel with H1)
*Claim*: a learned replacement for Z3's `trail > 0.5 * trail_avg` predicate beats it.
*Predicts*: improved timing of stable/focused (or SAT/UNSAT-posture) switches.
This is independently publishable and does not depend on H1.

### Advancement gates (adopted from the report, tightened for this codebase)

| Gate | Requirement |
|---|---|
| **Soundness** | Every SAT model verified; DRAT/LRAT certificate checked for every UNSAT. `bench/z3_parity/run_parity.sh` clean. Non-negotiable per AGENTS.md. |
| **Determinism** | Byte-identical results across repeated runs at fixed seed, with and without the policy. |
| **Overhead** | Feature extraction + inference < 0.5% of solver CPU, measured against the no-op-call control from E0. |
| **Attribution** | Beats random-selector and frequency-matched controls (H4). |
| **Generalization** | No negative aggregate on any locked family. |
| **Net** | Solved-count increase or ≥3% PAR-2 on two disjoint held-out suites. |

---

## 5. Sequencing

1. **Deterministic replay harness** (`(instance, seed, action-prefix) → exact run`). Everything
   depends on it.
2. **A0 baseline completion** — target phases, real rephase, per-mode counters, wire
   `AgilityTracker`. Measure (E0). *This alone may be the most valuable deliverable.*
3. **E1 oracle study** → H1 go/no-go.
4. **E2 offline predictability** → H2 go/no-go.
5. **E3 static sweep** → establishes how much is schedule vs state.
6. **E4/E5 online policy** → H3.
7. **E6 controls** → H4. Only now is a positive result meaningful.
8. A3 posture classifier and A4 per-variable, in that order.

Steps 1–3 involve no machine learning and are worth doing on their own merits.

## 6. Deliverables that hold value even if the RL result is negative

- CaDiCaL-fidelity phase machinery in `nixie-sat` (target phases, faithful rephase schedule)
- Deterministic replay / counterfactual-rollout harness
- Five orphan modules either wired-and-tested or deleted
- Wall-clock-free feature instrumentation
- A quantified answer to "how much headroom does rephase action selection actually have?" —
  which, as far as the cited literature goes, nobody has published.
