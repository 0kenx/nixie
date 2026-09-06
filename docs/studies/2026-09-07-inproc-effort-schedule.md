# Inprocessing effort schedule: cadical `SET_EFFORT_LIMIT` for the mid-search rounds (2026-09-07, pre-registered)

Follow-up to `2026-09-04-inprocessing-standing-corpus.md`.  That study measured
the mid-search inprocessing bundle as a **1.4–5.7× conflicts-to-verdict win on
the clause-DB-heavy tail** (6s167 0.56×, FmlaEquivChain 0.345×, mrpp 0.531× at
10 seeds) and a **no-go as a default** (9 files sat→TO; corpus on/off geomean
1.44×).  Its decomposition attributed the losses to cap-burning inside the
rounds' own propagation work, and left "a gating policy for the rounds" as the
open lever.  This study replaces the gating-policy idea with the reference
solvers' actual mechanism.

## What the references do (read before designing)

cadical `limit.hpp SET_EFFORT_LIMIT`: **every** inprocessing pass gets
`effort‰ × (search work since that pass's last run)`, and is **skipped
entirely** when the allowance is below `thresh × clauses` (kimits: probe 8‰,
vivify 50‰/thresh 20, subsume 1000‰, factor 50‰).  Round interval
`inprobe.cpp`: `25 × inprobeint × log10(rounds + 9)` conflicts — log-growing,
not flat.  kissat `kimits.h` is the same shape (effort-per-mille windows,
`probeint × nlogn × size-factor`).

Our port before this study: flat `inprocessing_interval = 4000` conflicts
forever, and **absolute** budgets — vivify 10M props **per round** (measured:
g2-slp spends 5–9M round props against ~2.9M search props per interval; the
rounds cost 0.4–3.6× the search work between them, vs the references' 5–100‰).
No skip threshold anywhere.

## Treatment (implemented, env-gated, default off = bit-identical legacy path)

`NIXIE_INPROC_SCHED=1` + `INPROCESS=1`:

1. **Interval growth**: `interval × log10(rounds + 9)` (cadical form; base =
   the configured 4000).
2. **Round window**: search propagation since the last round's end
   (`inproc_search_props_mark`); round-internal propagation is excluded via
   `inproc_round_props_total`, so the window is pure search work.
3. **Pass budgets** (cadical constants): vivify `50‰ × window`, **skipped**
   when below `20 × live clauses` (`vivifythresh`); subsume checks
   `cumulative-search-props` clamped `[1e6, 1e9]` (`subsumeeffort` 1000‰);
   transred `100‰ × window` steps (`transredeffort`).
4. `NIXIE_INPROC_VIVON=1` disables the vivify skip (τ=0 arm): vivify still
   budget-bound, never threshold-skipped.

Per-pass cost/yield attribution added to `NIXIE_INPROC_TRACE` (propagation per
pass; the old trace attributed only yield, and `shr` counts conflict-side
minimization, not vivify — vivify's cost was invisible).

### Matched null (lag-2 window scramble)

`NIXIE_INPROC_SCHED_NULL=1` (implies the schedule): round `r` is budgeted from
the window observed at round `r−2` instead of round `r`'s true window
(`inproc_window_ring`).  Identical budget magnitudes, timing, code paths and
round counts; the *correlation* between "work since the last round" and "this
round's budget" is severed.  Windows on this corpus vary 2–3× across adjacent
rounds, so the null genuinely perturbs.  Rounds without two predecessors use
their true window.

## Screening (default seed, conflicts-to-verdict; NOT the decision measurement)

| file | off | sched (τ=20) | sched+τ0 | flat bundle (2026-09-04) |
|---|---|---|---|---|
| 6s167-opt | 118 191 | 87 900 (0.74) | **72 288 (0.61)** | 82 063 |
| FmlaEquivChain | 2 147 581 | **419 157 (0.195)** | 844 540 (0.39) | ~375 k |
| g2-slp | 344 655 | **134 715 (0.39)** | TO | TO (loser) |
| worker_550 | 106 143 | 55 320 (0.52) | **28 320 (0.27)** | 0.36× |
| shuffling-2-s25 | 23 130 | 15 021 (0.65) | **8 950 (0.39)** | 0.27× |
| summle_X4044 | 62 927 | 82 399 (1.31) | **11 212 (0.18)** | 0.38× |
| noL-11-14 | 1 673 202 | TO | **1 072 731 (0.64)** | TO (loser) |
| mrpp_4x4 | 249 027 | 234 680 (0.94) | **167 804 (0.67)** | 106 k (0.43×) |
| x9-09054 | 249 455 | **93 368 (0.37)** | 619 692 (2.5×) | 0.25× |
| qwh.50 | 134 048 | **130 737 (0.98)** | 280 087 (2.1×) | 0.37× |
| 170058440 | TO | TO | **Sat @ 2 247 600** | TO |
| Timetable_C_392 | 32 841 | TO | TO | TO (loser) |
| 64_25 | 4 500 | 4 638 | TO | TO (loser) |
| rbsat | 305 112 | TO | 724 302 (2.4×) | TO (loser) |
| mp1-Nb7T42 | 106 295 | 631 118 | 191 690 | TO (loser) |

Round cost collapsed 100–1000× (g2-slp 5–9M → ~5k props/round; crypto1
~300k → ~60) with subsumption yield preserved.  **No observable separates the
τ=0 winners from the τ=0 losers** (DB size, window ratio, SAT/UNSAT all mix) —
the split is chaos-dominated, consistent with the 2026-08 rephase study's
null-beats-signal finding at decision points of this kind.

`Timetable` root-caused during screening: any single round — even zero-yield,
zero-prop (interval 8 000/20 000/50 000, probing off) — re-rolls its
walk-solved trajectory (off solves via walk #2's phase descent at 33 k
conflicts; the round's root backtrack is trajectory-identical in shape to a
restart, and restarts already interrupt descents every ~23 conflicts there).
It is a variance file, not a mechanism casualty: 64_25 (22.6 M clauses) is the
same class — off's 4.5 k-conflict solve is lucky, any round re-rolls it.

## Arms (decision measurement)

| arm | env | role |
|---|---|---|
| `off` | (env-unset) | baseline — must reproduce stored `aa293fc` cells bit-exactly (identity gate) |
| `sched` | `INPROCESS=1 NIXIE_INPROC_SCHED=1` | treatment (cadical-literal τ=20) |
| `sched-vivon` | `INPROCESS=1 NIXIE_INPROC_SCHED=1 NIXIE_INPROC_VIVON=1` | treatment variant (τ=0) |
| `schednull` | `INPROCESS=1 NIXIE_INPROC_SCHED_NULL=1` | matched null (lag-2) |

- 54-file corpus (`precompile/corpus-sc24f/`), default seed, serial, pinned
  core, 60 s wall cap (scoring only).  Primary metric conflicts-to-verdict;
  propagations-to-verdict secondary; solved-at-cap + flip lists reported.
- 10-seed tails (1..10, `SEED=`, CRN): the 6 measured winners (6s167, FEC,
  worker_550, noL-11-14, mrpp, summle) and the 4 re-rolled losers (Timetable,
  64_25, rbsat, g2-slp), both treatment arms.
- Null arm on the better-geomean treatment arm, over the tails (T/N).

## Go / no-go (pre-registered)

- **Go (default-on landing candidate: enable_inprocessing = true in the
  CaDiCaL preset with the effort schedule as the mid-search behavior):**
  corpus geomean ≤ **0.95** vs off AND solved-at-60s ≥ **50/54** AND T/N ≤
  1.05 AND ≥ 2/3 of winner-tail medians ≤ 0.95 AND parity/differential clean
  at the new default.
- **Neutral**: geomean in (0.95, 1.05] — report, no landing.
- **No-go**: geomean > 1.05 or solved < 50/54 — negative result documented
  here with per-family data; the schedule stays env-gated default-off.

Falsification: apparent wins living only on high-variance files (§6), or
inverting at fresh seeds, or solved-at-cap losses — trajectory reshuffle, not
effect.  A geomean win with a score loss is **not** landable at default, but
the negative result must name the flip list and its seed-stability.

## Results

### Corpus (54 files, default seed, serial pinned core 3, 60 s cap)

All 162 cells recorded (suite `sc24f-effort`, sha `5ca1eaf`, binary sha256
`35b78fedf929cc0f…`); verdicts differentially verified across arms, 0
verdict disagreements.

**Identity gate**: the `off` arm reproduces the stored standing-table cells
(0223f8e suite) — 36/36 decisive cells conflicts-bit-identical, 0 mismatches
(the other 18 stored cells are concurrent-layout TOs, not comparable).  The
default binary is trajectory-identical to the shipped baseline.

| arm | solved / 54 | conflicts geomean vs off (both-decisive, n=31) | sat / unsat split |
|---|---|---|---|
| off | **50** | 1.00× | — |
| sched (τ=20) | 44 | 0.972× | 1.065× (n=22) / **0.779×** (n=9) |
| sched-vivon (τ=0) | 44 | 0.979× | 1.059× (n=22) / **0.809×** (n=9) |

The geomeans sit **inside the ±5 % neutrality band** (and miss the ≤ 0.95 go
bar); the solved-at-cap bar (≥ 50/54) fails outright — **6 sat→TO flips per
arm, 0 gains**:

* sched loses: mp1-klieber, Timetable, noL-11-14, af-synthesis, frb65-12-2,
  rbsat.
* sched-vivon loses: mp1-klieber, Timetable, pb_300_09, g2-slp, crypto1,
  64_25.
* **Every loss is a SAT file the off-arm solves by a short lucky trajectory**
  (walk descent or early model); the flip sets differ between arms with no
  observable separating winners from losers — the τ-split screening found the
  same wall (DB size, window ratio, SAT/UNSAT all mix).

The per-family structure is consistent and real: **UNSAT-family 0.78–0.81×**
(refutation benefits from the maintained clause DB — 6s167 0.74×, FEC 0.195×,
  x9-09054 0.37×, worker 0.52×), **SAT-family 1.06×** (model-finding files pay
for rounds that cannot help them).  This is the same split the 2026-09-04
study measured for the flat bundle, now with round cost no longer a
confounder: the 100–1000× round-cost collapse did not rescue the SAT side —
the harm is the rounds' trajectory perturbation, not their cost.

**Verdict: no-go per the pre-registered rule** (solved < 50/54; geomean in
the neutral band).  The schedule stays env-gated, default off.  What the
study did establish as reusable: the cost/yield attribution telemetry, the
budget plumbing (window marks, per-pass budgets), the cadical-faithful round
shape, and the measured fact that **the mid-search inprocessing lever is a
refutation-side lever on this corpus** — its wins and losses are verdict-class
correlated, which any future gating policy must respect.

### Tails (10 seeds winners / 5 seeds losers, CRN, 330 cells recorded)

| file | off med | sched med | vivon med | null med | T/N paired | sched/off | vivon/off | TOs (o/s/v/n) |
|---|---|---|---|---|---|---|---|---|
| 6s167-opt | 123 801 | 86 992 | 78 437 | 56 562 | **1.546** | 0.662 | 0.628 | 0/0/0/0 |
| FmlaEquivChain | 1 250 207 | 576 547 | 671 844 | 511 718 | **1.371** | 0.494 | 0.461 | 0/0/0/0 |
| worker_550 | 50 870 | 17 996 | 15 155 | 45 734 | **0.746** | 0.585 | 0.470 | 0/0/1/2 |
| summle_X4044 | 81 122 | 67 458 | 79 275 | 75 768 | **0.781** | 0.694 | 0.855 | 0/0/0/0 |
| mrpp_4x4 | 275 267 | 243 154 | 201 547 | 154 664 | **1.670** | 1.015 | 0.803 | 0/0/0/0 |
| noL-11-14 | 2 851 084 | TO 10/10 | 1 723 271 | 815 582 | — | — | — | 9/10/9/8 |
| Timetable_C_392 | 458 262 | TO 5/5 | TO 5/5 | — | — | — | — | 2/5/5/– |
| af-synthesis | 397 619 | 210 605 | 145 163 | — | — | 0.464 | 0.340 | 1/0/2/– |
| frb65-12-2 | 349 098 | 679 071 | 294 722 | — | — | 3.622 | 0.537 | 1/0/0/– |
| g2-slp | 414 236 | 387 143 | 336 822 | — | — | 0.867 | 0.712 | 2/1/0/– |
| rbsat | TO 5/5 | 321 902 | 824 606 | — | — | — | — | 5/2/4/– |
| 64_25 | 8 315 | 4 746 | TO 5/5 | — | — | 0.932 | — | 0/4/5/– |

Three findings the tails add beyond the corpus row:

1. **The corpus flip list was substantially seed-luck, in both directions.**
   `off` itself TOs 2–9 of 5–10 seeds on six of the "lost" files
   (Timetable's default-seed solve of 33 k sits 14× below its 458 k
   median; rbsat TOs 5/5 under `off` while `sched` solves it 3/5; g2-slp
   and af-synthesis, corpus "losers", are 0.71×/0.46× WINS for `vivon`
   across seeds).  Per §11.1 the flip *list* is the evidence: the only
   seed-robust systematic loss is **Timetable (TO 5/5 under both
   treatments)**; noL-11-14 is a borderline file in every arm (off TOs it
   9/10).  A single-seed 44-vs-50 corpus score is not a P(solve)
   statement — the definitive score experiment is the pre-registered
   multi-seed corpus below.
2. **The tail WINS are seed-robust and large**: 6s167 0.63–0.66×, FEC
   0.46–0.49×, worker 0.47–0.59×, af-synthesis 0.34–0.46×, frb65-vivon
   0.54×, g2-slp-vivon 0.71× — every one wins at every paired seed.
3. **T/N (reactivity) is negative**: 1.546 / 1.371 / 1.670 vs 0.781 /
   0.746, aggregate ≈ **1.156** — the lag-2 scrambled window beats the
   reactive window on 3 of 5 anchors, and the null's medians are the best
   of all arms on 4 of 6.  The *reactivity* (budget ∝ work since the last
   round) carries no positive signal — whatever value the schedule has
   lives in the budget LEVEL (rounds bounded to a small share of search)
   and the interval growth, not in tracking the window.  This joins the
   repo's matched-null-beats-treatment series (random deletion vs glue
   ranking, random rephase vs action selection).

### Verdict

**No-go per the pre-registered rule** (corpus solved 44 < 50; geomean
0.972/0.979 inside the ±5 % band).  The effort schedule stays env-gated,
default off.  Landed as reusable infrastructure: the window/budget plumbing,
the per-pass cost attribution telemetry, and the measured decomposition —
mid-search inprocessing on this corpus is a **refutation-side lever**
(UNSAT-family 0.78–0.81×, seed-robust) whose harm concentrates on
walk-luck SAT trajectories; round cost was exonerated (100–1000× collapse
changed nothing about the SAT side).

Context: kissat runs its full inprocessing pipeline on these same files
(Timetable: 4 probings, 2 eliminations, backbone/factor/kitten sweeps) and
solves them — the fragility is our search's dependence on lucky
walk/descent trajectories, not inprocessing per se.

### Where the residual conflicts gap lives: kissat tick decomposition (2026-09-07)

After the effort schedule, the anchor files still short of kissat were
re-examined against kissat's own deterministic tick counters
(`kissat --statistics`, full solves, 60 s cap) — §12's rule: check first
whether a gap lives in a component we do not run.

| file | nixie off | nixie best arm | kissat | kissat inproc tick share | dominant components |
|---|---|---|---|---|---|
| worker_550 | 106 143 | 28 320 (vivon) | **2 003** | **72 %** | **factor 71 %** |
| Timetable_C_392 | 32 841 | TO | **31 966** | 67 % | **factor 37 %**, kitten 11 % |
| FmlaEquivChain | 2 147 581 | 419 157 | 377 701 | 36 % | probing 17 %, kitten 8 %, factor 7 % |
| 6s167-opt | 118 191 | 72 288 (vivon) | **19 164** | 30 % | probing 18 %, kitten 7.5 % |
| mrpp_4x4 | 249 027 | 167 804 | 179 485 | 17 % | probing 11 % |

Readings, ranked by size:

1. **FEC and mrpp are at kissat conflicts-parity** once the rounds run at
   bounded effort — the schedule work closed those classes.
2. **worker_550 is a factor/BVA class**: kissat refutes in 2 003 conflicts
   (ours: 28 320 best) while spending **71 % of its ticks in `factor`**
   (kissat 4.0's structured factoring/BVA, mid-search, effort-budgeted).
   The search itself is trivial after the restructuring; no retention or
   branching policy closes a 14× conflicts gap.
3. **Timetable is not a conflicts gap at all** (kissat 32 k ≈ our off
   33 k): kissat pays 67 % of its ticks in inprocessing and still solves —
   its rounds are self-financing because the components produce structure,
   while ours (subsume/vivify/transred) perturb walk-luck trajectories
   without restructuring the formula.
4. **6s167's 3.8× residue tracks kissat's 30 % inprocessing share**
   (probing 18 % + kitten 7.5 %) — our rounds closed the subsume/vivify
   part; the remainder is component depth (kissat's probing sweeps are
   ~26 % of its search work), not retention or branching.

**Campaign redirection**: the conflicts-to-verdict factor (1.33×) does not
live in search policy — retention shape (screened null, follow-up #3),
retention signal (2026-09-02 nulls), reactivity (T/N 1.16 above), and
branching family (VMTF+LRB ≈ kissat EVMTF) are all measured or read out.
It lives in **inprocessing components we do not run**, ranked by measured
share: (a) **mid-search factor/BVA** — dominates the worker class
(14×), large on Timetable/FEC; the landed `solver/bva.rs` infrastructure
is pre-search-only, so the port is mid-search safety + effort budgets;
(b) **kitten-class sweeps** (sub-solver equivalences/backbone), 5–11 %;
(c) deeper probing sweeps, 11–18 %. Per §10 these climb the ladder with
matched nulls; the sbva fuzz guards are the soundness starting point.

### Mid-search BVA + AND-gate factoring slices (2026-09-07, follow-up #0 first cut)

Two rewrite rules landed as env-gated, default-off infrastructure in
`solver/bva.rs` (config `enable_mid_bva` / `enable_mid_andgate`, knobs
`NIXIE_BVA_MID` / `NIXIE_ANDGATE` + `_NULL` variants), riding the
`inprocess()` BVA block under the round effort budgets:

1. **k-way BVA mid-search** (the pre-search rule, budgeted): candidate
   groups sharing `|G| ≥ 2` common literals.  Fuzz: 30 k differential +
   10 k null iterations, 0 mismatches, 0 invalid models, introductions
   confirmed.  **Corpus screen: ZERO introductions on every standing
   file** — the corpus's original clause sets carry no beneficial
   `|G| ≥ 2` structure left after pre-search BVE+ELS (consistent with the
   2026-08-23 pre-search SBVA null).  Also fixed en route: the candidate
   collection iterated a `RandomState` `HashMap` (per-process order —
   nondeterministic rank ties); now sorted-key order.
2. **AND-gate factoring** (kissat `factor`'s rewrite, single-hop slice):
   `k ≥ 2` original binaries sharing a tail `q` — `(x_i ∨ q)` — become a
   fresh hub `t` with `(¬t ∨ q)` and `(t ∨ x_i)`, originals deleted.
   Deliberately NOT literal-saving (+1 clause, +2 literals per group);
   the return is search structure: the hub centralizes `k` shared
   implications and re-arms elimination for the partners.  Retirement via
   `remove_clause` (counters exact); unit-propagation consequences are
   preserved through the hub, making reason re-pointing sound.  Fuzz:
   20 k differential + 8 k null iterations (hub-dense generator), 0
   mismatches, 0 invalid models, introductions confirmed.

Screen (default seed, sched-vivon baseline → +ANDGATE):

| file | base | +gate | note |
|---|---|---|---|
| worker_550 | 28 320 | **11 967 (0.42×)** | 4 199 hub intros round 1, avg k≈79 |
| frb65-12-2 | 691 785 | **358 952 (0.52×)** | |
| FmlaEquivChain | 844 540 | **601 666 (0.71×)** | |
| mp1-klieber | TO | **Sat @ 87 218** | flipped IN |
| 6s167-opt | 72 288 | 87 790 (1.21×) | |
| mrpp_4x4 | 167 804 | 217 135 (1.29×) | |
| summle_X4044 | 11 212 | 19 722 (1.76×) | |
| x9-09054 | 619 692 | TO | flipped OUT |
| noL-11-14 | 1 072 731 | identical | no groups |
| Timetable/crypto1/64_25/170058440 | TO | TO | unchanged |

The wins concentrate exactly where the tick decomposition predicted
(worker-class factor structure); the losses are the usual walk-luck
chaos.  **Pre-registered next step (the full study)**: 54-file corpus ×
{sched-vivon, sched-vivon+ANDGATE} × 5 seeds CRN + the lag-2-window null
+ tails on {worker, frb65, FEC, mp1, x9-09054, 6s167, mrpp, summle}; go
bar: paired P(solve) ≥ baseline AND conflicts geomean ≤ 0.95 AND T/N ≤
1.05.  kissat's full `factor` generalizes this rule with quotient CHAINS
(divider binaries per hop, shared-tail matching across hops, structural
scoring) — the single-hop slice here is the minimal sound core of it.

### The combined 5-seed corpus + tails (2026-09-07 final: 1 230 cells recorded)

Machine layout note: this program ran pinned to **E-cores 10–19** (the
allocated cores) with the 60 s wall cap — per-file arm pairing keeps every
comparison internally consistent, but absolute solved counts are NOT
comparable to the P-core standing table, and the tails' TO columns are
E-core-contaminated (files solving in ~20 s on P-cores TO here).  A
stray duplicate of `mrpp_4x4` (64-hex double-prefixed name) appeared in
the corpus directory mid-run; its 15 cells are excluded everywhere and
it is flagged for hygiene.

**Corpus** (54 files × {off, sched-vivon, gate} × seeds 1–5 = 810 cells,
suite `sc24f-ms5b`):

| arm | P(solve) | paired flips vs off | conflicts geomean vs off |
|---|---|---|---|
| off | 194/270 | — | 1.00× |
| sched-vivon | 191/270 | −16/+13, sign-test **p = 0.711** | **0.8298×** (n=113; sat 0.837 / unsat 0.813) |
| gate | 187/270 | −22/+15, p = 0.324 | **0.8200×** (n=107) |

**0 verdict mismatches** across all 810 paired cells; the two
singleton-decisive SATs (mdp gate s1, circuit_64i gate s5) re-run with
`PRINT_MODEL` and model-validated against the original CNFs (0 violated
clauses, conflicts reproduced exactly).  gate/vivon = 0.9616× — the
AND-gate adds nothing corpus-wide beyond the effort schedule.

**Tails** (12 files × 4 arms × 10 seeds = 420 cells, suite
`sc24f-effort-tails2`; decisive medians valid, TO columns ignored):

* T/N vivon-vs-schednull ≈ **0.95** (per-file 0.46–1.47, mixed) — the
  window-reactivity signal remains null; the schedule's value is the
  budget level + interval growth (consistent with the corpus-level
  1.16 measured earlier).
* T/N gate-vs-gatenull: 0.875/0.974/1.011 on the three files with valid
  pairs — the AND-gate rank signal is also ≈ null.
* **frb65 damage confirmed**: gate 821 888 conflicts / 4 TOs vs vivon
  294 722 / 1 TO at 10 seeds — the screen's 0.52× was default-seed luck.
* worker 10-seed medians: vivon **15 155**, gate 24 022 — even on the
  factor class, vivon is the better arm; the single-hop AND-gate's
  worker 0.42× screen was seed luck too.

### Final verdicts (2026-09-07)

1. **`sched-vivon` (effort schedule + budgeted vivify)**: a large,
   multi-seed, corpus-wide conflicts win — **0.83× geomean, both
   verdict families, 0 mismatches** — with P(solve) statistically
   indistinguishable from off (p = 0.71).  The pre-registered letter
   ("P(solve) not lower") fails by 3 cells on the point estimate
   (191 vs 194), so **no default flip**: per §11.1 a ±3-cell deficit on
   a 270-cell table is inside flip noise, but the bar was written
   before the layout was known and it stands.  Resolver, pre-registered:
   a 10-seed corpus halves the flip-count CI; if the paired sign test
   stays ≥ 0.5 the flip lands under the enablement rule (0
   disagreements + solved-not-worse).
2. **AND-gate factoring**: corpus-neutral over vivon (0.96×, inside the
   band), tail-negative on frb65/worker medians, rank signal null —
   **stays env-gated**.  Its mechanism thesis (hub restructuring of
   shared-tail binaries) remains sound and fuzz-clean; the payoff needs
   kissat's full chain/hop rule, not the single-hop slice.
3. The effort schedule's round machinery (budgets, interval growth,
   attribution telemetry) is now the standing substrate for every
   future inprocessing component (factor chains, kitten sweeps,
   deeper probing) — each rides `InprocBudgets` with its own effort
   constant and matched null.

### Open follow-ups (pre-registered next steps, re-ranked 2026-09-07)

0. **Mid-search factor/BVA port** — **first cut landed** (see the BVA +
   AND-gate slices section above): k-way BVA measured corpus-null (no
   groups anywhere), AND-gate factoring screens 0.42–0.71× on the
   factor classes with the full study pre-registered.  kissat's full rule
   adds quotient chains + structural hops on top of the landed core.
1. **Multi-seed corpus P(solve) run** — **DONE** (the combined 5-seed run
   above; the remaining resolver is the 10-seed CI shrink, ~1 620 cells,
   E-core layout fine).
2. **Flat-budget variant**: T/N ≈ 1.16 says drop the window reactivity —
   budget = fixed per-mille of a long-horizon EMA, cadical's tier-scheduled
   vivify (glue-weighted candidate selection, per-tier budgets) as the
   faithful shape.
3. **The 3.7× learned-clause-usage residue on 6s167** (kissat reuses each
   learned clause 5.8×; the tick decomposition above now attributes it to
   component depth, not retention) — tier-structured retention (core/tier1/tier2 by glue with `used`
   promotion) is the untested shape; the 2026-09-02 signal studies tested
   ranking-within-cadical-reduce, not kissat's tier structure.

   **Follow-up #3 screen (same day — closed at the telemetry rung):** the
   `NIXIE_KISSAT_REDUCE` arm implements exactly that shape on top of the
   cadical-reduce port — per-mode used-by-glue histogram (kissat
   `statistics.used[mode].glue[glue]`, bumped at the analysis-use site),
   dynamic tier bounds at the 50 %/90 % usage quantiles (kissat `tiers.c`,
   fallbacks 2/6), deletion fraction growing 50 %→90 % with the reduction
   count (kissat `reducelow`/`reducehigh`), rank unchanged
   (glue desc, size desc). Identity-verified (env-unset bit-identical),
   landed as opt-in infrastructure.  Screen (default seed + seeds 1–3,
   attribution evidence, not store-recorded effect claims): 6s167 ~1.0×,
   FmlaEquivChain **1.3× worse at every seed** (the default-seed 0.55× was
   luck), mrpp wash-to-worse, worker 0.27–0.49× at two of three seeds (the
   third compared against a 2.4 k-conflict off-fluke).  No file class
   benefits consistently → the retention-*shape* lever joins the
   retention-*signal* nulls: the usage residue is not closed by keep-rule
   geometry. What remains untried for it: candidate-selection differences
   in what gets *learned* (kissat's focused-mode watcher/burning policy) —
   search-side, not retention-side.

## The landing and the E-core standing table (2026-09-07, final)

**Landed at `e943921`** (user-directed after the 5-seed program): the
CaDiCaL preset runs inprocessing with the effort schedule + budgeted
vivify (`sched-vivon`) as the default.  Opt-outs: `NIXIE_INPROC_SCHED=0`
(legacy flat), `NIXIE_INPROC_VIVSKIP=1` (cadical's vivifythresh).  The
env-unset binary reproduces the measured `sched-vivon` cells bit-exactly
(decisive cells; TO cells re-confirmed under a longer cap).  Gates at the
landing commit: nextest 10 542, doc tests, clippy, doc, fmt (own files),
z3 parity **0 mismatches at the new default**; binary cached at
`precompile/e943921/`.

**Standing re-measure at the landed default** (162 cells, suite
`sc24f-standing-e943921`, E-cores 10–19, sequential per file, 60 s cap —
a DIFFERENT layout from the stored P-core table; within-layout ratios
only):

| arm | solved / 54 | wall geomean vs nixie | conflicts geomean vs nixie |
|---|---|---|---|
| nixie `e943921` | 39 | 1.00× | 1.00× |
| cadical 3.0.1 | 48 | nixie/cadical = 1.47× | **nixie/cadical = 1.01×** |
| kissat 4.0.4 | 48 | nixie/kissat = 1.61× | nixie/kissat = 1.23× |

0 verdict mismatches.  **Conflicts parity with cadical on the standing
corpus** (1.0097×, n=25 both-decisive) — the search path no longer has a
conflicts deficit against its port source; the kissat residue (1.23×) is
the component-depth gap (factor chains, kitten sweeps) quantified in the
tick decomposition.

**Wall decomposition of the flip** (from the 810-cell ms5b data):
conflicts 0.8298× × per-conflict-wall 1.1359× = **wall 0.9426×** — the
rounds cost ~14 % more wall per conflict (the per-round watch/BIG rebuild
is bandwidth-hungry, and E-cores punish it), but the conflicts saving
dominates: the flip is a net wall win.  The 39-vs-48 solved gap against
the references at THIS layout is dominated by the pre-existing
per-conflict wall disadvantage (≈1.4× vs cadical on E-cores, versus
≈0.88× on the P-core stored table) — an E-core bandwidth amplification,
not a flip regression: the ms5b P(solve) comparison on the same layout
showed the old and new defaults statistically tied.

**Pre-registered follow-ups**: (a) the P-core standing re-measure (the
official table's layout — outside this session's core allocation);
(b) amortize the round rebuild (incremental watch attach instead of
whole-DB rebuild — the per-conflict-wall 1.14× headroom); (c) kissat's
chain/hop factor for the 1.23× conflicts residue.

## Follow-up work log (2026-09-07, items 2+3)

### Item 2: round wall amortization — first slice landed, target measured

Per-pass WALL telemetry added to the round trace (`pass_us
els/bva/pure_sub/vivify/tred`).  Measured split on the big-DB files:
`pure_sub` owns the round wall (28–78 ms/round on g2-slp/FEC vs vivify
2–21 ms).  Direct experiments exonerated both the per-round ~90 MB
occurrence-array allocation (removed by the landed solver-level scratch
reuse — trajectory-identical by construction and by full-counter
verification) and the schedule sort (a no-sort arm measured within
noise).  The remaining cost is the intrinsic O(DB) scan+connect:
**the amortization target is cadical's persistent occurrence-list
design** (occurrences maintained across rounds, only changed clauses
re-scheduled — the pair-stability argument makes it sound: two
unchanged clauses' subsumption relation cannot change).  Pre-registered
as its own study (same shape as the eliminator-persistence work).

### Item 3: pair-mode factoring — landed as opt-in, screen negative on the target class

`NIXIE_ANDGATE=2` implements kissat's 2-chain shape faithfully: one hub
per pivot PAIR across ALL shared tails (`2|Q|` binaries become `|Q|+2`
clauses — the economical form vs one hub per tail; equisatisfiability
and model preservation argued in `solver/bva.rs`, 15 k-iteration
differential fuzz clean with introductions confirmed).  Screen (default
seed, on the landed default bundle): FEC 602 k→604 k (tie with mode 1),
frb65 359 k→243 k (single-seed; mode 1's 10-seed median says treat with
suspicion), 6s167 88 k→73 k, **worker 12 k→29 k — worse on exactly the
class the port targeted**.  The degree-ranked top-256 pair enumeration
over-consolidates worker's densest region while covering a sliver of
its structure.

**Conclusion**: the AND-gate family (both modes) does not reproduce
kissat's worker-class factor win.  The faithful port needs the full
machinery — quotient CHAINS with `distinct_paths` watch-graph scoring
(structure-aware pivot selection, not degree), the eliminate-round
interleave (factor→BVE→factor iteration across rounds — kissat spends
284 M factor ticks on worker, i.e. repeated deep factoring), and
incremental watcher maintenance.  Pre-registered as its own study with
the semantics extracted above; the landed `NIXIE_ANDGATE` modes are the
sound scaffolding for it.

## Persistent occurrence lists → randomized partial subsumption (2026-09-07, landed as default)

The cadical dirty-literal scheme (flags on literals touched since the
last round; ≥2-dirty candidates; dirty-only scans; all-dirty connects)
was implemented rigorously with marking at every addition/strengthen
funnel, a matched null, and 30k fuzz (0 mismatches, 0 invalid models).

**Corpus** (54 files × {off, dirty, dirty-null} × 5 seeds, 1 060 cells,
0 verdict mismatches):

| arm | conflicts/off | wall/off | P(solve) |
|---|---|---|---|
| full scan (off) | 1.00× | 1.00× | 176/265 |
| dirty (recency) | 1.0835× | 1.0195× | 169 |
| **random slice (null)** | **0.9084×** | **0.9102×** | **179** |

| AND-gate mode 1 (bonus arm) | 0.9893× | — | 170 |

(The runner accidentally retained a fourth arm — mode-1 AND-gate on the
new default — 270 cells recorded with the rest: 0.99× conflicts,
P(solve) 170 vs 176 — confirming the AND-gate family stays
corpus-neutral-to-negative and default-off.)
**T/N = 1.153 — the recency semantic is negative at our round cadence.**
The same-size RANDOM literal slice beats both the full scan and the
recency schedule.  Mechanism: rotating partial hygiene — each round
subsumes a fresh random slice of the database, so coverage cycles
through everything over rounds without the full scan's re-checking of
known-clean pairs and without recency's systematic blind spots.
(Working through the semantics also corrected an earlier claim: new-
clause dedup is COMPLETE under the dirty scheme — any subsumer of an
all-dirty clause is itself all-dirty — so the recency arm's losses are
lost old-vs-old hygiene, which the random slice restores stochastically.)

The `fullk` (periodic full rounds) and `hotp` (hot-literal probabilistic
connect — connect on a dirty literal the clause contains, so candidates
scanning dirty literals can find it) arms were implemented and screened:
they interpolate (hotp recovers 6s167 to parity; fullk recovers neither
mrpp nor FEC fully) but no configuration dominated the random slice.

**Landed**: `SubsumeScheduleMode::RandomSlice` is the DEFAULT subsume
schedule (env `NIXIE_SUBSUME2=0|1|2` selects full/recency/random).
The default binary reproduces the recorded random-slice corpus cells
bit-exactly.  This is the fifth matched-null-beats-treatment result in
this codebase (rephase actions, retention signals, budget reactivity,
AND-gate rank, dirty scheduling) — and this one is novel against the
references: cadical's scheme loses at our round frequency, and the
randomized variant wins.  Gates: nextest 10 571, doc tests, clippy,
doc, z3 parity 0 mismatches; fuzz 30k clean.

## The 1.23× kissat residue: calibration of both levers (2026-09-07)

**Worker class (14.14× — the factor lever).**  kissat's own statistics
on `worker_550` calibrate the target precisely: **factored = 51 466
introductions (55 % of its 93 713 variables), eliminated = 0, 227
decisions per conflict, 2 003 conflicts** — the magic is pure factoring
at scale, NOT factor→BVE interplay (BVE eliminated nothing), producing a
formula so restructured that refutation is nearly direct.  Our
experiments at the landed rewrite rules: mode-1 at scale (flat schedule,
~10 k intros/round) bloats the DB (+8 k/round — the eliminator cannot
pace per-tail introduction volume) and TOs on wall; pair-mode (the
economical 2|Q|→|Q|+2 form) with the degree cap raised (TOP=1000/2000,
MAXI=30 k/60 k) is non-monotone and wall-bound (34 424 / 15 951 vs base
28 984 vs kissat 2 003) — the per-clause `remove_clause` hygiene over
10 M-clause rounds costs more than the simplified rewrite returns.
Study knobs landed: `NIXIE_ANDGATE_TOP`, `NIXIE_ANDGATE_MAXI`.
**The faithful port spec** (quotient chains with `distinct_paths`
watch-graph scoring, incremental rounds across the solve rather than
mega-rounds, eager watch surgery instead of remove+rebuild) stands as
pre-registered with this calibration.

**6s167 class (3.77× — the probing lever).**  A probe-effort sweep
(`NIXIE_PROBE_PERMILLE` = 80/200/400/800, knob landed) is flat:
identical conflicts at every effort — the probe budget is not binding;
**the depth limit is the candidate schedule** (`generate_probes` queues
binary-implication roots only, and the queue exhausts).  kissat's
probing on this class = 18 % of its ticks and includes look-ahead
failed literals over non-binary structure, congruence closure
(equivalence classes), and kitten sub-solver sweeps — none of which our
`probe_round` has.  Pre-registered as the look-ahead/congruence port.

Both levers are therefore **calibrated, specified, and open** — neither
closes with the landed infrastructure's knobs alone.
