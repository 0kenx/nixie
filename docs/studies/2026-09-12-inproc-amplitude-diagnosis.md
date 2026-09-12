# Inprocessing amplitude on the unsolved class: the diagnosis (2026-09-12)

Priority-1 item from the round-8 close: four corpus files sit at 0/5 where
references solve (`circuit_64in64out`, `Timetable_C`, `170058440`, `64_25`),
with the recorded hook that cadical subsumes 54 % of clauses / strengthens
34 % / vivifies 19.9 k mid-search on circuit_64in64out — an amplitude we do
not run. Pre-registered decision tree: run `NIXIE_INPROC_TRACE=1`, tabulate
our per-round per-pass yields against cadical's; if structurally lower, the
lever is the existing `inproc_budgets` knobs (a screened amplitude arm); if
they match, the files are search-class and close cheaply.

**Verdict: the yields are structurally lower — but the lever is not the
budgets.** The dominant gaps are *mechanisms we do not run* (analyze-time
OTF subsumption/strengthening, eager subsumption at clause addition,
eliminator gate extraction), with budgets secondary (vivify only). Two of
the four files close cheaply, in opposite directions. All numbers below are
deterministic conflict counters; wall times are load-contaminated context
only.

## Instrumentation landed first

Vivify's shortenings ticked no `SolverStats` counter (the mixed `sub=` trace
field cannot separate vivify's subsumptions from the subsume round's), so the
per-pass yield table had a hole. `vivify_clauses` now returns
`(shortened, subsumed)` and `inproc_diag` grew 6 → 8 slots
(`[..., vivify-shortened, vivify-subsumed]`); the `NIXIE_INPROC_TRACE` round
line prints `viv_short= viv_sub=`. Verified trajectory-identical three ways
on circuit_64in64out @ 15 k conflicts (conflicts/decisions/propagations/
restarts bit-equal: trace-on, trace-off, and vs the pre-instrumentation
`precompile/8082e335` binary).

## The four files

### circuit_64in64out — the cascade never starts (mechanism gap)

The formula is **384 variables, 507,904 clauses, every one of size 13**
(plus 64 units). Size-13 originals can only subsume each other by identity,
so *any* subsumption of the original mass must be driven by smaller clauses:
learned clauses (promoted), strengthened clauses, or shrunken originals.
cadical @ 373,215 conflicts (Sat, ~14 s quiet):

| pass | cadical | nixie @ 400 k | ratio |
|---|---|---|---|
| subsumed | 387,625 (54.5 % of all clauses) | 64,265 | **6.0×** |
| — analyze-OTF subsumed | 163,186 | **0** (mechanism absent) | — |
| — eager-sub at add | 38,097 | **0** (mechanism absent) | — |
| — subsume rounds + elim-side | ≈ 176 k | ≈ 42.5 k | 4.1× |
| — vivify-side subsumed | 9,930 | 3,933 | 2.5× |
| strengthened | 242,026 (34.0 %) | self_subsumed **0** + vivify 12,379 | ≈ 20× |
| — analyze-OTF strengthened | 178,782 | **0** | — |
| vivified | 19,889 | 12,379 | 1.6× |
| vivify props | 215,784 | ≈ 55 k | 3.9× |
| restarts | 18,869 (0.051/conf) | 38,005 (0.095/conf) | 1.9× |
| final irredundant clauses | **1,660** | **507,928** | — |

cadical ends with **0.3 % of the original formula left**; we remove
essentially nothing from it. The mechanism, read out of
`../temp/cadical/src/analyze.cpp` (1152-1200): during conflict analysis,
whenever the partial resolvent is smaller than the antecedent
(`resolvent_size < antecedent_size`, antecedent > 2 lits, ≥ 1 resolution),
cadical **rewrites the antecedent clause in place** to the resolvent
(`on_the_fly_strengthen`), and at `resolved == 1` subsumes the original
conflict clause outright — ~0.96 subsumptions + 0.97 strengthenments per
conflict on this file (192 % of conflicts). That both deletes mass directly
*and* continuously feeds small promoted subsumers into the subsume rounds.
Our only strengthening paths are BIG-based self-subsumption (structurally
starved here: the formula has **zero binary clauses**) and vivify (tiny
amplitude, though 4.5× cadical's per-prop yield: 12,379 shortened on ~55 k
props vs cadical's 19,889 on 216 k).

Budgets are demonstrably not the binding constraint on the subsume rounds:
our late-round check allowance grew to 7.5-8.0 M (the cumulative-search
1000 ‰ shape working as coded) — comparable to cadical's *entire-run*
13.8 M subchecks — while per-round yields *decayed* (1,600 early → ~500
late; hit rate ≈ 0.01-0.1 % vs cadical's 2.8 %). We also fire ~10× more
rounds (64 vs cadical's 10 subsumerounds) over a comparable horizon. The
deficit is the subsumer *population* and the strengthening cascade, not the
scan budget.

### Timetable_C — eliminator amplitude, gate-shaped (mechanism gap)

cadical @ 184,851 conflicts (Sat):

| pass | cadical | nixie @ 250 k |
|---|---|---|
| eliminated vars | 147,478 (**52.2 %**) | 80,862 (28.6 %) |
| — AND-gate extraction | 17,009 gates, 15,161 substitutions (`elimands` path) | **mechanism absent** |
| subsumed | 107,784 | 81,500 |
| strengthened | 100,275 (60 % elim-OTF: 60,492) | 6,264 + vivify 9,816 |
| vivified | 0 (never scheduled) | 9,816 |

Our elim phase structure (NIXIE_LOG_ELIM): phase 1 (at 2,000 conflicts)
eliminates 74,733 in round 1 — then yields collapse (198 → 1,732 → 379 over
the next rounds) while cadical's 7 phases average 21 k, carried by gate
extraction/substitution and elim-side OTF strengthening (both in
`elim.cpp`, both absent here). Note the 2026-09-07 study's variance
finding stands alongside: with inprocessing off, a walk descent solves this
file at 33 k conflicts — but cadical's *deterministic* elimination route
(52 % of variables gone) is the mechanism difference, not luck.
Notably our phase-1 elimination balloons the DB 1.75 M → 2.33 M clauses
(resolvents) where cadical's gate path shrinks it.

### 64_25 — closes cheaply: we solve it (cap artifact)

**We solve it: Sat @ 9,538 conflicts (seed 0; cadical 5,026).** Elimination
amplitude is at parity (ours 3,509,694 vars vs cadical 3,620,659 = 74.8 %),
subsumed 1,019,013 vs 564,748. The 0/5-at-60 s is preprocessing wall time on
a 13.1 M-clause file (parse + 3.5 M-var elimination ≈ minutes under load;
cadical's whole run is ~52 s). This is a throughput/cap-class file, not an
amplitude file; it belongs in the tails campaign at a wider cap, not in the
inprocessing program.

### 170058440 — closes cheaply the other way: endurance for everyone

320 vars / 1,120 clauses: nothing to inprocess (883 clauses subsumed over
3 M conflicts; BVE 0). References: **kissat Sat @ ≈ 12.1 M conflicts /
540 s; cadical UNKNOWN at 900 s / 10.3 M conflicts** (its own inprocessing
amplitude on this file: 776 k subsumed = 7.7 %, 12.6 k strengthened,
6 k vivified — and still no verdict). Ours: Unknown at 3 M conflicts
(default seed and seed 0; the 2026-09-07 screen's Sat @ 2,247,600 no longer
reproduces at HEAD — intervening landings re-rolled it). The "references
solve" premise holds only via kissat's 9-minute grind; the file is
search-endurance class (the tiered-schedule item's territory), not an
amplitude file.

## What this does to the priority-1 lever

- The `inproc_budgets` amplitude arm is **the wrong first screen** for the
  class as measured: round allowances already exceed cadical's total spend
  where yields lag 4-6×, and the strengthening deficit is 20× with the only
  in-budget pass (vivify) already the highest-yield-per-prop component.
- The amplitude program item reshapes into **mechanism ports**, in measured
  impact order: (1) analyze-time OTFS (cadical `analyze.cpp` — the single
  largest missing component on circuit_64in64out, 1.9 events/conflict);
  (2) eliminator gate extraction + elimination-side OTF strengthening
  (cadical `elim.cpp` — the Timetable gap); (3) eager subsumption at clause
  addition (38 k on circuit64, 48 % of subsumed on Timetable). A vivify
  amplitude screen (existing knobs) remains the one cheap budget arm worth
  a null-screened try on circuit-class files.
- These ports are structural, reference-grounded work items for the next
  sessions, joining the tiered per-mode schedule (priority-2). OTFS in
  particular is *soundness-sensitive* (in-place antecedent rewrite during
  analysis must respect reason invariants and proof logging) and needs the
  same matched-null discipline as the schedule port.

## Standing item: sc24f re-baseline at HEAD 8082e335

270 cells (54 files × seeds 0-4, default config, 60 s wall cap, 5 workers,
machine load ~8) filed under `precompile/8082e335/benchmark/runs/sc24f/`.
**31/54 files at 5/5, 13 files at 0/5, 180/270 cells solved; 0 verdict
disagreements; every non-unknown cell verified** (SAT by clause-by-clause
model check, UNSAT by cadical agreement — no in-repo DRAT checker; basis
recorded per cell). 0/5 files: the four above, plus all three summle
files, both 48in64out-800gates files, g2-slp, crypto1, si2-b03m,
j3037_10_mdd_b. The summle triple and si2 at 0/5 reproduce the 2026-09-11
Gent-chaos losses under a load-censored 60 s cap (their counter-based
solves sit at 42-90 k conflicts ≈ the cap boundary under load) — treat the
0/5 row as wall-artifact-prone; conflict medians from the solved cells
carry the signal. This table is the fresh baseline any new claim must
screen against.

## Verification

- Trajectory identity of the telemetry: bit-identical counters trace-on /
  trace-off / pre-instrumentation binary (circuit_64in64out @ 15 k).
- `cargo nextest run --workspace --all-features`: 10,966 passed; the 27
  failures are all in `nixie-tla-syntax` (another agent's same-day landing
  `b33e3588`; depends only on thiserror/smallvec — pre-existing at HEAD,
  not touched here).
- clippy `-D warnings` (nixie-sat), fmt, `cargo doc` (nixie-sat): clean.
- Z3 parity 4.16.0: 175 files, 174 correct, **0 wrong**, 1 inconclusive
  (Z3 itself Unknown) — unchanged from the historical baseline.
- `precompile/8082e335/stats_solve` + `build-identity.json` recorded (the
  shared tree's one dirty file, `nixie-theories/src/bv/solver.rs`, is not a
  dependency of the example target; noted in the identity file).
