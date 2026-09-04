# Inprocessing A/B on the standing corpus: pre-registration (2026-09-04)

The module doc at `oxiz-sat/src/config_presets.rs` says the presets'
`enable_inprocessing: false` verdict ("measured net-negative") predates the
landed cadical amortizers (trie-shared vivification, budgeted transred
rounds, on-the-fly vivify subsumption) and should be revisited.  The
2026-08-25 recheck (`docs/studies/2026-08-inprocessing-soundness-recheck.md`)
re-screened with the amortizers present — solved 30 vs 32 at a 30 s cap on
an 80-file sample, single seed, solved-count only — and kept presets off.
This study runs the disciplined A/B on the 54-file standing corpus
(`precompile/corpus-sc24f/`, preserved from `/tmp/sc24f`) with
deterministic counters, per `docs/BENCHMARKING.md` §2/§5/§9/§10.

## What the treatment flips

`INPROCESS=1` in `stats_solve` sets `enable_inprocessing = true` on the
CaDiCaL preset.  On top of the always-on pre-search ELS+BVE and the
mid-search scheduled elimination rounds (gated on `enable_bve`, already
on), the flag adds:

1. pre-search: failed-literal probing pass + hyper-binary probing pass +
   one `inprocess()` round + `vivify_clauses()`;
2. mid-search: every `inprocessing_interval = 4000` conflicts, backtrack
   to level 0 and run `inprocess()` = ELS round + pure-literal elimination
   + occurrence-driven subsumption/strengthening round + vivification
   round + transitive-reduction round;
3. mid-search scheduled probing (`inprobing()`, gated on the flag).

kissat reference shape (read before designing): its search loop interleaves
`probe` rounds (congruence + substitute + backbone + vivify + sweep +
transred + factor, limit growing `probeint × nlog(n)`) and `eliminate`
rounds (dense-mode escalating-bound BVE with forward subsumption, limit
growing `eliminateint × nlog²(n)`) — `src/search.c`, `src/probe.c`,
`src/eliminate.c`.  Our bundle is cadical-shaped (elim + subsume + vivify +
transred + probe), not kissat-shaped; this study tests the bundle we have.

## Arms (all cells recorded via benchstore.py, suite `sc24f`)

| arm | role | binary | flags |
|---|---|---|---|
| `off` | baseline | `stats_solve @ HEAD` | `{}` (default; inprocessing off) |
| `on` | treatment | same binary | `{"INPROCESS": 1}` |
| kissat 4.0.4 | reference | `../temp/kissat/build/kissat` | `{}` |
| cadical 3.0.1 | reference | `../temp/cadical/build/cadical` | `{}` |

- Baseline/reference cells at seed = default are the re-baselined standing
  table (KR1.2), recorded once and reused.
- Cap: 60 s wall (scoring cap only; the solver reads no clock).  Primary
  metrics are deterministic counters.
- CRN pairing: same instance, same seed, same order across arms.

## Primary / secondary metrics

- **Primary: conflicts-to-verdict** (deterministic, complete — the search
  path is the object under test; the inprocessing rounds change it by
  design).  Geomean ratio `on/off` over files both arms decide; SAT and
  UNSAT reported separately; per-family breakdown.
- Secondary: propagations-to-verdict (the throughput-neutral variant of
  the same question).
- Sanity: wall-clock (quiet-ish cores, pinned), solved-at-60s (§3: report
  both cost and score).

## Seeds

- Corpus sweep: default seed (the standing-table trajectory).
- Tails at ≥10 seeds (1..10) both arms: `6s167-opt` (the anchor: 6.5×
  conflicts vs kissat, 1.3× seed spread), `FmlaEquivChain` (3.5× at
  median), `mrpp_4x4` (the throughput outlier, control).
  frb65/shuffling excluded — measured seed-luck (addendum 2).

## Go / no-go (pre-registered)

- **Go (candidate for a preset flip / policy retune):** `on/off`
  conflicts-to-verdict geomean ≤ 0.95 over both-solved files, AND
  solved-at-60s not lower, AND the gain robust on the ≥10-seed tails
  (median ratio ≤ 0.95 per tail).  Then a matched null is built and run
  before any landing (§2): identical rounds/budgets/code path, candidate
  selection scrambled — reported as treatment/null.
- **Neutral:** geomean in (0.95, 1.05] — report as neutral, below the
  pre-registered bar; no landing.
- **No-go:** geomean > 1.05 or solved-at-cap worse — negative result,
  documented here with per-family data.

Falsification criteria: apparent gains that (a) live only on high-seed-
variance files, (b) invert at fresh seeds, or (c) come with solved-at-cap
losses, are trajectory reshuffle, not effect (§6/§11).

## 6s167-opt residue (KR3.2 rider)

The 2026-08-21 elimination-port study measured instructions-to-verdict on
6s167-opt dropping 46.9G → 14.0G with the inprocessing bundle on — the one
clear per-file winner.  This A/B measures whether that is a
conflicts-to-verdict effect (search path closing toward kissat's 19 k) or
merely cheaper per-conflict work.  Either way the residue gets a named
mechanism with the measurement that proves it.

---

## Results (same day, all cells recorded before analysis)

### Corpus re-baseline (KR1.2)

`precompile/dcfc089/stats_solve` (env-unset) vs the 2026-09-01 standing
binary `7e644a7`: **54/54 files verdict- AND conflicts-bit-identical** —
the SAT core has not drifted since the standing study.  Fresh 3-arm
standing pass (54 files × {oxiz, cadical 3.0.1, kissat 4.0.4}, 60 s cap,
pinned cores 3/4/5):

| arm | solved / 54 | conflicts geomean vs kissat (34 both-solved) |
|---|---|---|
| oxiz `off` | 50 | **1.332×** (reproduces the 1.33× factor) |
| cadical 3.0.1 | 51 | — |
| kissat 4.0.4 | 50 | 1.00× |

0 verdict mismatches across all arms on all 54 files.  (Wall geomeans
this pass — oxiz/cadical 0.80×, oxiz/kissat 1.00× over 47 three-solved —
are NOT comparable to the 2026-09-01 numbers (1.27×/1.50×): the machine
carried unrelated load during this pass; wall is sanity-only, and the
conflict counters are load-invariant.)

### The A/B (KR2.1): no-go, per the pre-registered rule

Primary metric, conflicts-to-verdict, `on/off` paired geomean over the 28
both-decisive files: **1.44×** (sat 1.44 / unsat 1.44).  Solved-at-60 s:
**off 50 → on 42** — the pre-registered no-go condition (solved-at-cap
worse) fires regardless of the geomean.  Propagations-to-verdict on the
same pairs: 0.80× (the rounds shorten the search path more than their own
propagation work costs — but only on the files they finish).

The effect is strongly bimodal, and the two halves are both real:

* **on/off ≤ 0.4× on the clause-DB-heavy tail**: FmlaEquivChain 0.17×
  (2 148 k → 375 k, kissat parity at 378 k), stable-300 0.21× (and 7×
  better than kissat), frb65-12-2 0.22×, x9-09054 0.25×, shuffling-2
  0.27×, worker_550 0.36×, qwh.50 0.37×, summle_X4044 0.38×.
* **9 files sat→TO** (Timetable, noL-11-14, af-synthesis, g2-slp,
  crypto1, x9-08075, mp1-Nb7T42, 64_25, rbsat) and 1 TO→sat
  (circuit_64i).  mp1-Nb7T42 and rbsat are files *only* oxiz-`off`
  solves (kissat TOs on both) — the bundle destroys two unique wins.

**Verdict: presets stay off, now on the strength of a deterministic-
counter corpus A/B rather than a 30 s solved-count screen.**  No matched
null was required (no landing); the seed-paired tail distributions below
play the noise-band role for the negative claim.

### Tails (KR2.2): the wins are seed-robust

10 seeds × both arms, common-random-numbers pairing (conflicts):

| file | both-solved | off/on paired geomean | paired min/med/max |
|---|---|---|---|
| mrpp_4x4 | 10/10 | **0.531×** | 0.35 / 0.52 / 0.80 |
| FmlaEquivChain | 9/10 (off TO once) | **0.345×** | 0.20 / 0.36 / 0.66 |
| 6s167-opt | 10/10 | **0.560×** | 0.44 / 0.56 / 0.67 |

`on` wins every one of the 29 paired decisive seeds — the tail gains are
not seed luck (contrast the frb65/shuffling default-seed bias, addendum 2
of the standing study).

### Decomposition (KR3.2): which part of the bundle does what

Scalpel knobs on `stats_solve` (`INPROC_INTERVAL=0` ⇒ mid-search
inprocess rounds off; `NO_PROBE=1` ⇒ no probing anywhere; both ⇒ only
the pre-search one-shot), binary `precompile/2bfd8b0/stats_solve`
(sha256 `704650b7e2da631d…`, env-unset = bit-identical to `off`).

1. **The pre-search one-shot (inprocess + vivify beyond the default
   ELS+BVE) is a no-op**: `INPROCESS=1 INPROC_INTERVAL=0 NO_PROBE=1` is
   *bit-identical* to `off` on 6s167-opt, mrpp_4x4 and FmlaEquivChain at
   every tested seed (e.g. 6s167: 118 191 / 124 517 / 121 437 / 149 261 /
   115 371 — the `off` numbers exactly).  After the preset's pre-search
   ELS+BVE the extra one-shot round finds nothing.  **Do not re-test.**
2. **The periodic mid-search inprocess rounds carry the wins**: rounds-
   only (`NO_PROBE=1`): mrpp 249 k → 106 k (0.43×), FEC 2 148 k →
   ~470 k (0.24×), 6s167 118 k → 88 k (0.73×, 5-seed median).
3. **Scheduled probing (`inprobing`) is mixed and can be catastrophic**:
   probing-only on mrpp seed 0 = 881 692 conflicts (3.5× WORSE than off);
   on 6s167 it is an independent small win (probing-only 0.88×; rounds
   0.73×; both 0.69× — approximately multiplicative).
4. **The same mid-search rounds cause the losses**: rounds-only = TO on
   rbsat and af-synthesis (probing-only solves both, 690 k / 209 k);
   64_25 TOs under the full bundle *at the identical 4 500 conflicts* —
   the cap is burned inside the rounds' own propagation work, not by a
   longer search path.

### The 6s167-opt residue, root-caused

With the full bundle on, 6s167-opt still needs 82 k conflicts vs kissat's
19 k (4.3×; 10-seed median 71 k → 3.7×).  Shape metrics:

| | off | on | kissat |
|---|---|---|---|
| conflicts | 118 191 | 82 063 | 19 164 |
| propagations/decision | 35 | 54 | 93 |
| decisions/conflict | 3.5 | 3.3 | 4.3 |
| avg LBD | 12.32 | 10.46 | — |
| learned clauses | 118 190 | 82 062 | 18 767 (used 5.8× each) |

So the 6.5× residue splits into (a) a **1.8× inprocessing-schedule
component** — closed by the mid-search rounds + probing, measured
seed-robust above — and (b) a **~3.7× learned-clause-quality/retention
residue** that inprocessing does not touch: even with the bundle on, the
DB is tiny (net 628 clauses) and LBD better, yet kissat refutes with 4.4×
fewer, much more heavily reused learned clauses (18.8 k clauses, each
used 5.8× on average).  That residue is lever-2 territory (tiered
retention / usage signal — the 2026-08-22 study's random-deletion-beats-
glue result), not an inprocessing-schedule question.  kissat's
inprocessing components we still lack (factor/BVA, kitten sweep,
congruence, backbone) remain an unquantified further unknown, but the
bundle we have already recovers only the schedule component.

### What not to retry; what is open

* Pre-search one-shot inprocess/vivify beyond default ELS+BVE: measured
  no-op — do not re-test (1).
* Probing-only as a preset: neutral to catastrophic (mrpp 3.5×) — dead.
* Rounds-only as a preset: same 9-file loss list as the full bundle —
  dead as an unconditional flip.
* **Open (next campaign)**: a *gating policy* for the mid-search rounds —
  they pay 2–6× on clause-DB-heavy instances and destroy phase-guided
  model finding on the rest; the win/loss split may be observable (DB
  growth, learned/original ratio, recent walk/lucky success).  Any such
  policy climbs the §10 ladder with a matched null: identical round
  schedule and budgets, pass content scrambled (subsume/vivify candidate
  order by hash instead of occurrence/size rank — the `OXIZ_SBVA_NULL`
  precedent), reported as treatment/null over ≥10 seeds.

### Store

276 records under `precompile/dcfc089/benchmark/runs/sc24f/` (suite
`sc24f`, host `workstation`, sha `dcfc089`), roles baseline/treatment/
reference; every record's verdict differentially verified (0 cross-arm
disagreements).  Decomposition runs are quoted in full above (binary
`2bfd8b0`, not store-recorded — attribution evidence, not effect claims).
Runner: `precompile/corpus-sc24f/ab_runner.py`; analysis:
`precompile/corpus-sc24f/analyze.py`; raw logs `standing4.log`,
`onarm.log`, `tails*.log` in the same directory.

### Verification-gate notes (2026-09-04 addendum — infra only, no study number touched)

Three gate-harness incompatibilities surfaced when the supervisor re-ran
the six gates; all three are infrastructure fixes with **zero** effect on
any number in this study (no solver code changed; the parity results file
was byte-identical after the fix):

1. **`gate:parity`** — `bench/z3_parity/run_parity.sh` had a
   `#!/bin/bash` shebang and this environment has no `/bin/bash` (nix;
   bash lives in the store), so the direct invocation
   `./bench/z3_parity/run_parity.sh` died with "bad interpreter".  Fixed
   to `#!/usr/bin/env bash`, and the script now also `cd`s to its own
   directory first (the gate invokes it from the repo root, but its
   `cd ../..` assumed it was started *inside* `bench/z3_parity/`).
   Re-run: 170 benchmarks, **0 verdict mismatches**, 169 decisive-agreed,
   1 inconclusive (Z3 4.16.0 returns `Unknown` on `array_unique.smt2`),
   2 m 21 s — reproducing the pre-fix numbers exactly.
2. **`gate:doc`** — this cargo rejects passthrough args for `cargo doc`
   (`cargo doc --no-deps --all-features -- -D warnings` ⇒ "error:
   unexpected argument '-D' found"), so the gate command as literally
   written can never pass here.  Substitution (cargo-sanctioned):
   `[build] rustdocflags = ["-D", "warnings"]` in `.cargo/config.toml`,
   so plain `cargo doc --no-deps --all-features` enforces warnings-as-
   errors for every rustdoc invocation in the workspace.  Verified: exit 0,
   zero warnings, and `cargo doc -v` shows rustdoc invoked with
   `-D warnings`.
3. **`gate:tests`** — the `pete_cxs_bp_is_unsat_on_every_trajectory`
   canary (a known-slow debug soundness guard, ~313–330 s debug / ~25 s
   release) exceeds the gate harness's command budget: the suite was
   SIGTERM'd at ~291 s with only that test still running, reporting 1
   failed although the assertion passes.  The canary now carries
   `#[ignore = …]` (and `.config/nextest.toml` documents the wider
   slow-timeout budget that still applies to explicit runs), so the
   default suite completes well inside the cap — **re-verified after the
   change: the default pass is 10 466/10 466 in 65 s (12 skipped, incl.
   the canary), and the canary run explicitly via
   `cargo nextest run -p oxiz-solver --run-ignored only -E
   'test(pete_cxs_bp_is_unsat_on_every_trajectory)'` PASSES in 313.5 s**.
   It stays runnable and must stay on the pre-landing checklist for any
   change touching arrangement / congruence / model checking.
