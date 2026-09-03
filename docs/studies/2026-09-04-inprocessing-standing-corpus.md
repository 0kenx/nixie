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
