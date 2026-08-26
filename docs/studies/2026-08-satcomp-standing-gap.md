# SATCOMP standing gap vs CaDiCaL after the 2026-08 landings (2026-08-25)

## Standing table (261 files: satcomp2024 bench ×2 encodings + satcomp2025 main_easy_mid)

| | oxiz (CaDiCaL preset, `cc78521`) | cadical (reference build) |
|---|---|---|
| solved (60 s, 6-way) | **128** | **159** |
| verdict mismatches | — | **0** (522 runs) |

Soundness is clean across every run; the entire gap is solving power.

## Gap taxonomy (35 one-sided losses)

1. **Trajectory-sensitive trio** (cheap, knob-level): `battleship-16-31`
   (cadical 1.1 s), `intel047`, `mp1-Nb7T45` — each is solved by disabling
   exactly one pre-search pass (BVE=0 or EQUIV=0) or enabling inprocessing;
   the BVE+ELS-processed starting DB sends the search wandering.  Not a
   family property: single files, opposite fixes.
2. **Genuinely-hard trio** (all knobs TO): `fsf-300-354` (3.2 s),
   `noL-11-14` (5.2 s), `x9-09054` (6.3 s).
3. **Known follow-up family**: `worker_550` ×2, `circuit_64i` ×2 (the
   studies' named decision-quality/amplitude items).
4. Long tail: 30–55 s cadical solves (pb/frb/Timetable/af-synthesis …) —
   uniform slowness, no single lever.

## noL-11-14 diagnosis (the hard-trio representative)

1419 vars, 7821 ternary clauses + 14 units, SAT.  cadical: 5.2 s (exit 10).
oxiz: TO under default, `PRESET=default`, `STABLE=1`, `INPROCESS=1`,
`REPHASE=0` — every knob.  Capped run: 200 k conflicts in 4.6 s
(43.6 k conflicts/s — throughput is NOT the problem) at **9.5 decisions
per conflict** (healthy CDCL runs 1–3): the learned clauses do not drive
propagation to contradiction, and a SAT instance survives 1 M decisions
without a model — a *branching/phase-quality* deficit on dense
combinatorial 3-CNF, not a data-structure one.  Profile (symbols build):
propagate 30 %, conflict analysis ~30 % (`shrink_and_minimize` 15 % +
`analyze_mark` 5 % + `minimize_literal_plain` 5 %), elim+subsume ~21 %.

### cadical's own numbers on the same file (correction of the first read)

| metric | oxiz | cadical |
|---|---|---|
| conflicts | 200 k cap hit (TO at 60 s ≈ 2.6 M) | **232 k** (solves) |
| conflicts/s | 43.6 k | 53.1 k |
| decisions | 1.05 M at the cap | 716 k |
| decisions/conflict | **9.5** | **3.1** |
| chronological backtracks | (feature off) | **26 % of conflicts** |
| phase machinery | rephase only | walked 6, weakened 7484, rephased 21 |

So cadical does NOT need fewer conflicts — it survives to 232 k and
**finds the model** there, while our search passes 2.6 M without one.
Conflict throughput is comparable (0.82×); the deficits are (a) 3× more
decisions per conflict and (b) phase guidance to satisfying assignments
(cadical's walking/weakening/chronological mix).  Our chronological
backtracking exists but is default-off (measured neutral-negative
elsewhere); re-evaluating it *on this class* is a cheap first trial for
the follow-up.

### Erratum (same day): the CHRONO trial was a cap artifact; the hard trio is a 10× speed gap, not unsolvable

The "cheap first trial" above was run and **falsified cleanly**: the
CaDiCaL preset *already* sets `enable_chronological_backtrack: true`
(as does `SolverConfig::default()`) — cadical's 26 % chronological
behaviour is already matched, and the `CHRONO=1` "solves" of `noL-11-14`
(55.4 s) and `rbsat-v760c` (50.6 s) reproduced identically **with no env
at all**: they were the 60 s cap of the screen vs the 40 s cap of the
earlier spot-check, not a chrono effect.  (The knob conflated
chronological backtracking with the separately-gated `chrono_reuse`
trail-saving, which is the measured neutral-negative feature.)

Corrected facts:

- **`noL-11-14` and `rbsat-v760c` solve serially in ~51–56 s under the
  default config.**  The standing table's 60 s 6-way-parallel cap turns
  these into TOs by load margin — the table systematically
  under-counts borderline files by roughly one load factor.
- The hard-trio deficit is therefore a **~10× speed gap** (55 s vs
  cadical's 5.2 s), not a solve/no-solve boundary.
- The remaining named difference vs cadical on this class is the
  **phase machinery**: cadical ran walked 6 / weakened 7484 / rephased
  21 (walk-based target phases toward satisfying assignments).  That,
  not chronological backtracking, is the open lever for the
  decisions-per-conflict deficit (9.5 vs 3.1).
- `cnf_solve` gains an explicit `CHRONO=0|1` override so future A/Bs
  can test the *off* arm without rebuilds (it was previously only
  settable via preset internals).

### Second erratum (same day): the "walk-based target phases" lever is also already implemented and firing

Measured on `noL-11-14` (400 k conflict cap, default config): the walk
port (`solver/walk.rs`, default-on, in the rephase rotation) fired
**8 walks / 49 113 flips** — cadical ran 6 walks; the counts are
comparable — but **plateaued at 74 broken clauses**, never reaching a
satisfying assignment.  (`weakened 7484` was a misread: it is
extension-stack accounting for cadical's 390 BVE eliminations, not a
walk mechanism.)  dec/conf at the 400 k cap measures **4.7** (the 9.5
figure was the 200 k cap; the ratio is front-loaded in the search).

**Net**: two consecutive "obvious levers" (chronological backtracking,
walk-based phases) were both already present and firing.  No missing
feature remains.  The hard-trio gap is intrinsic CDCL decision quality —
cadical reaches the model at **232 k conflicts** where we pass **400 k**
(18 s) without one, at 3.1 vs 4.7 decisions/conflict.  Closing that is
the worker550-class deep study (multi-seed, matched nulls, branching and
learned-clause quality), not a config flip.

### Third screening: the VSIDS arm — dec/conf fixed, corpus negative

The schedule-level comparison had come out nearly identical to cadical
(stable share 51 % vs 58 %, rephases 21 vs 21, walks 6 vs 6, restarts
comparable), isolating the deficit to *decision content*.  Switching the
preset's VMTF to VSIDS-in-both-modes (`VSIDS=1`, new knob) on `noL-11-14`:

| arm | dec/conf (250 k) | model found |
|---|---|---|
| VMTF (default) | 5.1 | no (even at 600 k / 120 s) |
| VSIDS | **3.1** (= cadical) | **no** (even at 600 k / 120 s) |

dec/conf is *fixed* to exactly cadical's figure — and the model still is
not found: decision density was a symptom, not the cause.  Corpus screen
(80 files, 30 s, 6-way): **VSIDS 33 vs VMTF 36 solved** (gained 4, lost
7, 0 mismatches) — corpus-negative; do not flip.  Three cheap levers are
now falsified (chronological backtracking = cap artifact; walk phases =
already firing; VSIDS arm = fixes the metric, loses the corpus).  The
deep study remains: learned-clause quality (glue distribution, reduction
policy, otfs at 215-vs-ours unknown) and the branching *signal* itself,
multi-seed with matched nulls per `docs/BENCHMARKING.md`.

### Fourth screening: learned-clause quality counters — the first REAL mechanism gap (quantified)

Counters at cadical's solve point on `noL-11-14` (232 k conflicts,
default config both sides):

| metric | oxiz | cadical |
|---|---|---|
| learned / conflict | 100 % | 97.1 % |
| **literals removed / conflict (shrink+minimize)** | **2.36** | **~9.6** (shrunken 5.68 + minishrunken 3.96) |
| `minishrunken` (in-block per-literal fallback) | **1** | **893 234** |
| deleted (reduction) / conflict | 96.2 % | 76.3 % |
| chronological backtracks | **0 %** | **26 %** |
| avg LBD | 21.6 | — |

Two anomalies, both verified against cadical source:

1. **Recursive minimization saves ~nothing** (`minishrunken = 1`).
   `improve_learnt_clause` runs the block-shrink path only (classic
   `minimize_learnt_clause` runs only under LRAT/shrink-off), and the
   in-block fallback (`shrunken_block_no_uip`) — implemented, guards
   cadical-faithful incl. the Knuth `seen.count < 2` gate at depth 0 —
   removes essentially zero literals.  cadical removes 3.96/conflict
   through the same fallback.  Net: our learned clauses carry ~7 extra
   literals each, directly explaining fat clauses / worse propagation /
   higher dec-per-conflict.  Hypotheses to test next: block-size
   distribution (blocks of 1 are skipped entirely — `i-j+1 < 2` keeps
   them), failure frequency of the walk (the fallback only runs on
   *failed* walks), and whether `seen_level_count` is populated on the
   shrink path (the plain minimizer's Knuth gate reads it; if the block
   walk does not maintain it, depth-0 calls always reject).
2. **Chronological backtracking fires 0 %** (counters
   `chrono_backtracks=0`) despite `enable_chronological_backtrack:
   true` — semantics verified identical to cadical
   (`level − jump > chronolevelim(=100)` → chrono).  Since our restart
   interval matches cadical's (~22), the anomaly is that our trails
   apparently never span >100 levels — consistent with the reduction
   policy deleting 96 % as many clauses as conflicts (cadical 76 %):
   an over-aggressive reduction keeps fewer long clauses, shallowens
   the search, and starves both deep levels and the shrink fallback.

**This is the deep study's first positive finding**: a quantified,
mechanism-level gap (2.36 vs 9.6 literals removed per learned clause)
with two concrete candidate causes.  Next steps: instrument
`shrink_block` (block count/size, walk success/fail, fallback savings)
and `seen_level_count` maintenance on the shrink path; compare
reduction-policy targets against cadical's `reduced 76 %`.

## Recorded follow-ups

- **Decision quality on dense 3-CNF** (the worker550-class item, with the
  noL diagnosis attached): cadical reaches the model at 232 k conflicts
  where we pass 400 k (3.1 vs 4.7 decisions/conflict).  Both "obvious"
  levers (chronological backtracking, walk phases) are already
  implemented, default-on, and firing on this class — the deficit is
  intrinsic (branching heuristics and learned-clause quality), and needs
  the deep multi-seed study, not a config flip.  This is the biggest
  single lever for the 35-file gap.
- **Shrink/minimize savings gap** (fourth screening, quantified above):
  2.36 vs ~9.6 literals removed per learned clause; `minishrunken=1` vs
  893 k.  Instrument block sizes, walk failures, `seen_level_count`
  maintenance; then compare the reduction policy (96 % vs cadical's
  76 % deletion rate) — the two anomalies may be one causal chain.
- The trajectory trio: revisit whether pre-search BVE+ELS *composition*
  (order/interaction) systematically worsens satcomp2025-style starting
  DBs — single-file evidence only; needs a paired corpus A/B before any
  change.
- Re-run this standing table after any landing that claims SAT-side wins.
