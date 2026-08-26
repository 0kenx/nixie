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

## Recorded follow-ups

- **Decision quality on dense 3-CNF** (the worker550-class item, with the
  noL diagnosis attached): cadical reaches the model at 232 k conflicts
  where we pass 400 k (3.1 vs 4.7 decisions/conflict).  Both "obvious"
  levers (chronological backtracking, walk phases) are already
  implemented, default-on, and firing on this class — the deficit is
  intrinsic (branching heuristics and learned-clause quality), and needs
  the deep multi-seed study, not a config flip.  This is the biggest
  single lever for the 35-file gap.
- The trajectory trio: revisit whether pre-search BVE+ELS *composition*
  (order/interaction) systematically worsens satcomp2025-style starting
  DBs — single-file evidence only; needs a paired corpus A/B before any
  change.
- Re-run this standing table after any landing that claims SAT-side wins.
