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

### SOLVED (same day): the fallback direction was inverted — poison cascade

Instrumentation (`OXIZ_SHRINK_TRACE=1`, now a documented diagnostic
surface) on `noL-11-14` at the 232 k cap isolated it:

| signal | value |
|---|---|
| multi-blocks / analyze | 4.66 (avg size 3.8), walks: 1.36 OK / **3.30 FAIL** |
| fallback savings | **0.000** (≈2.9 M calls, none removed) |
| walk-fail reasons | ALL `level < blevel` minimize failures (765 785) |
| fallback depth-0 rejects | **poison 813 636** + no-reason 428 347 + early-abort 337 438 |

**Root cause**: cadical's `shrunken_block_no_uip` iterates the block
**oldest→newest** (reverse iterators over the trail-descending sort),
so a KEPT older literal satisfies newer literals' reason walks
(`MF_KEEP → removable`: the classic in-clause pivot argument).  Our
port iterated `start..=end` — **newest→oldest** — so reasons descended
into *unclassified* older literals, which failed and set `MF_POISON`;
the poison cascaded through the whole block (813 k self-inflicted
rejects) and the fallback saved exactly nothing, on every instance.

**Fix (one line, cadical parity)**: iterate `(start..=end).rev()`.

| metric | before | after | cadical |
|---|---|---|---|
| fallback savings / analyze | 0.000 | **2.403** | 3.96 |
| depth-0 poison rejects | 813 636 | **0** | — |
| total shrink savings / conflict | 2.36 | **~4.8** | ~9.6 |
| `noL-11-14` verdict | TO at 120 s | **sat in 52.7 s** | sat 5.2 s |
| 80-file corpus (30 s, 6-way) | 36 | **37** | — |

The remaining half of the shrink gap is the 3.3-walk-failures/analyze
(cadical's block-UIP walks succeed more often) — recorded as the next
thread.  Gates: suite functionally green (the two wisas-canary SIGTERMs
in one loaded run were external-load artifacts — both pass serially in
~10 s on both pre- and post-fix binaries), differential **162 solved /
0 wrong** (standing level), parity **167/0/1 identical**, clippy/fmt/
doc clean.  Search-core change: SAT and SMT trajectories both perturbed
and re-verified.

### Post-landing note (same day): debug-profile wisas duration unresolved; release verified throughout

During post-landing re-verification under heavy external machine load
(another agent's builds; load spikes to 68–73, plus a mid-verification
`cargo clean` that deleted `target/`), debug-profile `wisas_xs_8_13`
test runs exceeded every timebox (148 s→fail, 447 s→fail, 800 s/1500 s
timeouts) while the RELEASE binary solves the identical fixture in
13 s (`unsat`, both pre- and post-fix binaries, serial, quiet machine).
No panic, no OOM line, no verdict change was ever captured — only
timeouts under contention.  The full workspace suite passed at
`9749a7d` twice BEFORE the load spikes; oxiz-sat 870/870 and the
pete/arrangement subset 8/8 re-verified under timebox today.

**Open item (owner: next quiet-machine session)**: measure debug-wisas
serially on a quiet box at `e1d77bc` (pre-fix) vs `9749a7d` (post-fix).
If post ≫ pre in debug too, the fallback fix shifted the wisas
TRAJECTORY onto a much longer debug path (release unaffected — but
explain the profile divergence, e.g. a debug-only assertion cost or a
`debug_assert`-guarded branch); if comparable, today's failures were
pure environment.  Do not treat today's timeouts as a regression
signal (the repo's own rule), and do not re-run suites while load > 10.

### REVERTED again (same day): the direction fix explodes the wisas canary by 50×+ CPU — and the landing's verification was corrupted

The full controlled matrix (20-core box; pre/post binaries of verified
provenance; load held roughly constant across cells):

| | release | debug test |
|---|---|---|
| pre-fix (`2d55fc7`) | 10–14 s `unsat` (load 83) | **17 s pass** (load 134) |
| post-fix (`9749a7d`) | **>120 s ×5** (load 83) | **>900 s** |

CPU-truth run: post-fix burned **515 s user CPU without finishing**
vs pre-fix ~11 s — a 50×+ CPU regression, both profiles.  wisas is this
codebase's designated trajectory-fragile instance (the trie-vivify
lesson): the fallback's changed learned clauses (soundly justified —
each removal individually entailed) shift the SMT trajectory onto a
catastrophically longer path.

**The landing's "canaries pass in ~10 s" was wrong**: those runs used
`target/release/oxiz` from the SHARED target dir during another
agent's builds — a "32 s incremental" build after a full `cargo clean`
is impossible, so the binary measured was not the fixed one.  Lesson
recorded: after any `cargo clean` on this shared tree, binary
provenance requires a full-duration build (or the precompile copy)
before a canary can certify anything.

**Disposition**: the one-line direction change is REVERTED (newest-first
restored, equally sound, saves less); the instrumentation, the root-
cause analysis, and the measured component win (+2.4 fallback
lits/analyze, poison rejects 813 k → 0, noL TO → sat, satcomp 128→133)
all stand in this study.  Relanding requires either understanding
wisas's fragility or a policy that keeps the canary affordable — e.g.
bounding the fallback per block and matching cadical's exact iteration
semantics *including* its walk-failure rates (our walks fail 3.3/a vs
cadical succeeding more, which changes which literals the fallback ever
sees).

Post-revert verification (timeboxed, fresh-provenance builds): wisas
release `unsat` 7 s; debug canary subset (wisas+pete+pr30+cegar)
28/28; oxiz-sat 870/870; clippy/fmt clean.  **Differential at the
revert commit: 162 solved / 0 wrong; parity 167/0/1** — the revert is
itself a SAT-core change and shipped with the fresh differential the
corollary requires (both trajectory families verdict-clean either
way; the revert is about the canary, not soundness).

Direction parity has since been re-confirmed from cadical source at
BOTH levels (across blocks: `shrink_and_minimize_clause` iterates
`rbegin_block` from the trail-descending sort's tail = oldest block
first; within the fallback: `shrunken_block_no_uip`'s forward reverse
iterators = oldest literal first) — the inverted direction was a real
port bug, the fix is genuinely cadical-parity, and the wisas
explosion is a trajectory interaction with our (differently-shaped)
walk-failure distribution, not an implementation error.  Relanding
therefore means closing the 3.3-walk-failures/analyze gap first
(cadical resolves those blocks to UIPs where we fall back), so that
the fallback rarely fires — or understanding wisas's fragility
directly.

### Correction (same day, instrumented cadical): that premise was WRONG — cadical's walks fail MORE

An instrumented cadical build (counters patched into `shrink.cpp` in a
`/tmp` copy, never touching the reference tree) produced the missing
comparison cell on the same file:

| per analyze | oxiz (232 k cap) | cadical (solve run, 225 k) |
|---|---|---|
| learned lits at shrink entry | 34.7 | **43.9** |
| multi-blocks (avg size) | 4.66 (3.8) | **7.51** (3.6) |
| walk UIP success | 1.36 (29 % of blocks) | 3.29 (**44 %**) |
| walk fail → fallback fires | 3.30 | **4.21** |
| fallback literals saved | ~0 (reverted) / 2.40 (fixed) | 3.96 |
| total literals removed / conflict | 2.36 | 9.4 |

Two corrections to the record:

1. **cadical's walks fail MORE than ours** (4.21 vs 3.30 per analyze).
   The premise above — "cadical resolves those blocks to UIPs where we
   fall back" — was inferred from aggregate removal counts and was
   wrong.  cadical's 4× total savings decompose as: **longer learned
   clauses** (43.9 vs 34.7 literals at shrink entry — a whole-search
   property: deeper trails, different reduction policy) yielding
   **61 % more multi-blocks**, each with a somewhat higher UIP success
   rate (44 % vs 29 %).  The fallback is not vestigial in cadical — it
   fires constantly and saves heavily.
2. **The direction-fixed port is cadical-shaped**: with the fix, our
   fallback fired 3.28/analyze saving 2.4, vs cadical's 4.21/3.96 —
   the same operating profile.  The wisas explosion is therefore even
   more clearly a canary-specific trajectory accident, not a semantic
   divergence.  The corrected reland path: understand wisas, or attack
   the upstream clause-length gap (trail depth; the unexamined 96 % vs
   76 % reduction-deletion anomaly) — which is where cadical's
   advantage actually originates.

## Recorded follow-ups

- **Decision quality on dense 3-CNF** (the worker550-class item, with the
  noL diagnosis attached): cadical reaches the model at 232 k conflicts
  where we pass 400 k (3.1 vs 4.7 decisions/conflict).  Both "obvious"
  levers (chronological backtracking, walk phases) are already
  implemented, default-on, and firing on this class — the deficit is
  intrinsic (branching heuristics and learned-clause quality), and needs
  the deep multi-seed study, not a config flip.  This is the biggest
  single lever for the 35-file gap.
- **Shrink/minimize savings gap** — the fallback half SOLVED (see above:
  inverted direction, poison cascade; fixed to cadical's oldest-first).
  The remaining half is walk failures: 3.3/analyze vs cadical's higher
  success rate on block-UIP walks.  Reduction policy (96 % vs 76 %
  deletion) still unexamined.
- The trajectory trio: revisit whether pre-search BVE+ELS *composition*
  (order/interaction) systematically worsens satcomp2025-style starting
  DBs — single-file evidence only; needs a paired corpus A/B before any
  change.
- Re-run this standing table after any landing that claims SAT-side wins.

### Reduction used-shield (cadical `reduce.cpp` parity): sound, corpus-NEGATIVE, shipped default-off

The reduction-anomaly follow-up: cadical's `reduce` protects
recently-used glue clauses from deletion entirely (`glue <= tier1limit
&& used`, `glue <= tier2limit && used >= max_used-1` keep-tests before
any sort), with `used` decaying one per round; our tier-percentage
deletion (10/30/75 % by tier, activity sort) has no such shield — the
mechanism behind the 96 %-vs-76 % deletion anomaly, hypothesized
upstream cause of the clause-length gap (43.9 vs 34.7 lits at shrink).

Ported as `OXIZ_REDUCE_USED_SHIELD` (shield any clause with usage > 0;
decay-by-halving per round).  Results:

| | shield ON | OFF |
|---|---|---|
| noL-11-14 | sat 59 s | **sat 49 s** |
| 60-file satcomp sample (25 s, 6-way) | 23 | **25** |
| verdict mismatches | — | **0** |

Corpus-negative under OUR tier system — coherent with the design
difference: our tier *promotions* (Local→Mid at 3 uses, Mid→Core at
10/lbd≤2) already reward use, so the shield over-retains under the
tier-percentage policy; cadical needs it because its glue-limit
keep-tests carry no use-rewarding promotion ladder.  **Shipped
default-OFF** (`OXIZ_REDUCE_USED_SHIELD=1` for A/B); the parity port,
the `usage_of`/`decay_usage`/`set_usage` infrastructure, and this
negative result are kept for the reduction-policy deep study.

Canaries at default (shield inert): wisas `unsat` ~10 s, cxs-bp
`unsat`; differential 161/0 both arms (one file of load noise vs the
standing 162 — the paired inert run and the landed-default run agree
with each other); parity 167/0/1; oxiz-sat 870/870; clippy/fmt clean.


## THE GAP MOVER (2026-08-21): random polarity OFF in stable mode — +16 standing files, 129→145 of 261

### The phase-oracle experiment that isolated the root cause

Fresh standing table at `06a86af` (same-day, same box): oxiz **129** vs
cadical **162**, 0 mismatches, 37 one-sided losses — confirming the landed
slices had not moved the headline and re-prioritizing to the loss residue.

`worker_550` diagnosis (93 k vars, 10.3 M clauses, SAT; cadical 12 s at
**5 113 conflicts**, 58 dec/conf, chrono 31 %, **zero random decisions** —
`rand. dec phase: 0.00`; no walk, no flipping): we burn 200 k+ conflicts
without finding the model.  A phase-oracle instrument was added
(`Solver::set_phase_hint`, `PHASE_HINT=` in the stats harness): seed the
saved/target/best phase arrays with cadical's actual model.

| arm | result |
|---|---|
| hint + RANDPOL=0.02 (default randomness) | 100 k conflicts, **no model** |
| hint + RANDPOL=0 + REPHASE=0 | **sat with 0 conflicts** (28 987 decisions, pure descent) |
| no hint, RANDPOL=0 | sat in 60 s (default TOs) |

The machinery is sound — model-guided decisions would walk straight to
the model.  The **2 % random-polarity perturbation (an OxiZ extension;
cadical's `randec` defaults to 0) single-handedly destroys phase-guided
descent on model-finding instances**, and rephase-every-1000 wipes
whatever phase progress accumulates (tested separately: not the breaker;
randomness is).

### Why stable-mode gating is the right cut

Phase guidance (target phases) is cadical's *stable-mode* mechanism; our
loss-class files spend 73 %+ of conflicts in stable mode.  Full-off
(`RANDPOL=0` everywhere) measured corpus **1.082× ticks** (bimodal: wins
noL 0.52×/Ptn 0.04×, loses x9-06068 35×) — the 2 % is load-bearing
diversification in focused mode.  Stable-only gate
(`random_polarity_prob_stable: Some(0.0)`):

| measurement | value |
|---|---|
| 120-file corpus, both-solved ticks | **1.017×** (neutral band) |
| corpus solved | 51 vs 49 (6 gained / 4 lost, bimodal tail both ways) |
| verdict disagreements | **0** (both A/Bs) |
| **37 standing losses re-run** | **17 solved** (noL ×2, circuit_64i ×2, x9-09054 ×2, x9-08075 ×2, frb45 ×2, summle ×2, j3037, jgiraldezlevy, crusti_g2io, WS_500) |
| fresh standing table | **oxiz 145 / cadical 162**, 0 mismatches (was 129/162 same-day; 128/159 at `cc78521`) |

Landed as the preset default (`Some(0.0)` on all presets except the
intentionally-random `Random`/`Aggressive`, which keep `None`);
`RANDPOL` / `RANDPOL_STABLE` env knobs remain for A/B.  Gates: workspace
10 102 green, clippy/fmt/doc clean, differential **162/0** (par2 2 261,
best yet), parity 167/0/1, canaries hold (wisas `unsat` 7 s, cxs-bp
`unsat`, sorted `sat`).

Residual gap after this landing: 17 files (was 33) — the taxonomy's
"hard trio" remainder (noL now solved; fsf/x9-08075-class remain), the
long tail, and the 4 corpus files the gate loses at fixed caps
(rbsat/x9-10070/Ptn-7824/6s268r — watch in the next standing run).


### Shrink-fallback `.rev()` reland retest (2026-08-21, post-`00e83be`): canary moved, corpus still says NO — second rejection, now on corpus grounds

The reverted direction fix (cadical parity: fallback minimization
oldest-first; `4c212a8` reverted it when it exploded wisas 50×) was
retested against the new default, whose phase landing shifted every
trajectory.  Worktree build, functional provenance via
`OXIZ_SHRINK_TRACE` (fallback_saved **2.35/analyze** — the fix's
signature, matching the original +2.4):

| gate | result |
|---|---|
| wisas canary (the old blocker) | **holds** — `unsat` 10 s vs HEAD 12 s |
| cxs-bp / sorted / 6s167-opt | all hold |
| oxiz-sat suite | 870/870 |
| 60-file corpus screen (45 s, seed 71) | **fixed 23 vs HEAD 26**, ticks geomean **1.126×**, 0 verdict mismatches |
| flips | 0 gained; **lost mp1-klieber, af-synt, and noL** — the very file the phase landing had just won |

The pre-landing rejection (wisas 50×) and this one (corpus-negative,
different files) are the same phenomenon twice: the fallback's mechanical
saving is real but every perturbation of learned-clause shape reshuffles
the trajectory by more than the saving.  **The fix stays unlanded —
permanently, unless the clause-length gap itself is closed first** (the
upstream cause per the instrumented-cadical correction above); at that
point the fallback landscape changes and a third retest would be
justified.  The worktree was discarded after the measurement.
