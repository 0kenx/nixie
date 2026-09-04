# CaDiCaL `elim.cpp` port: sound, big per-family wins, net-negative as a default (2026-08-17)

> **Update 2026-08-21: the default flipped ON.** See the final section —
> BVE+ELS are now enabled in the `CaDiCaL` preset (reference parity).

## Motivation

`bench`-suite differential vs CaDiCaL (`/tmp` run, 94 files: 40× SATLIB `uf100`,
54× satcomp2024) showed Nixie's SAT core >1.5× slower than CaDiCaL on 22/94
files, with the worst gaps (66×, 29×, 25×, 18×) all on instances CaDiCaL
collapses via inprocessing — its log shows clause counts dropping 13.5k → 2.3k
through interleaved `e` (elim) / `s` (subsume) / `d` (distill) rounds before
1.2k conflicts refute the residue. Nixie ran *no* elimination by default: the
one-shot `bve.rs` pass was off in every preset, gated behind a documented
soundness hazard.

## What was done

Full port of CaDiCaL's bounded variable elimination to
`nixie-sat/src/solver/eliminate.rs` (~1.1k lines): occurrence-list driven,
score-ordered work-list schedule with re-entry on clause removal/shrink,
on-the-fly self-subsumption, backward subsumption of fresh resolvents,
eager unit propagation through the occurrence lists, growing elimination
bound (0→1→2→…→16), pre-search fixpoint + mid-search re-arm schedule
(`eliminating()`), model reconstruction through the existing `bve_def` /
`bve_order` extension stack. The old one-shot `bve.rs` pass was removed.

## Soundness bugs found and fixed while porting (all with reproducers)

1. **Resolvent built from one side only** — `elim_resolve_clauses` marked the
   c-side literals but only pushed the d-side into the resolvent; the
   "resolvents" were over-strong clauses → false UNSAT (fuzz seed 0x60fcfe…,
   13 vars). Fixed: build from both sides.
2. **Stale occurrence-list entries after in-place shrink** — a clause shrunk
   by dropping literal `l` kept its `occs[l]` entry; a later unit assignment
   then retired it as "satisfied by `l`", deleting a live constraint → false
   SAT (it143: entailed `(9∨¬10)` deleted after `(9∨¬10∨5)` shrank). Fixed:
   physically remove the clause from the dropped literal's occurrence list
   (cadical `remove_occs`).
3. **Learned clauses over eliminated variables left live** — cadical's
   `mark_redundant_clauses_with_eliminated_variables_as_garbage` pass was
   initially dropped from the port. A live learned clause over an eliminated
   variable is entailed by the formula, so an honest model must satisfy it,
   but reconstruction assigns that variable from `bve_def` (original clauses
   only) and can falsify it → false SAT (`crn_11_99_u`: learned `(57∨1101)`
   survived v57's elimination). Fixed: retire learned clauses with eliminated
   variables at the end of each round.
4. **Original clauses subsumed by learned clauses without promotion** —
   `subsume_round` deleted an original on the word of a *learned* subsumer,
   which can die later (reduction), leaving the deleted original's obligation
   uncovered → false SAT. Fixed with cadical `subsume_clause`'s rule: promote
   the learned subsumer to original (`learned = false`), and make
   `reduce_clause_database` skip promoted clauses.
5. **Binary-implication-graph edges outliving their clauses** — the subsume
   binary fast-path matched dead edges → false subsumption. Fixed: liveness
   check on the edge's clause id.

Two **pre-existing** bugs surfaced by the work (reproduce on baseline HEAD):

6. `pick_branch_var`'s fallback scan decided *eliminated* variables when the
   heaps drained → trail values that block ELS model reconstruction → wrong
   model on reintroduction (`a≡b` then `add_clause(b∨c)`). Fixed: the
   fallback now skips `var_eliminated` variables like the primary heuristics.
7. The pre-search fixpoint loop could spin forever when elimination is
   refused (LRAT attached / theory attached): `eliminate_phase` returns
   without advancing the phase counter. Fixed: the loop gate checks
   `elimination_allowed()`.

Differential fuzz harness (4 config variants × verdict cross-check + model
verification): ~40k iterations clean after the fixes, plus the two real-world
reproducers above.

## Performance verdict (94-file suite, CPU-time, 25s cap, vs CaDiCaL 4.x)

| config                       | >1.5× vs cadical | total Nixie time |
|------------------------------|------------------|-----------------|
| baseline (HEAD)              | 22/94            | 738 s           |
| elimination, full schedule   | 53/94            | 807 s           |
| elimination, pre-search only | 57/94            | 822 s           |
| new code, elimination off    | 23/94            | 750 s (noise)   |

Per-family the port is dramatic where elimination is the right tool:
`6s167-opt` 22s → 7.6s (cadical 0.3s), `crn_11_99_u` 3.9s → 1.3s,
`noL-11-14`… but it regresses previously-fine families (`barman-pfile06`
1.1× → 38×, `constraints_17` 6.2× → 24×, `si2-b03m` 1.6× → 12×): our search
lacks the companion techniques that make elimination pay off in CaDiCaL
(interleaved probing, vivification of originals, transitive reduction,
distillation). Enabling elimination perturbs CDCL trajectories without those
amortizers, and the phase cost itself (occurrence-list rescans) is not yet at
CaDiCaL's efficiency (0.77s pre-search on 6s167 vs ~0.03s for CaDiCaL).

**Decision: `enable_bve` stays `false` in every default.** The port ships as
an opt-in (`SolverConfig { enable_bve: true, .. }`) — sound, tested, and the
right tool for elimination-friendly instances. Re-evaluate after interleaved
vivification and probing land; those are the known missing amortizers.

## What not to retry

- Turning `enable_bve` on by default *without* first landing mid-search
  vivification + probing: measured net-negative twice (full schedule and
  pre-search-only).
- Scheduling the pre-search fixpoint unbounded: phases 2+ eliminate ~50 vars
  each for a full database rescan (19 phases = 1.5s on 6s167); the
  productivity gate + 4-phase cap is the shape that works.

## Follow-up (same day): inprocessing soundness + BCP throughput

### Sixth soundness bug: `forward_subsumption` watch-position corruption

Enabling the (pre-existing) inprocessing pipeline reproduced a false UNSAT
instantly on `noL-11-14` (SAT per CaDiCaL): `forward_subsumption`'s normalize
prologue sorts every clause's literals in place, but the pass only rebuilt
the watch lists when it actually subsumed something (`removed > 0`).
`propagate` requires the two watched literals at stored positions `[0]/[1]`
(the same invariant class as the `learn_clause` bug fixed in `b0f2db8`), so
a normalize-only reorder left every watcher pointing at stale positions; BCP
then propagated never-implied literals and the search concluded UNSAT in 6
conflicts. Notably the corrupted pass had been *luckily* "solving"
`mrpp_4x4#12_12` (0.02s, verdict matched) — a reminder that speedups from a
corrupting pass are worthless. Fix: unconditional watch rebuild after the
pass. Regression: `tests/fs_watch_position_soundness.rs` (noL under a
conflict budget must not answer UNSAT).

This also explains the historical "BVE + forward-subsumption reproduces
noL-11-14 false UNSAT" comment in `SolverConfig`: same defect, misattributed
to the BVE interaction.

### BCP throughput work (deterministic, no policy change)

Measured on `stable-300` (300 vars / 17.5k clauses), 100k conflicts fixed:
ours 49.4G instructions vs CaDiCaL 20.3G (2.5x), 3.74M vs 2.91M
propagations, 570k vs 128k decisions. Per watch visit: ~125 inst vs ~66.
Visits per propagation: ~105 (blocker hit rate 55%).

Landed: eager watcher detach on clause-database reduction (cadical
`detach_clause`; deleted clauses no longer sit in the hot lists until their
literals fire), removal of a full `Clause::clone` per deleted clause in
`ClauseDatabase::remove`'s stats path, and direct indexing in
`Trail::lit_val` (the `.get()`+match bounds-check dance on the hottest
lookup). ~5% on dense random instances.

### Suite effect (94-file CaDiCaL differential, 25s cap, default config)

22/94 → **18/94** above 1.5x; total 738-750s → **653s**; 0 disagreements.

### Where the remaining gap lives (next study)

The residual ~2.9x time gap on the timeout files decomposes into ~1.4x
instructions per watch visit (SmallVec discriminant + `self→trail→values`
pointer depth; `#![deny(unsafe_code)]` rules out the raw-pointer fix), ~1.3x
more propagations, and ~4.5x more decisions per conflict — the last is
search policy (restart/reuse/branching interplay), which per
`docs/BENCHMARKING.md` requires the matched-null, ≥10-seed methodology
before any conclusion. That is the next lever for `stable-300`, `qwh`,
`frb65`, `summle_*`, `noL-*`.

### Trail-reuse heap mismatch (fix, perf-neutral)

`reuse_trail()` gated the restart-reused prefix on **VSIDS** activities, but
the default focused mode branches via **VMTF** (the function's comment
predates VMTF-focused becoming the default). The mismatched threshold almost
never matched the actual branching order, so reuse collapsed to ~0 and every
restart re-descended from the root. Fixed by mirroring `pick_branch_var`'s
mode-dependent choice and, for the VMTF branch, comparing bump timestamps
(cadical `restart.cpp` `reuse_trail`, queue branch). Effect on `stable-300`:
restarts at 100k fixed conflicts 19 205 → 3 409 (cadical-parity rate).

**Measured effect: neutral.** The single-seed 94-file suite showed 653s →
699s ("worse") with 17 files improving and 14 regressing >2s — textbook
trajectory reshuffling. A seed study over the 31 moved files (8 seeds per
arm, CPU-time, 30s cap) gave 11 wins / 10 losses and mean-sum 706.0s vs
712.7s (0.9%, inside noise). The fix ships on faithfulness grounds, not on a
speed claim. The decisions-per-conflict gap vs CaDiCaL (5.7 vs 1.27 on
`stable-300`) persists and tracks propagation-cascade depth per decision
(6.5 vs 23) — a search-quality question for the policy study, not a
mechanical bug.

## Arena follow-up: f32 header + the latent stride-desync bug it exposed

### The bug (gdb hardware watchpoint, exact write caught)

`ClauseArena::scale_live_activities` walked the arena recomputing each slot's
stride as `slot_size(current_len)` — but a clause's physical slot size is
fixed at allocation while `shrink` later lowers `len`. After a 4→3-literal
shrink the walk's stride (32→24) diverged from the real layout, landed
mid-slot, and collected a bogus offset as "live". The rescale then did an
f32 read-modify-write 8 bytes past that offset: it read a real clause's
`len` field (raw `4`) as the denormal `5.6e-45`, multiplied by `1e-20`, and
the underflow-to-zero result was stored — `len` became bit-pattern zero.
Propagation later indexed the empty clause; `crn_11_99_u` answered `sat`.

**Latent since the arena commit, not introduced by f32.** The same walk
existed under the f64 header; it was unreachable at verification scale
because the rescale trigger sat at `increment > 1e100` (≈230k conflicts),
above every corpus cap, and `iter_ids` (the only other would-be walker) uses
the refs table. Lowering the bound to MiniSat's `1e20` — mandatory for f32,
whose range ends at 3.4e38 — moved the first rescale to ≈46k conflicts and
exposed it inside the regression suite. Lesson recorded: the trajectory-
identity corpus (≤30k caps) and the 25s-capped suite could not see a bug
whose only trigger fires at 46k+ conflicts; soundness gates need at least
one corpus that crosses every periodic policy trigger.

Fix: refs-driven activity scaling (the refs table is the authoritative slot
list, exact under shrink by construction); stride-walking deleted.

### f32 activity + 12-byte header

Activity is only the reduce sort key; `1e20`/`1e-20` rescale keeps stored
values ≈1e23, inside f32 range (the old 1e100 policy would saturate f32 to
`inf` and collapse the ordering — the bound change was forced, not tuned).
Pinned: 3-lit slot 24B → two ternaries per cache line (48B); 5-lit slot
exactly 32B (half a line; 4 was the f64 ceiling). Perf at 300k fixed
conflicts on stable-300: neutral (18.6s → 18.6s interleaved ×3). f32
rounding intentionally retires bit-identical trajectories as a regression
net for future clause-DB changes; verdicts + fuzz + parity carry it.

## Minor-gap sweep + blocker refresh (cadical parity in propagate)

Three changes:

1. **Portfolio wiring closed**: `Context::set_solver_config` now propagates
   `restart_strategy` / `enable_inprocessing` / `inprocessing_interval` into
   the live SAT engine (`nixie_sat::Solver::update_search_config`); those
   fields are read live by the restart/inprocessing schedules, so portfolio
   workers' strategy triplets now genuinely diversify search. Construction-
   seeded state (chrono thresholds, stabilize schedule, eliminator limits)
   deliberately remains construction-only. Regression test in
   `nixie-solver/src/solver/tests.rs`.

2. **Eliminator occurrence pass merged**: `elim_round`'s two full-database
   scans (satisfied-check, then connect) are one; retiring and connecting
   act on disjoint clauses within an iteration. The residual eliminator
   cost is per-round scratch allocation (cross-round `Eliminator`
   persistence is the known follow-up).

3. **Satisfied-replacement blocker refresh** (cadical `propagate.cpp`'s
   `if (v > 0) j[-1].blit = r`): when the replacement scan finds a
   *satisfied* literal, the watcher now stays on the current list with its
   blocker refreshed — no clause write, no watch-list move; only an
   *unassigned* replacement moves the watch. Our previous `>= 0` branch
   moved in both cases. Gent's saved-position scan (`clause->pos`) was
   deliberately NOT ported: it needs a header field that would grow the
   12-byte header to 16 and break the pinned 5-literal half-line property.

### Measurement discipline (two traps, both hit)

- Fixed-conflict instruction counts are **invalid** for trajectory-diverging
  changes: the blocker change measured +53% at 100k fixed conflicts on
  stable-300 purely because the new trajectory does more propagation per
  conflict on those particular conflicts. Wall-clock was equally void —
  the machine spent much of this window at load 8-18 from another agent's
  job (and two day-old orphaned test processes had to be killed).
- Valid metric: **instructions-to-verdict**, deterministic, paired per file,
  both binaries fully solving. Result over 64 files (both-solve, <45s):
  geomean 0.9889 (-1.1%), 26 wins / 38 losses — small losses, large wins
  (mrpp -50%, ddc/6s167 -15%). Verdict identical on every file.

Honest verdict: faithfulness-motivated (matches cadical's mechanic),
performance roughly neutral with a slightly positive geomean. Kept on the
same grounds as the reuse_trail fix.

## 2026-08-21: the default flips on (BVE + ELS in the `CaDiCaL` preset)

### Trigger

Fresh 94-file CaDiCaL differential (`/tmp/opencode/sat_vs_cadical.json`,
25 s cap): 15 nixie-only timeouts where CaDiCaL solves (4-23 s), worst paired
ratios 6s167-opt 52.7x, mrpp 7.3x, crn 3.7x, constraints_17 3.1x. CaDiCaL's
own log on 6s167-opt shows the win is inprocessing (582 substituted vars,
1126 vivified, 2974 subsumed clauses, 377 fixed; 0.28 s total).

### Why the 2026-08-17 "net-negative as default" verdict no longer holds

That verdict predates three landed changes: the eliminator single-pass
backward queue (first elimination phase 630 ms -> 9.4 ms, 67x), the ELS
value-filtered rewrite (cadical `decompose` semantics), and the cadical probe
schedule (`inprobeint`-based, 3bfd6bf). The eliminator is no longer paying a
full-database rescan per eliminated variable, so the cost side of the ledger
collapsed while the benefit side (smaller formula) stayed.

### Measurement (instructions-to-verdict, PMU `cpu_core/instructions`,
### pinned CPU 6, deterministic trajectories)

Both arms are deterministic (no RNG axis in this path; repeat runs bit-stable
to ~1e-8 modulo PMU interrupt noise), so single-run comparisons are true
values, not draws — the stochastic-baseline trap of `BENCHMARKING.md` §4 does
not apply. Wall-clock was only used for the suite-cap capability table and
was measured under external load (run alongside, same conditions both arms).

| file | base | +BVE+ELS | +inprocessing | BVE only |
|---|---|---|---|---|
| 6s167-opt | 118.6G | **46.9G** | 14.0G | 32.7G |
| mrpp_4x4#12_12 | 109.1G | **46.0G** | 52.6G | 73.9G |
| frb65-12-2 | 120.1G | **38.5G** | 105.0G | 78.1G |
| stable-300 | 245.2G | **81.8G** | 310.5G | 131.2G |
| summle_X4044 | 115.2G | **62.9G** | 116.9G | 157.2G |
| summle_X4053 | 127.4G | **71.3G** | 227.2G | 60.1G |
| summle_X11112 | TO400 | **129.1G** | 203.5G | 247.0G |
| circuit_700gates | TO400 | **62.3G** | 78.5G | 62.3G |
| j3037_10_mdd_b | 83.6G | **49.1G** | 80.6G | 261.0G |
| constraints_17 | 40.3G | 63.4G | 205.4G | 153.1G |
| qwh.50.1250 | 55.7G | 67.9G | 1088G | 350.5G |
| x9-09054 | 13.7G | 509.1G | 1173.9G | 423.3G |
| x9-08075 | 326.1G | 344.6G | 618.8G | 324.6G |
| uf100-* (2 files) | = | = | = | = |

Verdicts agree with CaDiCaL on every file in every arm.

Decisions from this table:

1. **BVE + ELS on** (the bundle, matching what CaDiCaL actually interleaves).
   BVE-only is a different and worse configuration: without ELS,
   qwh.50 collapses to 350G and constraints_17 to 153G (ELS is doing real
   work on the equivalence chains those families carry). ELS-only is also
   worse alone (6s167 181.8G, stable-300 320.3G).
2. **Inprocessing stays off**: the periodic `inprocess()` round destroys the
   BVE+ELS gains on stable-300/summle (back to base level or worse) and
   collapses qwh.50 by 20x. Only 6s167-opt benefits (46.9G -> 14.0G). The
   missing amortizers are vivification and transitive reduction — the same
   two named in the 2026-08-17 verdict.
3. **Known regressions kept** (documented in the preset comment): x9-09054
   13.7G -> 509G (37x, one adversarial crypto file), constraints_17 1.6x,
   qwh.50 1.2x. Against: 7 files at 1.7-3.1x, 2 timeout->solved, and
   family-consistency (all four summle files improve; wins cluster on
   elimination-shaped instances, losses do not).

### Not the reshuffle signature

`BENCHMARKING.md` requires asking whether an aggregate win is trajectory
reshuffling. Three reasons it is not, here: (a) the arms are deterministic —
there is no seed distribution to confuse the estimate with; (b) the wins are
family-clustered (every summle, both stable, mrpp, frb65, 6s167 — the
elimination-shaped instances), while reshuffle noise is per-instance random
in sign; (c) the mechanism is countable — BVE shrinks the formula (vars and
clauses eliminated), it is not a trajectory perturbation of the same search.

### Soundness gate

400k-iteration differential fuzz (`examples/diff_equiv`, stack on vs off,
verdict agreement + model validation of every SAT model): 268k sat, 0
mismatches, 0 invalid models. Full workspace suite (10 059), clippy, fmt,
doc, Z3 parity 168/168 clean.

### Suite result (the user's own harness, 25 s cap, jobs=8, same load)

| | before (16:36) | after |
|---|---|---|
| nixie solved | 69/94 | **73/94** |
| paired geomean nixie/cadical | 0.918 | **0.461** |
| files >=1.5x faster than cadical | 22 | **42** |
| files >=1.5x slower | 9 | 12 (x9-09054 joined) |
| disagreements | 0 | 0 |

Remaining gap: the 15-file cadical-only-timeout class (circuit_800, worker,
crypto, rbsat, FmlaEquivChain need 250-500G instructions — cadical's
vivify/sweep amortizers; several DO solve now given 200 s: rbsat 484G,
noL-11-14 410G, FmlaEquivChain 257G). Next lever: port vivification.
