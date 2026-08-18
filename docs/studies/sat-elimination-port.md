# CaDiCaL `elim.cpp` port: sound, big per-family wins, net-negative as a default (2026-08-17)

## Motivation

`bench`-suite differential vs CaDiCaL (`/tmp` run, 94 files: 40× SATLIB `uf100`,
54× satcomp2024) showed OxiZ's SAT core >1.5× slower than CaDiCaL on 22/94
files, with the worst gaps (66×, 29×, 25×, 18×) all on instances CaDiCaL
collapses via inprocessing — its log shows clause counts dropping 13.5k → 2.3k
through interleaved `e` (elim) / `s` (subsume) / `d` (distill) rounds before
1.2k conflicts refute the residue. OxiZ ran *no* elimination by default: the
one-shot `bve.rs` pass was off in every preset, gated behind a documented
soundness hazard.

## What was done

Full port of CaDiCaL's bounded variable elimination to
`oxiz-sat/src/solver/eliminate.rs` (~1.1k lines): occurrence-list driven,
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

| config                       | >1.5× vs cadical | total OxiZ time |
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
