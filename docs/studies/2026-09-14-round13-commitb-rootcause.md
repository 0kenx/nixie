# Round-13 execution: commit B's re-apply, the false-sat cure, and the divergence pinned to one conflict analysis (2026-09-14)

Execution of `docs/studies/2026-09-14-round13-handoff.md`.  Entry
condition repaired first: the machine had lost `smt-lib/` — refetched
from Zenodo record 16740866 (12 logics, 108 659 files, refill recipe in
`smt-lib/PROVENANCE.md`), and the entry benchmark ran (nixie/kissat/z3
agree 10/10 on a seeded QF_BV sample —
`docs/studies/2026-09-14-round13-bench-smt10.md`).

## What this session did

1. **Re-applied commit B** (the Vec deletion) from the handoff's recipe in
   a private worktree (`/tmp/wt-commitb`, branch `commitb-round13`, off
   `5d835221`): CSR-only `add`/`remove_clause`/`relocate` (relocate now
   records the ghost tick debt), `CsrWatchLists::{take_combined,
   put_back_combined}` with take semantics for the legacy path, the
   session driver as the span-copy + overflow-take roundtrip with the CSR
   as `destinations`, `push_watch`/`push_watch_unique` pushing the CSR
   (the dedup reads the combined view), the kernel's notification
   branches stripped, the rebuild adopting the counting-sort layout
   unconditionally, `packed_snapshot` as the CSR clone.
2. **Found and fixed a false `sat`** in the first B build: the rewritten
   rebuild dropped the `binary_graph.build_edge` calls — every rebuild
   after the first emptied the BIG, binary propagation died, and 6s167
   returned `s SATISFIABLE` (0 decisions) on an UNSAT formula.  With the
   edges restored the verdict is correct: **UNSAT at 33 154 conflicts**
   (A: 33 028 — the standing divergence, now +126 ≈ 0.4 %).
3. **Built the instrumentation the handoff called for** (`NIXIE_CSR_MUT_TRACE`)
   and ran the two-run diff program it prescribed, then kept digging with
   six further instruments until every layer was either proven identical
   or pinned as the divergence site.

## The instruments (all landed on main, env-gated, zero default cost)

| env | logs |
|---|---|
| `NIXIE_CSR_MUT_TRACE=<code>\|all` | every push/drop/rewrite of one (or every) literal's watch list, Vec and CSR sides, with a global op counter |
| `NIXIE_DB_DIGEST=<step>` | per-conflict hash of the clause DB (full literals, all positions) + live count |
| `NIXIE_DB_DUMP_AT=<conflicts>` | full per-clause `(ref, lits0, lits1, len)` dump at one conflict |
| `NIXIE_WDUMP_RANGE=<lo>-<hi>` | per-conflict dump of every literal's watch list (the representation the tree actually scans) |
| `NIXIE_DUMP_WATCHES_POST` / `NIXIE_DUMP_BIG_POST` | post-rebuild watch / BIG dumps (the pre-rebuild ones existed) |
| `NIXIE_ENQ_TRACE=1` | every trail assignment with level and reason id |
| `NIXIE_HEAD_TRACE=1` | every propagation dequeue with the queue head |
| `NIXIE_CONFLICT_TRACE=1` | every propagation conflict (list scan and BIG scan) with the conflicting clause id |
| `NIXIE_BUMP_TRACE=1` / `NIXIE_PICK_TRACE=1` | the VMTF bump stream / each decision's queue walk |

The instrumented A-tree (flip A + probes only) is **trajectory-identical**
(6s167 33 028, no envs), clippy/fmt clean, 1092 tests green.

## What was measured (all on 6s167-opt, A = flip-A + probes, B = the re-apply)

**Identical through the divergence window** (conflicts ≤ 16483):
- watch lists, **including A's scanned `Vec` (not just the mirror) and
  B's combined view, per conflict** through 16482;
- the BIG, pre- and post-rebuild, through 16483;
- the clause DB under a full-literal hash (every position, not just the
  watched pair) through 16483;
- the whole assignment stream with reasons, the dequeue stream with
  heads, the conflict stream (list + BIG) — millions of events;
- the push/drop watch-event streams (act, code, ref, blocker) —
  5 739 005 primary events before the first difference;
- drift: A's Vec and CSR stay in lockstep everywhere we looked (the
  handoff's "which cleaning path" candidates are **eliminated**: no
  cleaning-path asymmetry exists in an equal-trajectory run — every
  8440 push enters clean state, zero dedup asymmetries, zero push
  asymmetries in swapped mode).

**The divergence, pinned**: at conflict 16483's inprocessing round (a
rebuild bracketed by factor/subsume work — NOT an elim phase; those run
at 2000/6003/12166/20166/30169), the first differing event anywhere is
**one conflict analysis whose reason walk resolves one extra variable
(var 4064) in A** (bump #1 413 063 of ~1.9 M).  Every input to that walk
that we hashed — trail, levels, reasons, the conflicting clause, the
full clause literals — is identical.  The extra resolution changes the
learned clause, the backtrack level, the chronological compaction of the
trail, and therefore `assignments[617]`: A dequeues literal 188 next,
B dequeues 191 (dequeue #2 967 865).  Everything downstream (watch
content at 16484, DB hash at 16484, decisions, BIG at 25524, elim phase
5, final count 33 154 vs 33 028) follows from that one analysis.

## The next entry (the remaining question, sharply)

One conflict analysis inside the 16483 inproc round walks differently
with all hashed inputs equal.  The unhashed inputs to `analyze` /
minimization, in suspicion order:
1. **the per-clause `searched` saved-position caches** (steer the
   watch-move swap choices in the phase's scans — they change clause
   tails, which the full-literal hash covers only at conflict
   granularity, not inside the round);
2. **`level_starts` / `var_info` level snapshots at analysis time**
   (the walk's stopping condition);
3. **the on-the-fly minimization's redundancy walk** (its `seen` bitmap
   seeds and recursive reason reads).

The probe that settles it: dump, at conflict 16483's analysis entry,
the full input tuple (conflict clause literals + each reason clause's
literals + levels + searched per touched clause) in both binaries and
diff — the first differing tuple is the root.  The B tree lives in
`/tmp/wt-commitb` (branch `commitb-round13`); the A tree that landed is
main itself.  **Do not re-apply B from the study's recipe again — the
worktree's B includes the BIG fix the recipe lacks.**

## Traps added

8. **The rebuild's BIG edges are load-bearing for correctness, not just
   trajectory**: dropping `build_edge` in a rewrite yields a silent
   false `sat` (binaries unwatched ⇒ no conflicts ⇒ empty-model SAT) —
   caught by the verdict check, not by any trajectory gate.
9. **Instrumentation asymmetry lies**: an A-side that logs two
   representations (Vec + mirror) and a B-side that logs one produce
   "divergences" that are pass-ordering artifacts; compare
   primary-representation streams, and never normalize away `path`
   (operation kind) or `blk` (blocker).
10. **Charge-stream identity ≠ content identity** (same lengths,
    different entries is possible), and **assignment-stream identity ≠
    trail identity** (the chronological compaction rewrites the array
    without logging) — hash the actual structures at the actual read
    points.
11. Worktrees need the corpus symlinks (`smt-lib`, `satcomp2024/2025`,
    `satlib`) or the corpus tests fail `[corpus-missing]`; a nextest
    TIMEOUT can be pure parallel load — re-run before believing it.

## Continuation (same day, second session): the root pinned to the post-phase decision; the phase's interior remains

Five more instruments (all landed, same rules): `NIXIE_AWALK_TRACE`
(per-analysis reason-walk steps `[astep]` with each reason clause's
literals+levels, plus the raw learnt clause `[learnt]`), `NIXIE_CWRITE=<id>`
(every arena write to one clause: `shrink`, `swap_lits`, the kernel's
watch-move swap with its tail index, and `NIXIE_CVISIT`-style per-visit
`searched`+tail-value profiles), `NIXIE_BT_TRACE` (every backtrack with
level and new trail length), the searched-cache-inclusive DB digest, and
per-clause full-literal dumps at a chosen conflict (`NIXIE_CLAUSE_AT`).

**The chronology is now closed.**  Interleaving every event class
(assignments with reasons, backtracks, watch visits/writes, analysis
walks, conflicts, dequeues) in single runs of both binaries: the first
diverging event anywhere is the **level-15 decision after the 16483
inproc round — A decides literal 188 (var 94), B decides 191 (var 95)**.
Everything previously observed — the differing clause-38260 literal
order (a 3-cycle on tail positions 2..7), the differing learnt clause
(same permutation), the differing saved-position swap (i=2 vs i=5), the
differing tail-value profile at the clause's next visit, the differing
backtrack — is *downstream of that decision*.  The decision reads the
VMTF queue, whose search pointer the phase's bump sequence left at 3509
(A) vs 4251 (B); the phase's bump sets differ by exactly one variable
(4064, one extra resolution in one mini-conflict analysis inside the
round), while the reason-walk steps of every phase analysis are
event-identical.

**Eliminated this session**: the searched/saved-position caches (a
searched-inclusive digest still first diverges only at conflict 16484),
the factor fresh-var bumps (tagged; absent from the divergent bump),
probe backtracks (tagged; the probe does not run in the window), the
distiller (does not read watch lists), and any pre-phase state
difference (every digest, dump, and stream matches through 16483,
including a per-conflict comparison of A's actually-scanned `Vec`
against B's combined view).

**The remaining suspect** — the only unlogged reader inside the round:
**the learnt-clause minimizer's block walks**
(`shrink_and_minimize_clause` resolves blocks against reason clauses
below the conflict level without any step logging) and, if it runs in
the default schedule, the legacy `vivification::propagate` (whole-DB
iteration).  One of those reads a clause whose content the round itself
had already rewritten differently — the rewrite order born in the same
unlogged interior.  The next probe: `[bstep]` logging inside the block
walk (same shape as `[astep]`) + a vivify candidate log; diff at the
16483 round.  The B tree (`/tmp/wt-commitb`, branch `commitb-round13`)
now carries the same probe family; both binaries are cached
(`precompile/f5d1115e`, `precompile/scrap-commitb-round13`).

Operational note: the per-visit clause-identity capture in the kernel is
env-armed (`mut_trace::cwrite_target`, a `OnceLock`) — an unconditional
`live.reason()` there cost enough on the hot path to timeout two
reduce-arm tests; keep it lazy.

## Third continuation: the destination-layer bisection and the exhausted-hypothesis boundary

**The decisive bisection**: A run in swapped-dual mode
(`NIXIE_CSR_SHADOW=1 NIXIE_CSR_SCAN=1` — the CSR scanned via the same
span-copy + overflow-take roundtrip, pushes to `Vec` destinations +
mirror) solves at **exactly 33 028**, while B (CSR destinations) is
33 154.  **The divergence lives in the kernel's destination layer —
not in the scanning.**  The two structural deltas there: (1)
`push_watch_unique`'s dedup reads the CSR's combined view (the Vec
world reads the destination list), and (2) plain pushes land directly
in the CSR's overflow (the Vec world: Vec push + mirror `scan_push`).

Fixes applied in the B tree for (1)'s sharpest form: `scan_parts` now
takes BOTH segments (the span's live end drops to its start for the
scan's duration — matching `mem::take` for the span too, so mid-scan
self-dedups read an empty combined view).  Trajectory-neutral on
6s167 (the suppression case never fires here — consistent with the
zero `B_WOULD_SUPPRESS` measurement).

**The chronology, corrected and closed at checkpoint granularity**:
with tick totals, the substitution/BVE/`probe_propfixed` tables, and
the searched-inclusive DB hash all folded into the per-conflict
digest, the FIRST divergence of ANY hashed or streamed state is the
**DB hash in the checkpoint window (16 400, 16 500]** — everything
else (ticks, tables, assignments, backtracks, walks, bumps, picks,
probe queues) is identical there and before.  The earliest behavioral
difference (the `r=d` probe-literal sequence 188-then-191 vs
191-skipping-188) sits inside that same window; the probe queue
generation, the memo, the budget inputs, the hyper-binary derivation
inputs (reasons, dominator folds — order-insensitive), and the lucky
phase (never runs on this instance) are all verified identical.

**Exhausted this session**: the phase-bump attribution (the bump-set
difference at ~#1.41 M belongs to a round whose walks are identical —
it is downstream of the DB divergence, not inside the 16 483
inprocessing round), the searched caches, the minimizer block walks
(`[bstep]` logging — aligned past the divergence), the VSIDS/VMTF pick
streams, the `unbranchable` tables, `backtrack_to_size` (test-only),
`reset_propagation_head` (queue rewind — read-side only), and the
lucky-phase tick restore (never armed).

**The handoff target, sharpened to one mechanical step**: construct
B' = swapped-A minus the `Vec` list itself (push to a scratch
destination + flush into the CSR exactly where swapped-A's mirror
lands them).  B' at 33 028 ⟹ the delta is the dedup reader's view of
the destination; B' at 33 154 ⟹ the delta is the push/flush semantics.
Instruments landed with this round: `NIXIE_AWALK_TRACE` now also logs
`[bstep]` (every minimizer/block-walk reason fetch) and `[learnt]`;
`NIXIE_CWRITE`/`NIXIE_CVISIT` per-clause write/visit traces (env-armed
identity capture — an unconditional `live.reason()` on the hot path
costs enough to timeout reduce tests); `NIXIE_BT_TRACE`;
`NIXIE_PROBE_QUEUE_TRACE` (queue + per-probe memo/size + tick
snapshots); `NIXIE_LUCKY_TRACE`; the `[decide]`/`[vsids-pick]`/
`[skip]` decision traces; the digest now hashes the searched caches,
the substitution/BVE/probe tables, and prints the tick totals.

## Fourth continuation: the flip-bisection protocol; `add`'s Vec write is load-bearing

The reverse-dedup probe (`REVERSE-ASYMMETRY`: the Vec-side suppresses
while a CSR-side reader would push) fires **zero** times in swapped
mode, and removing B's dedup entirely (`NIXIE_DEDUP_OFF`) leaves B at
33 154 — **the dedup is exonerated in both directions.**  The
charge-stream horizon re-verified on clean trees: swapped-A vs B first
differs at scan 2 965 082 (the literal-188 window).

A **flip-bisection** from the clean 33 028 baseline (main +
unconditional swapped, `NIXIE_CSR_SHADOW=1`):

- **B′0** (baseline): 33 028.
- **B′1** (sweep reader → combined view only): 33 028 — the reader
  gate is inert.
- **B′2** (`add` drops its Vec write, CSR-only): **33 153** — the
  first flip that diverges.  Adding the two consistent-reader fixes
  (dedup on the CSR, charge on the CSR's combined length) lands at
  32 548 — a third trajectory, NOT 33 028: with every identified
  reader moved to the CSR, the absence of the Vec write still changes
  the run.  **`add`'s Vec-side write is load-bearing through a reader
  that is none of {dedup, charge, sweep-env, mirror-putback}** —
  the remaining candidates are the VecScanMirror's in-scan state
  itself (its list is the `mem::take` target the swapped driver
  carries) and the `merged.write = watches.len()` plumbing.

Retracted this session (measurement hygiene, recorded as a trap): two
intermediate charge/mut comparisons ran against a worktree still
carrying earlier bisection edits — their horizons (17 161) were
artifacts of a hybrid world, not evidence.  Every number above is from
a tree verified by `git status` + a fresh 33 028/33 154 check before
the measurement.

**Next entry (one of two experiments settles it):**
1. From clean B′0, flip the mirror out: keep the Vec destinations but
   replace the VecScanMirror + `mem::take`/putback with a post-scan
   refresh of `destinations[code]` from the CSR's combined view — if
   33 028 survives, the in-scan mirror state is not the reader, and
   the load-bearing path must be `merged.write`/`watches.len()`-family
   plumbing; if it moves, the mirror's taken-list visibility during
   the scan (the keeps-so-far the dedup/charge could theoretically
   see) is the carrier despite the zero-asymmetry probes.
2. Or instrument every read of `destinations[...]` in the swapped
   driver+kernel with a use-site log and diff the two worlds' read
   sets directly.

## Fifth continuation: the mid-interval drift hypothesis killed; the CSR's internal order diverges

The decisive null: instrumenting clean-A's swapped mode to print **both**
the Vec's and the CSR's length at every one of 4 049 044 scans —
**`vec≠csr` at exactly zero scans.**  The "charge reads the drifted Vec"
hypothesis is dead: the two representations are length-identical at every
charge point in the clean world.

The flip-bisection, redone carefully (one-pass edits, `git status`-verified
before each measurement):

- **B′2c** (add→CSR-only + charge on CSR + dedup on CSR): 32 548.  The
  charge-trace artifact (the print still showed `watches.len()`, the Vec)
  initially faked a divergence at scan 17 161; the real charge divergence is
  at scan 1 984 341.
- **B′3** (+ the sweep reader → combined-only): **still 32 548.**  All four
  identified Vec readers (charge, dedup, sweep, mirror-putback) are now on
  the CSR or inert — and the trajectory still moves.

**The mechanism, caught mid-act**: with `add` CSR-only, the Vec misses the
added entries; the next scan of that literal takes the short Vec while the
CSR (complete) drives the scan; the `VecScanMirror` receives more
notifications than the taken Vec has slots and **silently drops the keeps
beyond its length** (`if self.read >= self.list.len() { return; }`) — the
Vec's rebuilt content is now the CSR's first-N prefix, not the true list.
The corrupted Vec persists across putbacks.

**The residual divergence (the handoff's question)**: with every named
reader on the CSR, the two worlds' CSRs still diverge — not in content
multiset but in **combined-view order** (event #1 141 on literal 4583: A's
scan drops `ref=1423816` first, B's drops `ref=882104` first — both then
process the other).  The order of `[span] ++ [overflow]` differs, which
means the span/overflow *split* or the overflow *arrival order* diverged —
through a path from the corrupted Vec back into the CSR that is none of
the four flipped readers.  Remaining candidates: a second sweep-adjacent
reader (`iter_combined` call sites beyond the collapsed one), the legacy
`take_combined_vec` path (believed dead on the default config), or an
interaction between `push_watch`'s Vec-push ordering and a subsequent
CSR-side dedup/push sequence.

**The corrected interpretation of the whole bisection**: every flipped arm
diverged (33 153 / 32 548) *without reaching B's 33 154* — the arms are
NOT steps toward B; they create their own corrupted-Vec worlds.  The
bisection method itself (flip one Vec-role at a time) is unsound when the
Vec's corruption feeds back through unflipped readers.  The sound protocol
is the reverse: start from B (33 154, no Vec) and *add back* one Vec-role
at a time until 33 028 appears.
