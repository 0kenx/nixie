# Binaries out of the watch lists (BIG-authoritative BCP): pre-registration + results (2026-09-01)

Successor of the closed arena-layout study (`2026-09-arena-8byte-header.md`)
— its closing line named **structural visit-count reduction** as the
remaining propagate lever. This is that slice, discovered in this codebase's
own architecture rather than a cadical port: we already have a binary
implication graph (BIG) that propagates binaries *before* the watch scan,
so the binary entries carried in the watch lists are pure redundancy.

## The measurement that names the target (diag build, worktree scratch)

Visit-mix instrumentation (`NIXIE_VISIT_STATS`, MAXC=40000/20000, cadical
preset) on the loss files and then the 54-file corpus:

| file | visits | blocker-hit | bin arena-miss | binary share of watch **entries** |
|---|---|---|---|---|
| circuit_64in | 222 M | 84.8 % | **0** | ~0 % |
| frb45-21-2 | 79 M | 82.6 % | **0** | **80.5 %** |
| si2-b03m | 117 M | 72.3 % | **0** | ~0 % |
| noL-11-14 | 53 M | 65.0 % | **0** | 0 % |
| worker_550 | — | — | — | **99.8 %** (20.6 M entries ≈ 250 MB) |
| shuffling-2 | — | — | — | 84.4 % (7.7 M) |
| g2-ak128 (×2) | — | — | — | 66.7 % / 45.4 % |

`bin_miss = 0` everywhere: a binary watch entry **never reaches its arena
load**, because the BIG scan already assigned the other literal true (or
conflicted) moments earlier in the same `propagate()` call. Binary entries
are therefore scanned (12 B + blocker-value load + branch + 12 B self-write,
every propagation of their key) to re-discover work the BIG already did.
Corpus-wide: **15 files > 50 % binary entries, 17 > 30 %**, 36.4 M redundant
entries total.

## The change

**Invariant: a live arena clause of len == 2 is registered in the BIG
(both directions) and in *no* watch list; len ≥ 3 clauses exactly as
today.** The BIG becomes the only propagation mechanism for binaries
(it already runs first in `propagate()`), and the watch lists lose the
redundant binary entries — visit volume, watcher memory (12 B × binary
count), and list-growth churn all drop.

Implementation (all sites audited; every lifecycle path funnels through
one of two choke points):

1. `attach_watchers(cid, l0, l1)` becomes binary-aware: len == 2 → two
   BIG edges; else two watch entries. The seven call sites that add BIG
   edges *next to* an attach for binaries (`add_clause` ×2, learn ×2,
   probe, LS-operator, subsume-strengthen) drop their explicit adds
   (dedupe).
2. `rebuild_watches_and_binary_graph`: len == 2 → BIG only.
   Every shrink-to-binary path either funnels through `attach_watchers`
   (strip path, vivify-strengthen, subsume-strengthen) or is followed by
   the phase-end rebuild (BVE/elim/ELS).
3. Deletion is already disciplined: `purge_binary_edges` runs at every
   binary retraction (pop, `forget_learned_since`, sweep retire,
   `retire_clause`); reduce skips len ≤ 2.
4. **Tick parity (the load-bearing detail).** The tick counters (restart
   and stable/focused schedules) are computed from watch-list *sizes*,
   which today include the binary entries. Removing the entries would
   silently change every restart/mode boundary — a heuristic-class
   divergence no perf measurement could disentangle. Instead
   `WatchLists` grows a per-literal `bin_phantom: u32` counter that
   models **exactly the old binary-entry count**: +1 per direction at
   attach (binary branch) and at rebuild (reset + refill from live
   binaries), *never* decremented on retire/purge (the old entries
   lingered lazily until the next rebuild — the phantom counter must
   reproduce even that), and the tick formula reads
   `1 + lines(ws.len() + phantom, 8)`. With phantom parity, the CNF
   corpus (congruence sentinel edges exist only mid-ELS-round and the
   mid-round propagate is post-rebuild; hyper-binary is default-off)
   should stay **bit-identical** — Gate 1.
5. Debug invariant (`check_watched_literals`): every live len==2 arena
   clause must have both BIG edges; no watch entry may reference a
   len==2 clause; every non-sentinel (`ClauseId(u32::MAX)`) BIG edge
   must reference a live len==2 clause whose literals match the edge.
   The stale "dual mechanism / add_theory_reason_clause registers only
   the watch list" comment there is corrected (that site registers both
   since the deletable-reasons change).
6. `propagate_probe` (preprocessing) builds its **own** temporary watch
   lists from the database — unaffected. xor.rs uses its own map;
   lucky.rs snapshots whatever lists exist.

## Change class

Path-preserving *given* tick parity (Gate 1 is the proof); without
parity it would be heuristic-class. Soundness-relevant invariant change
(BIG completeness becomes load-bearing for binary propagation), so the
battery below is run regardless of the perf outcome.

## Go / no-go (pre-registered BEFORE measuring)

1. **Gate 1 — trajectory identity.** 54-file `/tmp/sc24f` corpus,
   `stats_solve` (CaDiCaL preset), `MAXC=60000`, default seed, vs
   `precompile/5f3ae49`: counters + verdict bit-identical. Divergence =
   a parity leak (phantom accounting or a BIG gap) — find it before
   measuring anything.
2. **Gate 2 — instructions** (`cpu_core/instructions`, pinned, private
   target dir, binary shas recorded):
   (a) fixed `MAXC=40000` on the binary-heavy class (worker_550,
   shuffling-2, frb45, qwh.50.1250, ITC2021_Early_3, g2-ak128boothbg2msaig,
   rbsat-v760c43649gyes9, af-synthesis_stb_50_100_9): geomean(old/new)
   ≥ **1.02**;
   (b) controls circuit_64in / si2-b03m / noL-11-14 in 0.99–1.01
   (binaries ~absent there; any movement is a red flag);
   (c) both-solve corpus geomean ≥ 1.00 (no regression).
   1.00–1.05 on (a) = neutral, below the bar → revert and record.
3. **Soundness** (regardless of gates): workspace suite + clippy/fmt/doc;
   `diff_equiv` ≥ 200 k iterations; corpus verdict sweep old-vs-new
   0 mismatches (generous caps); SMT differential 0 disagreements
   (theory-reason binaries now BIG-registered — the SMT path exercises
   `add_theory_reason_clause`, pop/forget, `restore_to_trail_size`);
   z3 parity suite; the new invariant checker active in debug runs
   (tests + fuzzing build).

## Hazards

- A missed BIG edge = a lost binary implication = **wrong answer** (not
  just slower). The attach/rebuild choke points cover all audited
  creation paths; the invariant checker is the tripwire; the SMT
  differential and diff_equiv are the empirical gates.
- Duplicate BIG edges (an explicit add left next to a binary-aware
  attach) are sound but double-scan and double-bump phantoms — the
  dedupe list in (1) is exhaustive by audit; the invariant checker also
  verifies edge↔clause correspondence.
- Shared `target/` (private `CARGO_TARGET_DIR`, sha-diff each arm);
  atom PMU (`cpu_core/...` + `taskset`); process-group kill on wall
  caps; wall-clock never primary.

## Results — LANDED

**Every gate passed.**

- **Gate 1 (trajectory identity): 54/54 bit-identical** — result,
  conflicts, decisions, propagations, restarts, learned at `MAXC=60000`
  vs `precompile/5f3ae49` (old sha `b88cbd78…`, new sha `50fe131e…`).
  The phantom tick-parity mechanism held exactly: the refactor is
  semantically invisible to the search.
- **Gate 2a (fixed `MAXC=40000`, binary-heavy class): geomean
  old/new = 1.0639** — outside the ±5 % neutrality band, well above the
  1.02 bar:

  | file | old | new | old/new |
  |---|---|---|---|
  | ITC2021_Early_3 | 0.628 G | 0.559 G | **1.1232** |
  | af-synthesis_stb | 34.14 G | 31.69 G | 1.0773 |
  | frb45-21-2 | 9.80 G | 9.16 G | 1.0706 |
  | rbsat-v760 | 9.34 G | 8.82 G | 1.0596 |
  | qwh.50.1250 | 45.21 G | 42.70 G | 1.0587 |
  | shuffling-2 | 139.3 G | 131.9 G | 1.0562 |
  | g2-ak128msaig | 6.06 G | 5.76 G | 1.0522 |
  | worker_550 | 168.2 G | 165.6 G | 1.0161 |

  Controls (binaries ~absent): circuit 1.0011, si2 1.0013, noL 0.9979 —
  geomean **1.0001**, exactly the predicted null. worker's modest 1.6 %
  matches its profile (shrink/parse-bound, its 20.6 M redundant entries
  cost memory more than scans).
- **Gate 2b (both-solve corpus, 12 s cap): geomean 1.0219 over 20 cells,
  0 verdict mismatches** — the corpus-level no-regression gate passes
  with a real positive (the binary-heavy cells lift the geomean).
- **Gate 3 (soundness)**: `nixie-sat` 879/879 (3 new tests: BIG-only
  registration, the purged-edge tripwire, phantom parity semantics);
  workspace 10 418/10 418; clippy/fmt/doc clean; `diff_equiv` 200 k
  release iterations + 20 k debug iterations (invariant checker active
  at every reduce) — 0 mismatches, 0 invalid models; corpus verdict
  sweep at 60 s/arm **54/54, 0 mismatches, identical solve sets**; SMT
  differential **160 solved / 0 disagreements** (par2 2 320.8); z3
  parity **169 correct / 1 inconclusive / 0 wrong** (z3 4.16.0, as in
  the prior sessions' snapshots).

Audit notes recorded for the next agent: the pre-change
`check_watched_literals` comment claiming `add_theory_reason_clause`
registers binaries "only in the watch list" was stale (it registers both
since the deletable-reasons change) — corrected; `transred` only reads
the BIG and retires whole clauses through `retire_clause` (edge purge
included), so it is safe under BIG-authority; the knobbed strip path
(`NIXIE_ROOT_SWEEP_STRIP=1`) now also gains BIG edges for its
  shrink-to-binary products (via `attach_watchers`), which can change
  trajectories *under that knob* — the knob's own verdict gates govern
  there, not trajectory identity.

Remaining propagate lever after this landing: the large-clause visit
  itself (circuit/si2/noL-class, blocker-hit volume 65–85 % with
  binaries now gone from the lists only on the binary-heavy files) —
  the miss-path micro-cuts (branchless other-literal à la cadical
  `lits[0] ^ lits[1] ^ lit`, blocker-field-only rewrite on refresh) and
  Gent's saved-position scan (needs a header field — see the closed
  arena-layout study for why header surgery must re-litigate the 12-
  byte pin) are the recorded candidates.
