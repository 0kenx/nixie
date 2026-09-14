# CSR watch lists: the dual-write BCP scan landed (slice 2+3, 2026-09-14)

Round-11 handoff item 1, executed.  The centerpiece the kickoff designed —
the dual-write BCP scan — is landed and validated, together with the
cold-path dual bookkeeping (slice 3 in the handoff's numbering, done in the
same change because the drifted-state comparison is meaningless without it:
every learned-clause attach between rebuilds would otherwise mismatch).
`docs/studies/2026-09-13-csr-watches-kickoff.md` remains the design
reference; this documents what landed, the validation evidence, and the
perf arc.

## What landed

- **`CsrScanFrame` + the scan mirror** (`watched.rs`): `begin_scan`/
  `scan_keep`/`scan_remove`/`scan_push`/`end_scan` on `CsrWatchLists`.
  The frame snapshots the scanned literal's primary/overflow split before
  the `Vec` list is taken; per-entry notifications resolve the *source
  segment* from the notification count (`read < p_len` ⟺ primary), so
  survivors compact into their own segment exactly where the `Vec` scan's
  write cursor puts them.  `end_scan` compacts each segment's unvisited
  tail behind its survivors and truncates the overflow — including
  dropping mid-scan pushes into the scanned literal itself, which is
  precisely what the `Vec` put-back overwrite does (the repair-can-target-
  self shape is unit-tested).
- **All three scan bodies dual-write**: `list_kernel::scan` (the session
  path, default), `watch_kernel::Cursor::scan` (LRAT / lazy-HBR /
  reason-stats), and the legacy inline loop in `propagate.rs` (bcp-stats /
  oracle tests).  Watch moves (`push_watch`, `push_watch_unique`,
  `destinations.add`) mirror as overflow appends; dedup reads the `Vec`
  (ground truth), so `push_unique` stays exact.
- **Cold paths**: `WatchLists::add`, `remove_clause`, `relocate_refs`,
  `clear`, `packed_snapshot`/`restore` all mirror; `propagation_parts`
  hands the session the CSR beside the destination slice.
- **The rebuild** (`equiv.rs`) now does the two comparisons the plan
  called for: the **drifted** CSR vs the drifted `Vec` lists (order
  included) *before* either resets — the empirical order-isomorphism
  proof — then the fresh-build comparison, then adopts the fresh layout
  as the new drift baseline (`csr_take` detaches the shadow during the
  fill; the fill uses the mirror-free `push_only`).
- **Const-generic `MIRROR` specialization**: the session driver, both
  kernel scans and the push helpers monomorphize over `MIRROR`; the
  flag-off instantiations contain no CSR code at all (see the perf arc).
  The legacy loop keeps runtime gating (diagnostics-only path).

## Validation evidence

- **Unit tests** (`watched.rs::csr_tests`): a 200-trial randomized
  reference-model test (chained scans, early exits, blocker rewrites over
  mixed primary/overflow lists), the move/self-push parity test, and a
  `WatchLists`-level round trip incl. snapshot/restore and a fabricated-
  divergence detection.  Full `nixie-sat` suite: 1054 passed with the
  flag off **and** with `NIXIE_CSR_SHADOW=1`.
- **Corpus (54 files, seed 0, 60 s cap)**: verdict + conflicts identical
  across {treatment flag-off, treatment flag-on, pre-change baseline};
  every apparent mismatch re-ran clean at a raised cap and was bit-
  identical (conflicts/decisions/propagations/restarts) — wall-cap
  censoring, the screen's known artifact class.
- **Drift**: `mismatched=0` on every drift comparison across the corpus
  (up to 101 rebuilds on FmlaEquivChain_4_6_6), on **all four driver
  configurations**: default session, `NIXIE_REASON_STATS=1` (watch
  kernel), `NIXIE_BCP_STATS=1` (legacy loop), `HYPER=1` (lazy hyper-
  binary mutating between scan steps).  Conflicts identical across all
  four (33028 / 23527 / 450623 on the three probe files).

## The perf arc (flag-off cost)

Wall A/B was unusable this round (load average 40-60 from concurrent
agents), so the flag-off cost was measured with deterministic instruction
counts (`perf stat -e cpu_core/instructions/u`, pinned core, ±0.02%
reproducible; a dead-code canary build moved totals 0.02%, controlling
layout noise):

1. Naive runtime `Option` checks in the scan bodies: **+1.18%** on
   6s167-class.  Fixed by const-generic `MIRROR` (off-path `scan`
   instantiations are size-identical to baseline: 0x52c/0x50a bytes).
2. The mirror branch outlined `WatchLists::add`/`remove_clause` out of
   their inlined callers (+2%/+5% samples on si2/worker): `#[inline]`/
   `#[inline(always)]` restored inlining (documented as load-bearing).
3. The rebuild fill paid a dead mirror branch per entry while the shadow
   is detached: `push_only` removed it.
4. **Residual, accepted and recorded**: +0.55% (si2), +0.66% (6s167),
   +1.46% (worker_550) instructions, deterministic, with **no hot spot**
   — the high-resolution `perf diff` attributes worker's delta to
   `main`/`dimacs_to_lit`/`quicksort` (untouched code), which the canary
   shows pure layout cannot explain.  Primary screen metric (conflicts)
   is bit-identical; the residual is an open attribution item for the
   slice-4 reader switch, where the `Vec` side is dropped and the cost
   profile inverts.  Do not re-litigate without the canary control.

## Traps hit this round (additions to the handoff's list)

- **Wall-clock A/B under concurrent agents is void** (load 40-60 on 20
  cores moved the *baseline itself* 0.84→1.29 s between runs).  Use pinned-
  core instruction counts with the canary control.
- The workspace suite's 14 failures are all `[corpus-missing]` panics —
  `smt-lib/` is absent from this machine's disk entirely (fails identically
  at the baseline commit).  `NIXIE_CORPUS_MISSING=skip` trips the meta-test
  guarding silent skips; the right check is "all failures are corpus-
  missing".

## Next session (unchanged from the kickoff, now unblocked)

Slice 4: switch all readers to the combined view (`get`, `len`, subsume
candidate scans, `as_mut_ptr` consumers), drop the `Vec` lists — the drift
machinery landed here is exactly the maintenance the CSR needs to be the
primary.  Then slice 5: ELS rewatching on CSR (the 2026-09-12 surgery
design verbatim) A/B'd against memcpy-rebuild on the si2 class.

Runners: `outputs/csr_slice2_corpus_check.py` (three-arm corpus check +
drift), `outputs/csr_slice2_ab_serial.py` (serial wall A/B — only under
quiescent load).

## Slice 4/5 entry point: design, economics, and the safety-net handoff (2026-09-14 close)

**The dual-write cost, measured** (`perf stat` instructions, pinned
core, profile-perf build at `8a91386c`): flag-ON vs flag-OFF —
6s167 +27.3 %, si2 +23.1 %.  Decomposition: the flag carries two pure
diagnostics that production would not pay — the fresh two-sweep build
and the drifted comparison per rebuild (6s167: 37 rebuilds × ~0.3 ms ≈
2 % of run; si2: 14 × 12–18 ms ≈ 16 %), leaving a **true mirror cost
of ~25 % (6s167) / ~8 % (si2)**.  Slice 4's instruction-level
economics are therefore not clearly positive by themselves: it trades
the Vec-side work (mem::take/put-back per literal, pushes, the rebuild
fill, the Vec-of-Vecs churn) against a similar amount of CSR-side
work.  Its wins are **memory** (the ~2.6 M per-literal Vec headers and
slack on si2-class, the transient clone in snapshots) and — the real
prize — **unlocking slice 5** (ELS rewatching surgery, the ~5.3 %
watch-rebuild half plus the surgery design space).  The migration
should be justified on those, not on raw instruction counts.

**Slice 4 decomposition** (each step keeps the full net; land green or
not at all):

1. *Read switch* (`NIXIE_CSR_READ=1`, diagnostic-gated while the drift
   net still exists): `get`/`len`/`count` consumers move to a
   two-span combined-view API.  ~50 sites (16 in propagate.rs alone)
   plus nixie-solver's watched_propagator/propagation_opt consumers.
   Unconditional read-switch alone would make the mirror cost default
   (a measured regression) — hence the gate.
2. *BCP span switch*: the kernels' `&mut [Watcher]` + take/put-back
   become two-segment scans — the slice-2 mirror's `pw`/`ow`
   segment logic IS the design (it already tracks exactly what each
   segment's write cursor must do); `entries`-span borrows split
   cleanly from `overflow`/`prim_end` field borrows, so no take/put-
   back is needed at all.
3. *The flip* (one commit): CSR becomes the only representation,
   Vecs deleted, drift comparison retired — **the safety net
   disappears exactly when it is needed**, so the gate is full
   trajectory identity against the pre-flip binary (conflicts/
   decisions/propagations bit-identical) + the corpus screen + Z3
   parity, and the E2E model/proof checks.

**Slice 5 can start BEFORE slice 4 — inside the shadow** (this is the
load-bearing realization): implement the ELS rewatching surgery on the
shadow CSR (surgical span updates for the clauses ELS touched) while
the Vec side still runs its rebuild.  The per-rebuild drifted
comparison then becomes an **exact equivalence oracle**: drift=0 ⟺
the surgery produced precisely what the rebuild would have.  Develop
and prove the surgery with the net up; only the *payoff* (deleting the
rebuild) waits for slice 4.

## Slice 5 started inside the shadow: the oracle works, and it found the
real blocker — watch-position drift (`NIXIE_ELS_CSR_SURGERY=1`)

The ELS-rewatching surgery was implemented on the shadow CSR (the
design above): surgical hooks re-point the CSR's watchers at every
clause mutation — the ELS rewrite loop's shrink, BVE's central
`elim_retire_clause_lits` / `elim_shrink_clause` / resolvent arming,
and the general `retire_clause` — while the `Vec` side still rebuilds
wholesale as ground truth.  The rebuild runs a **contract oracle** on
the detached surgical state: every live long clause must keep exactly
two watchers, every dead/binary clause none (`csr_surgery_contract_audit`;
the rebuild's re-normalization of untouched clauses to stored literal
order is churn the surgery deliberately does not reproduce, so
literal-granularity comparison is the wrong bar — the oracle design
went through three refinements to learn that: (ref, blocker) multisets
fail on blocker drift, ref multisets fail on the rebuild's
re-normalization, the per-clause contract is the invariant that
matters).

**Findings, in order:**

1. *The hooks' coverage is complete and their pair-tracking is exact
   where pairs are normalized*: BVE-round rebuilds audit clean
   (wrong-count 0, stale ≈ 0-100 of ~700 k entries).
2. *The blocker is watch-position drift*: ELS rounds that follow a
   search interval fail the audit massively — si2 `@6003` after 4 k
   conflicts of drift: **158 465 live clauses with wrong watcher
   counts** (entries 1.1 M vs ~700 k — pair-assumed removals miss the
   actual watch positions, then fresh adds pile duplicates); 6s167
   shows the same shape (7-11 k wrong-count at ELS rounds, 0 at
   adjacent BVE rounds).  During search the BCP moves watches and only
   re-normalizes *visited* clauses' stored order, so the assumption
   "watched pair == (lits[0], lits[1])" decays for unvisited clauses —
   exactly the normalization problem that sank the 2026-09-12 `Vec`
   surgery, now measured precisely on the CSR.

**The named next step for slice 5**: a ref → watched-positions index.
The dual-write machinery already observes every position change (scan
moves, repairs, attaches, removals), so maintaining the index there is
natural; the surgery's removals then key on actual positions instead
of assumed pairs.  The index's maintenance cost vs the rebuild's
arena sweep is the real slice-5 economics — measure it before
building the production surgery.  (The experiment ships default-off
and the default path is bit-identical: 6s167 33 028 conflicts
re-verified.)

## The position index landed — exact through real drift; the surgery's
remaining mystery localized (same day, second increment)

**Landed**: `CsrWatchLists::positions` — a ref → watched-literal-codes
index (BTreeMap, deterministic) maintained by the same funnels as the
entries (`push_overflow`, `remove_clause`, the scan notifications with
their leaving ref, `relocate` rekeying, `adopt_layout` rebuild,
`clear_all`).  **Validated**: `csr_index_audit` reports 0 missing / 0
stale positions out of 351 k refs through si2's real drift — the
dual-write machinery observes every position change, exactly as
designed.  The index-driven surgical removal
(`csr_surgery_remove_clause`) replaces the pair-assumed one.

**Two defects the nets caught** (both fixed): the relocate rekey called
`live_identity` on lingering dead entries — a panic the compaction
test caught; HashMap iteration order made `WatchLists`'s Debug output
nondeterministic — the kernel-equivalence test caught it (BTreeMap).

**The experiment's shape lesson**: CSR-only surgical edits desync the
dual-write mirror — any later scan of a diverged literal trips the
precondition and *suspends the mirror for that scan* (the one-time
warning is easy to miss; a backtrace probe is now wired at the site).
The BVE-path hooks (retire/strengthen/resolvent-arming inside
elimination rounds) are therefore **removed** — BVE's inter-round
propagations scan diverged lists.  The surgery is now confined to the
**ELS rewrite-loop window** (`els_surgery_window`), which is scan-free
from edits to the re-adopting rebuild.  Result: BVE-round audits are
clean (live-with-wrong-count 0–1).

**Remaining mystery (next session's entry)**: the ELS round itself
still fails its audit (158 k wrong-count at si2 `@6003`) with one
precondition violation immediately before it — the symbolized
backtrace points at `sweep_equivalence_candidates → sweep_assign_unit →
propagate` — i.e. a scan fires somewhere around the ELS window despite
the loop being scan-free by construction.  Prime suspects: the
pre-search ELS fixpoint loop's between-round activity
(`mod.rs:4181ff`), or the mid-search caller interleaving sweep at the
same boundary.  The probe set (entry counters, index audit, contract
audit, backtrace gate) is all in place to pin it quickly.

## The surgery is CORRECT — the mystery solved and the contract oracle
green end-to-end (same day, third increment)

The ELS-round failure's root cause: **two un-windowed hook leaks**.  The
central `retire_clause` hook and BVE's `elim_retire_clause_lits` hook
still gated on the env flag (`csr_surgery_on`) instead of the scan-free
window — so every retirement during BVE rounds, subsume, vivify,
probing *and the pre-search sweep* surgically edited the CS mid-drift,
the next scan of a diverged literal tripped `begin_scan`'s precondition
and **suspended the mirror for that scan** — and the suspension
compounded silently (the warning prints once per process; the
symbolized-backtrace probe at the site is what localized it: the first
violation fires in the pre-search `sweep_round` propagate, before any
ELS round).  Both hooks are now window-gated (the BVE one removed
outright — BVE never runs inside the window).

**Result — the experiment's question is answered**: with the leaks
fixed,

- `live-with-wrong-count = 0` at **every** contract audit across the
  whole si2 solve AND 6s167 (whose audits also show
  `stale-on-dead-or-short = 0`): every live long clause keeps exactly
  two watchers through index-driven surgical re-pointing plus real
  search drift;
- trajectories are bit-identical with surgery on (si2 23 527/11 121
  conflicts — the CS-only edits cannot perturb the search, verified);
  the residual `stale-on-dead` entries on si2 (400-2 000 per rebuild)
  are lazy-removal semantics — identical to what the `Vec` itself
  carries for un-hooked retire paths between rebuilds.

**Slice 5's correctness is proven inside the shadow.**  What remains is
purely economic and structural: the production surgery needs slice 4
(the CSR as the only representation — the surgery then replaces the
rebuild's watch half outright), and the cost model to beat is the
touched-mass × span-scan vs the rebuild's arena sweep (the ops counters
and entry counters landed here are the measurement instruments).

## Slice 5 economics, measured: batched surgery is a wash on mass
rewrites, a 46× win on sparse rounds (same day, fourth increment)

Instrumentation (`csr_surgery_visits`/`csr_surgery_nanos` in the oracle
line, against the same round's two-sweep `build=`us — the post-slice-4
watch-rebuild cost):

- **Per-ref removal (the first shape): 3–4× LOSS** on si2's mid-search
  ELS rounds (525 ms vs 141 ms at `@4000`; 1.6 B entry visits).  Root
  cause: ELS re-points every clause to its two *smallest-code* literals
  — the densest lists in the formula (~1 800 entries) — and a span scan
  per ref pays O(refs × span).
- **The cure, measured feasible then built**: primary spans are
  *strictly sorted by ref byte-offset* (verified 100 % of spans across
  all rounds — the fill pushes in clause-id order, arena offsets
  allocate monotonically, compaction preserves order), and better, the
  removals can be **batched by literal**: collect `(ref, positions)`
  from the index during the window, then one filtered pass per
  *distinct* touched literal.  The batch collapsed the visits 1.6 B →
  0.7 M (2 300×) and the time 525 → 129 ms.  One ordering bug the
  oracle caught immediately: re-points must **defer their adds** until
  after the removal flush (a re-point onto a literal the clause already
  watches would have its fresh entry deleted by the batch) — fixed, all
  audits green again.
- **The verdict table** (si2, batched surgery vs two-sweep build):

  | round | surgery | build | ratio |
  |---|---|---|---|
  | `@0` (pre-search, sparse) | 2.5 ms | 116 ms | **0.02 (46× win)** |
  | `@4000`–`@20939` (mass ELS rewrites) | 80–129 ms | 64–112 ms | 0.96–1.37 (wash) |

  On whole-formula rewrites the touched-literal mass *is* the whole
  watch content, so the surgery's span passes and the rebuild's two
  arena sweeps are the same work by construction — the wash is
  structural, not tunable.  The sparse regime (subsume/BVE-class
  rounds — ~8 of si2's 14 rebuilds) is where surgical re-pointing
  pays, and it pays 46×.

**Slice 5 closes with a complete measured map**: correctness proven
(contract oracle green end-to-end), the production shape identified
(batched-by-literal removal via the position index, deferred adds), and
the economics bounded (wash on ELS, 46× on sparse mutators).  The
payoff path runs through slice 4 (CSR-primary): wire the batched
surgery into the sparse-mutator rebuilds (subsume/BVA/BVE rounds), keep
the counting-sort rebuild for mass rewrites (ELS), and the ~5 % si2
watch-rebuild cost splits into its efficient halves.

## Slice 4 implementation plan: the CSR-primary flip, via the
swapped-dual gate (2026-09-14 close — the next session's entry point)

**Methodology** (the one that carried slices 2/3, the index and the
surgery): develop inside the shadow with the drift comparison as the
oracle, gated by a flag; the flip deletes the old side only after the
gate is green corpus-wide.

**The crux is the BCP scan, and the swap design is now concrete**
(`NIXIE_CSR_SCAN=1`, requires the shadow): today's dual-write scans the
taken `Vec` and mirrors into the CSR; the swapped-dual scans the CSR
and mirrors into the taken `Vec`.  Per propagated literal `L`:

1. Split-borrow the CSR: `span: &mut [Watcher]` (`entries[start..
   prim_end[code]]` — contiguous, the kernels' existing `&mut
   [Watcher]` shape), `overflow_dests: &mut Vec<Vec<Watcher>>`, and the
   bookkeeping fields — disjoint-field borrows, no take needed for the
   span.
2. `mem::take(&mut overflow_dests[code])` (the overflow *is* a movable
   `Vec`); `mem::take(&mut watches[code])` (the Vec-mirror target).
3. Run `scan_list` **twice** — span pass then overflow pass — with the
   push funnel (`push_watch`) writing **both** the destination
   overflows and the destination `Vec` lists, and a `VecScanMirror`
   receiving keep/remove notifications to rebuild the taken list (kept
   entries in order + unvisited tail — order-isomorphic to the old
   in-place compaction by the drift invariant; the mirror over-writes
   where the old scan skipped self-writes, an accepted gated-mode
   cost).  The kernels' notification sites gain a mode: the existing
   `csr` mirror param becomes the *scan target selector* (off / csr-
   mirror / vec-mirror) — const-generic MODE, three instantiations.
4. Put-backs: the span's compaction end becomes `prim_end[code]`; the
   taken overflow returns truncated; the taken `Vec` list returns at
   the mirror's length; the index maintenance rides the existing
   `scan_push`/`scan_remove` funnels (they are already the production
   semantics).
5. **Oracle**: the drift comparison stays valid — it compares the CSR
   (now primary-scanned) against the Vec (now mirrored) — and the
   phantom/ghost tick charging moves verbatim (it reads lengths:
   `span_len + overflow_len`).

**Reader inventory (measured)**: ~25 sites — propagate.rs ×11 (9 are
the take/put-back scan + ticks), watched.rs-internal ×10, xor/sweep/
watch_kernel/equiv ×4 — plus nixie-solver's watched_propagator/
propagation_opt consumers (verify: their own lists vs ours) and the
`get_mut` pair (267/632 — the non-session scan, same span-switch
treatment; 1047 is test code).  The two-span read API
(`get_combined(lit) -> (&[Watcher], &[Watcher])`) switches them
mechanically; `len` = `span_len + overflow_len` (phantom parity already
documented).

**Gate sequence**: (a) swapped-dual green on the corpus (drift zero,
trajectory identity, all four driver configs), (b) readers switched
under `NIXIE_CSR_READ=1` (still dual-maintained — reads from CSR),
(c) **the flip** — one commit: delete the `Vec` lists and the Vec
mirror, CSR becomes the only representation; the safety net dies at
this commit, so its gates are full trajectory identity + corpus screen
+ Z3 parity + the E2E model checks.  Post-flip, wire the batched
surgery into the sparse-mutator rebuilds (the 46× regime) and keep the
counting-sort rebuild for mass rewrites.

**Cost anchors (all measured this session)**: flag-off dual-write
residual +0.55–1.46 % instructions; shadow-on dual cost +23–27 %
(diagnostics ≈ 2/16 %); surgery 46×/wash.  The flip's business case is
memory (the ~2.6 M `Vec` headers on si2-class) + the sparse-rebuild
payoff + the surgery design space — not raw instruction counts.

## Slice 4's crux LANDED: the swapped-dual scan (`NIXIE_CSR_SCAN=1`)

The BCP session kernel now scans the CSR's span+overflow as the
**primary** with the taken `Vec` list as the **mirror** — the roles of
slice 2 exchanged, exactly per the plan above.  Mechanics: the span is
copied out per scan (avg ~34 entries — keeps the kernel's CSR accesses
alias-free), scanned with the unchanged cursor kernel, written home
with its live end committed; the overflow is taken and scanned second;
a `VecScanMirror` (write-cursor over the taken list) reproduces the old
in-place `Vec` compaction from the notifications, consuming both passes
sequentially (the combined order the drift invariant maintains); pushes
funnel to both representations (`scan_push` is direction-agnostic).

Three defects the nets caught on the way (each a one-fix
localization): the conflict path truncated the unvisited overflow
(every conflict-path scan wiped that literal's CSR); two of the six
notification sites silently missed their mirror branches (fmt had
reformatted the anchors — the per-scan cross-check probe caught the
misalignment in one run); and the two-pass work-counter merge
overwrote instead of accumulating (`take_watch_scan`).  The
kernel-equivalence test now compares combined views under the CSR
diagnostic flags (dead tails beyond `prim_end` are representation
garbage, not observables — the drift oracle is the invariant).

**Validated**: 6s167/si2/FmlaEquivChain/circuit/af-synthesis —
conflicts/decisions/propagations/restarts **bit-identical** to default,
drift comparisons 100 % zero (37/37, 29/29, 101/101, 85/85, 33/33),
1092 tests green under shadow-only, shadow+scan, and
shadow+scan+surgery configs.  The flip's remaining surface: the same
treatment for the non-session take/put-back path, the reader switch
(~25 sites), then the deletion commit.

## The reader gate landed — all three pre-flip gates stack (`NIXIE_CSR_READ=1`)

`NIXIE_CSR_READ=1` (shadow required): production readers iterate the
CSR combined view (`get_combined` / `iter_combined` /
`csr_read_active` — the predicate also requires an adopted shadow, the
pre-first-rebuild window has none; two diagnostics caught exactly
that).  The reader surface turned out to be **four production sites**
(the sweep environment scan, the regions emptiness probe, the legacy
loop's two repair-dedup reads) — the kickoff's "16 len / 13 get"
counted scan machinery and internal API; nixie-solver's `watches` are
its own theory-layer maps, untouched by the flip.

**The stacked validation** (shadow + swapped-scan + CSR-read): 6s167 /
si2 / x9-08075 — conflicts **bit-identical** (33 028 / 23 527 /
641 631) with drift 37/37, 29/29, 97/97 zero; 1092 tests green in both
flag-off and fully-stacked configs; clippy clean; default unchanged.

**The flip is now one commit away**, with every surface pre-proven:
session scan (swapped ✓), non-session scan (csr-mirror keeps the CSR
correct; its direct-scan conversion is the flip's only new scan code,
in the validated copy/two-pass shape), readers ✓, writers (CSR forms
exist: `push_overflow`, `remove_clause`, `relocate`, `adopt_layout`,
snapshot/restore).  The flip: force the CSR always-on, convert the
non-session take/put-back, delete `watches: Vec<Vec<Watcher>>` + the
mirror machinery + the VecScanMirror + the drift oracle itself; gates =
full trajectory identity + corpus screen + Z3 parity + E2E model
checks.  Post-flip: wire the batched surgery into the sparse-mutator
rebuilds (the 46× regime).
