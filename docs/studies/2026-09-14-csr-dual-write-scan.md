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
