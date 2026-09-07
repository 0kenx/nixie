# Tier-3 BCP restructure: inline tagged binary watchers (built, measured, reverted)

**Date:** 2026-09-07
**Lever:** `docs/studies/2026-09-07-throughput-campaign.md` → Tier 3 (the one
structural rewrite left).
**Status:** COMPLETE — the arm was built in full, measured per this
pre-registration, failed both bars, and was reverted. Results and the
mechanism-level explanation below.

## The mechanism under test

Replace the two-pass BCP (per-literal BIG CSR scan, then watch-list scan)
with a **single-pass** scheme in the cadical shape: binary clauses become
ordinary watch entries carrying a tag, visited inline in the same list
scan.

* **Tagged entry** = the existing 12-byte `Watcher` with
  `r = BIN_TAG` (a `ClauseRef` sentinel), `clause = cid` (clean — every
  existing id comparison site is untouched), `blocker = the other
  literal`.  Width is unchanged on purpose: the 8-byte density variants
  are a separately measured-dead class (+0.7 % instructions, 0 cycles;
  `2026-08-watcher-8byte.md`), and this arm isolates the *structure*
  (one pass, no CSR probe, no second loop) from *density*.
* **Binary visit**: blocker check above (unchanged); on miss (blocker not
  true) the entry is unit-or-conflicting with **zero arena deref**:
  `v(blocker) < 0` → conflict via `cid`; `v == 0` → assign `blocker`
  with reason `cid`.  No swap, no replacement scan (a binary has no
  replacement literal).
* **The BIG stays** — transred, ELS, AND-gate/factor, probing read it;
  only `propagate()` stops consulting it.  Attach/rebuild maintain both.
* **Ticks** in inline mode count real entries
  (`1 + ceil(8·len/128)`, no phantom) — exactly what the phantom
  machinery emulated; the mode is a different trajectory by construction
  (binary visits interleave with large visits in list order instead of
  BIG-first), which is why the primary metric below is work-matched, not
  trajectory-paired.

**Arm selector:** `NIXIE_BCP_INLINE_BINS=1` (read once at solver
construction; default off = current two-pass BIG-authoritative BCP,
bit-identical to `main`).

## Why this is worth building despite the campaign's downgrade

The downgrade priced the merge as "adds a branch to 100 % of visits"
against a 15–25 % estimate.  But the tagged-entry form does **not** add a
per-visit branch in the hot path for the default arm (no tagged entries
exist there), and in the inline arm the binary check rides the existing
blocker load: the marginal cost is the `r == BIN_TAG` compare only on the
miss path, against removing the per-literal CSR probe (2–3 loads), the
second loop setup, and the per-edge indexed loads.  The honest expected
effect, from the measured precedents: 1–3 % instructions; the *open*
question the arm actually tests is whether any of it converts to cycles
(the PGO result says instructions usually do not) and whether the
removed BIG fixed cost shows on the BIG-heavy anchors (worker-class,
where BIG edges/prop is far above 6s167's 1.37).

## Pre-registered measurement protocol

* **Primary (structure, work-matched):** paired binaries from the same
  commit, PMU `instructions` and `cycles`, pinned E-core (campaign
  harness rules: `taskset` outside `perf`, touch + md5sum the binaries),
  at **fixed conflict budgets** — 22-file corpus sample `MAXC=40000`,
  6s167 + crypto1 full solve, worker_550 `MAXC=30000` (the BIG-heavy
  anchor).
* **Bars (landing rule — this change adds a second propagate mode, i.e.
  real complexity, so it must clear, not tie):**
  land iff cycles geomean ≤ 0.99× AND instructions geomean ≤ 0.99× on the
  corpus sample, with no anchor slower than +1 % on cycles.
  Anything else → revert the arm, keep the study.
* **Sanity gates:** verdicts identical on every measured file; full
  workspace suite; the 20 k fuzz differential unaffected (mode off by
  default); Z3 parity canary green.
* **Trajectory:** none claimed — binary/large interleaving changes
  propagation order by construction; conflicts-to-verdict is reported for
  the record with the seed-chaos caveat and no causal claim.
* **Matched-null note:** the null for "binaries inline in list order"
  would be "binaries inline in BIG order" (section bookkeeping); that
  variant cannot be built without O(section) inserts on the watch-move
  path (19 M moves × bin-tail on worker-class), so the null is
  impractical — hence the fixed-work primary instead of a conflicts
  claim.

## Results (2026-09-07, paired binaries at pinned cpu10, fixed budgets)

**Verdict: NO-GO on both pre-registered prongs — the arm was reverted.**

Work-matched corpus pairs (both arms hit `MAXC=40000`, n=11):
instructions geomean **1.0055×**, cycles geomean **1.0106×** (bar: both
≤ 0.99×).  Anchor 6s167 (full solve, both decisive, 62 241 vs 69 295
conflicts): **+12.9 % instructions / +14.5 % cycles** (bar: no anchor
above +1 %).  Worst work-matched regressions: `ITC2021_Early_3` +11.6 %
instr / +32.0 % cycles; `summle_X4053` +4.6 % / +24.9 %.  Best:
`g2-slp-synthesis-aes` −5.9 % / −30.3 %, `mdp-28-14` −0.2 % / −4.3 %.

Raw CSV: `/tmp/paired_bcp2.csv` (copied into
`precompile/9ad050c/benchmark/bcp_inline_bins/`); verdicts identical on
every work-matched file.

### Why it loses (the mechanism, not the measurement)

Putting binaries INTO the watch lists lengthens every per-literal scan
by the binary degree (VISITS/prop rises from 17.4 by the BIG-edge rate,
1.37 on 6s167), and every miss-visit pays the new `is_binary` dispatch —
against a *saved* fixed cost of ~3 loads + a loop setup per propagated
literal.  At our watcher shape (blocker-in-watcher, 12 B) that trade is
negative on BIG-light instances and roughly neutral elsewhere — the
separate CSR pass was the better design, which is the same conclusion
the 2026-09 BIG-authoritative landing measured from the other direction.
This closes Tier 3's last open question the same way the campaign closed
the codegen half: **the two-pass BIG BCP is not where recoverable cost
lives**.

### Trajectory observations (recorded, no claim — chaos class)

Not work-matched, so they carry no causal weight, but they are large:
`worker_550` full solve **25 532 → 6 796 conflicts** under the inline
order (0.45× instructions to verdict); `crypto1` 29.4 M → 0.89 M
conflicts (0.017×).  Binary/large visit interleaving changes propagation
order, and on these two files the new trajectory was dramatically lucky.
A seeds campaign (≥5 × both arms) would be needed before claiming
anything; given the structure verdict above, the arm is not worth that
campaign in its current form — but the observation that *propagation
order alone* moves worker_550 by 3.7× is itself evidence for the
"search-paradigm, not rewrite" disposition of the factor-port study.

### Soundness work the arm surfaced (kept)

Building the arm found and fixed one real bug class before any
measurement: an inline-binary **conflict-path entry loss** (the
compaction slot was not written before the tail copy, silently deleting
the binary clause from its watch list — 51 invalid models in the
`mid_andgate` differential) and the stale-entry propagation hazard
(inprocessing tombstones binaries without a watcher sweep; the inline
miss path validated liveness against the DB).  Both lived only in the
arm and revert with it; the fuzz harness gained an env-gated
CNF-dump-on-invalid-model hook (`DUMP_INVALID=1`) that stays — it cut
this bisection from hours to minutes.

### What was reverted

`watched.rs` (`Watcher::binary`/`is_binary`, BIN_TAG), `memory.rs`
sentinel, the `bcp_inline_bins` field/env/attach/rebuild plumbing, the
propagate gate + fast path, the mode-conditional invariants, and the
lucky trace — all of it; `main`'s default path is untouched.  The study
and the fuzz hook are the landing.
