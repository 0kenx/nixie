# CSR commit-B rebuilt on the post-congruence tree: trajectory-identical, env-gated (2026-09-20)

Execution of the 2026-09-19 handover's open item 1 (the CSR-watches
migration — the load-wall campaign).  Entry state: flip-A had been
**gated back off** (`f5796de0`, 2026-09-16: the unconditionally attached
mirror cost 2.5-6× wall at identical counters), the default path was
pure `Vec<Vec<Watcher>>` again, and the deletion commit (B) sat parked
after five attempts with its divergence pinned to the kernel's
destination layer but never root-caused
(`docs/studies/2026-09-14-round13-commitb-rootcause.md`).

## What this session did

1. **Confirmed tree health at arc close**: perf gate PASS (1.013 vs the
   1710e125 pin = dc3c2f34's own known heuristic-landing delta; zero
   verdict mismatches); re-pinned BASELINE to dc3c2f34.
2. **Re-validated the A-world on the post-congruence tree** — mandatory:
   the congruence/factor landings (09-17→19) rewrote `equiv.rs` /
   `congruence.rs` (watch-touching code) *after* the last CSR validation
   (09-16).  si2 flag-off vs `NIXIE_CSR_SHADOW=1 NIXIE_CSR_SCAN=1`
   (swapped-dual): bit-identical `sat @ 25,930`, drift `mismatched=0`
   at every rebuild including the fold's doubled rebuilds.
3. **Rebuilt commit-B from scratch as `NIXIE_CSR_B=1`** — an env-gated
   mode on the landed tree rather than the preserved patch (which no
   longer applies: 9 files moved).  A and B are the **same binary**,
   eliminating compiler-layout confounds from every comparison.  The
   rebuild folds in, a priori, every asymmetry fix the parked attempts
   discovered, plus the take-semantics:
   - `scan_parts` **empties the span's live end** for the scan's
     duration (take semantics): a mid-scan self-dedup reads an empty
     combined view — exactly the old taken-`Vec` slot.  The kernel's
     const-`B` instantiation pushes and dedups straight into the CSR;
     the `Vec` side is dead weight whose lists stay empty (reads of it
     in this mode are bugs to flush out, not silent divergence).
   - `relocate_with_debt` (CSR-side ghost-tick charging — a missing
     charge diverges restart/stable schedules).
   - The kernel's dedup (`push_watch_unique`) reads the CSR's combined
     view; the session driver charges ticks from the pre-scan combined
     length (computed from the copied span + taken overflow).
   - The rebuild adopts the counting-sort CSR layout and skips the dead
     `Vec` fill; `add` skips the `Vec` half.
4. **Three real B-mode breakers found and fixed by the nets** (each a
   class the old patch's parked state also had, per its own notes):
   - `shadow_begin_scan` compared the CSR against **the dead Vec's
     length** and suspended the legacy-path mirror (the LRAT /
     lazy-HBR / reason-stats scans) — it now takes the scanned length
     as a parameter.  Symptom: 11 LRAT-test timeouts with
     `scan precondition violated ... combined 1 vs vec 0`.
   - The debug invariant `check_binary_registration` and
     `check_ref_consistency` read the dead Vecs — moved to combined
     view (`iter_combined` / `iter_combined_always`; identical content
     on every other mode).
   - `preprocessing_core::propagate_probe` read the dead Vecs —
     moved to `iter_combined`.
5. **Made the position index opt-in** (`maintain_index`, implied by
   `NIXIE_CSR_SHADOW` / `NIXIE_CSR_INDEX` / the surgery knob): its
   BTreeMap write per watcher-add measured **+24% whole-run
   instructions** in B mode — the `f5796de0` cost class.  Off by
   default in B.

## Evidence

- **Default path untouched**: perf gate conflicts/decisions **1.000**
  vs the dc3c2f34 pin; nixie-sat suite 1115/1115; clippy/fmt clean.
- **B mode**: si2 OFF = swapped-dual = commit-B at bit-identical
  **25,930** conflicts.  Suite under `NIXIE_CSR_B=1`: **1097/1115**
  — every soundness, LRAT/PR26 proof, reproducibility and differential
  test green; the 18 failures are uniformly dead-`Vec` test scaffolding
  (asserts through `get`/`get_mut` on lists that are empty by design in
  this mode; no production reader remains).
- **A/B corpus scan** (same binary, env-differenced): gate corpus +
  satcomp2024 + 170 decompressed satcomp2025 files, 90 s cap under
  load — **0 trajectory divergences on every completed cell**
  (44 bit-identical verdict+conflicts cells; 156 censored cells are
  both-arms-timeout hard instances plus B-cost censors).  The four
  A-solved/B-censored cells re-verified serially with a 600 s cap:
  **identical** (WS_500 376,277 / constraints_17 31,486 / b21 161,812
  / gm16spctrc 18,019).

## Interpretation — why this B is clean where the parked patch diverged

The honest caveat first: the historical divergence vehicle (6s167) is
**not on this disk** (the sc24f corpus was wiped from `precompile/`),
so the exact historical divergence cannot be re-run; the old A/B
numbers (33,028 vs 33,154) are irreproducible.  The claim is
therefore prospective, not retrospective: on the current tree, with
every documented asymmetry fixed up front — take-semantics on the
scanned span, the dedup on the combined view with correct mid-scan
emptiness, CSR-side ghost debt, `add` CSR-only, the legacy-path
mirror precondition on the scanned length, and the probe/invariant
readers on the combined view — the CSR-only mode is trajectory-neutral
on every input tried.

Reading the five parked attempts' evidence against this result, the
most probable historical culprit classes were exactly the ones fixed
here: the fourth attempt's "`add`'s Vec write is load-bearing" is the
corrupted-mirror feedback of a half-migrated world, not a semantic
need; the fifth attempt's combined-view ORDER divergence arose in a
`B′3` world whose `VecScanMirror` silently dropped keeps beyond the
dead list's length.  A single-shot flip with correct take-semantics
never enters those states.

## Cost accounting (measured, deterministic instruction counts)

- B with the index on: **+24%** (Carry_Bits, 8.08G → 10.04G).
- B with the index off: **+21%** (8.08G → 9.76G) — the residue is the
  per-scan `span.to_vec()` copy (alloc + memcpy of the whole span;
  watch-dense instances pay most) plus `Option` plumbing per
  notification.  The landing-time fix is the kickoff's split-borrow
  in-place span scan (`entries`-span borrows split cleanly from the
  overflow array — no copy at all); profiled hot spots confirm the
  copy dominates.

## The load-wall payoff is NOT yet claimed

`CsrWatchLists::overflow` is itself `Vec<Vec<Watcher>>` — before the
first rebuild every watch lives in a per-literal overflow `Vec`, so a
naive B boot reproduces the 18.7M-allocation storm on the CSR side.
The payoff needs **slice 6** (the bulk-load study's plan): the CLI
bulk-attach path builds the CSR directly via `CsrWatchBuild`
(count → layout → fill from the flat stream) — zero per-literal
allocations at load.  That, plus the in-place span scan, is the next
session's slice; only then do the `14.normalised` / `GP_190` / hwmcc
load walls get measured and the `Vec<Vec<Watcher>>` field deleted.

## Next slices (in order)

1. Split-borrow in-place span scan (kills the +21% residue; the
   kernel takes `(&mut [Watcher], &mut Vec<Vec<Watcher>>)` pieces).
2. The load-path counting-sort build (slice 6) + measure the load
   wall on the 9.4M-var class.
3. The 18 dead-Vec test-scaffolding failures → combined-view asserts.
4. The flip commit: delete `watches: Vec<Vec<Watcher>>`, make B the
   only mode; gates = trajectory identity + corpus screen + Z3 parity
   + E2E model checks (the drift oracle retires with the `Vec`).

## Traps added

12. `git merge --ff-only` into the shared main aborts on *your own*
    dirty BASELINE re-pin (identical content is still "local changes")
    — commit the re-pin on main first, re-merge the branch, then ff.
13. Decompressing 170 sc25 files (30 GB) onto `/` fills the root
    filesystem (the box's `/` shares the build target's pressure) —
    decompress to `/media/data` or stream.
14. The scan runner's both-arms-timeout censors hide B-cost regressions
    — always serially re-verify every "A-solved/B-censored" cell at a
    raised cap before counting it clean.
