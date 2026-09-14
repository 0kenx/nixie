# SAT performance program — round-12 handoff (2026-09-14 close)

> Round-11's three items are ALL CLOSED.  Entry points:
> `docs/studies/2026-09-14-csr-dual-write-scan.md` (item 1),
> `docs/studies/2026-09-14-amplitude-trajectory-answer.md` (item 2),
> `docs/studies/2026-09-14-metric-decision.md` (item 3).

## Final addendum 2: slice 5's ECONOMICS measured (`ab5bc6ee`)

The batched-by-literal surgery (collect from the index, one filtered
pass per distinct literal, deferred adds) collapsed the per-ref 3–4×
loss to a **wash on mass ELS rewrites (0.96–1.37×)** and a **46× win on
the sparse pre-search round**.  Primary spans verified strictly sorted
by ref (100 %).  The measured map is complete: correctness proven,
production shape identified, economics bounded — the payoff path is
slice 4 (CSR-primary) + wiring the batched surgery into the
sparse-mutator rebuilds (subsume/BVA/BVE — 8 of si2's 14 rebuilds)
while keeping the counting-sort rebuild for mass rewrites.  Details in
the CSR study's fourth increment section.

## Final addendum: slice 5's CORRECTNESS is proven (`c31cf26c`)

The blocker dissolved under debugging: the 158 k-wrong-count audits
were two **un-windowed hook leaks** (the central `retire_clause` and
BVE's retire hook gated on the env flag, firing during BVE/subsume/
vivify/probing and the pre-search sweep — desyncing the mirror, whose
`begin_scan` precondition then silently suspended it; the one-shot
symbolized-backtrace probe at the site localized the first violation to
the pre-search `sweep_round` propagate).  With both window-gated, the
**contract oracle is green end-to-end**: `live-with-wrong-count = 0` at
every audit across whole si2 and 6s167 solves, through index-driven
surgical re-pointing plus real drift; trajectories bit-identical with
surgery on; the landed ref→positions index audits exact (0 missing /
0 stale of 351 k).  **What remains for slice 5 is economics only**
(touched-mass × span-scan vs the rebuild's arena sweep — the ops/entry
counters are the instruments) plus slice 4 (the CSR-primary flip that
lets the surgery replace the rebuild).  The prior "watch-position
drift" framing below is preserved as the finding that motivated the
index — the index is the cure and it works.

## Late addition (same day): slice 5 STARTED and hit its measured blocker

`3e9b2b51` + `bd06ae67`: the ELS CSR-surgery experiment landed
(`NIXIE_ELS_CSR_SURGERY=1`, default-off) — surgical watcher re-pointing
on the shadow at every clause mutation, with the rebuild's per-clause
**contract oracle** (live long ⟺ exactly two watchers) as the
equivalence net.  The oracle works and delivered the result: hooks are
complete and exact where pairs are normalized (BVE rounds audit clean),
but **watch-position drift** breaks pair-assumed removals after search
intervals (si2 ELS round: 158 k clauses wrong-counted) — the 2026-09-12
Vec-surgery normalization problem, now precisely measured on CSR.
**Slice 5's named prerequisite: a ref→watched-positions index maintained
by the dual-write hooks (they observe every position change); its
maintenance cost vs the rebuild's arena sweep is the economics to
measure before building the production surgery.**  See the appended
section in `2026-09-14-csr-dual-write-scan.md`.

## What closed this round

1. **CSR dual-write BCP scan landed** (`0e005231`, slices 2+3): the
   `CsrScanFrame` mirror maintains the CSR through all three scan bodies
   and every cold path; the per-rebuild **drifted-state comparison**
   reports `mismatched=0` corpus-wide on all four driver configs
   (session, reason-stats, bcp-stats, hyper-binary); trajectories
   bit-identical; const-generic `MIRROR` keeps the flag-off path free
   of CSR code (residual 0.55–1.46 % instruction overhead, canary-
   controlled, no hot spot — recorded open for the reader switch).
   Z3 parity 4.16.0: 176/177 correct, 0 disagreements.
   **Next: slice 4 (switch readers to the combined view, drop the Vecs),
   then slice 5 (ELS rewatching on CSR, A/B vs memcpy-rebuild).**
2. **The amplitude→trajectory question answered** (`e4a72db5`): the
   one-sided arm's losses are *carried-phase-state collapse*, not
   formula hardness — a fresh search on the arm's dumped formula is
   consistently EASIER (median ~540 k vs ~700 k+ conflicts); the
   default's 20–100× edge is phase state (phase-reset at the boundary:
   32 k → 314 k/840 k); the one-sided retirement removes exactly the
   pure-side region that state encodes (LBD doubles within 2 k
   conflicts of the resume).  cadical survives the same elimination at
   185 k because its aggressive rephase/walk cadence never leans on
   cross-elimination carry.  **The named lever for any future amplitude
   arm: package it with a state cadence the search tolerates — a JOINT
   schedule redesign (cadence + rephase policy), not another single-
   step swap (the clock matrix already falsified those).**
3. **The metric question settled** (`8d0f52e8`): the recorded
   "aggregate conflicts favors amplitude" numbers were survivorship
   bias — both-decided geomeans exclude the arms' timeout losses
   (21–30 arm-loss cells vs 3–6 arm-win cells per arm).  Under a
   censoring-aware mean log-ratio, every amplitude arm is costlier,
   including scaled (0.978 recorded → +0.082..+0.286 censored).
   **Decision: the 60 s solved-cells gate stays primary; the
   both-decided geomean is retired as a headline (report with exclusion
   accounting or use the censored score — reference implementation at
   `docs/studies/assets/amp-traj-2026-09-14/sc24f_censored_reanalysis.py`);
   300 s wide-cap stays the borderline tie-breaker, not a gate.**

## New infrastructure

- `NIXIE_DUMP_ELIM_PHASE=<n>` — dump the formula at any elimination
  phase entry (`dump_elim_state`, factored from the phase-1 dump).
- `NIXIE_ELIM_RESET_PHASES=<min-retired>` — reset phase tables at the
  elimination boundary (the ghost-attractor probe).
- `outputs/csr_slice2_corpus_check.py` (three-arm corpus + drift check),
  `outputs/csr_slice2_ab_serial.py` (serial wall A/B — quiescent load
  only); amp-traj runners under `docs/studies/assets/amp-traj-2026-09-14/`.
- Precompile: `0e005231` (CSR landing, certified), `8a91386c` (amp-traj
  diagnostics binary).  `107b7868` remains the standing default baseline.

## Traps added to the standing list

1. **Both-decided aggregates lie about censored arms** — any future
   screen summary must report decided-by-one cells or use the censored
   score (item 3's mechanism; it flipped a "best aggregate" claim).
2. **The one-sided arm's 60 s screen cells were never filed** (the
   non-hex sha bogus-tag trap) — its recorded 229→221/0.974 live only
   in the study text; re-measuring it means fresh cells under a valid
   tag.
3. **`smt-lib/` is absent from this machine's disk** — the workspace
   suite shows exactly 14 `[corpus-missing]` failures (all in
   nixie-solver corpus tests), fails identically at any commit, and
   `NIXIE_CORPUS_MISSING=skip` trips the meta-test.  The correct gate
   read is "all failures are corpus-missing".  Corpora in worktrees:
   symlink per the test's own instructions.
4. **The ff agent's landed code (03732576/75b3977b) breaks workspace
   clippy (8 errors) and strict doc (2 errors) on main** — pre-existing,
   in nixie-core/nixie-math; it also MASKED nixie-sat lint failures in
   the round-11 gate run (fixed after the fact in `e4a72db5` — always
   grep clippy output for your own crate's paths when upstream fails).
5. **/tmp and the root disk run full under concurrent agents** (this
   round: 100 % on /tmp from other agents' worktrees, 95 % on
   /media/data from accumulated private target dirs).  Use
   `TMPDIR=/media/data/...` for builds and delete private target dirs
   the moment their binaries are in `precompile/`.

## Standing items (unchanged)

- The workspace is shared: private paths, clean worktrees, revert by
  explicit sha, never stash.
- `NIXIE_ELIM_ONESIDED` (and the other five arms) stand as measured
  default-off infrastructure; per item 2's answer, reviving any of them
  requires the joint state-cadence redesign, not re-arming.
- CSR slices 4–5 are the open engineering arc, with the dual-write
  machinery now validated and the drift comparison as the safety net.
