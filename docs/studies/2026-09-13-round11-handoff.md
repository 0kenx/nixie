# SAT performance program — round-11 handoff (2026-09-13 close)

> Entry point for the next agent.  Full detail in
> `docs/studies/2026-09-13-*.md` (start with
> `2026-09-13-elim-bound-growth.md` — nine measured follow-ups — then
> `2026-09-13-csr-watches-kickoff.md`, `2026-09-13-extstack-reconstruction.md`,
> `2026-09-13-widecap-portfolio.md`).  Everything below assumes the
> discipline of `AGENTS.md` + `docs/BENCHMARKING.md`.

Round-10's three items all ran to measured conclusions, plus one
unscheduled soundness fix that the screens themselves surfaced.  In
priority order:

## 1. CSR watch lists: the dual-write BCP scan (the engineering centerpiece)

Economics validated by profile: the ELS cluster is **~12 % of si2-class
wall** (rebuild 5.3 %, substitute 5.0 %, refresh 2.0 %), so the
incremental-surgery payoff (~2-3 %) is real.  Landed so far:
`CsrWatchBuild` (count→layout→fill, validated equal-and-ordered at
every rebuild), `CsrWatchLists` (the four mutation ops, unit-tested),
and the **slice-plan correction** discovered the hard way: survivors'
blockers are rewritten in place during the scan
(`entry.keep(Some(blocker))`), so a moves-only shadow sink is
insufficient — maintaining the shadow through the scan *is* slice 3
implemented as a **dual write** (a parallel write cursor over the CSR
span mirroring keep/remove/moves; `list_kernel.rs` 277 lines +
`watch_cursor.rs` 230).  Order: dual-write scan → cold-path mutations →
reader switch/drop the Vecs → ELS rewatching (the 2026-09-12 study's
surgery design carries over verbatim).  Trajectory-identity + screen
bar per slice.

## 2. The amplitude→trajectory translation (the research question)

The elimination-amplitude program closed at its root: **the phase-1
yield gap was one-sided variables** — cadical eliminates them inside
BVE (`elim_resolvents_are_bounded` returns `lim.elimbound >= 0`), our
port skipped them.  Armed as `NIXIE_ELIM_ONESIDED` (default-off):
Timetable round 1 goes 74 757 → 91 788 (cadical parity restored) and
the corpus conflicts geomean hits **0.974 — the best aggregate of any
elimination variant tried**.  But: the 60 s screen loses 8 cap cells,
the 300 s re-run shows those were artifacts yet the arm is only
cell-equal there — **and Timetable itself times out under the arm**.
The open question: why does a 17 k-variable-richer elimination slow
the search?  Candidate angles: the formula-shape interaction with
restarts/phase-saving (all tuned on the old elimination), the
occurrence-list mass the extra retirements leave behind, or the
learned-clause quality over a faster-shrinking formula.

## 3. The metric question (program level)

The 60 s mini-bench cap anti-correlates with elimination amplitude
**five independent ways** (indexed schedule −20, scaled clock −24,
combo −15, live occ-gate: mp1 destroyed, one-sided −8) while the
aggregate-conflicts direction favors every amplitude arm (0.968-0.974).
The wide-cap study showed default@300 s converts 12/13 of the "hard"
class by itself.  Whether the standing screen's 60 s cap is the right
acceptance metric for elimination work — or a 120/300 s standard
should gate defaults — is a methodology decision worth settling before
more amplitude work.

## Standing items

- **Baseline cells**: `precompile/107b7868` is the valid default
  (bit-identical default path confirmed through `3036fe32`; re-certified
  8/8 paired counters).  `8082e335` is historical.  `32c88866`/`3036fe32`
  binaries are default-identical; their cell sets exist under their own
  shas.
- **The workspace is shared.**  This session lost a /tmp worktree to
  another agent's cleanup and hit concurrent-build collisions twice:
  use private paths (`outputs/`, `CARGO_TARGET_DIR=...`) and clean
  worktrees for verification.  `git revert HEAD` once reverted the
  wrong commit (another agent landed between) — **revert by explicit
  sha**.
- The shared-tree clippy is intermittently blocked by other agents'
  in-flight files (mbqi/model_checker.rs this round); verify from a
  clean worktree (recipe in `2026-09-12-elim-subfix.md`).

## Infrastructure you inherit

- **Arms** (all default-off = bit-identical, all soundness-netted):
  `NIXIE_OTFS`, `NIXIE_EAGER_SUB`, `NIXIE_AND_GATES`, `NIXIE_TIERED`,
  `NIXIE_ELIM_SUBFIX` (now both pre-phase and inter-round fixpoint
  slots), `NIXIE_ELIM_ONESIDED` — plus the earlier restart-family arms.
- **Elimination diagnostics** (`NIXIE_LOG_ELIM`): the phase line carries
  `marks= bound=`; the round line `added= bw_retired= otf_shrunk=
  tried= remain=`; the inter-round line `residue_old= residue_fresh=`.
  `NIXIE_LOG_ELIMDTL` traces every per-variable decision with per-pair
  class counts.  `NIXIE_DUMP_ELIM_ENTRY` dumps the formula at the first
  elimination phase (the controlled-differential tool that found the
  root cause).
- **Logging cadical** (per-var LOG traces; LOG gates on `--log=true`,
  *not* verbose): `cp -r ../temp/cadical/{src,scripts,contrib,
  configure,test,LICENSE,README*,makefile*,VERSION} <private-dir>/ &&
  ./configure -l && make` — the reference tree stays untouched.
- **CSR shadow** (`NIXIE_CSR_SHADOW`): per-rebuild validation,
  mismatched=0 across the corpus.
- **Screen runners** under `docs/studies/assets/inproc-amplitude-2026-09-12/`
  (incl. the 300 s wide-cap runner and the one-sided wide-cap check).

## Traps that cost real time this round

1. **cadical verbose=3 logging writes ~110 GB on Timetable and filled
   the root disk.**  Always pipe through `grep --line-buffered … |
   head -n N` — never to a raw file.
2. **benchstore rejects non-hex `git.sha_short`** — cells run under a
   bogus tag are silently unrecorded (the run log's printed verdicts
   are the fallback; parse them).
3. **Model-check failures are loud events, never silent downgrades.**
   The 2026-09-12 baseline hid 138 false-witness cells (and a 6.5 s
   solve of summle_X4053 s2!) behind downgraded unknowns — class
   definitions built on downgraded cells inherit the corruption.  The
   fixed binary verifies all of them (10/10 re-checked).
4. **`subsume_round`'s RandomSlice mode re-rolls the dirty set at every
   round's end** — any extra `subsume_round()` call (even zero-yield)
   diverges trajectories; nulls for schedule changes must control for
   it.
5. **/tmp is shared** — private scratch only, and expect concurrent
   agents' builds in the cargo target dir.
