# The BVE-after-fold skip policy — implemented, pinned, and the flip it guarded is refused (2026-09-21)

Item 2 of `docs/handovers/2026-09-21-sat-next-three.md`.  The short
version: **the premise moved**.  On today's tree the armed fold stack is
net-positive on the motivating instance and BVE no longer re-entangles
it — but the corpus-wide powered experiment refuses the default flip
(geomean 1.11× conflicts, regressions to 2.01×).  The policy lands as
the standing opt-in guard (default-off, bit-identical), with its
live-value dependency recorded: **gate-based subsumption (item 3)
raising the fold's retirement ratio is what would arm it.**

## The landscape shift (measured on bv_ILA, current tree)

The 2026-09-18 study's arms, re-run on the 2026-09-21 tree
(`8d34ea72`+):

| arm | conflicts (study, 2026-09-18) | conflicts (today) |
|---|---|---|
| default | 302,978 | **16,023** |
| fold (`NIXIE_SSR_BIN=1 NIXIE_ELS_PRESEARCH=1`) | 354,947 (net-negative) | **8,098** (2× win) |
| fold + `NIXIE_SAT_BVE=0` | 155,417–172,203 | 10,357 (**worse** than fold) |

The "36M-resolution phase-1 elim destroys the fold" interaction is
**gone** — eliminating after the fold is now the *better* order on the
motivating instance.  The default arm itself improved 19× (other arcs'
landings), and the composition flipped from net-negative to a 2× win.
Consequence: the skip policy never fires on bv_ILA today — the fold
retires < 25% of originals there (phase 1 runs, `NIXIE_LOG_ELIM`
confirms; orig=400,022 → live_orig=210,781 happens *inside* phase 1,
not in the fold).

## The powered experiment (the flip verdict)

10 seeds × the 12-cell standing corpus, deterministic conflict
geomeans, treatment = the armed fold stack vs default, verdict
agreement checked per cell/seed (zero mismatches):

| cell | armed/default |
|---|---|
| frb35-17-5_ext | **0.4908** |
| circuit_48in64out_800gates | 0.9570 |
| 6s299b685_Iter22 | 0.9421 |
| SCPC-500-13 | 0.9956 |
| b21 | 1.0078 |
| s38584 | 1.0194 |
| Carry_Bits_Fast_19 | **1.5901** |
| x9-07092 | **1.7670** |
| WS_500_16_90_70 | **2.0105** |
| GP_105 / 6s163 / 6s299b685 | 0-conflict load cells (n=0) |
| **geomean (9 cells)** | **≈ 1.11** |

The handover's bar — "no family regresses beyond the band" — fails
(three families regress 1.59–2.01×).  **The default stays off; the env
knobs stay** (the gate-dense family's 2× is real and opt-in).

## What landed

- `fold_orig_at_entry` / `fold_retired` recorded by the pre-search ELS
  arm (`NIXIE_ELS_PRESEARCH`); ratio gates `NIXIE_FOLD_BVE_SKIP=1`
  (threshold `NIXIE_FOLD_BVE_SKIP_PCT`, default 25 %).
- The skip **consumes** the phase-1 trigger — advancing `elim_phases`,
  clearing the mark set, syncing `last_elim_fixed` and `lim_elim`
  (exactly a completed zero-yield phase's bookkeeping) — rather than
  returning false from `eliminating()`, which would re-fire the
  unconditional phase-1 branch on every conflict.  Subsequent phases
  still arm on genuinely new level-0 units or fresh marks (cadical
  subsequent-phase semantics).
- Five unit tests (`fold_bve_skip_tests.rs`): trigger consumption
  (phases/marks/limit/never-refire), below-threshold and unarmed
  control legs, zero-denominator guard, the arm's entry accounting
  (with the lucky-pre-solver reachability trap documented), and an
  end-to-end verdict screen.
- Test-knob plumbing (`test_knobs::set_fold_bve_skip`) — the crate
  denies `unsafe`, so no env mutation in tests.

## Why the policy code stays despite a refused flip

Its enabling condition (a fold that retires ≥ 25 % of originals) is
exactly what **gate-based subsumption (item 3)** would produce — kissat
subsumes 108,484 clauses = 44 % of tried through the repr-canonicalized
literals on this family.  If that port lands, fold+skip is the natural
composition to re-power.  Until then the policy is dormant opt-in
machinery with pinned semantics, the same posture as `NIXIE_CSR_B=1`.

## Traps

- **Lucky pre-solving answers toy fixtures before the ELS arm's
  block** — any unit test driving the pre-search arm must set
  `enable_lucky: false` (the all-true-satisfiable gate-twin anatomy is
  answered by the uniform guess in microseconds; the SSR tests' own
  fold assertions pass through the *mid-search* one-shot, not the
  pre-search block).
- **Re-measure the premise before powering the experiment.**  Two
  intervening arcs moved both arms of this study's motivating instance
  by 19×/44× and inverted the BVE interaction; the policy as specced
  (skip when the fold collapses) is aimed at a problem the tree no
  longer has.
