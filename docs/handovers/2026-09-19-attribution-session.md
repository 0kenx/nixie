# Handoff: after the attribution session — the false-`sat` found by the new SHAPES is closed, the gap re-baselined, what remains (2026-09-19)

**Read `AGENTS.md` first.** This succeeds
`docs/handovers/2026-09-19-wide-lp-post-landing.md` (executed this
session). The session's full record, with the probe evidence and the
per-item analysis, is
`docs/studies/2026-09-19-gap-attribution-fi1.md` — where they disagree,
the study wins. Landed as `7ab21fb5` (binary
`precompile/7ab21fb5/nixie`, plus a `nixie-debug` for the sweep).

## What this session changed

1. **A live false `sat`, closed at the root** — the B&B leaf's
   feasibility `check()` re-optimizes onto a different vertex than the
   integrality scan read; acceptance on feasibility alone published
   fractional-vertex models (the settled-atom gate arm cannot catch its
   own feed). Found by the new boundary SHAPES on their first fresh-seed
   run; the leaf (and the dive's base case) now re-scan integrality at
   the re-solved vertex. Reproducer pinned never-`sat` in
   `arith_wide_literal_regressions.rs`.
2. **The residual gap re-attributed** (the item-67 recipe, ~75
   `NIXIE_GAP_PROBE` tags, `gap_survey.py` now captures decline stderr
   per member — re-attribution is one command now): 47 members = 27
   sticky resource-exhaustion (7 `find_wide_pivot_col` NOCOL storms, 20
   B&B depth divergence), 9 parse-gate, 5 blocking-nongenuine, 3 BV
   minting, 3 big-const uncertified, **MBQI zero**. One machine: search
   capacity over div/mod-structured LIA at wide constants.
3. **fi1 decoded** (still honest `unknown`, z3 `sat` at `xi=5, yi=2^62`):
   the free `/7` div-slack's zero-split walks an unbounded ray — up-
   branches refute, down-branches descend one level forever — and the
   cuts cannot see the mod-7 lattice (item 55's honest unmarking of
   rescaled rows). The study's §B lists the three candidate levers in
   promise order.
4. **`eval_linear` exact** (the last unchecked narrow accumulation in
   the evaluator's periphery), **boundary-literal SHAPES landed** in
   both fuzz generators (the fixed-seed survey re-baselines: **150
   members, 140 wall-literal** — the div/mod+beyond-width frontier;
   documented breakpoint, not a regression).

## What's next, in value order

1. **The wall-frontier capacity campaign** — the re-baselined survey's
   140 wall-literal members are one class: div/mod nesting under
   beyond-width witnesses. The levers (all heuristic-class: matched
   null, ≥10 seeds, no wall-clock): NOCOL repair eligibility, the B&B
   ray-walk branch signature (fi1's §B), real divisibility lemmas from
   the div/mod axiom rows (intern the mod-slack's `[0,d)` window at
   intern time).
2. **The bound-shadowing journal** — the design is sharpened to landing
   spec in the study's §F: the trail's full-clone undos are already
   pop-exact under LIFO; the journal's job is keep-the-tighter-live
   without losing the displaced bound's reason set. Do NOT land a
   decline without it.
3. **The model-blocking retry-succeeds fixture** stays open — 12
   hand shapes tried, all preempted by repairs/theories (study §E);
   the honest options are recorded there.
4. The wide-constant parity refutation (`2y + 4q = 2^62 − 3` — the
   Diophantine layer declines at `2^62`) would close the new
   regressions from `unknown` to `unsat`; capacity, not soundness.

## Process notes from this landing

* Two fresh-seed differential runs (six seeds total) around the merge;
  the FIRST found the false `sat`, the second validated the fix — the
  SHAPES paid for themselves before their landing commit existed.
* The full debug suite's DWARF is ~97 GB on a full workspace;
  `CARGO_PROFILE_DEV_DEBUG=0` keeps debug assertions at a fraction of
  the size — the linker bus-errors under disk-full are silent failures
  otherwise.
* The perf gate resolves `precompile/` relative to the CWD: symlink the
  primary's `precompile` into a worktree before running it there.
* `gap_survey.py`'s stderr capture + `NIXIE_GAP_PROBE=1` on any binary
  reproduces the attribution table in one run — keep the tags' output
  stable if touching decline sites.
