# Handoff: the arithmetic arc, item 96 — the A2 budget slice executed and closed as a negative result; the ray class named for the branch channel (2026-09-20)

**Read `AGENTS.md` first — it is canonical.** This handoff executes
`docs/handovers/2026-09-19-arithmetic-arc-items86-95-handoff.md`'s open
list. The arc's memory is `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
(items 1–96; item 96 is this session — read it before touching
arithmetic). Where they disagree, the study wins.

## What this session did

Every open item of the predecessor handoff, in its priority order:

1. **A2 B&B budgets — measured DEAD (negative result, do not retry).**
   The class re-attributed at 76 members on `precompile/f6daed038/nixie`:
   51 J5 (big-const certify gate, no budget tags), **24 = the depth ray**
   (`lia:bnb-depth-budget`, entirely `LIA_MAX_DEPTH`; zero node-budget /
   dive / cut-round members), 1 simplex-rl. Dose-response (probe-only env
   knobs, never landed): depth 16 384 → still depth-tagged; depth 65 536 →
   flips to node-budget (the one-live-branch-per-level signature); depth
   65 536 + 300k nodes + 60 s → 20 `unknown`, 4 timeouts, **zero
   recovery**. The unstick probe (arith-Unknown no longer poisoning later
   Sat candidates): still 24/24 `unknown` — the sticky gate is not the
   blocker; the search never reaches a certifiable candidate. The ray
   decoded on `NIXIE_BRANCH_TRACE`: two mutually-defining UNBOUNDED
   basics in a unit cycle (`v6 = −4/57·v2 + …`, `v2 = −57/4·v6 + …`)
   walking one level per node; z3's models sit far off the ray.
   **The owner is architectural — Z3's branch is CDCL-visible
   (`lia_move::branch`, no internal depth budget, free vars branch at
   offset 0); ours is internal and clause-blind. The fix is the
   pivot-storm study's map item 1: the branch-lemma/case-split channel
   (`TheoryResult` extension), reducing the internal B&B to a dive.**
2. **The 8 reshuffled members attributed** (survey re-run at
   `precompile/01fc31a0/nixie`, diff vs current): 6 ray, 2 J5 — folded
   into the map above.
3. **fi1 CLOSED**: `docs/studies/assets/2026-09-17/false-unsat-fi1.smt2`
   answers `sat` in 48 ms (z3 agrees); model `{xi=0, yi=2^62}` validated
   by binding + negation in BOTH z3 and nixie. The item-95 read fix plus
   the Hermite widening retired the old branch-walk blocker.
4. **Item 75's strict-stranding reproducer LANDED**
   (`strict_lt_stranded_row_rehomes_with_strict_bound` + the Gt twin, in
   `nixie-theories/src/arithmetic/solver.rs`): deterministic
   constructions at the solver surface, pinning the strict re-intern
   (defining row), the STRICT zero re-assert (`delta` sign — never
   weakened), the direction (never flipped), and the atom's own live
   reason. Revert-checked both halves (item 96 records the trap: the
   two `slack_forms` recording sites are textually identical — target
   the strict one). **Item 71's channel question remains open.**
5. **The doc gate FIXED** (`2a60cb54`): the breakage was committed on
   main (ctx_simplify's private links + CSR slice-6's private link), not
   in-flight. De-linked; `RUSTDOCFLAGS="-D warnings" cargo doc` is green.

The wrong-verdict ledger stayed empty: every survey member honest
`unknown`, fi1's model z3-validated, zero verdict disagreements anywhere.

## The verdict map (measure before believing)

Fixed seeds 20261000–02 × 600 at `f6daed038`: **76 members**
(78 → 76 over the SAT slice-6 landing: 2 recovered, 0 lost). Cumulative
arc run: 150 → 110 → 91 → 79 → 75 → 73 → 78 → **76**.

* **J5 × 51** — the big-const certify gate on genuinely bad candidates
  (the dive-leaf divergence class; item 89's map). Entry point:
  `integral_dive`'s leaf acceptance vs the div/mod defining axioms'
  tightness. NOT a budget class.
* **The ray × 24** — `lia:bnb-depth-budget`; budget-immune (measured);
  owned by the CDCL-visible branch channel.
* 1 simplex resource-limit tail, plus **10 timeout members** not in the
  76 (2 + 0 + 8 across the seeds; 9 z3-`sat`, 1 z3-`unsat`) — the
  probe-silent tail, not tagged this session.

## Open items, in priority order

1. **The CDCL-visible branch channel** — the architecture project that
   owns the ray class (24 members) and is the named prerequisite in the
   pivot-storm study (`docs/studies/2026-09-20-lia-pivot-storm-dissected.md`,
   map item 1). Solver-core feature: a `TheoryResult` branch/case-split
   move (or a lemma channel), the arith branch emitting `x ≤ k`
   literals, the internal B&B reduced to a dive. Z3's `int_branch.h` /
   `int_solver.cpp` are the spec. This is multi-session work; the
   acceptance test is the ray class recovering without budget changes.
2. **J5 candidate quality (51 members)** — the dive's leaf satisfies the
   tableau but not the original formula. Items 89/91 own the map; the
   certifier probes (`[cert-false]` + `INTERP`) are the tool.
3. **Item 71's channel question** — why the rehome's re-assertion is
   load-bearing when the stranded slack stays equation-tied (the
   `parity_infeasibility` repro; reason-side tracing).
4. **The sticky-flag precision question** (measured, not urgent): the
   arith-Unknown arm of `theory_manager`'s `resource_exhausted` poisons
   all later Sat candidates for the instance's lifetime. The unstick
   probe recovered none of the ray class, so it is NOT a near-term
   recovery lever — but a genuine later-candidate Sat is still dropped
   there whenever an earlier check abstained. If touched: the
   dropped-CONFLICT arms are sound-critical and must stay sticky; only
   the abstention arm is a precision candidate, and any change ships
   with the full battery (it is soundness-adjacent).

## The instrument set (recipes)

* **`NIXIE_GAP_PROBE=1` tags are session-local** (the item-67 recipe,
  rebuilt this session): auto-tags at every statement-position Unknown
  return (`slv:`/`lia:`/`smx-rl:` `fn:line`) plus the hand vocabulary
  (`lia:bnb-depth-budget`, `lia:bnb-node-budget`, `lia:dive-leafbudget`,
  `lia:inteq-incumbent-fail`, `lia:inteq-giveup`). `gap_survey.py`'s
  stderr capture is landed — attribution is one survey run.
* **`NIXIE_BRANCH_TRACE=1`** (also session-local): the branch dump with
  the branched var's bounds and defining row (narrow or wide) — the ray
  decoder. Rebuild from item 96's description.
* The dose knobs (`NIXIE_PROBE_MAX_DEPTH`/`NIXIE_PROBE_MAX_NODES`) were
  probe-only and are NOT in the tree — the negative result stands on the
  recorded numbers.
* Standing: `NIXIE_LEAF_TRIPWIRE`, `NIXIE_BOUND_TRIPWIRE`, the atom-row
  canary, `bench/differential/gap_survey.py`, the polarity pipeline.

## Where things live

* The session's record: item 96 in the arc study (numbers, recipes, the
  revert-check trap).
* Regressions landed this session: the strict-stranding pair in
  `nixie-theories/src/arithmetic/solver.rs`.
* Binaries: `precompile/f6daed038/nixie` (the attribution baseline),
  plus this session's landing commits under their own `precompile/<sha>/`.
* Methods: `docs/BENCHMARKING.md`, `bench/differential/METHODOLOGY.md`,
  `bench/z3_parity/METHODOLOGY.md`.

The one-sentence version: **the budget question the predecessor handoff
named as its top open item is answered with measurements — the class is
a clause-blind internal B&B walking an unbounded ray that no budget
touches, the fix is Z3's CDCL-visible branch channel (the pivot-storm
map's architectural item), and everything else on the open list either
closed (fi1, the reproducer, the doc gate) or folded into that map.**
