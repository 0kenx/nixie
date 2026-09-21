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

## Update (later the same day): open item 1 EXECUTED — the channel is built, measured, and landed flag-gated

`63cae24b` lands the CDCL-visible branch channel (`NIXIE_LIA_BRANCH_LEMMA=1`,
default OFF).  The pure-addition variant (no internal budget cut — the
parallel session's `364c9c90` measured that trade regressing v20; reverted
in `e2b45aaf` in favor of this build).  Study:
`docs/studies/2026-09-20-lia-branch-lemma-channel.md` — armed survey 77 →
55, **16 genuine recoveries (models z3-validated, ledger empty), 6
timeout-class cost flips; matched null (k=0): 12 recoveries, treatment-only
10, null-only 0** — the go bar passed; default-off bit-identical (gate
1.000/1.000); armed differentials clean.  **Open: rung 3 (the default-flip
campaign: ≥10 seeds, per-family, benchstore, the 6-slow-flip cost
decision)**, and the J5-certify class is the next blocker IN SERIES on the
members the armed search now reaches (i116's decode: ray → J5).

## Update (final): rung 3 EXECUTED — the channel is the DEFAULT

`0edc05fc` flips the default (`NIXIE_LIA_BRANCH_LEMMA=0` restores the
unarmed search).  The campaign (12 seeds × 3 arms, pre-registered): **42
genuine recoveries on 11/12 seeds, all 40 sat models z3-validated by
binding + negation, zero wrong verdicts, the matched null dominated
(42-vs-28 genuine), timeout cost +2.0/seed** — every go-bar criterion
passed.  Full battery at the new default: suite 12 063 (the 15 failures
are the documented corpus class), clippy/fmt/rustdoc clean, parity
176/177 (0 wrong, z3 4.16.0), perf gate PASS, 9 fresh-seed differentials
clean, panic sweep 177/177.  **The combination with the Bareiss layer
(landed concurrently) spot-checked**: the e2e pin, a fresh differential,
and a default survey seed all behave as measured.

The remaining gap map post-flip: the J5-certify class (the members whose
armed searches still reach uncertifiable candidates — item 89/91's
dive-leaf divergence), the ~18 slow-class members, and the timeout tails.
Study: `docs/studies/2026-09-20-lia-branch-lemma-channel.md` (the
campaign, the traps, the honest-counting method).

## Update (the J5 half): J5-(a) CLOSED — 55 → 18 members

`a64738ff` lands the certificate fallback: the big-const gate's MBQI
certifier declines mixed Int/Real goals *without evaluating them* (a
fragment refusal), discarding valid models the armed search found.  The
gate now falls back to `model_certifies_assertions` (the value-only exact
certificate — original assertions, true constants, fails closed).  **37
of 55 post-flip members recovered; all 37 verdicts z3-agreeing; all 37
models z3-validated by binding+negation; zero false.**  The residual 18 =
J5-(b) (candidates the certificate genuinely refutes — item 89's
dive-leaf divergence, the next open item) + the ray/smx tails.

The arc's cumulative fixed-seed survey run: 150 → 110 → 91 → 79 → 75 →
73 → 78 → 76 (flip) → **18**.

## Update (J5-(b2) closed): 18 → 2 members

`1c71f4d9`: the certificate evaluator learns integer div/mod (exact
Euclidean, fail-closed on zero divisors / non-integral operands — the
terms previously fell to the opaque-leaf catch-all) and certificate-mode
equality (an exact collision VERIFIES the positive `=`; the refutation
gates keep their collision-conservatism untouched).  **16 of 18 members
recovered; all verdicts z3-agreeing; all 16 models z3-validated; zero
false.**  The residual 2: `gap_s20261001_i504` (a LINEAR-arithmetic
`Undetermined` source — no div/mod in the refusing conjunct's tree; the
next decode) and `gap_s20261000_i129` (the simplex resource-limit tail).

The arc's cumulative fixed-seed survey run: 150 → 110 → 91 → 79 → 75 →
73 → 78 → 76 → 18 → **2**.

## Update (i504 closed): the fixed-seed survey at 1 member

`8eede1d7`: the certificate now verifies the PUBLISHED model —
model-first user-var reads (compound constant spellings evaluated
exactly), a once-per-certificate δ₀ instantiation for live real reads
(`certify_delta0`), and `CmpStrictCertify` with read provenance
(strict-at-equality is decisively false when every contributing read was
concrete; a live read that may have dropped a positive delta keeps the
soften).  i504 answers `sat` (model z3-validated).  **The fixed-seed
survey residual: 1 member — i129, the simplex resource-limit tail (a
different class).**  The arc's cumulative run: 150 → … → 18 → 2 → **1**.
The next hunt is fresh-seed surveying (the fixed seeds are exhausted).

## Landing note (RESOLVED: `286f63bd` landed)

The ff completed after preserving the warm-start session's uncommitted
restyle on the `warm-start-restyle-snapshot` branch (nothing discarded;
their session had closed at `553a44f8`).  The i504 fix is on main as
`286f63bd`; the landed tree re-verified (build, the certificate pins,
the 1670-test theory suite, fmt/clippy; i504 `sat`, i129 honest
`unknown`), binary cached at `precompile/286f63bd/`.

(original note:)

The i504 fix's CODE commit is ready but its fast-forward is BLOCKED by
the warm-start session's uncommitted restyle of `model_eval.rs` /
`solver/mod.rs` in the primary checkout (30+ minutes in-flight — their
battery).  Git refuses both `merge --ff-only` and `push . HEAD:main`
while their tree is dirty; discarding their work is forbidden.  The
commit lives on the `nixie-wt-r4` worktree (rebased on `6cf69d91`,
`80cc7170`); the NEXT session (or the warm-start session's own landing)
rebases it — a textual conflict with their restyle is expected and
mechanical (my hunks' context is the pre-restyle spelling).  The
measured binary is cached at `precompile/8eede1d7*/` and the full
battery ran on exactly that tree.
