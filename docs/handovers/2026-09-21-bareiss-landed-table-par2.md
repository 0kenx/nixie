# Handoff: the Bareiss layer landed, the table carries par-2/geomean, LIA's arithmetic layer closed

**Follow-up (same night, later): step 3 EXECUTED.**  The ctx-simplify
fold pass reached the check-sat path — not as a fresh build but as the
CAMPAIGN completing the assert-fold session's flag-gated landing
(`a6349641`; their checkout had clobbered this session's independent
probe — reconciled per the item-96 precedent).  Landed (`6853f25c`):
default ON with `NIXIE_ASSERT_FOLD=0` kill-switch, REFUTE-ONLY adoption
(the always-rewrite variant measurably regressed the LIA mid-band),
ite structural gate, depth-aware contract (ctx_walk is natively
recursive — the depth-guard's fold-rescue LADDER owns deep spines).
69 nec-smt members `unknown -> unsat` with zero z3-disagreeing flips;
`prp-3-18` (47x cell) at 0 conflicts; `problem_2__014` (42x cell)
timeout -> `sat`/905 ms; standing LIA 33/60, par2 9429 -> 9088, median
0.55 -> 0.52.  Full record:
`docs/studies/2026-09-21-assert-fold-default.md` (binary
`precompile/6853f25c`).

----
**Morning follow-up (post-branch-channel).**  The arithmetic arc's
rung 3 landed (`0edc05fc`: the branch channel is the DEFAULT) — the
standing LIA counters now read **5517 -> 4502 -> 3209** across the arc
(Bareiss inert, the fold's refuted cells, then the channel's
recoveries; the measurement log has the runs).  The Bareiss follow-up
question (entering-solve zero-gcd) resolved **NEGATIVE** by profile:
<=2 % of the arithmetic mass — recorded, do not revisit without a
profile that moves it.  A clean calm-load wall snapshot of the
combined tree could NOT land this morning (one run rode my own
concurrent symbolized build — scheduling mistake, discarded; two rode
other agents' campaigns at load 10-399, discarded) — **the next
agent's cheap closure** is exactly the handover's step-1 recipe: the
table at sustained load <= ~8 on `precompile/cf8e497c` (or newer).

**Warm-start: taken and CLOSED NEGATIVE** (`2026-09-21-warm-start-negative.md`).
The addendum's premise expired: `crash_basis`/`update_assignment`
measure 0.00-0.03 % on both named probes (011: sat/0cf/18.4 s; 022:
churn) — pop's relax-only discipline plus basic-var branch bounds
retired the per-node pass for free.  **The profile map moved**: both
probes are now substitution-volume cells (~78 % of wall in
`pivot`+`checked_ratio_i128`+`gcd_i128`) — the canonical write-back
floor times the pivot count.  The write-back floor is the dominant
remaining ARITHMETIC cost; the named way past it is the full
integer-tableau architecture (lazy canonicalization of substituted
rows — the IntRow cache already holds the content; multi-session,
soundness-critical).  The pivot COUNT remains the architectural item
(pivot-storm Layer 3).

**Afternoon closures:** the conj-level fold probe RETIRES by experiment
(20-file seeded sample: zero fold wins; the `(assert (and …))`
re-expression itself regresses 16/20 with 8 sat->timeout flips — the
multi-assert pipeline shape is load-bearing; see the assert-fold
study's Addendum 2).  The next-session entry for the write-back floor
is WRITTEN: `2026-09-21-integer-tableau-design.md` (three phases,
pre-registered measurement, soundness rails).  The LIA leg reproduced
at the day's one true-calm window (33/60, par2 9100, median 0.52-0.55);
the full snapshot (BV leg) remains blocked on machine load — still the
next agent's cheap closure.

**The integer tableau, Phase 1 LANDED (both stages).**  Stage A
(`c5e8026a`, the behavior-identical bridge: `TableRow` storage, the
`row_lin` memoizing choke point, the Cow view, form-independent
`term_vars`) and Stage B (`45a2c742`, the win: `substitute_row_ff`
returns the `IntRow` alone, pivot commits store `TableRow::Int`, the
canonical write-back defers to first read, the `int_rows` cache
deleted, a `LinNoInt` negative variant guards the over-budget tail).
Measured: the write-back (`checked_ratio_i128`, 21.9 % of the churn
probe's wall) VANISHES; `materialize_lin` 2.3 %; end-to-end
17.6 s → 14.9 s with bit-identical counters; full bar green (gate
1.000/1.000, parity 176/177).  **Phase 2/3 remain** (the entering-rule
trio and `build_pivot_expr` still materialize one canonical row per
round; the born-integer solved form is Phase 3) — entry: the design
study's execution record.  Binary `precompile/45a2c742`.

**Phase 2 landed (`cefcd561`)** — the entering rules read signs
natively (either form, zero gcd, `&self` again; honest attribution: the
win is marginal — the memo shared the materialization with pivot's own
fetch — but the entering rules no longer force canonicity).  **Phase 3
is refined and ready** (the study's record): an `Int` leaving row's
solved form is exact-and-narrow BY CONSTRUCTION, `entering_int` dies,
`entering_big` goes lazy, the entering-value eval has a zero-gcd
integral fast path, and the entering commit stores the born `Int` row —
the last per-pivot canonical build on the hot path.  Binary
`precompile/cefcd561`.

**Phase 3 LANDED (`795abb8f`) — the integer tableau is COMPLETE.**  The
born-integer entering row (re-denomination, exact-and-narrow by
construction, pinned), `entering_int` = the born row, lazy
`entering_big`, the zero-gcd integral `eval_int_expr`, the `Int`
entering commit — plus a profile-exposed Stage-A cost fix
(`try_patch_column`'s owner scan reads its one coefficient from the
store form).  Bit-identical on all four probes, ~6 % wall on the churn
probe under load A/B, full bar green.  **The honest floor**: the churn
probe is now `substitute_row_ff` (~33 %) + `gcd_i128` (~30 %) — the
integer mul-sub and the joint-reduction chain, this architecture's
floor.  The design brief's three phases are closed.  Binary
`precompile/795abb8f`.

**Date:** 2026-09-21 (small hours).  **Arc:** executing
`docs/handovers/2026-09-20-smt-perf-arc-executed.md` — the calm-load
table (step 1), the Bareiss/row-denominator layer (step 2, landed), and
the harness upgrade the operator asked for (par-2 + geomean on every z3
comparison).  **Step 3 (the ctx-simplify fold pass) is NOT started** —
it remains an own-session project; its entry point is unchanged (the
2026-09-19 attribution study's step-zero-closed section,
`query/simplify.rs`'s memoized harness).

## What landed (in order)

1. `38cb15d4` — **the calm-load baseline snapshot** (binary
   `precompile/2edd5b34`): QF_BV 55/60 vs z3 54/60 **with the lead
   confirmed on par-2 (2425 vs 2615 ms) and geomean (122.6 vs 138.4)**,
   not just count; QF_LIA 32/60 vs 54/60, zero disagreements, real z3
   conflict columns for the first time.  `run_perf.sh` now records and
   prints par2 / geomean_all / both-solved median per family (counters
   stay the primary metric; these are the load-sensitive secondaries the
   calm-load discipline makes comparable).
2. `67eabbe0` — **the fraction-free (Bareiss-style) pivot substitution**
   (the pivot-storm addendum's item 2, the LIA class's structural
   arithmetic layer): rows mirrored as `IntRow` (integer numerators +
   one shared denominator ≤ 2^62) in a POINTER-VALIDATED cache
   (`Arc::ptr_eq` against the content-replaced tableau rows — stale
   encodings structurally unreachable), substituted as integer mul-sub +
   one row-level gcd chain + one single-gcd canonical write-back per
   term.  **Bit-identical output** to `substitute_row_fast`; gated to
   fire only when at least one side carries a fraction (all-integral
   substitutions keep the zero-gcd integer fast path — the ungated
   version taxed integral cells ~1.1×).  Pins: 4000-case equivalence
   grid, budget boundaries, cache pointer-coherence.
3. `0963911e` — **the ff-landing snapshot** (binary `precompile/67eabbe0`):
   QF_LIA counters bit-identical (5517), **geomean 246 → 144 ms (−41 %,
   now under z3's 164.7), both-solved median 1.71 → 0.55** (~1.8× faster
   than z3 on the common LIA mass); solved count unchanged at 32/60 —
   the count is the branch channel's to move, not arithmetic's.
4. `55ba292e` — the study with the design finding, evidence, and traps:
   `docs/studies/2026-09-21-lia-bareiss-fraction-free-rows.md`.

## Verification state at handoff

Perf gate PASS twice (conflicts/decisions 1.000/1.000 — the bit-identity
canary, both pre- and post-gate binaries); Z3 parity 176/177, 0
disagreements (z3 4.16.0); workspace nextest green (11842 + 2707; five
`scope_rebase`/`bv_odd_width` timeouts at load 150 re-verified in
isolation — the documented flake class); clippy `-D warnings`, fmt, and
rustdoc clean on every touched file.  The tree's only `-D` failures at
handoff were another agent's in-flight `nixie-cli/src/dimacs.rs` (their
parser arc) and `nixie-theories/src/graph/tests.rs`.

## The remaining map (for the next agent)

1. **The ctx-simplify fold pass** (the prp/nec 47×-wall class) —
   untouched, own-session, entry per the 2026-09-19 study.
2. **The branch channel rung-3 campaign** — item 96's territory
   (pre-registered `ca675e2e`).  With the churn layer now cheap, the CAV
   family's internal B&B should start completing round-trips; the
   campaign decides the `NIXIE_LIA_BRANCH_LEMMA` default.  Coordinate,
   don't duplicate.
3. **The natural ff follow-up** (only if a profile ever shows it):
   `build_pivot_expr` still pays ~k per-term-division gcds once per
   pivot (1/46th of the substitution mass).  The zero-gcd version is a
   re-denomination of the leaving row's cached `IntRow` (numerators
   negated, denominator := entering numerator) — the design note is in
   the study's "does NOT close" section.
4. **Solved-count movers on the table** are architectural (branch
   channel, SAT capacity cells), not arithmetic — the LIA par-2 floor is
   now the 28 timeout cells.

## Traps added this session

- **The shared `target/` is volatile under disk pressure**: ENOSPC
  triggered a wholesale purge mid-session, and `/tmp` scratch dirs
  (including isolated `CARGO_TARGET_DIR`s) were wiped twice.  Isolate
  measurement builds under `$HOME/.cache/...` (root fs), keep binaries
  you care about in `precompile/<sha>/` immediately, and never let an
  A/B depend on a shared-`target` binary surviving the hour.
- **Two agents running `run_parity.sh` concurrently share `/tmp` scratch
  names** — check result-file timestamps and the worktree paths in the
  log before attributing a run to your tree.
- **The table's fragile BV cell (`bench_16217`, ~9.9 s at cap 10)**
  bounces at load >~10 mid-run; the LIA family runs FIRST, so a run that
  creeps over load late still yields a clean LIA leg (disclosed in the
  snapshot's `run_note` when that happens).
- **num-rational's `+=` panics on intermediate overflow in debug** —
  test generators must merge through `checked_add_r64`, not
  `LinExpr::add_term`.

## The named-member audit after the integer-tableau landings (clean)

Per the arithmetic arc's discipline (re-run the named members after any
raced landing on solver surfaces): the fixed-seed survey
(`gap_survey.py`, seeds 20261000-02 × 600) on `precompile/795abb8f`
(the Phase-3 tree) yields **exactly 1 member — `i129`**, the known
simplex resource-limit tail — the arc's expected result on the prior
tree, reproduced precisely.  No silent drops from the integer-tableau
Stages A/B or Phases 2/3; no new members.  (The named pins i142/i116/
i504/i393/i566 live in the test files — green in the full suites run
at each landing.)
