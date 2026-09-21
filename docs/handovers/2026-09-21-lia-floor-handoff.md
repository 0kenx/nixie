# Handoff: the LIA floor — the pivot COUNT (architectural) or a fundamentally cheaper joint reduction

**Date:** 2026-09-21 (evening).  **From:** the arithmetic-layer arc
(Bareiss → assert-fold → the integer tableau, all landed).  **To:** the
next agent taking the two remaining levers on the LIA churn class.
**Read `AGENTS.md` first — it is canonical.**  This handoff succeeds
`docs/handovers/2026-09-21-bareiss-landed-table-par2.md` (read it for
the arc's cumulative record and the measurement-log discipline).

## Where the floor is (measured, current tree `795abb8f`)

`CAV/30-vars/problem__011` — `sat` at **0 SAT conflicts in ~17 s under
load / ~15 s calm**: the entire cost is inside theory checks.
Symbolized self-time on the 20 s window:

| symbol | share | what it is |
|---|---|---|
| `substitute_row_ff` | ~33 % | the integer mul-sub (THE WORK) |
| `gcd_i128` | ~30 % | the joint-reduction chain + write-back residues |
| `Simplex::pivot` | ~11 % | the pivot machinery (born rows: no canonical build) |
| everything else | <26 % | patch/cut/column machinery, alloc |

The canonical write-back is DEAD (integer tableau Phase 1–3: rows live
as `IntRow`s, the entering row is born-integer, the hot path builds no
canonical form).  `problem__022` (45 vars) still produces no verdict at
30 s.  **Two levers remain; everything else on this family is at the
measurement bar's floor.**

---

## Route A — the pivot COUNT (architectural; COORDINATE FIRST)

**The mechanism (pivot-storm Layer 3, still true post-everything):**
one theory check burns a 20 000-node internal B&B (`~2-3 pivots/node ≈
80 k pivots`), while z3's `int_solver::check` cascade
(`src/math/lp/int_solver.cpp`) does **ONE cheap move per call** — gcd
test → `patch_basic_columns` → cube → HNF (period-gated) → DIO → Gomory
`get_gomory_cuts(2)` on a period-4 gate → `int_branch` — with the
branch **CDCL-visible** (branch bounds become literals; learned clauses
prune; z3-old solves `problem__022` in 44 pivots + 4 branches).

**What is already landed:** the branch channel is the DEFAULT
(`0edc05fc`, the rung-3 campaign: 42 recoveries, zero wrong verdicts;
`NIXIE_LIA_BRANCH_LEDRA`-style opt-out is `NIXIE_LIA_BRANCH_LEMMA=0`).
But `problem__022` still churns: the death is INSIDE one check — the
internal `bnb_search` mopup runs to `LIA_MAX_NODES` before the channel
ever sees a round-trip.

**The fix shape:** bound the internal B&B to a DIVE (hand the
fractional variable to the channel after a small node/depth budget per
CHECK, not per search) — the channel is landed, default, and starved.
Entry points:

* `nixie-theories/src/arithmetic/solver.rs` — `bnb_search` (~L3413),
  `LIA_MAX_NODES` / `LIA_MAX_DEPTH`, `note_lia_branch_request` (the
  request channel — already fires at the depth/node caps today),
  `take_branch`, `integral_dive`.
* `nixie-theories/src/solver/mod.rs` + `theory_manager.rs` +
  `int_case_split.rs` — the channel's receiving side (item 96's
  territory).
* The reference: Z3 `int_solver.cpp` (READ ONLY, `../temp/z3`); the
  mirror `docs/studies/assets/ddm_mirror.py` (pivot-exact; answers
  behavioral questions in seconds).

**COORDINATION — non-negotiable:** the arithmetic arc's successor
handoff (`docs/handovers/2026-09-21-arithmetic-arc-simplex-family-handoff.md`)
claims the **simplex pivot-cap / resource-limit family** (6 fresh-seed
members + `i129`, entry tags `smx-rl:make_feasible:L3183`,
`smx-rl:check:L3015`) — the SAME class from the member side.  Their
instruments are wired (`bench/differential/gap_survey.py`,
seed-deterministic; fixed seeds 20261000–02 × 600 must hold at exactly
`i129`, fresh 20262600–02 at exactly the 6).  Read their handoff,
check the tree for their in-flight work, and either coordinate the
campaign jointly or take the half they are not in.  Their regression
discipline applies to you: after any raced landing, re-run the survey
and the named pins (i142/i116/i504/i393/i566).

**Negatives that bind (do not retry blind):**
* Node-budget cuts ALONE convert solvable → `unknown` (the wide-literal
  bnb pin needs >512 nodes) — a budget without the CDCL-visible
  round-trip is a completeness loss, not a win.
* The entering-rule magnitude guard (63→45 pivots on the mirror)
  REGRESSED two standing cells — mirror merit does not survive CDCL.
* `solve-eqs` for the SAGE family: withdrawn (substitution explosive).

**The campaign bar (this is a trajectory change, not a rewrite):**
matched-null discipline per `docs/BENCHMARKING.md` — the rung-3
campaign (`0edc05fc`) is the precedent and the harness exists
(`bench/perf_gate/env_ab.sh`, ≥10 seeds, benchstore cells).  Verdicts
must hold: the survey, the named members, parity, the gate.

## Route B — a fundamentally cheaper joint reduction (the ~30 % `gcd_i128`)

The chain per substitution: `g = gcd(D', N_c)` then an early-exit walk
over the numerators.  Settled (do not revisit): binary-vs-Euclid
(binary wins 34.8 vs 25.1 Mops/s on the measured distribution); a
Lehmer u64 kernel has ≤2× headroom on ≤25 % of wall.  **Open, un-sized,
in expected-payoff order:**

1. **Chain ORDER** (cheap experiment, hours): iterate the numerators
   smallest-magnitude-first — the early exit at `g == 1` fires sooner
   when a small operand meets a large one (the binary kernel's cost
   scales with the smaller operand's bits after alignment).  Measure
   the operand-magnitude distribution of the FIRST failing gcd on the
   churn probe before building.
2. **The Bareiss exact-division structure**: in integer-preserving
   elimination the previous pivot's minor divides the new entries
   EXACTLY — a per-row carried `last_divisor` replaces part of the gcd
   discovery with exact division (cheaper on large operands than
   computing the gcd at all).  The simplex's arbitrary pivot order
   weakens the textbook guarantee — measure how often the carried
   divisor actually divides on the churn probe's pivot sequence (the
   mirror can count this in minutes) before designing anything.
3. **Partial reduction**: reduce by `gcd(D', N_c)` plus the first few
   numerators only, skip the rest.  SOUND (any reduction is exact;
   admission declines to the old path when width blows) — the question
   is purely whether widths stay in budget as well (the negative-cache
   `LinNoInt` variant already meters the decline rate; compare it).
4. **Skip-when-one fast rejection**: if `D'`'s and some `N_i`'s
   trailing-zero patterns already force `g = 1` (2-adic valuation
   mismatch), exit before the kernel — the operand histogram said 58 %
   of calls carry a power-of-two operand; the chain currently still
   enters the kernel for the first gcd.

Route B is bit-identity-verifiable like everything in this arc (same
canonical content, cheaper reduction): the gate's 1.000/1.000 plus the
four-probe identity sweep (026/011/prp-3-18/022-45) are the fast
canaries; the equivalence grid (`substitute_row_ff_matches_rational_
reference_seeded_grid`) and the born-row pin extend automatically.

## The verification bar (both routes)

`cargo build --all-features`; `cargo nextest run --workspace
--all-features` (the `scope_rebase`/`bv_odd_width` cells are documented
load-flakes — re-run in isolation before believing a failure);
clippy `-D warnings` / fmt / doc; **`./bench/z3_parity/run_parity.sh`**
(z3 4.16.0; 176/177 with 0 mismatches is the standing result);
**`./bench/perf_gate/run_gate.sh`** (counters 1.000 for
identity-preserving changes; ≥10 seeds + matched null for trajectory
changes); the fixed-seed survey (exactly `i129`); and the standing
table at sustained load ≤8 with the **PAR-2/geomean readout** (solved
counts alone hide wall shifts — the operator's standing instruction).
Binaries → `precompile/<sha>/` at every landing.

## Traps (this arc's, still live)

* The shared `target/` and `/tmp` are volatile under disk pressure
  (three purges/clobbers this arc); isolate measurement builds under
  `$HOME/.cache/...`, land binaries to `precompile/` immediately, and
  **commit WIP early** — an `MM` file in the shared tree is someone's
  live work (a checkout clobbered one this arc; the addendum is in
  `2026-09-21-assert-fold-pass.md`).
* Never run the standing table next to a build or another campaign
  (two discarded runs this arc rode my own build / load 69–399); the
  z3-canary (z3 losing cells) is the contamination signature.
* `geomean_all` on ms-floor cells is load-noise-dominated — decide on
  par-2 + both-solved median + per-cell back-to-back A/B.
* The `checked_ratio_i128`-style `expect()` ban: budget-admitted
  `IntRow`s are provably narrowing — keep invariants as
  `debug_assert`s with the proof in the comment (see
  `materialize_lin`).

## Ordered next steps

1. Read the arithmetic arc's successor handoff + check the tree for
   their in-flight work; agree the Route-A split (their entry tags vs
   the dive/channel architecture) or take Route B if they're mid-campaign.
2. Route B's cheap experiments first if solo: (1) the chain-order
   operand histogram (the mirror counts it), (4) the 2-adic skip —
   both are hours, both bit-identity-verifiable.
3. The standing cheap closure when the machine quiets: the calm-load
   table (many landings since `7c38a5f9`; counters need re-baselining;
   binary `precompile/795abb8f` or newer).
4. Whatever you take: pre-register the measurement, run the full bar,
   land with the study, cache the binary.

The one-sentence version: **the arithmetic layer is at its architectural
floor (63 % substitution machinery, bit-identity-verified); the class's
remaining mass is the internal-B&B pivot volume — the arithmetic arc's
claimed campaign, coordinate — and the joint-reduction chain, whose
cheap experiments (chain order, 2-adic skip, Bareiss divisor) are
sized here for a solo session.**
