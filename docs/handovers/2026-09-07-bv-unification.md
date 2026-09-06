# Handover: BV-Circuit Unification Campaign

## Context

`BvSolver` owns an **embedded SAT instance** that bit-vector constraints are
asserted into and solved **in batches at theory-check time**. The main CDCL
core never sees the gate circuits: it decides atoms, the theory callback
blasts and asserts, and only at the next theory check does the embedded
solver run to consistency and hand back conflicts. This batching boundary
is the root cause of two measured performance ceilings:

1. **The BitVec row of the `distinct` table stays pairwise** (C(n,2)
   equality atoms for n > 32) because the order encoding – built, fully
   verified, and measured in Sep 2026 – was a *wash*: comparator decisions
   cannot propagate through gates during the main descent when the gates
   live in another solver checked once per assignment. n = 2000
   free-variable `distinct` over BV fails under *both* encodings today.
2. **Every QF_BV instance pays the batch latency**: propagation that would
   happen per-decision in a unified core happens per-theory-check, and
   each embedded check re-enters a second CDCL loop.

The full story, measurements, and the original flip-condition analysis are
in `docs/studies/2026-09-distinct-theory-owned-sorts.md` – read §"Attack 3"
and the four postscripts before starting. This handover is the engineering
map; the study is the evidence.

**This is a trajectory-changing campaign** (that is the point), so the full
`docs/BENCHMARKING.md` methodology applies: pre-registered cells, ticks not
wall as primary metric, ≥10 seeds for any stochastic comparison, the
escalation ladder, and the result-store protocol.

## Current Architecture Map

All anchors verified against main at `30c049c` (Sep 2026).

### The embedded solver and its pipeline

- `nixie-theories/src/bv/solver.rs` – `BvSolver` with its own
  `self.sat: SatSolver` (own `SatConfig`; note `chrono_backtrack_threshold:
  10_000`). Circuits are gate clauses in *this* instance.
  - `new_bv(term, width)` / `get_bv(term)` – per-term `BvVar { bits:
    SmallVec<Var>, width }`; the embedded solver's own var space.
  - `assert_eq / assert_neq / assert_ult / assert_ule / assert_slt /
    assert_sle / assert_const[_big,_limbs]` – build gate circuits via
    `binop_bits` (returns false when operands are not yet blasted – every
    caller must blast first or handle the false).
  - `encode_ult_result` with `ult_cache: FxHashMap<ComparisonKey, Var>` –
    shared comparison circuits; `assert_ule(a,b)` = build `ult(b,a)` and
    negate.
  - `record_constraint_term` / `collect_conflict_terms` – the conflict
    protocol: on embedded UNSAT, the explanation is the set of *all*
    recorded constraint terms (a sound superset, not a minimal core).
- `nixie-solver/src/solver/theory_bv_encode.rs` –
  `encode_bv_term_recursive(bv, root, manager, encoded)`: the term→circuit
  compiler. Pins `BitVecConst` leaves via `assert_const`; returns false for
  shapes it cannot model (e.g. `Apply`), where callers fall back to
  `new_bv` (a free bit-vector – the correct abstraction for a UF result).
- `nixie-solver/src/solver/theory_manager.rs`:
  - `bit_blast_bv_pair(lhs, rhs, manager)` – lazy blast-or-`new_bv` of both
    operands of an eq/neq constraint (called from `bv_check_eq/neq`).
  - The `Constraint::Le/Lt` BV arm in `process_constraint` (search for
    `is_bv_sorted`) – lazy-blasts operands, derives signedness from the
    recorded term's `TermKind`, then `assert_ult/ule/slt/sle`.
  - `bv_run_check(constraint_term, operands, manager)` – asserts then
    `bv.check()`; UNSAT → `conflict_from_terms`; SAT →
    `debug_verify_bv_circuits` (debug builds re-evaluate every blasted node
    concretely on the model – keep this, it is the circuit-soundness net).
  - `final_check` – the batch boundary: the embedded solver reaches
    consistency only here (and per constraint assert).
- `nixie-solver/src/solver/encode.rs`:
  - `blast_bv_circuits_at_base_scope(term, manager)` – *eager* walk of
    assertion subterms at base scope only (gated on `bv.at_base_scope()`);
    interior `blast_bv_term` + `encode_bv_term_recursive`.
  - `needs_ite_elimination(sort, manager)` – **read its comment before
    touching anything about ites**: BV operators desugar into BV-sorted
    `ite`s inside the term builder; hoisting them broke `bvsmod` with a
    false `sat` once.
  - `BvUle/BvUlt` encode arms also produce `var_to_parsed_arith` entries
    (unsigned bounded-integer view – a relaxation; `BvSlt/BvSle`
    deliberately do NOT, see the signed-mixing comment).

### Scoping and state

- `BvSolver::push/pop` (own `context_stack`); `at_base_scope()` gates eager
  blasting because base-scope circuits are permanent.
- The theory manager replays constraint processing per search round via
  the shadow trail (`resync_theory_state`); the embedded solver is reset
  and re-driven with it (see the reset sites in `check_core`).

### Land-mines with a history (each has a test – find it and keep it green)

- **Wide constants**: `assert_const` truncates to u64; width ≥ 64 must go
  through `assert_const_big/_limbs`. The 0-vs-2^64-at-width-128 false
  `unsat`/merge bug is why `interned_bv_constants` keys carry full limbs.
- **Signed comparisons** must never flow through the unsigned arith parse.
- **BV-sorted `ite` desugaring** (bvsmod, rotates, zero/sign-extend).
- **Value marks (NEW, `30c049c`)**: BV ground constants now carry e-graph
  distinguished-value marks instead of pairwise disequality edges;
  `are_proven_disequal` answers true for differing class-value summaries,
  and the merge-time atom re-test enqueues value-apart eq-atoms with an
  empty (tautological) justification. Unification must not regress these
  (`nixie-theories/src/euf/solver/tests.rs`, `value_*` tests) – and note
  they serve the EUF-congruence join that the bit level cannot see, so
  they stay even after unification.

## The Two Design Options

### Option A (recommended): unify the circuits into the main SAT core

The gate clauses and bit vars live in the *main* solver's var/clause
space. The BvSolver becomes a circuit *builder* over the main core (it
already has all the gate constructors; they need an abstraction over
"which SAT instance receives this clause/var"). Consequences to design
for, not discover:

- **Conflict explanations change character**: today the embedded UNSAT
  returns a superset of constraint terms which `terms_to_conflict_clause`
  converts to main-core literals. In a unified core the learned clause is
  a gate-level clause over bit vars; the analysis engine must translate it
  back to atom literals or learn over bits directly. Decide early: bit-level
  learning is stronger but pollutes the main core with auxiliary vars
  (deletion/DRAT implications); atom-translation is weaker but
  protocol-compatible. A staged plan: keep `record_constraint_term` as the
  explanation source (assume-gate the circuit clauses on their atoms,
  Tseitin-style, so a conflict over gates resolves to atoms) and only
  later consider native bit learning.
- **Phase/branching**: bit vars become branchable by the main heuristics.
  This is *the win* (mid-descent propagation) but changes every QF_BV
  trajectory. Freeze-set discipline (`freeze_theory_vars`) may need
  revisiting for bits.
- **Scoping**: base-scope permanence of circuits must map onto the main
  core's push/pop (clauses added at base scope survive pops – same
  property the embedded solver had).
- **The embedded solver's SatConfig choices** (chrono threshold etc.) are
  lost/replaced by the main core's schedule – acceptable, but note it in
  the study.

### Option B (stepping stone): per-decision propagation bridge

Keep the embedded solver; give it a propagation interface the main loop
calls on every decision (drain embedded units → main trail; push main
atom decisions → embedded assumptions). This is incremental and
checkpoint-able but keeps two var spaces and two watches per constraint;
my measurements predict it captures only part of the win. If you need a
de-risked first stage, do B with the explicit success criterion "the
order encoding's n=2000 cell flips from timeout to solved", then proceed
to A.

## What NOT To Do (measured negatives from the distinct campaign)

- **Do not inject large batches of new clauses into a live search** and
  expect digestion: 780 trichotomies at once measurably derailed a
  re-descent (~300 full assignments between generalizing conflicts);
  256-at-a-time converged. Whatever the unified core does, add circuits
  incrementally per atom, never in bulk round-batches.
- **Do not set phases in the wrong solver instance**: deterministic phases
  set on the main core do nothing for embedded bit vars (and vice versa)
  – the `phase_hint_bits` API exists on `BvSolver` for the embedded side.
- **Do not write nested threshold conditions like `a > if c { x } else {
  y } && z`**: it compiled and silently mis-parsed (the distinct threshold
  bug of `754926d`'s first attempt). Use an explicit helper function.
- **Do not gate safety mechanisms unconditionally**: the honesty gate had
  to be conditioned on the `distinct` term being *true* in the model – an
  unconditional gate degraded legitimate ¬distinct models. Any new gate
  needs the same polarity review.
- **Do not trust the first plausible fix** for a slow shape: three of the
  four distinct campaign "next enabling changes" turned out to be
  something else entirely (root causes: missing trichotomy on refine
  atoms; proposal-polarity blindness; clique-vs-chain proposal shape).
  Instrument (`--stats`, PROBE eprintlns, `NIXIE_*` env traces) before
  designing.

## Existing Infrastructure You Can Reuse

- **Binaries** (`precompile/<sha>/nixie`): `30c049c` (current), `b9c750d`,
  `754926d`, `d09f992`, `86b6168` – the full campaign lineage for A/B.
- **Corpus A/B harness pattern**: 300-file random sample, verdict-mismatch
  count (hard zero), wins/losses at 1.3×, timeout deltas – used twice in
  the studies; ~30 lines of Python, see postscripts 3–4.
- **Corpora are untracked** – symlink `smt-lib`, `satcomp2024`, `precompile`
  from the primary checkout into your worktree or corpus tests fail
  cryptically.
- **Ticks**: `nixie --stats file.smt2` prints decisions/conflicts/
  propagations – deterministic, use these as primary metrics.
- **The order encoding design** is fully specified in the study (comparator
  mux + strict chain + identity phase hints + 0-1-principle tests); the
  code was reverted after the wash verdict (~120 lines to re-derive, the
  bitonic recursion is written out in §Attack 1's neighborhood). Restore
  the 0-1 tests with it – they are the correctness proof of the network.
- **Value-mark machinery** (`declare_value_const` / `fresh_value_id` /
  `class_value` / `classes_value_apart`) – see the e-graph tests for the
  contract.

## Calibration Data (reproduce with `precompile/30c049c`)

Order-encoding vs pairwise (release, Sep 2026 – both correct, wash):

| cell | pairwise | order network |
|---|---|---|
| n=300 w=16 sat | 4.15 s | 3.80 s |
| n=300 w=16 unsat (explicit) | 0.055 s | 0.179 s |
| n=600 w=32 sat | 51.4 s | 42.1 s |
| n=2000 w=16 sat | timeout | timeout |
| dense n=600 w=10 sat | 35.6 s | 33.2 s |

Constant-density (value marks, `30c049c` vs `754926d`): k=2000 BV
constants under UF: 4.75 s → 0.37 s; k=4000: 9.26 s → 0.64 s.

The unified core should be calibrated against these same cells plus a
pre-registered QF_BV corpus sample (the 46 348-file extracts; sample once,
commit the list, never re-sample).

## Expected Outcome and the Flip Decision

Pre-declare the flip conditions so the decision is mechanical:

1. **QF_BV corpus sample**: geomean tick improvement ≥ 1.15× with zero
   verdict mismatches vs `30c049c` and vs z3 (parity suite 100%).
2. **Order-encoding re-run**: after unification, rebuild the order
   encoding and re-measure its table; if it beats pairwise by ≥ 1.5× on
   the n ≥ 300 cells, flip the BitVec row (gate: n > 32, `SortKind::BitVec`,
   with the totality whitelist comment already in the study).
3. **No regression** on the ite/bvsmod/wide-const/signed battery
   (`nixie-solver/tests/bv_*.rs`) and the `value_*` e-graph tests.

## Verification Checklist (every landing)

```
cargo build --all-features
cargo nextest run --workspace --all-features
cargo clippy --all-features --all-targets -- -D warnings
cargo fmt --all -- --check
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features
./bench/z3_parity/run_parity.sh        # 100% or investigate
```

Watch the disk (`target/` churns 100+ GB; `CARGO_INCREMENTAL=0` and
`CARGO_PROFILE_DEV_DEBUG=1` for full-suite runs). Land via worktree +
`git push . HEAD:main` or ff-merge from the primary if clean; confirm
with `git merge-base --is-ancestor <sha> main` (a landing was once
believed done and wasn't). Cache every landed binary in
`precompile/<sha>/`. Clean up worktrees and branches when idle.
