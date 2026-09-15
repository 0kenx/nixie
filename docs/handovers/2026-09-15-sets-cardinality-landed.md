# Handoff: finite sets + cardinality arc — landed, next steps, open chores

**Date:** 2026-09-15
**Landed by:** the sets arc (commits `fc9c979e`, `d3793ea9`, `8812b0bb`, `0682a6ed`, `8dbf0908`)
**Context doc:** `docs/studies/2026-09-14-sets-cardinality-and-sat-watch-blocker.md`
(note: that study's "SAT blocker" section is now historical — `0aa996f2`
reverted `e987b4b6` and the watch-layer symptoms are gone; its "next steps"
section is still current and is the roadmap below).

## Where things stand

The ground finite-set theory with cardinality is **in and green**:

- SMT-LIB surface: `(Set X)` sorts; `set.union/inter/minus/member/subset/
  singleton/insert/card/complement/choose/is_empty/is_singleton`;
  `(as set.empty …)` / `(as set.universe …)` in both applied and standalone
  position; Z3-classic bare aliases (`union`, `member`, `card`, …) that yield
  to user declarations. `bag.`/`rel.` namespaces are reserved (undeclared use
  errors honestly) but **not implemented**.
- Decision procedure: `nixie-solver/src/solver/set_theory/` — `mod.rs` (the
  membership/extensionality reduction) + `cardinality.rs` (Venn-region/slack
  encoding: counting equations with equivalence-class dedup guards keyed by
  `(set, element-list)`, inclusion–exclusion over twins, slack monotonicity,
  subset↔size rules, finite-universe bounds, choose). Every emitted clause is
  a valid consequence of the theory, so a wrong `sat` cannot be manufactured;
  caps (cone > 40 sets, element list > 24) and unsupported constructs raise
  the honesty gate (`set_terms_unconstrained`) → honest `unknown`.
- Tests: `nixie-solver/tests/finite_sets_cardinality.rs` (32) +
  `finite_sets_decision.rs` (37) + `finite_sets_sort_and_terms.rs` — **78/78
  pass, nothing ignored**. At the last run: nixie-solver lib 1169/1169,
  nixie-core lib 1829/1829, fmt clean, clippy clean for all files in this
  arc.

Two soundness traps closed along the way (do not reintroduce):
slacks must key on the exact element list (per-assert re-runs grow the list;
sharing a slack across lists conjoins two valid equations into a false
`unsat`), and the builder rewrites (`~~s = s`, `s ∪ ∅ = s`, …) are
load-bearing (without the invololution `~~s ≠ s` survives the encoding).

## Open chores (do these first)

1. **Parity was NOT re-run after `0682a6ed`/`8dbf0908`.** The last parity run
   (after `d3793ea9`) was byte-identical to the recorded snapshot: 144
   correct / 33 inconclusive / 0 mismatch, z3 4.16.0. The follow-up commits
   touch `set_theory` and the parser's `(as …)` path, so the gate should be
   re-run: `./bench/z3_parity/run_parity.sh`. Expect no movement (the corpus
   has no set problems) but record it.
2. **`precompile/0682a6ed/` was not populated** — the release build was
   aborted by the user mid-command. If you need the binary, build
   `cargo build --release -p nixie-cli` and copy it in.
3. **Workspace-wide `--all-features` suite never completed** in this
   environment: the shared disk repeatedly hit 100 % mid-link (lld bus-errors
   on a full FS). Per-package runs substituted (numbers above). When the disk
   has headroom, one full `cargo nextest run --workspace --all-features`
   would close the verification bar properly.
4. `nixie-math/tests/ff_gb_scale_regression.rs` and
   `monomial_order_regressions.rs` still fail `clippy -D warnings` —
   pre-existing, committed by the math agent (`1f8fbea2`), not touched here.

## Roadmap (value order)

1. **Set model synthesis for `sat` + `get-value`.** Verdicts are now correct,
   but set-sorted variables print the factory default (`Value::Set([])`) —
   the model is not faithful for display. Needed: Z3-`set.unique`-style
   construction — each slack region contributes `slack` fresh elements,
   ground memberships read from the member atoms' final assignment. Touch
   points: `nixie-solver/src/solver/model_builder.rs`, `model_eval.rs`
   (SetMember/SetSubset currently fall to the unhandled arm), the slack
   variables are the `@set_card_slack_*` Ints the reduction creates.
2. **Relations** (`rel.join`, `rel.transpose`, `rel.product`, `rel.iden`):
   tuples can ride the datatype machinery (`(Tuple A B)` = auto-declared
   constructor + `(_ tuple_select i)`), and CVC5's `theory_sets_rels.cpp`
   membership rules reduce to this same eager scheme — join's existential
   witness skolemizes per (element, join-term) exactly like the disequality
   witnesses already do.
3. **Bags**: `bag.count` gives pointwise max/min/add identities; the
   cone/slack skeleton carries over with region *multiplicities*. Surface
   names: see cvc5 `smt2_state.cpp` (`bag.union_max`, `bag.difference_subtract`,
   …). AST needs a `SortKind::Bag(SortId)` plus ~10 TermKinds — the compiler
   will find every exhaustive match.
4. **Caps re-measurement** (`MAX_CONE_SETS=40`, `MAX_COUNT_ELEMENTS=24` in
   `cardinality.rs`): once the TLA+ corpus runs green end-to-end again,
   measure whether the caps gate real specifications and tune.

## Environment notes for whoever picks this up

- The shared disk (1.8 TB, multiple other projects) hovers at 95–100 %.
  `target/debug` grows ~25 GB per full test build; prune
  `target/debug/incremental` and old large artifacts in `target/debug/deps`
  before big builds (`find target/debug/deps -maxdepth 1 -type f -size +15M
  -mmin +5 -delete`). Use `CARGO_INCREMENTAL=0`.
- Parallel agents are active (SAT round-13/CSR watch work, FF/QF_UFFF,
  mfinder). Before committing: `git reset -q` to unstage everything, then
  stage only your files — the index regularly contains *their* staged work.
  `git status` twice; never stash.
- The `nixie-theories/src/set/*` module (~8 k lines) is **dead code** — a
  standalone unconsumed SetSolver from an earlier sweep. Not removed (out of
  scope); if you touch it, know that nothing in the solving path uses it.
