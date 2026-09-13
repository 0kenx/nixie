# HANDOFF — UFLRA/quantifier parity: finish the set-family sat gap

You are picking up an in-flight work stream in the nixie repo (pure-Rust SMT
solver, `/media/data/proj/nixie`, main checkout on `main`). Read AGENTS.md
first — it is canonical. This prompt assumes you have.

## Mission

"Pick any theory class and close the gap with z3." The theory picked (by
`shuf`) was **UFLRA**. Six commits landed the machinery and closed most of
the measurable gap. One well-defined piece remains.

## Current state (verify before trusting)

Landed arc, oldest first (`git log` on main):
- `cbe525fc` — Z3-style nested model checker + arith-interface repair (FFT parity)
- `d18b6f36` — universe seeding, nested-binder ownership, honest encoding
- `a95b3909` — nested-∃ skolemization at assert + Rodin false-sat veto
- `2e02da6c` — closed-world Bool else + redundant-entry collapse
- `a9fe0ec9` — macro completion wired end to end
- `b8f8db60` — sixth-pass study (designs recorded, code reverted)

Corpus state (`smt-lib/non-incremental/UFLRA/`, z3 4.16.0 as oracle):
- `FFT/*` (10 files): all **unsat**, matching z3. Was 2 × `unknown`. CLOSED.
- `misc/set9,set16,set19`: z3 `sat`, nixie `unknown`. THE REMAINING GAP.
- `misc/list2,set14`: z3 itself times out — not a gap.
- `AUFLIA/20170829-Rodin/smt4688353851435564037`: `:status unsat`; nixie must
  answer `unsat` or `unknown`, never `sat` (a pre-existing false-sat was
  contained; dozens of archived `precompile/*/nixie` binaries answer `sat` on
  it — it is the canary for this whole area).

Regression pins: `nixie-solver/tests/uflra_quantifier_regressions.rs` (7 tests,
including the exact Rodin transcription). Parity suite
`bench/z3_parity/run_parity.sh` must stay 176 Correct / 1 Inconclusive
(the one is z3-side `Unknown` on `array_unique.smt2`, pre-existing).

The complete technical record — every root cause, every dead end, every
reverted experiment with its reason — lives in
`docs/studies/2026-09-12-uflra-parity-nested-model-checker.md` (six dated
passes; read it end to end before touching code; the "Fifth pass" and "Sixth
pass" sections carry the current frontier).

## Architecture you inherit

- `nixie-solver/src/mbqi/model_checker.rs` — the Z3 `smt_model_checker` port:
  completed model (entries + else), ite-chain completion, Skolemized nested
  refutation (`aux_refute`), term-level falsifier mining, `check_veto`
  second opinion gating the legacy `Satisfied`. Budgets everywhere
  (per-quantifier cap 2, global 50k conflicts, depth-2 nesting guard,
  entry caps counting *chain-relevant* entries only).
- `nixie-solver/src/mbqi/model_completion.rs` — `CompletedModel` now carries
  `macros: FxHashMap<Spur, MacroDef>`; `MacroSolver::solve_macros` extracts
  `∀x. f(x) = body` definitions but `macro_to_interpretation` still builds an
  EMPTY interpretation (the defining body travels via `macros`, not entries).
- `nixie-solver/src/mbqi/integration/mod.rs` — escalation wiring (only when a
  round's cex search found nothing), the lazy veto gate at the legacy
  `Satisfied`, `deep_simplify` (note: NO Forall/Exists arms on main — that
  is the emission-side root cause, see below).
- `nixie-solver/src/solver/encode/exists_skolem.rs` — NNF-skolemization at
  assert for positive-polarity ∃ under a ∀ (witness-in-implication shape).
- `nixie-solver/src/solver/mod.rs` — `intern_compound_uf_args_into_arith`
  (interface repair), `register_unit_lemma_quantifiers` (guarded binder
  ownership), MBQI round loop with unproductive-streak bail (10).

## The remaining work, precisely scoped

Two items, to be landed as ONE measured unit:

**(1) The blocking-clause model repair (Z3 `add_blocking_clause`).** Final
mechanism, fully diagnosed: the universe admits *compound constructor terms*
(`union(b,a)`) as elements. A definitional axiom (`seteq(z,z)=(z=z)`) fails at
every unpinned compound diagonal; the forcing instance would pin it, but the
enumerative seeder's per-quantifier budget is exhausted by the time the
compound term enters the universe, so the pin never lands and the rounds
spin on duplicate falsifiers. Repair: at the escalation's
duplicate-falsifier point, block the model arrangement — emit a clause that
excludes the falsifier's supporting commitments — forcing the next model to
either produce the witness the committed-false Boolean claims (∃x.¬φ) or
flip the commitment. Read Z3's `src/smt/smt_model_checker.cpp`
(`add_blocking_clause`, `check`) — reference trees are at `../temp/z3`.

**(2) Re-land the emission-side collapses.** `deep_simplify_cached` has no
Forall/Exists arms; quantifiers are opaque, so
`(∀x. P(x)⇒P(x)) ⇒ subset(z,z)` keeps its wrapper and the SAT core dodges
via the wrapper's free Boolean. The full working implementation existed
(QuantBody frame, binder descent, `∀x.true → true` constant collapse — sound
under SMT-LIB non-empty domains, `p→p` collapse already on main) plus
`SatisfiedWithPins` (certifying a macro's defining axiom also emits its
defining instances at universe tuples) and the simplest-body macro
preference inside `solve_macros`. All of it was REVERTED because the
collapses reshape every MBQI instance's clauses — a SAT trajectory shift
costing the 600-rerun convergence pins 1.5–1.9× single-threaded
(`scope_rebase_tests`). Designs and exact code shapes are in the study's
"Sixth pass" section. Re-land TOGETHER with (1), then run the matched-null
protocol (docs/BENCHMARKING.md) — the collapses' clause-shape change IS the
treatment; a matched null re-shapes clauses without the semantic content.

## Verification bar (all of it, before any landing)

```
cargo build --all-features
cargo nextest run --workspace --all-features      # may be blocked by other agents' WIP; then run the six core crates
cargo clippy --all-features --all-targets --workspace -- -D warnings
cargo fmt --all -- --check
cargo doc --no-deps --all-features --workspace    # with RUSTDOCFLAGS="-D warnings"
./bench/z3_parity/run_parity.sh                   # z3 4.16.0; record the version
```
Plus the differential screen (the thing that caught two false-sats this arc):
sample 150+ files from `smt-lib/non-incremental/{AUFLIA,UFLRA,UFLIA}` at 10s,
compare verdicts to z3, ZERO wrong answers acceptable. And the heaviest
convergence pin single-threaded:
`cargo test -p nixie-solver --all-features --no-run scope_rebase` then run
`target/debug/deps/nixie_solver-* --test-threads=1 \
 scope_rebase_tests::re_running_the_search_on_an_unchanged_goal_converges`
— baseline ~55–90s single-threaded user time; investigate before landing
anything that pushes it past ~2 min.

After landing: `cp target/release/nixie precompile/$(git rev-parse HEAD)/`.

## Hard-won traps (each cost real time this arc)

- **Trajectory sensitivity**: any change to MBQI instance clause shapes
  shifts the SAT trajectory; the rerun pins measure trajectory, not code
  cost. Bisect cost in a clean worktree (`git worktree add /tmp/wt HEAD`;
  copy suspect files in one at a time) before believing a regression is
  yours — and before believing it ISN'T.
- **The completed model's universes contain bound-variable artifact terms**
  (entry args harvested by `collect_universes_from_model`). Any reasoning
  "X is in the universe ⇒ X is a domain element" must first check
  `is_symbolic` — one false fold through this fabricated a fake falsifier.
- **Sampled "universes" for Int/Real are samples, not domains.** Skolem
  restriction to them fabricates unsat. Only uninterpreted sorts.
- **Budget-exhausted quantifiers (`can_instantiate() == false`) are NOT
  satisfied** — the veto in the per-quantifier loop is load-bearing (the
  Rodin false-sat mechanism).
- **`sync_guard_commitments` marking committed-false guards inactive is a
  loophole for lemma-registered binders** — a committed-false inner binder
  is an existential claim, not a vacuous branch.
- The nested `Solver`'s `Model` does not report Set-sorted Skolem values —
  that's why falsifier mining is term-level (odometer over combos), not
  model-readback.
- **The shared tree**: never `git stash`/`restore`/`checkout --` (other
  agents work in parallel); stage only your files; other agents' WIP
  (nixie-sat, nixie-tla, nixie-core set theory) may block whole-workspace
  builds — verify your crates in a clean worktree then. Disk fills
  repeatedly; clean `target/debug/{incremental,examples}` and stale deps.
- Another agent is building a native set theory
  (`nixie-solver/src/solver/set_theory.rs`, commits `f63b41f1`+). Coordinate
  before investing heavily — their work may subsume the set family entirely.
  The fixes above are logic-independent and worth landing regardless.

## Reproducers (keep them)

- `FFT` shape: pinned as `fft_periodicity_is_unsat` (test).
- Rodin: exact transcription pinned as `rodin_goal_quantifiers_are_never_falsely_satisfied`.
- set16 minimal: 6-axiom UFLRA script in the study ("Fifth pass" shows it);
  rebuild from there. Never-wrong pinned, but the goal is `sat`.
- `NIXIE_DEBUG_MC=1` enables the model-checker debug channel;
  `NIXIE_DEBUG_QROUNDS=1` the round trace. Both print to stderr.
