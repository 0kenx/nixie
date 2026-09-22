# Handover — the FSM theory arc: guarded NFAs, checked certificates, and a witness-speed campaign (2026-09-22)

The full arc for the MonoSAT-style FSM feature, from spec to benchmark.
Everything here is **landed on `main` and pushed** (through `f667e809`;
later commits on main are other agents'). AGENTS.md applies as always.
Semantics reference: `docs/FSM.md`; campaign record:
`docs/studies/2026-09-22-fsm-perf-vs-z3.md`.

## What landed (five commits, oldest first)

1. **`bff44efd` (orig. `4320da52`) — feat(fsm): guarded-NFA acceptance
   constraints.** `nixie_theories::fsm::FsmModel` + `Solver::register_fsm`
   + the Z3-`declare-rel`-style SMT-LIB command surface (`declare-fsm`,
   `fsm.initial/accepting/transition/accepts`). Acceptance lowers to
   graph reachability over per-(automaton, word) product graphs;
   acceptance atom = `∨_{qF} reach((q0,0),(qF,n))` + the zero-length
   constant. Enablers that landed with it: **shared guard terms across
   graph edges** (`by_var: Var → Vec<(term, lit)>` in the adapter — a
   term and its negation can both be watched) and
   `FsmModel::accepts_under`, the independent reference interpreter.
   Verified by exhaustive oracles (every consequence against all guard
   completions), an independent exact SAT encoding, and synthesis
   read-backs.
2. **`a895c69c` (orig. `f722fe05`) — checked path/cut/cycle
   certificates.** `GraphStatement` (immutable declaration snapshots,
   Arc-identity) + certificates on every graph consequence; `register_
   graph`/`register_fsm` count as *proved* callbacks; certified
   Sat/Unsat verdicts stand on checked chains; `CpProof` grew
   `graph_lemmas` (envelope v2). FSM reduction is validated against the
   automaton declarations at registration by independent re-derivation.
3. **`1cbb34e9` — fix(fsm): late `fsm.accepts` queries register
   incrementally.** A **false sat**: the registration guard silently
   dropped FSM declarations arriving after the first assert; the
   constant stayed unconstrained. Found by the benchmark's
   verdict-agreement canary; regression suite
   `nixie-solver/tests/fsm_script_lifecycle.rs`. Registration is now
   epoch-based; mutating a registered automaton errors loudly.
4. **`ef51d4d4` — the benchmark itself.** `bench/fsm_perf/` (paired
   generator + runner, seed-pinned) and the study. Its canary caught
   item 3 before any number was recorded.
5. **`f667e809` — perf: witness-form certificates.** Profiling showed
   the recompute checker (O(V·E) closures per consequence, in the CDCL
   loop) was **96 % of solve cost**. Now the propagator attaches the
   witness it already computed (`GraphRule::Path/Cut/NoCycleThrough/
   Cycle/TopoOrder`) and checking is linear. Benchmark total vs Z3:
   **1.34 → 0.123** (nixie 8× ahead; unsat families 40–170×).

## Ranked open items

1. **Propagator per-event O(V+E) scans** — the remaining ceiling
   (s64_w80 ≈ 2 G instructions of graph maintenance). Upgrade:
   incremental (Ramalingam–Reps) reachability + prefix layer sharing
   across words of one automaton. This is the next real FSM perf slice.
2. **Min-cut explanations** (smaller cut clauses) — would compound the
   refutation advantage. *Heuristic* change: full matched-null + ≥10-seed
   discipline applies (docs/BENCHMARKING.md §2).
3. **cvc5 third benchmark column** — runner already accepts any SMT-LIB
   binary; cvc5 just isn't installed here.
4. **Doc drift**: `docs/GRAPH.md`'s certification paragraph still says
   checking "recomputes explicit closures" — now only the cold
   proof-reconstruction path (`GraphStatement::check_lemma`); the hot
   path is witness-form. One-paragraph fix, unlanded.
5. **Formal full-workspace run** since `f667e809` — the landing battery
   covered the three touched crates (7135/7136 + gates; the 1 timeout is
   the known-slow `scope_rebase` test, passes solo). Untouched crates
   make risk low, but the AGENTS bar is workspace-wide.
6. **`dae75398`** — one orphaned corrupt tree (unreachable from any
   branch) still trips `git fsck`. Inert; removable via reflog expire +
   repack in a quiet window.

## Traps this arc hit — read before touching any of it

- **The hybrid-PMU counter trap (this machine).** Unpinned
  `perf stat -e instructions:u` inflates by load-dependent per-cluster
  scaling — identical binaries measured **6× apart**. Any instruction
  benchmark here must pin to one P-core and use
  `-e cpu_core/instructions/u` (A/A then agrees to 1e-6). The first
  campaign's absolute numbers were partly noise; ratios in the study are
  the pinned ones.
- **`g` and `¬g` as guards in one model**: a term can be one edge's
  atom and another's negation — premise classification must be per-edge,
  never a global atom/negation partition (bug caught mid-redesign by the
  all-features suites; the exhaustive graph oracles pin it).
- **Self-pair reach** (`reach(u,u)` = cycle-through-u) is the recurring
  sharp edge: cuts for it need the `NoCycleThrough` T-form witness
  **and T-form reasons** (edges leaving `closed ∪ {u}`), which differ
  from the ordinary cut's into-closure reasons. Any new emission site
  must split on `from == to`.
- **Path witnesses are collected backwards** (parent walks); they must
  be reversed to walk order before certification.
- **Registration is permanent per epoch**: new `fsm.accepts` after
  solving began → incremental registration; *structural* fsm
  declarations after that → loud error. Both behaviors are pinned by
  `fsm_script_lifecycle.rs`; don't "simplify" them back to one-shot.
- **Same-word double reification** (accept ∧ reject the same word via
  two queries) is pathological for *any* encoding — the solvers must
  derive the two reifications' equality through shared guards alone.
  Keep canaries short-worded.
- **Git on this box**: disk-full windows corrupted a tree (duplicate
  `docs/` entries — the `1255312e` repair, re-parented descendants
  `8cec1b9e..b43ef769`); git 2.54's merge-ort crashes replaying
  rebase-i over such churn (use `git pull --no-rebase` on divergence
  until git is fixed); the shared target/ gets pruned by parallel agents
  mid-session — rebuilds may be needed before gates.
- **Worktree hygiene**: another agent snapshotted my in-flight files
  once (`e0bfaf7d` pattern) and staged files in my worktree another
  time — always commit with explicit pathspecs, never `-a`, and check
  `git status` belongs to you before landing.

## Where the code lives

- `nixie-theories/src/fsm/` — model, reduction, interpreter, oracle tests.
- `nixie-theories/src/graph/proof.rs` — statements, witness rules,
  checkers (hot: `GraphCertificate::check`; cold: `check_lemma`).
- `nixie-theories/src/graph/mod.rs` — emission sites (all certificate
  constructions), `forward_ge1_set`, `ge1_leaving_negations`,
  `nonfalse_topo_order`.
- `nixie-solver/src/solver/user_propagation.rs` — statement retention,
  `certificate_valid`, model-gate statement checks, `register_graph/
  register_fsm`.
- `nixie-solver/src/solver/cp_proof.rs` — `GraphLemma`, envelope v2.
- `nixie-solver/src/context.rs` — command surface, eager validation,
  epoch-based `ensure_fsm_registered`.
- `bench/fsm_perf/` — `gen.py` (paired instances, seed 20260922),
  `run.sh` (pinned methodology).
- Tests: `fsm/tests.rs`, `graph/tests.rs`, `graph/proof.rs` unit tests,
  `nixie-solver/tests/{fsm_constraints,fsm_script_lifecycle,
  graph_constraints}.rs`.
- Binaries: `precompile/4320da52*/` (≡`bff44efd`), `precompile/a895c69c/`,
  `precompile/1cbb34e9/`, `precompile/f667e809/` (current).
