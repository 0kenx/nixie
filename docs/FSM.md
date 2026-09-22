# Explained finite-state-machine constraints

`nixie_theories::fsm::FsmModel` provides **symbolic acceptance constraints
over fixed finite NFAs with guarded transitions** through
`Solver::register_fsm` — MonoSAT's FSM acceptor theory
(`../temp/monosat/FiniteStateMachines.md`) realized as a reduction to the
explained symbolic graph propagator (`docs/GRAPH.md`). This is a Rust API
plus an SMT-LIB command surface (below); it is not a new SMT-LIB theory.
No external solver or FFI is used. `nixie-spacer` is unaffected.

```rust
use nixie_core::ast::TermManager;
use nixie_solver::{Solver, SolverResult};
use nixie_theories::fsm::{FsmModel, Label};

let mut tm = TermManager::new();
let mut fsms = FsmModel::new(&tm);
let a = fsms.new_automaton(2, 2)?;              // states {0,1}, symbols {0,1}
fsms.set_initial(a, 0)?;
fsms.add_accepting(a, 1)?;
let g = tm.mk_var("t", tm.sorts.bool_sort);
fsms.add_transition(a, 0, 1, Label::Symbol(1), g, &mut tm)?;  // exists iff t
let accepts_1 = fsms.accepts(a, &[1], &mut tm)?;              // reified atom
let mut solver = Solver::new();
solver.register_fsm(fsms, &mut tm)?;
solver.assert(accepts_1, &mut tm);             // demand acceptance of "1"
assert_eq!(solver.check(&mut tm), SolverResult::Sat);
// asserting (not accepts_1) instead forces t false: rejection via cuts.
# Ok::<(), nixie_theories::fsm::FsmError>(())
```

## Semantics

An automaton fixes a **finite state universe** `0..states`, a **finite
alphabet** `0..alphabet` (size zero allowed: epsilon-only automata), exactly
one **initial state**, and zero or more **accepting states**. A transition
`(from, label, to, guard)` exists in a candidate automaton **exactly when
its Boolean guard term is true**; guards may be any Boolean-sorted terms —
variables, negations, conjunctions, arithmetic comparisons, the constants
`true`/`false` — and the **same term may guard any number of transitions**
across positions, words, and automata: it keeps one meaning everywhere
(shared-term aliasing in the underlying graph model). Nondeterminism,
self-loops, parallel transitions (same `from`/`to`/`label`, different
guards), cycles, epsilon transitions and epsilon cycles are all allowed.

`accepts(word)` (constant word, symbols in `0..alphabet`) is reified as a
single fresh Boolean atom — usable positively, negatively, and in arbitrary
Boolean formulas, including with other theories — whose value is *defined*:
in every reported model it equals the automaton's acceptance of the word
under the model's guard assignment. **Acceptance** means some run consumes
the entire word and ends in an accepting state (runs start at the initial
state, take only existing transitions, consume one symbol per symbol
transition, nothing per epsilon transition). **Negated acceptance excludes
every accepting run.** The **empty word** is accepted exactly when the
initial state reaches an accepting state through epsilon transitions — in
particular when it *is* accepting.

Repeated `(automaton, word)` queries return the same atom. Malformed
declarations and references (unknown handles, out-of-range states, symbols,
or word symbols, missing/repeated initial state, duplicate accepting state,
non-Boolean guards, reused acceptance names, oversized products) are
explicit errors — never silently dropped.

## Procedure: product construction over the graph propagator

Acceptance lowers to reified graph reachability (MonoSAT's `NFAGraphAccept`,
`opt_fsm_as_graph`):

- Each `(automaton, word)` query builds a product graph with vertices
  `(state, position)` for `position ∈ 0..=len(word)`.
- A symbol transition `(q, a, q', g)` contributes the edge `(q,p) →
  (q',p+1)` at every position `p` where `word[p] = a`; an epsilon
  transition contributes `(q,p) → (q',p)` in **every** layer. Product edges
  reuse the guard term verbatim.
- The acceptance atom is defined by `atom ⟺ ∨_{qf ∈ F}
  reach((q0,0),(qf,n))` — two ordinary clauses asserted at registration —
  plus the constant `true` when `n = 0 ∧ q0 ∈ F`, and the constant `false`
  when `F = ∅`.

Why the disjunction (and not a fresh sink vertex with unconditional edges
from `(qf, n)`, the other construction we evaluated): Nixie graph
reachability counts paths of **length ≥ 1**, so the zero-length accepting
run (`n = 0`, `q0 ∈ F`) is exactly the extra constant; every other
accepting path has length ≥ n ≥ 1. The sink variant is equivalent but
needs unconditional product edges — additional asserted-true variables —
while the disjunction reuses only the reach atoms the propagator already
reifies, with no registration-time assertions beyond the biconditional
itself. Constant guards: `true` lowers to one per-model variable asserted
true at registration; `false` contributes no product edges (statically
dead transition).

Soundness is graph-reachability soundness plus the path/run correspondence:
a path in the product over present edges *is* an accepting run. Under
MonoSAT's forced/possible scheme, a path over forced (true-guard) edges
proves acceptance (explanation: the path's guard literals); the absence of
any path in the possible (non-false-guard) graph refutes it (explanation:
the cut of all false guards into the backward closure — for the FSM, a set
of disabled transitions blocking every accepting run). Learned clauses are
therefore justified by valid runs/cuts with correct polarity, and identical
guard terms appearing at several product positions explain together — the
graph propagator deduplicates repeated literals.

Epsilon cycles are handled *by construction*: they are cycles in the
layer graph, and reachability traverses cycles natively — no positional
unrolling assumptions are made.

## SMT-LIB command surface

Z3-style extension commands (the `declare-rel`/`rule` precedent for
non-standard theories), executed by `Context`:

```lisp
(set-logic ALL)
(declare-fsm A 3 2)                      ; 3 states {0,1,2}, alphabet {0,1}
(fsm.initial A 0)
(fsm.accepting A 2)
(declare-const g Bool)
(fsm.transition A 0 1 0 g)               ; guard g: exists iff g
(fsm.transition A 1 2 0 true)            ; unconditional
(fsm.transition A 1 1 1 eps)             ; epsilon (label `eps`)
(fsm.accepts A (0 0) accepts_00)         ; declares Bool const accepts_00
(assert (not accepts_00))                ; "00" must be rejected
(check-sat)                              ; sat iff some g makes "00" rejected
```

`fsm.accepts` **declares and defines** the named Boolean constant (the
parser registers the name for subsequent terms; the constant appears in
`get-model` and `get-value`). State/symbol/word positions are numerals; the
epsilon label is spelled `eps`. The declaration set is validated eagerly at
each command (unknown automata, out-of-range indices, duplicate names are
command errors) and re-validated at registration. The model registers
lazily at the first solving/asserting/pushing command — always at assertion
scope zero, matching the propagator lifecycle — and re-registers
automatically after `reset-assertions` (declarations survive, per SMT-LIB);
`reset` clears them.
`reset` clears them.

**Late acceptance queries register incrementally.** A `fsm.accepts`
arriving after registration has already fired (e.g. interleaved with
asserts — a natural authoring order) registers an *additional*
propagator for the new query at the next command; earlier queries stay
bound by the first registration. Mutating a registered automaton
(`fsm.transition`/`fsm.initial`/`fsm.accepting` after solving began) is a
loud command error: its product graphs are live and cannot be
retrofitted — never a silent drop. (The original registration guard
silently dropped late queries, leaving their constants unconstrained —
a false-sat found by the `bench/fsm_perf` verdict-agreement canary and
pinned by `nixie-solver/tests/fsm_script_lifecycle.rs`.)

## Scope, lifecycle, and limits

- **In scope**: guarded NFAs, constant-word acceptance and rejection,
  synthesis from positive/negative word examples via guard search,
  automata mixed freely with all other theories.
- **Out of scope** (not implemented, not advertised): symbolic words,
  generators, acceptor–generator composition, transducers, minimization,
  unbounded state universes, and any Spacer/CHC interaction.
- **Lifecycle**: register at assertion scope zero before the first check;
  afterwards `push`/`pop`, repeated checks, assumptions, and `reset` follow
  the graph/CP contract (`docs/CP.md`). The propagator is stateless across
  backtracking; the defining biconditionals and the asserted-true variable
  are root-level assertions and survive every legal scope change.
- **Scale**: the product graph has `|Q|·(|w|+1)` vertices and
  `O(|δ|·|w|)` edges per query; construction uses checked arithmetic and
  fails closed (`"product graph too large"`) instead of overflowing. Layer
  sharing across words (MonoSAT's prefix tree) is a documented future
  optimization, not implemented.
- **Guard terms and SAT variables**: a guard may be any Boolean term. A
  term and its negation may both appear as guards (or as guards plus
  assertions): watch routing supports several watch terms per SAT variable.
  Guards must not be acceptance atoms *of the same model* (rejected);
  across two separately registered models, an acceptance atom of one may
  guard the other.

## Proof and certification boundary

FSM registrations are **proved callbacks**. At registration,
`FsmModel::graph_statements` re-derives every product graph from the
original automaton declarations by an independent computation (matching
labeled transitions advance a layer, epsilon stays, constant guards
resolve to the asserted-true variable / no edge, duplicates collapse) and
checks the statement's vertex count, edge set, and reach-atom pairs
against it — a mismatch is an explicit error, so the retained statements
that anchor certificate checking are provably the reduction of the
declared automata and words. From there the graph certificate chain
applies (`docs/GRAPH.md`):

- every consequence carries a checkable path/cut witness over the
  product statements; checking recomputes explicit closures — for the
  FSM, a path lemma *is* an accepting run of the declared automaton and
  a cut lemma *is* a set of disabled transitions blocking every
  accepting run;
- certified and proof-producing verdicts stand on the checked chain:
  models are re-validated against the closure oracle (which, through the
  registration-time equivalence, validates against the original
  declarations), and unsat refutations are reconstructed from
  certificate-checked graph lemmas plus LRAT (`GraphLemma` records in
  the proof envelope, version 2).

Ordinary solving remains complete for the fragment, and
`FsmModel::accepts_under` is an **independent reference interpreter**
(iterative `(state, position)` search with epsilon steps — no product
construction) for validating models against the original declarations;
the test suites use it as the primary oracle. SMT unsat cores, when
available, are relative to the permanently installed FSM constraints.

## Test and audit basis

- `nixie-theories/src/fsm/tests.rs` — propagator-level exhaustive oracles:
  for every case automaton, every partial guard assignment is replayed
  through `UserPropagatorManager`, and every emitted consequence is checked
  against **all guard completions** with a per-target run oracle (runs
  ending at one specific accepting state — the exact meaning of one product
  reach atom, including the `n = 0` self-pair epsilon-cycle case). The
  interpreter-vs-disjunction equality is checked per completion. Covers
  chains with shared guards, skip edges, epsilon back-edges, epsilon
  cycles, the empty word, parallel and constant guards, self-loops,
  disconnected states, multiple accepting states, guard sharing across two
  automata, negated and compound guards, determined propagation at
  all-fixed, malformed declarations, oversized products, query caching and
  naming.
- `nixie-solver/tests/fsm_constraints.rs` — end-to-end CDCL(T) level:
  exhaustive differential against the interpreter (every total guard
  assignment × both acceptance polarities × every case word, with
  independent re-validation of every returned model), agreement with an
  **independent exact SAT encoding** (layered one-hot reachability with
  bounded epsilon-relaxation unrolling — structurally unrelated to the
  product reduction; the layering makes its biconditional system acyclic,
  hence exact), synthesis from positive and negative examples with
  interpreter validation, contradictory requirements, structural
  unsatisfiability, Boolean combinations with arithmetic guards,
  push/pop lifecycles, and certified-mode fail-closed.
- `nixie-solver/src/context.rs` tests — SMT-LIB surface: synthesis script
  with `get-value`, epsilon/empty-word script, malformed-input command
  errors, `reset-assertions` re-registration, `reset` clearing, compound
  and shared guards through the parser.

### Invariants audited (and where)

| Invariant | Evidence |
|---|---|
| Product path ⟺ accepting run (incl. zero-length, epsilon cycles) | interpreter-vs-disjunction checks in `fsm/tests.rs` (per completion); empty-word/epsilon-cycle oracle cases |
| Shared guards keep one meaning across positions/words/automata | graph `oracle_shared_guard_edges` (all partial states × all completions); `shared_negated_and_compound_guards`; `fsm_script_compound_shared_guards` |
| Consequences valid over partial assignments, correct polarity | `fsm/tests.rs` consequence validation vs. per-target run oracle over all completions |
| Solver verdicts match interpreter on complete assignments | `fsm_constraints.rs` exhaustive differential |
| Reduction agrees with an independent encoding | `independent_sat_encoding_agrees` |
| Models validate against original declarations | model re-validation in the exhaustive differential; synthesis read-back |
| Backtracking / scope correctness | graph propagator oracles (inherited), `push_pop_lifecycle`, script push/pop, `reset_assertions` re-registration |
| Malformed input rejected explicitly | `rejects_malformed_declarations`, `rejects_oversized_product`, script error tests |
| Certification/proof fail-closed | `certified_mode_fails_closed` (Unknown in certified mode) |
| Term/negation watch routing (adapter change) | `negated_duplicate_watch_terms_both_route`; full graph/CP/solver suites re-run |

Reference: Bayless, Bayless, Hoos, Hu, *SAT Modulo Monotonic Theories*
(AAAI 2015); MonoSAT's `FSMAcceptDetector` and `NFAGraphAccept`
(`../temp/monosat/src/monosat/fsm/`). Semantics deviations from MonoSAT
(none in the acceptance relation itself; MonoSAT's per-query
initial/accepting states are automaton-level here) are documented above
rather than inherited silently. MonoSAT's experimental FSM implementation
is a design reference, **not** a correctness oracle — the oracles above
are independent.
