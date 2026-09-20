# Explained finite directed-graph constraints

`nixie_theories::graph::GraphModel` provides **symbolic graph constraints over
fixed finite vertex universes** through `Solver::register_graph`. This is a
Rust API, not a new SMT-LIB theory. The constraints run inside the CDCL(T)
search via the explained user-propagator integration
(`Solver::register_user_propagator`); the standalone
`nixie_theories::special_relations::SpecialRelationSolver` is unrelated
bookkeeping that no solving path consults. No external solver or FFI is used.

```rust
use nixie_core::ast::TermManager;
use nixie_solver::{Solver, SolverResult};
use nixie_theories::graph::GraphModel;

let mut tm = TermManager::new();
let mut graphs = GraphModel::new(&tm);
let g = graphs.new_graph();
let a = graphs.add_vertex(g)?;
let b = graphs.add_vertex(g)?;
let e_ab = graphs.new_edge(g, a, b, &mut tm)?;
let e_ba = graphs.new_edge(g, b, a, &mut tm)?;
let reaches = graphs.reach(g, a, b, &mut tm)?;
let acyclic = graphs.acyclic(g, &mut tm)?;
let mut solver = Solver::new();
solver.register_graph(graphs, &mut tm)?;
solver.assert(reaches, &mut tm);   // a must reach b
solver.assert(acyclic, &mut tm);   // ... on an acyclic graph
assert_eq!(solver.check(&mut tm), SolverResult::Sat);
# Ok::<(), nixie_theories::graph::GraphError>(())
```

## Semantics

Graphs are **directed** and each has a **fixed finite vertex universe**,
extended one vertex at a time with `add_vertex` (opaque `VertexId` handles,
local to their graph; `VertexId::new` addresses them by index). A model may
hold several independent graphs.

An **edge** is a Boolean term — either a fresh variable from `new_edge`, or
any non-constant Boolean term of your own via `add_edge` (a conjunction, an
arithmetic equality, ...). The edge is present in the graph exactly when its
term is true in the model. Parallel edges (several terms for one ordered
pair) and self-loops are allowed; the same term cannot name two edges or a
graph atom within one model. Atoms minted by `new_edge`/`reach`/`acyclic`
carry a per-model salt, so several models over one term manager never
silently share atoms through name interning; passing the *same* user term
to two models deliberately aliases those edges.

`reach(g, u, v)` reifies **reachability**: it is true iff some directed path
of **length ≥ 1** over present edges leads from `u` to `v`. **Zero-length
paths do not count** — unlike MonoSAT's `reach`, which counts the empty path
and therefore holds trivially for `u = v`. The strict reading is the more
expressive primitive:

- `reach(g, u, u)` is true exactly when `u` lies on a directed cycle
  (a self-loop suffices), and it is unsatisfiable together with `acyclic(g)`.
- Reflexive reachability is `(u = v) ∨ reach(g,u,v)` — a disjunction callers
  build themselves when they want the MonoSAT convention.

`acyclic(g)` reifies **acyclicity**: true iff the present-edge subgraph
contains no directed cycle, self-loops included. Assert the atom to demand a
DAG; assert its negation to demand a cycle.

Both atom families are **defined**, not constrained: in every reported model
each atom's value equals the graph-theoretic fact (enforced by lazy
propagation plus a complete final check, and re-validated independently
before a model is reported).

## Callback and explanation contract

Registration follows the CP lifecycle (`docs/CP.md`): register at assertion
scope zero **before the first check**; afterwards normal `push`/`pop`,
repeated checks, assumptions, and `reset` all work, and registrations are
permanent until `reset`. `register_graph` is a thin wrapper over
`Solver::register_user_propagator` with the model's own watch list (edge
atoms, reach atoms, acyclicity atoms). `check_sat_only` cannot bypass the
constraints.

Every propagation and conflict is explained over **signed edge assignments**:
a `Consequence` whose justification is a list of edge literals — the edge
atom for a true edge, its negation for a false one — plus, for conflicts, the
offending graph atom's literal. The solver learns ordinary clauses:

| Fact | Explanation (MonoSAT correspondence) |
|---|---|
| `reach(u,v)` forced true | the concrete path's true edge atoms (`buildReachReason`) |
| `reach(u,v)` forced false | every false edge into the backward-reachable set of `v` (`buildNonReachReason`'s cut) |
| `acyclic` forced false | a concrete directed cycle's true edge atoms (`buildDirectedCycleReason`) |
| `acyclic` forced true | all currently false edges (the trivial clause, `buildNoDirectedCycleReason`) |

The negative-reachability cut deserves emphasis, because an attractive
shortcut is unsound: the cut must be taken over the **backward** closure of
the target (vertices that can reach `v` through possible edges), and it must
include *every* false edge into that set. A forward-closure cut can justify
`¬reach(u,u)` with an empty justification, which becomes a permanent unit
clause and can then wrongly refute graphs that re-enable those edges — a
false `unsat`. The exhaustive oracle tests caught exactly this during
development; the shipped form is validated against all completions.

The propagator is **stateless**: every event re-derives the forced graph
(edges true) and the possible graph (edges not false) from the current fixed
values, so search `push`/`pop` needs no trail and cannot leak scope state.
The cost is a full recomputation per watched-atom event — O(V·E) per event in
the worst case. This first integration targets tens of vertices and hundreds
of edges; it makes no throughput claim relative to MonoSAT, whose incremental
dynamic-graph algorithms (Ramalingam–Reps reachability, dynamic max-flow
min-cuts, PK topological order) are the documented upgrade path.

## Procedure and references

The propagator implements the Boolean monotonic-theory scheme of

- Sam Bayless, Noah Bayless, Holger H. Hoos, Alan J. Hu,
  *SAT Modulo Monotonic Theories*, AAAI 2015,

as realized in MonoSAT's `ReachDetector` and `CycleDetector`
(`../temp/monosat/src/monosat/graph/`): reachability is monotone increasing
in the edge assignment and acyclicity monotone decreasing, so an
under-approximation (true edges) decides positive polarity, an
over-approximation (non-false edges) decides negative polarity, and the two
approximations converge at complete assignments, where `final_check`
enforces the defining biconditional. MonoSAT's `-conflict-min-cut`
variant (max-flow minimum cuts for smaller negative explanations) and its
theory-directed decision heuristics are future work; the BFS cut and SAT
default decisions are complete for this fragment.

## Limits

- **Scope**: directed graphs, fixed finite vertex universes, Boolean edge
  presence, reified reachability/non-reachability, reified acyclicity.
  **Deferred**: weighted/shortest-path constraints, flows, undirected
  connectivity, spanning trees, unbounded or dynamic vertex universes, and
  edge forcing (MonoSAT's `buildForcedEdgeReason`).
- **Zero-length paths** are excluded from `reach`; see above.
- **Performance**: recomputation per event, memoized through a
  content-addressed view cache (per-source forced BFS, per-target backward
  BFS and cycle checks are reused whenever the packed true-/non-false-edge
  bits are unchanged — false assignments keep the forced view, true
  assignments keep the possible view, backjumps often revisit seen keys);
  no incremental algorithms. Measured against MonoSAT (see the studies
  below): on the release corpus (n ≤ 150) Nixie runs at ≈1.65× MonoSAT's
  geomean after the 2026-09-20/21 throughput passes (was 5.1×). The
  propagator maintains its views **incrementally from edge events** (O(1)
  per event; BFS trees merge on edge additions; backtracks re-read from
  scratch), so recomputation is paid only after backtracking — the
  remaining gap is term interning + the general SMT stack, not the graph
  theory.
- **Certification**: graph registrations are trusted client callbacks
  without independently checkable certificates. Proof-producing and
  certified checks fail closed to `Unknown` for them (the same boundary as
  arbitrary user propagators; built-in CP constraints are the model for how
  certificates would be added). Ordinary solving is complete for the
  fragment, and returned models are replayed through the propagator before
  being reported. Unsat cores, when available, are relative to the
  permanently installed graph constraints and do not serialize them.

## A realistic network-policy example

Zones `internet → dmz → app → db` with switchable links, plus a deployment
dependency overlay that must stay acyclic (the same scenario as the
executable test `network_policy_scenario` in
`nixie-solver/tests/graph_constraints.rs`):

```rust,ignore
let mut graphs = GraphModel::new(&tm);
let net = graphs.new_graph();
// four vertices: internet(0) dmz(1) app(2) db(3)
let l_in_dmz   = graphs.new_edge(net, v(0), v(1), &mut tm)?; // internet → dmz
let l_dmz_app  = graphs.new_edge(net, v(1), v(2), &mut tm)?; // dmz → app
let l_app_db   = graphs.new_edge(net, v(2), v(3), &mut tm)?; // app → db
let l_in_app   = graphs.new_edge(net, v(0), v(2), &mut tm)?; // bypass
let l_dmz_db   = graphs.new_edge(net, v(1), v(3), &mut tm)?; // shortcut

let internet_reaches_dmz = graphs.reach(net, v(0), v(1), &mut tm)?;
let internet_reaches_app = graphs.reach(net, v(0), v(2), &mut tm)?;
let internet_reaches_db  = graphs.reach(net, v(0), v(3), &mut tm)?;
let app_reaches_db       = graphs.reach(net, v(2), v(3), &mut tm)?;

solver.register_graph(graphs, &mut tm)?;
solver.assert(internet_reaches_dmz, &mut tm);      // public entry point live
solver.assert(app_reaches_db, &mut tm);            // app uses the database
solver.assert(mk_not(internet_reaches_db), &mut tm); // db never internet-exposed
// Sat: the solver disables dmz→app, internet→app and dmz→db; the only
// enabled paths are internet→dmz and app→db.
solver.push();
solver.assert(internet_reaches_app, &mut tm);
// Unsat: admitting the internet to the app tier transitively exposes the
// database — exactly the transitivity a firewall review must catch.
```

The dependency overlay (a second graph in the same model) declares
`app→db`, `dmz→app` and the reverse `db→dmz` dependency; asserting the first
two plus `acyclic(deps)` is satisfiable, and additionally asserting `db→dmz`
makes the overlay cyclic — unsatisfiable. Together the two graphs check a
segmentation policy *and* a deployment-order constraint in one query.

## Test and audit basis

- `nixie-theories/src/graph/tests.rs` — propagator-level exhaustive oracles:
  every partial edge/atom state of each case graph is replayed through
  `UserPropagatorManager`, and every emitted consequence/conflict is checked
  against **all** concrete graphs (not just completions of the current
  state), with verdicts compared to an independent violation analysis.
  Covers triangles with cycles and chords, parallel edges, self-loops,
  disconnected vertices, empty graphs, complete assignments in every atom
  polarity, scoped replay, non-Boolean fixation fail-closed, multi-graph
  independence, malformed construction, and the zero-length-path rule.
- `nixie-solver/tests/graph_constraints.rs` — end-to-end: all `2^(n²)`
  digraphs for n ≤ 3 with model re-validation against a closure oracle;
  exhaustive single-atom-flip unsat (both polarities); exhaustive acyclic
  classification (n ≤ 3) plus a sampled n = 4 run; brute-forced
  partial-assignment verdicts; push/pop lifecycles; combinations with
  Boolean structure and linear arithmetic; certified-mode fail-closed; and
  the network-policy scenario above.

The reference for the procedure is MonoSAT's source and the AAAI 2015 paper;
semantics deviations (zero-length paths) are documented above rather than
inherited silently.

## Performance study

`docs/studies/2026-09-19-graph-perf-vs-monosat.md` profiles the integration
against MonoSAT, lands six semantics-inert optimizations (manager undo
journals replacing per-level state clones, O(1) watch lookup, hash-set
registration dedup, gated set/bag and BV per-assertion surveys, and the
graph view cache), and verifies inertness by **bit-identical
conflicts/decisions/propagations** on the whole corpus plus the full gate
battery. Several fixes benefit every SMT workload, not just graphs: the
set/bag re-survey was quadratic in the number of assertions for any goal
without set/bag terms.

## Differential campaign against MonoSAT

`bench/graph_differential/` runs verdict parity against the MonoSAT
reference implementation itself on randomly generated GNF instances
(generator + driver script; `nixie-solver/examples/graph_gnf.rs` reads the
supported unweighted directed subset and rejects self-pair reach loudly,
since that is where the two reach conventions split). Recorded result
(`docs/studies/2026-09-19-graph-constraints-differential.md`): **1 600/1
600 instances agree** across 2–20 vertices per graph, with a healthy
sat/unsat split (860/740), no skips, no `Unknown`s, plus scale probes to
n = 100.
