//! Explained finite-state-machine constraints (MonoSAT-style acceptors).
//!
//! This module provides **symbolic acceptance constraints over a fixed
//! finite NFA**: the automaton's state universe, alphabet, initial state and
//! accepting states are fixed at declaration, and every transition carries a
//! Boolean **guard** term — the transition exists in a candidate automaton
//! exactly when its guard is true. `accepts(word)` reifies acceptance of a
//! constant word as a single Boolean atom that the solver must assign the
//! acceptance value; assert it, negate it, or combine it in arbitrary
//! Boolean formulas (with arithmetic, BV, strings, ...). Because guards are
//! ordinary terms, several transitions — across positions, words, and
//! automata — can share one guard, which is what makes **synthesis** from
//! positive and negative word examples possible: the solver searches over
//! guard assignments until one automaton accepts every positive example and
//! rejects every negative one.
//!
//! This is the acceptor half of MonoSAT's FSM theory
//! (`../temp/monosat/FiniteStateMachines.md`): constant words, symbolic
//! transitions. Symbolic words, generators, transducers and minimization
//! are explicitly **not** provided.
//!
//! # Semantics
//!
//! - The state universe `Q = 0..states` and alphabet `Σ = 0..alphabet` are
//!   fixed at [`FsmModel::new_automaton`]; exactly one initial state is
//!   required, zero or more accepting states.
//! - A transition is `(from, label, to, guard)` where `label` is a symbol
//!   or **epsilon**. Nondeterminism (several transitions from one state on
//!   one symbol), self-loops, parallel transitions, cycles and epsilon
//!   cycles are all allowed. The transition *exists* exactly when its guard
//!   is true in the model; guards may be any Boolean terms (variables,
//!   negations, conjunctions, arithmetic comparisons, constants).
//! - `accepts(word)` is true iff some run consumes the entire word and ends
//!   in an accepting state. A run starts at the initial state, follows only
//!   existing transitions, consumes one symbol on a symbol transition and
//!   nothing on an epsilon transition. The **empty word** is accepted
//!   exactly when the initial state reaches an accepting state through
//!   epsilon transitions (in particular when it *is* accepting).
//! - Negated acceptance — `¬accepts(word)` — excludes every accepting run.
//!
//! # Procedure: reduction to explained graph reachability
//!
//! Acceptance is lowered to the symbolic graph propagator
//! ([`crate::graph`]) by a product construction (MonoSAT's
//! `NFAGraphAccept`, `opt_fsm_as_graph`):
//!
//! - For each `(automaton, word)` query a product graph is built with
//!   vertices `(state, position)` for `position ∈ 0..=len(word)`.
//! - A symbol transition `(q, a, q', g)` with `a = word[p]` contributes the
//!   product edge `(q,p) → (q',p+1)` guarded by `g`; an epsilon transition
//!   contributes `(q,p) → (q',p')` in **every** layer `p`.
//! - Product edges reuse the transition's guard term verbatim, so one guard
//!   keeps one meaning across all positions and words (shared-term aliasing
//!   in the graph model).
//! - `accepts(word)` is reified as a fresh atom defined by
//!   `∨_{qf ∈ F} reach((q0,0), (qf, n))` — plus the constant `true` when
//!   `n = 0` and `q0 ∈ F` (Nixie graph reachability counts paths of length
//!   ≥ 1 only; the zero-length accepting run is exactly this constant, and
//!   every other accepting path has length ≥ n ≥ 1, so the disjunction is
//!   exactly acceptance). With `F = ∅` the definition is the constant
//!   `false`.
//!
//!   An alternative "sink" construction (a fresh sink vertex with
//!   unconditional edges from `(qf, n)` for each accepting `qf`, acceptance
//!   = one reach atom) is equivalent, but needs unconditional product
//!   edges — extra asserted-true variables — while the disjunction above
//!   reuses only the existing reach atoms; that is the construction
//!   implemented here.
//!
//! Correctness follows from graph-reachability soundness: a path in the
//! product is exactly an accepting run (guards present ⇔ transitions
//! exist), an under-approximation path proves acceptance, and a cut over
//! the over-approximation refutes it — MonoSAT's forced/possible scheme,
//! with explanations carried by the guard literals themselves.
//!
//! # Scope, lifecycle, and certification
//!
//! Registration follows the CP/graph lifecycle (`docs/CP.md`,
//! `docs/FSM.md`): build the model, then `Solver::register_fsm` at
//! assertion scope zero **before the first check**; afterwards push/pop,
//! repeated checks and assumptions behave normally. The propagator is the
//! graph propagator (stateless across backtracking); acceptance atoms are
//! defined by ordinary biconditional clauses asserted at registration, so
//! they survive every legal scope change. Constant guards are exact: a
//! `true` guard lowers to a per-model variable asserted true at
//! registration, a `false` guard contributes no product edges at all (the
//! transition is statically dead).
//!
//! Like all client callbacks, FSM registrations have no independently
//! checkable certificate: **proof-producing and certified checks fail
//! closed to `Unknown`** for them. Ordinary solving is complete for this
//! fragment, and returned models are replayed through the propagator
//! before being reported; [`FsmModel::accepts_under`] provides an
//! independent interpreter for validating models against the original
//! declarations.
//!
//! # Example
//!
//! ```rust,ignore
//! use nixie_core::ast::TermManager;
//! use nixie_solver::Solver;
//! use nixie_theories::fsm::{FsmModel, Label};
//!
//! let mut tm = TermManager::new();
//! let mut fsms = FsmModel::new(&tm);
//! let a = fsms.new_automaton(2, 2)?;            // states {0,1}, symbols {0,1}
//! fsms.set_initial(a, 0)?;
//! fsms.add_accepting(a, 1)?;
//! let g = tm.mk_var("t", tm.sorts.bool_sort);
//! fsms.add_transition(a, 0, 1, Label::Symbol(1), g, &mut tm)?;
//! let accepts_1 = fsms.accepts(a, &[1], &mut tm)?;       // accepts "1" iff t
//! let mut solver = Solver::new();
//! solver.register_fsm(fsms, &mut tm)?;
//! solver.assert(accepts_1, &mut tm);
//! assert_eq!(solver.check(&mut tm), nixie_solver::SolverResult::Sat);
//! // ... and asserting (not accepts_1) forces t false instead.
//! ```

use crate::graph::{GraphModel, VertexId};
use crate::prelude::{FxHashMap, FxHashSet};
use crate::user_propagator::UserPropagator;
use nixie_core::ast::{TermId, TermManager};

/// Invalid FSM construction or query (rejected before installing any
/// constraint, or before minting any product edge).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsmError(pub &'static str);

impl core::fmt::Display for FsmError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}
impl core::error::Error for FsmError {}

/// A transition label: one symbol of the fixed alphabet, or the
/// non-consuming **epsilon**.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Label {
    /// The alphabet symbol with this index (`0..alphabet`).
    Symbol(u32),
    /// Epsilon: consumes no input.
    Epsilon,
}

/// Handle to one automaton inside an [`FsmModel`]. Handed out by
/// [`FsmModel::new_automaton`]; the zero-based index is addressable via
/// [`AutomatonHandle::new`] for serialization-style tooling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AutomatonHandle(usize);

impl AutomatonHandle {
    /// The automaton with zero-based index `index`. Only indices below the
    /// owning model's automaton count are meaningful; all APIs validate
    /// them.
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// The handle's zero-based index.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Handle to one declared transition of one automaton.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TransitionId(u32);

impl TransitionId {
    /// The transition with zero-based index `index` in its automaton.
    #[must_use]
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    /// The handle's zero-based index.
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

/// One declared transition. `constant` records a Boolean-constant guard
/// (`Some(true)`/`Some(false)`); such guards never become product edge
/// atoms (`true` lowers to the model's asserted-true variable, `false`
/// contributes no edges) and the interpreter evaluates them directly.
#[derive(Debug, Clone)]
pub(crate) struct TransitionSpec {
    pub(crate) from: u32,
    pub(crate) to: u32,
    pub(crate) label: Label,
    pub(crate) guard: TermId,
    pub(crate) constant: Option<bool>,
}

/// One automaton's fixed declaration.
#[derive(Debug, Clone)]
pub(crate) struct AutomatonSpec {
    pub(crate) states: u32,
    pub(crate) alphabet: u32,
    pub(crate) initial: Option<u32>,
    pub(crate) accepting: Vec<u32>,
    pub(crate) transitions: Vec<TransitionSpec>,
}

/// `(automaton, word) -> [(accepting state, reach atom)]`: the
/// disjunction composing each acceptance definition.
type AcceptsDisjuncts = FxHashMap<(usize, Vec<u32>), Vec<(u32, TermId)>>;

/// Per-instance salt for minted atom names (the same convention as
/// [`crate::graph`]).
fn next_model_uid() -> u64 {
    static COUNTER: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
    COUNTER.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
}

/// Assertions an [`FsmModel`] needs installed alongside its propagator:
/// the asserted-true variable backing constant-`true` guards, and the
/// defining biconditionals of every reified acceptance atom. Consumed by
/// `Solver::register_fsm`.
#[derive(Debug, Clone, Default)]
pub struct FsmRegistration {
    /// Variable to assert true (constant-`true` guards' product edges).
    pub true_var: Option<TermId>,
    /// `(atom, defining term)` pairs; each atom is defined by
    /// `atom ⟺ defining`.
    pub bindings: Vec<(TermId, TermId)>,
}

/// A collection of guarded NFAs with reified constant-word acceptance,
/// installable with `Solver::register_fsm`.
///
/// Construct the model before registering it; handles are local to one
/// model, and all constraints must be declared before
/// `into_propagator`/`register_fsm` (the underlying graph model is
/// consumed then). The same guard term may be used by any number of
/// transitions in any number of automata: it keeps one meaning everywhere.
pub struct FsmModel {
    uid: u64,
    automata: Vec<AutomatonSpec>,
    /// The lowering target: one product graph per acceptance query.
    graph: GraphModel,
    /// Lazily minted variable asserted true at registration, backing
    /// constant-`true` guards' product edges (graph edge atoms must be
    /// non-constant terms; this variable is exactly-true by assertion).
    true_var: Option<TermId>,
    /// `(automaton, word) -> reified acceptance atom` (query idempotence).
    accepts_cache: FxHashMap<(usize, Vec<u32>), TermId>,
    /// Defining biconditionals to assert at registration.
    bindings: Vec<(TermId, TermId)>,
    /// Names already minted for acceptance atoms (reject aliasing two
    /// queries onto one name).
    used_names: FxHashSet<TermId>,
    /// `(automaton, word) -> per-accepting-state reach atoms` composing
    /// each acceptance definition (see [`FsmModel::acceptance_reach_atoms`]).
    disjuncts: AcceptsDisjuncts,
    /// Acceptance queries in creation order; `query_order[i]` owns product
    /// graph `i` (one graph per built query, in the same order).
    query_order: Vec<(usize, Vec<u32>)>,
    /// Salted counter for internally named acceptance atoms.
    accepts_counter: u64,
    true_term: TermId,
    false_term: TermId,
}

impl core::fmt::Debug for FsmModel {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("FsmModel")
            .field("automata", &self.automata.len())
            .field("queries", &self.bindings.len())
            .finish()
    }
}

impl FsmModel {
    /// Start an FSM model using the same term manager as the SMT solver.
    pub fn new(tm: &TermManager) -> Self {
        Self {
            uid: next_model_uid(),
            automata: Vec::new(),
            graph: GraphModel::new(tm),
            true_var: None,
            accepts_cache: FxHashMap::default(),
            bindings: Vec::new(),
            used_names: FxHashSet::default(),
            disjuncts: FxHashMap::default(),
            query_order: Vec::new(),
            accepts_counter: 0,
            true_term: tm.mk_bool(true),
            false_term: tm.mk_bool(false),
        }
    }

    fn automaton(&self, a: AutomatonHandle) -> Result<&AutomatonSpec, FsmError> {
        self.automata
            .get(a.0)
            .ok_or(FsmError("unknown automaton handle"))
    }

    fn automaton_mut(&mut self, a: AutomatonHandle) -> Result<&mut AutomatonSpec, FsmError> {
        self.automata
            .get_mut(a.0)
            .ok_or(FsmError("unknown automaton handle"))
    }

    /// Declare an automaton with `states` states (`0..states`, addressed by
    /// index) over an alphabet of `alphabet` symbols (`0..alphabet`).
    /// `states` must be at least one; `alphabet` may be zero (epsilon-only
    /// automata). Both must fit `u32`.
    pub fn new_automaton(
        &mut self,
        states: usize,
        alphabet: usize,
    ) -> Result<AutomatonHandle, FsmError> {
        if states == 0 {
            return Err(FsmError("automaton must have at least one state"));
        }
        if states > u32::MAX as usize || alphabet > u32::MAX as usize {
            return Err(FsmError("state or alphabet count exceeds u32"));
        }
        self.automata.push(AutomatonSpec {
            states: states as u32,
            alphabet: alphabet as u32,
            initial: None,
            accepting: Vec::new(),
            transitions: Vec::new(),
        });
        Ok(AutomatonHandle(self.automata.len() - 1))
    }

    /// Set the (unique) initial state of automaton `a`. A second call is an
    /// error, as is a state index outside `0..states`.
    pub fn set_initial(&mut self, a: AutomatonHandle, state: usize) -> Result<(), FsmError> {
        let spec = self.automaton_mut(a)?;
        if state >= spec.states as usize {
            return Err(FsmError("initial state out of range"));
        }
        if spec.initial.is_some() {
            return Err(FsmError("initial state already set"));
        }
        spec.initial = Some(state as u32);
        Ok(())
    }

    /// Mark `state` accepting. Repeated calls add more accepting states; a
    /// duplicate or out-of-range state is an error. Zero accepting states
    /// is legal (the automaton then accepts nothing, including the empty
    /// word).
    pub fn add_accepting(&mut self, a: AutomatonHandle, state: usize) -> Result<(), FsmError> {
        let spec = self.automaton_mut(a)?;
        if state >= spec.states as usize {
            return Err(FsmError("accepting state out of range"));
        }
        let state = state as u32;
        if spec.accepting.contains(&state) {
            return Err(FsmError("state already accepting"));
        }
        spec.accepting.push(state);
        Ok(())
    }

    /// Add transition `from --label--> to` guarded by Boolean term `guard`
    /// (the transition exists exactly when `guard` is true). The guard may
    /// be any Boolean-sorted term, including the constants `true`/`false`
    /// and terms shared with other transitions or automata. Parallel
    /// transitions (same `from`/`to`/`label`, different guards) are allowed.
    pub fn add_transition(
        &mut self,
        a: AutomatonHandle,
        from: usize,
        to: usize,
        label: Label,
        guard: TermId,
        tm: &mut TermManager,
    ) -> Result<TransitionId, FsmError> {
        let spec = self.automaton_mut(a)?;
        if from >= spec.states as usize || to >= spec.states as usize {
            return Err(FsmError("transition state out of range"));
        }
        if let Label::Symbol(s) = label
            && s >= spec.alphabet
        {
            return Err(FsmError("transition symbol out of range"));
        }
        let node = tm.get(guard).ok_or(FsmError("unknown term"))?;
        if node.sort != tm.sorts.bool_sort {
            return Err(FsmError("transition guards must have Boolean sort"));
        }
        let constant = match node.kind {
            nixie_core::ast::TermKind::True => Some(true),
            nixie_core::ast::TermKind::False => Some(false),
            _ => None,
        };
        let id = TransitionId(spec.transitions.len() as u32);
        spec.transitions.push(TransitionSpec {
            from: from as u32,
            to: to as u32,
            label,
            guard,
            constant,
        });
        Ok(id)
    }

    /// Reify acceptance of `word` (symbols in `0..alphabet`) by automaton
    /// `a` as a fresh Boolean atom, or return the existing atom for the
    /// same `(automaton, word)`. The atom is *defined* by the model: in
    /// every reported model its value equals the automaton's acceptance of
    /// the word under the model's guard assignment.
    pub fn accepts(
        &mut self,
        a: AutomatonHandle,
        word: &[u32],
        tm: &mut TermManager,
    ) -> Result<TermId, FsmError> {
        self.accepts_impl(a, word, None, tm)
    }

    /// [`FsmModel::accepts`] with an explicit name for the reified atom.
    /// The name must not already name an acceptance atom in this model.
    /// The SMT-LIB front end uses this to declare the atom as an ordinary
    /// Boolean constant of the script.
    pub fn accepts_named(
        &mut self,
        a: AutomatonHandle,
        word: &[u32],
        name: &str,
        tm: &mut TermManager,
    ) -> Result<TermId, FsmError> {
        self.accepts_impl(a, word, Some(name), tm)
    }

    fn accepts_impl(
        &mut self,
        a: AutomatonHandle,
        word: &[u32],
        name: Option<&str>,
        tm: &mut TermManager,
    ) -> Result<TermId, FsmError> {
        // The named form bypasses the (automaton, word) cache: a name maps
        // to exactly one query, but the same query may legitimately be
        // reified under several names (each name gets its own atom, defined
        // by the same product graph).
        if let Some(&atom) = self.accepts_cache.get(&(a.0, word.to_vec()))
            && name.is_none()
        {
            return Ok(atom);
        }
        // Validate and read the declaration before touching the product.
        {
            let spec = self.automaton(a)?;
            for &s in word {
                if s >= spec.alphabet {
                    return Err(FsmError("word symbol out of range"));
                }
            }
            if spec.initial.is_none() {
                return Err(FsmError("automaton has no initial state"));
            }
        }
        // Mint (or check) the acceptance atom *before* building anything,
        // so a rejected name leaves the model untouched.
        let atom = match name {
            Some(name) => tm.mk_var(name, tm.sorts.bool_sort),
            None => {
                let name = format!("fsm{}_accepts{}", self.uid, self.accepts_counter);
                self.accepts_counter += 1;
                tm.mk_var(&name, tm.sorts.bool_sort)
            }
        };
        if !self.used_names.insert(atom) {
            return Err(FsmError("acceptance atom name already used by this model"));
        }

        let (def, disjuncts) = build_product(
            &self.automata[a.0],
            word,
            &mut self.graph,
            &mut self.true_var,
            self.uid,
            tm,
        )?;

        self.bindings.push((atom, def));
        self.accepts_cache
            .entry((a.0, word.to_vec()))
            .or_insert(atom);
        // Every built query owns exactly one product graph, in build order
        // (cached lookups build nothing; the named form always builds).
        self.query_order.push((a.0, word.to_vec()));
        self.disjuncts.insert((a.0, word.to_vec()), disjuncts);
        Ok(atom)
    }

    /// The per-accepting-state product reach atoms that compose the
    /// acceptance definition of `accepts(a, word)`: `(qf, atom)` pairs
    /// where `atom` reifies `reach((q0,0), (qf, n))` — a run consuming the
    /// entire word and ending exactly at `qf`. Acceptance is the
    /// disjunction of these atoms (plus, when the word is empty and the
    /// initial state is accepting, the constant true). Introspection for
    /// tests, tooling and certificate building; an empty list with a
    /// missing-word `Err` distinguishes an unasked query from one with no
    /// accepting states.
    pub fn acceptance_reach_atoms(
        &self,
        a: AutomatonHandle,
        word: &[u32],
    ) -> Result<Vec<(usize, TermId)>, FsmError> {
        if a.0 >= self.automata.len() {
            return Err(FsmError("unknown automaton handle"));
        }
        Ok(self
            .disjuncts
            .get(&(a.0, word.to_vec()))
            .ok_or(FsmError("acceptance not queried for this word"))?
            .iter()
            .map(|&(qf, atom)| (qf as usize, atom))
            .collect())
    }

    /// The automaton's state count.
    pub fn num_states(&self, a: AutomatonHandle) -> Result<usize, FsmError> {
        Ok(self.automaton(a)?.states as usize)
    }

    /// The automaton's alphabet size.
    pub fn alphabet_size(&self, a: AutomatonHandle) -> Result<usize, FsmError> {
        Ok(self.automaton(a)?.alphabet as usize)
    }

    /// The automaton's initial state, if declared.
    pub fn initial_state(&self, a: AutomatonHandle) -> Result<Option<usize>, FsmError> {
        Ok(self.automaton(a)?.initial.map(|s| s as usize))
    }

    /// The automaton's accepting states, in declaration order.
    pub fn accepting_states(&self, a: AutomatonHandle) -> Result<Vec<usize>, FsmError> {
        Ok(self
            .automaton(a)?
            .accepting
            .iter()
            .map(|&s| s as usize)
            .collect())
    }

    /// The automaton's transitions as `(from, label, to, guard)` tuples, in
    /// declaration order (parallel transitions included).
    pub fn transitions(
        &self,
        a: AutomatonHandle,
    ) -> Result<Vec<(usize, Label, usize, TermId)>, FsmError> {
        Ok(self
            .automaton(a)?
            .transitions
            .iter()
            .map(|t| (t.from as usize, t.label, t.to as usize, t.guard))
            .collect())
    }

    /// The distinct non-constant guard terms of automaton `a`, in first
    /// declaration order — the terms whose model values determine the
    /// candidate automaton (for tests and model validation).
    pub fn guards(&self, a: AutomatonHandle) -> Result<Vec<TermId>, FsmError> {
        let mut seen = FxHashSet::default();
        let mut out = Vec::new();
        for t in &self.automaton(a)?.transitions {
            if t.constant.is_none() && seen.insert(t.guard) {
                out.push(t.guard);
            }
        }
        Ok(out)
    }

    /// Independently evaluate acceptance of `word` under a total guard
    /// assignment (`truth` answers the value of a non-constant guard term;
    /// constant guards are evaluated directly). This is the reference
    /// interpreter: an iterative forward search over `(state, position)`
    /// configurations with epsilon steps — **no** product construction, no
    /// graph machinery — so agreement with the solver is genuine
    /// cross-validation.
    ///
    /// Returns `true` iff some run consumes the entire word and ends in an
    /// accepting state.
    pub fn accepts_under(
        &self,
        a: AutomatonHandle,
        word: &[u32],
        truth: &dyn Fn(TermId) -> bool,
    ) -> Result<bool, FsmError> {
        let spec = self.automaton(a)?;
        for &s in word {
            if s >= spec.alphabet {
                return Err(FsmError("word symbol out of range"));
            }
        }
        let Some(initial) = spec.initial else {
            return Err(FsmError("automaton has no initial state"));
        };
        let n = word.len();
        // seen[state][position]; iterative worklist, no recursion.
        let mut seen = vec![vec![false; n + 1]; spec.states as usize];
        let mut worklist = vec![(initial, 0u32)];
        seen[initial as usize][0] = true;
        let mut head = 0;
        while let Some(&(state, pos)) = worklist.get(head) {
            head += 1;
            if pos as usize == n && spec.accepting.contains(&state) {
                return Ok(true);
            }
            for t in &spec.transitions {
                if t.from != state {
                    continue;
                }
                let present = match t.constant {
                    Some(v) => v,
                    None => truth(t.guard),
                };
                if !present {
                    continue;
                }
                let next = match t.label {
                    Label::Symbol(s) => {
                        if pos as usize == n || word[pos as usize] != s {
                            continue;
                        }
                        pos + 1
                    }
                    Label::Epsilon => pos,
                };
                if !seen[t.to as usize][next as usize] {
                    seen[t.to as usize][next as usize] = true;
                    worklist.push((t.to, next));
                }
            }
        }
        Ok(false)
    }

    /// The registration payload (asserted-true variable and defining
    /// biconditionals) for `Solver::register_fsm`; the model itself is
    /// unchanged.
    pub fn registration(&self) -> FsmRegistration {
        FsmRegistration {
            true_var: self.true_var,
            bindings: self.bindings.clone(),
        }
    }

    /// The product-graph statements of every acceptance query, **validated
    /// against the original automaton declarations by an independent
    /// re-derivation**: for each query, the statement's vertex count, edge
    /// set (pairs and guard atoms, including the asserted-true variable for
    /// constant-`true` guards and the exclusion of statically dead
    /// constant-`false` guards), and reach-atom pairs must equal exactly
    /// what the declaration and word determine. A mismatch is an explicit
    /// error — never a silently trusted reduction — so consumers retaining
    /// these statements (certificate checking) are anchored to the FSM
    /// inputs. Call before `into_propagator`/`register_fsm`.
    pub fn graph_statements(
        &mut self,
        tm: &mut TermManager,
    ) -> Result<Vec<crate::graph::GraphStatement>, FsmError> {
        let statements = self.graph.statements();
        if statements.len() != self.query_order.len() {
            return Err(FsmError(
                "internal: product graph count does not match the query log",
            ));
        }
        let mut true_var = self.true_var;
        for (qi, statement) in statements.iter().enumerate() {
            let (a, word) = &self.query_order[qi];
            let spec = self
                .automaton(AutomatonHandle::new(*a))
                .map_err(|_| FsmError("internal: query log references an unknown automaton"))?;
            let initial = spec
                .initial
                .ok_or(FsmError("automaton has no initial state"))?;
            let n = word.len();
            let v = |q: u32, p: usize| q + (p as u32) * spec.states;

            // Independent re-derivation of the expected edge set: matching
            // labeled transitions advance a layer, epsilon stays, identical
            // `(u, v, atom)` duplicates collapse, constant guards resolve
            // to the asserted-true variable / no edge.
            let mut expected: Vec<(u32, u32, TermId)> = Vec::new();
            let mut seen: FxHashSet<(u32, u32, TermId)> = FxHashSet::default();
            let mut push =
                |from: u32, to: u32, t: &TransitionSpec, out: &mut Vec<(u32, u32, TermId)>| {
                    let atom = match t.constant {
                        Some(false) => return,
                        Some(true) => *true_var.get_or_insert_with(|| {
                            tm.mk_var(&format!("fsm{}_true", self.uid), tm.sorts.bool_sort)
                        }),
                        None => t.guard,
                    };
                    if seen.insert((from, to, atom)) {
                        out.push((from, to, atom));
                    }
                };
            for p in 0..=n {
                for t in &spec.transitions {
                    if t.label == Label::Epsilon {
                        push(v(t.from, p), v(t.to, p), t, &mut expected);
                    }
                }
            }
            for (p, &symbol) in word.iter().enumerate() {
                for t in &spec.transitions {
                    if t.label == Label::Symbol(symbol) {
                        push(v(t.from, p), v(t.to, p + 1), t, &mut expected);
                    }
                }
            }
            // Compare against the statement (order-independent).
            let mut actual: Vec<(u32, u32, TermId)> = statement
                .edges()
                .iter()
                .map(|&(from, to, atom, _)| (from, to, atom))
                .collect();
            actual.sort_unstable();
            expected.sort_unstable();
            if actual != expected {
                return Err(FsmError(
                    "internal: product graph disagrees with the automaton declaration",
                ));
            }
            if statement.vertices_count() != spec.states as usize * (n + 1) {
                return Err(FsmError(
                    "internal: product graph vertex count disagrees with the declaration",
                ));
            }
            // Reach atoms: exactly the final-layer pairs of the disjuncts.
            let disjuncts = self
                .disjuncts
                .get(&(*a, word.clone()))
                .ok_or(FsmError("internal: missing disjuncts for a built query"))?;
            let mut expected_pairs: Vec<(u32, u32)> = disjuncts
                .iter()
                .map(|&(qf, _)| (v(initial, 0), v(qf, n)))
                .collect();
            expected_pairs.sort_unstable();
            let mut actual_pairs: Vec<(u32, u32)> = statement
                .reach_atoms()
                .iter()
                .map(|&(from, to, _, _)| (from, to))
                .collect();
            actual_pairs.sort_unstable();
            if actual_pairs != expected_pairs {
                return Err(FsmError(
                    "internal: product reach atoms disagree with the acceptance definition",
                ));
            }
        }
        self.true_var = true_var;
        Ok(statements)
    }

    /// All terms the propagator must watch (the underlying graph model's
    /// watch list: guards and reach atoms).
    pub fn watches(&self) -> Vec<TermId> {
        self.graph.watches()
    }

    /// Consume the model into the graph propagator and its watch list (for
    /// `Solver::register_user_propagator`; `Solver::register_fsm` also
    /// asserts [`FsmModel::registration`]).
    pub fn into_propagator(self) -> (Box<dyn UserPropagator>, Vec<TermId>) {
        self.graph.into_propagator()
    }

    /// The term manager's Boolean true constant (for tests and oracles).
    pub fn true_term(&self) -> TermId {
        self.true_term
    }

    /// The term manager's Boolean false constant (for tests and oracles).
    pub fn false_term(&self) -> TermId {
        self.false_term
    }
}

/// Build the product graph of one acceptance query and return the defining
/// term of the acceptance atom (the disjunction of the final-layer reach
/// atoms, with the zero-length accepting run's constant). Shared state
/// (`graph`, `true_var`) is threaded explicitly.
///
/// Layout: vertex `(q, p) = q + p * states` (layer-major). Constant
/// `false` guards contribute no edges; constant `true` guards use the
/// asserted-true `true_var` as edge atom. Identical `(u, v, atom)` edges
/// are deduplicated — parallel duplicates with one atom add no presence
/// information.
fn build_product(
    spec: &AutomatonSpec,
    word: &[u32],
    graph: &mut GraphModel,
    true_var: &mut Option<TermId>,
    uid: u64,
    tm: &mut TermManager,
) -> Result<(TermId, Vec<(u32, TermId)>), FsmError> {
    let states = spec.states;
    let initial = spec
        .initial
        .ok_or(FsmError("automaton has no initial state"))?;
    let accepting = &spec.accepting;
    let n = word.len();
    // Product vertex count with checked arithmetic: `states * (n+1)` must
    // index `u32` vertices (checked conversion, fail-closed).
    let layers = n.checked_add(1).ok_or(FsmError("word too long"))?;
    let vertices = (states as usize)
        .checked_mul(layers)
        .and_then(|v| u32::try_from(v).ok())
        .ok_or(FsmError("product graph too large"))?;

    let g = graph.new_graph();
    for _ in 0..vertices {
        graph.add_vertex(g).map_err(|e| FsmError(e.0))?;
    }
    let v = |q: u32, p: usize| VertexId::new(q + (p as u32) * states);

    // Epsilon transitions live in every layer; symbol transitions only at
    // matching positions. Identical `(u, v, atom)` edges are deduplicated —
    // parallel duplicates with one atom add no presence information.
    let mut true_var_local = *true_var;
    let mut outcome = Ok(());
    {
        let mut seen_edges: FxHashSet<(u32, u32, TermId)> = FxHashSet::default();
        let mut add = |from: VertexId,
                       to: VertexId,
                       t: &TransitionSpec,
                       graph: &mut GraphModel,
                       tm: &mut TermManager|
         -> Result<(), FsmError> {
            let atom = match t.constant {
                Some(false) => return Ok(()),
                Some(true) => *true_var_local.get_or_insert_with(|| {
                    tm.mk_var(&format!("fsm{uid}_true"), tm.sorts.bool_sort)
                }),
                None => t.guard,
            };
            if seen_edges.insert((from.index(), to.index(), atom)) {
                graph
                    .add_edge(g, from, to, atom, tm)
                    .map_err(|e| FsmError(e.0))?;
            }
            Ok(())
        };
        'outer: for p in 0..=n {
            for t in &spec.transitions {
                if t.label != Label::Epsilon {
                    continue;
                }
                outcome = add(v(t.from, p), v(t.to, p), t, graph, tm);
                if outcome.is_err() {
                    break 'outer;
                }
            }
        }
        if outcome.is_ok() {
            'words: for (p, &symbol) in word.iter().enumerate() {
                for t in &spec.transitions {
                    if t.label != Label::Symbol(symbol) {
                        continue;
                    }
                    outcome = add(v(t.from, p), v(t.to, p + 1), t, graph, tm);
                    if outcome.is_err() {
                        break 'words;
                    }
                }
            }
        }
    }
    *true_var = true_var_local;
    outcome?;

    // Definition: OR over accepting states of reach((q0,0),(qf,n)); plus
    // the constant true for the zero-length accepting run (n = 0 and the
    // initial state accepting — the graph's length-≥-1 reach cannot see
    // it). No accepting states: the constant false.
    let mut disjuncts: Vec<(u32, TermId)> = Vec::with_capacity(accepting.len());
    let mut terms = Vec::with_capacity(accepting.len() + 1);
    if n == 0 && accepting.contains(&initial) {
        terms.push(tm.mk_bool(true));
    }
    for &qf in accepting {
        let atom = graph
            .reach(g, v(initial, 0), v(qf, n), tm)
            .map_err(|e| FsmError(e.0))?;
        disjuncts.push((qf, atom));
        terms.push(atom);
    }
    Ok((tm.mk_or(terms), disjuncts))
}

#[cfg(test)]
mod tests;
