//! Quantifier-free Boolean combinations of exact, disjoint integer heaplets.
//!
//! Locations and values are mathematical integers; location zero is nil and
//! cannot be allocated. `emp` describes exactly the empty heap. A points-to
//! describes exactly one cell. Separating conjunction accepts only heaplets;
//! classical Boolean connectives accept their reifications. See `docs/HEAP.md`
//! for the reduction, completeness argument, and deliberately excluded syntax.

use crate::{CertificationMode, Solver, SolverConfig, SolverResult};
use nixie_core::ast::{TermId, TermManager};
use num_bigint::BigInt;
use std::collections::BTreeMap;
use std::sync::Arc;

mod model;
mod preprocess;
mod templates;

/// An invalid operation, foreign handle, or unverifiable model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeapError(pub &'static str);

impl core::fmt::Display for HeapError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for HeapError {}

#[derive(Clone, Debug)]
struct Handle {
    owner: Arc<()>,
    index: usize,
}

/// An integer expression belonging to one [`HeapSolver`].
#[derive(Clone, Debug)]
pub struct IntTerm(Handle);

/// A Boolean formula belonging to one [`HeapSolver`].
#[derive(Clone, Debug)]
pub struct Formula(Handle);

/// A separating conjunction of zero or more points-to assertions.
///
/// This is a flat representation: nesting `star` never nests the native stack.
/// Boolean formulas intentionally cannot be used as operands of `star`.
#[derive(Clone, Debug, Default)]
pub struct Heaplet {
    cells: Vec<(IntTerm, IntTerm)>,
}

impl Heaplet {
    /// The exact empty heap (the identity for separating conjunction).
    pub fn emp() -> Self {
        Self::default()
    }

    /// Exactly one cell, at `location`, storing `value`.
    pub fn points_to(location: &IntTerm, value: &IntTerm) -> Self {
        Self {
            cells: vec![(location.clone(), value.clone())],
        }
    }

    /// Disjoint union. Aliasing cells make the resulting assertion false,
    /// including when their stored values agree.
    pub fn star(mut self, other: Self) -> Self {
        self.cells.extend(other.cells);
        self
    }
}

// The original input arena, independent of the SMT reduction and its rewrites.
// Every edge goes to an earlier node. Evaluation and destruction are iterative.
#[derive(Clone, Debug)]
enum Node {
    Integer(BigInt),
    IntVar(String),
    Boolean(bool),
    BoolVar(String),
    Add(usize, usize),
    Sub(usize, usize),
    Scale(BigInt, usize),
    Eq(usize, usize),
    Le(usize, usize),
    Not(usize),
    And(Vec<usize>),
    Or(Vec<usize>),
    Heap(usize),
}

#[derive(Debug)]
struct Spatial {
    cells: Vec<(usize, usize)>,
    atom: TermId,
}

/// A concrete finite heap and total assignments to the declared variables.
///
/// Maps are public so callers can serialize or independently inspect them.
/// A modified model must pass [`HeapSolver::validate_model`] before being used
/// as a certificate. Missing variable assignments are rejected by that method.
#[derive(Clone, Debug)]
pub struct HeapModel {
    owner: Arc<()>,
    /// Allocated, non-nil locations and their exact integer values.
    pub cells: BTreeMap<BigInt, BigInt>,
    /// Integer variable assignments, keyed by their user-provided names.
    pub integers: BTreeMap<String, BigInt>,
    /// Pure Boolean variable assignments, keyed by their user-provided names.
    pub booleans: BTreeMap<String, bool>,
}

/// Independently selectable exact heap optimizations and diagnostic controls.
/// Configure before the first push/check. All combinations have the same semantics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HeapOptimizations {
    /// Derive other heaplets' validity from coverage of a valid anchor.
    pub anchor_coverage: bool,
    /// Substitute equalities and exact bounds entailed by active assertions.
    pub equality_propagation: bool,
    /// Reuse immutable encoding expressions across assertion scopes.
    pub cache_templates: bool,
    /// Opt in to guarded Boolean refinement (eager encoding is the default).
    pub lazy_boolean: bool,
}

impl HeapOptimizations {
    /// Diagnostic control retaining eager and redundant definitions.
    pub const NONE: Self = Self {
        anchor_coverage: false,
        equality_propagation: false,
        cache_templates: false,
        lazy_boolean: false,
    };
}

impl Default for HeapOptimizations {
    fn default() -> Self {
        Self {
            anchor_coverage: true,
            equality_propagation: true,
            cache_templates: true,
            lazy_boolean: false,
        }
    }
}

/// Read-only heap encoding sizes and backend search counters.
/// These counts do not measure total encoding or validation work.
#[derive(Clone, Copy, Debug)]
pub struct HeapStatistics {
    /// Number of registered heaplets.
    pub heaplets: usize,
    /// Nodes in the original input arena.
    pub original_nodes: usize,
    /// Interned terms in the backend term manager.
    pub backend_terms: usize,
    /// Nontrivial heap definitions in the current private check scope.
    pub definition_assertions: usize,
    /// Finite-map comparison requests in the current private scope.
    pub heap_comparisons: usize,
    /// Immutable encoding expressions actually built, over the solver lifetime.
    pub template_builds: usize,
    /// Successful template lookups, including diagnostic recomputation controls.
    pub template_hits: usize,
    /// Integer terms rewritten by current active equalities (before control selection).
    pub integer_rewrites: usize,
    /// Guarded rows added by lazy refinement in the current private scope.
    pub refinement_rounds: usize,
    /// Backend conflicts.
    pub conflicts: u64,
    /// Backend decisions.
    pub decisions: u64,
    /// Backend propagations.
    pub propagations: u64,
}

/// Incremental solving of Boolean combinations of exact heaplets and LIA.
///
/// Reify all heaplets at base scope, before the first check or push. Afterwards
/// assertions and `push`/`pop` use the same underlying solver and scope journal.
/// A returned `Sat` always has an independently validated [`HeapModel`].
pub struct HeapSolver {
    owner: Arc<()>,
    tm: TermManager,
    backend: Solver,
    nodes: Vec<Node>,
    terms: Vec<TermId>,
    spatial: Vec<Spatial>,
    assertions: Vec<usize>,
    scopes: Vec<usize>,
    closed: bool,
    proof_requested: bool,
    definition_scope_open: bool,
    definition_assertions: usize,
    simplify_definitions: bool,
    retain_anchor_redundancy: bool,
    heap_comparisons: usize,
    optimizations: HeapOptimizations,
    templates: templates::Templates,
    definition_terms: Vec<TermId>,
    integer_rewrites: usize,
    lazy_rows: Option<Vec<bool>>,
    refinement_rounds: usize,
    model: Option<HeapModel>,
    reason: Option<&'static str>,
}

impl Default for HeapSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl HeapSolver {
    /// Create a solver with the ordinary deterministic solver defaults.
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Configure backend resource limits. Heap translation proofs are not yet
    /// supported: proof-producing or certified configurations return `Unknown`.
    pub fn with_config(mut config: SolverConfig) -> Self {
        let proof_requested =
            config.proof || config.certification_mode != CertificationMode::Uncertified;
        config.model = true;
        let mut backend = Solver::with_config(config);
        backend.set_logic("QF_LIA");
        Self {
            owner: Arc::new(()),
            tm: TermManager::new(),
            backend,
            nodes: Vec::new(),
            terms: Vec::new(),
            spatial: Vec::new(),
            assertions: Vec::new(),
            scopes: Vec::new(),
            closed: false,
            proof_requested,
            definition_scope_open: false,
            definition_assertions: 0,
            simplify_definitions: true,
            retain_anchor_redundancy: false,
            heap_comparisons: 0,
            optimizations: HeapOptimizations::default(),
            templates: templates::Templates::default(),
            definition_terms: Vec::new(),
            integer_rewrites: 0,
            lazy_rows: None,
            refinement_rounds: 0,
            model: None,
            reason: None,
        }
    }

    fn invalidate(&mut self) {
        self.model = None;
        self.reason = None;
    }

    fn index(&self, handle: &Handle) -> Result<usize, HeapError> {
        if Arc::ptr_eq(&self.owner, &handle.owner) && handle.index < self.nodes.len() {
            Ok(handle.index)
        } else {
            Err(HeapError("term belongs to another heap solver"))
        }
    }

    fn node(&mut self, node: Node, term: TermId) -> Handle {
        self.invalidate();
        let index = self.nodes.len();
        self.nodes.push(node);
        self.terms.push(term);
        Handle {
            owner: self.owner.clone(),
            index,
        }
    }

    /// An arbitrary-precision integer constant.
    pub fn integer(&mut self, value: impl Into<BigInt>) -> IntTerm {
        let value = value.into();
        let term = self.tm.mk_int(value.clone());
        IntTerm(self.node(Node::Integer(value), term))
    }

    /// An integer variable. Reusing a name denotes the same variable.
    pub fn int_var(&mut self, name: &str) -> IntTerm {
        let term = self
            .tm
            .mk_var(&format!("heap.user.int.{name}"), self.tm.sorts.int_sort);
        IntTerm(self.node(Node::IntVar(name.into()), term))
    }

    /// A pure Boolean constant, true or false independently of the heap.
    pub fn boolean(&mut self, value: bool) -> Formula {
        let term = if value {
            self.tm.true_id
        } else {
            self.tm.false_id
        };
        Formula(self.node(Node::Boolean(value), term))
    }

    /// A pure Boolean variable. Reusing a name denotes the same variable.
    pub fn bool_var(&mut self, name: &str) -> Formula {
        let term = self
            .tm
            .mk_var(&format!("heap.user.bool.{name}"), self.tm.sorts.bool_sort);
        Formula(self.node(Node::BoolVar(name.into()), term))
    }

    /// Integer addition.
    pub fn add(&mut self, a: &IntTerm, b: &IntTerm) -> Result<IntTerm, HeapError> {
        let (a, b) = (self.index(&a.0)?, self.index(&b.0)?);
        let term = self.tm.mk_add([self.terms[a], self.terms[b]]);
        Ok(IntTerm(self.node(Node::Add(a, b), term)))
    }

    /// Integer subtraction.
    pub fn sub(&mut self, a: &IntTerm, b: &IntTerm) -> Result<IntTerm, HeapError> {
        let (a, b) = (self.index(&a.0)?, self.index(&b.0)?);
        let term = self.tm.mk_sub(self.terms[a], self.terms[b]);
        Ok(IntTerm(self.node(Node::Sub(a, b), term)))
    }

    /// Multiplication by an exact integer constant (linear arithmetic only).
    pub fn scale(
        &mut self,
        coefficient: impl Into<BigInt>,
        a: &IntTerm,
    ) -> Result<IntTerm, HeapError> {
        let a = self.index(&a.0)?;
        let coefficient = coefficient.into();
        let c = self.tm.mk_int(coefficient.clone());
        let term = self.tm.mk_mul([c, self.terms[a]]);
        Ok(IntTerm(self.node(Node::Scale(coefficient, a), term)))
    }

    /// Pure equality between integer terms.
    pub fn eq(&mut self, a: &IntTerm, b: &IntTerm) -> Result<Formula, HeapError> {
        let (a, b) = (self.index(&a.0)?, self.index(&b.0)?);
        let term = self.tm.mk_eq(self.terms[a], self.terms[b]);
        Ok(Formula(self.node(Node::Eq(a, b), term)))
    }

    /// Pure integer less-than-or-equal comparison.
    pub fn le(&mut self, a: &IntTerm, b: &IntTerm) -> Result<Formula, HeapError> {
        let (a, b) = (self.index(&a.0)?, self.index(&b.0)?);
        let term = self.tm.mk_le(self.terms[a], self.terms[b]);
        Ok(Formula(self.node(Node::Le(a, b), term)))
    }

    /// Classical negation, including negated heaplet assertions.
    pub fn not(&mut self, a: &Formula) -> Result<Formula, HeapError> {
        let a = self.index(&a.0)?;
        let term = self.tm.mk_not(self.terms[a]);
        Ok(Formula(self.node(Node::Not(a), term)))
    }

    /// Classical conjunction on the same heap. The empty conjunction is true
    /// on every heap, unlike `emp`.
    pub fn and(&mut self, args: &[Formula]) -> Result<Formula, HeapError> {
        let ids = args
            .iter()
            .map(|a| self.index(&a.0))
            .collect::<Result<Vec<_>, _>>()?;
        let term = self
            .tm
            .mk_and(ids.iter().map(|&i| self.terms[i]).collect::<Vec<_>>());
        Ok(Formula(self.node(Node::And(ids), term)))
    }

    /// Classical disjunction on the same heap. The empty disjunction is false.
    pub fn or(&mut self, args: &[Formula]) -> Result<Formula, HeapError> {
        let ids = args
            .iter()
            .map(|a| self.index(&a.0))
            .collect::<Result<Vec<_>, _>>()?;
        let term = self
            .tm
            .mk_or(ids.iter().map(|&i| self.terms[i]).collect::<Vec<_>>());
        Ok(Formula(self.node(Node::Or(ids), term)))
    }

    /// Reify a heaplet into a Boolean formula before the first push/check.
    /// Definitions are installed at check time, specialized by entailed Boolean
    /// units. All handles are checked before registering the heaplet.
    pub fn reify(&mut self, heaplet: Heaplet) -> Result<Formula, HeapError> {
        if self.closed {
            return Err(HeapError("reify heaplets before the first push or check"));
        }
        let cells = heaplet
            .cells
            .iter()
            .map(|(l, v)| Ok((self.index(&l.0)?, self.index(&v.0)?)))
            .collect::<Result<Vec<_>, HeapError>>()?;
        let atom = self.tm.mk_var(
            &format!("heap.atom.{}", self.spatial.len()),
            self.tm.sorts.bool_sort,
        );
        let index = self.spatial.len();
        self.spatial.push(Spatial { cells, atom });
        Ok(Formula(self.node(Node::Heap(index), atom)))
    }

    /// Enable exact Boolean specialization of heap definitions (the default).
    /// Disabling it is a diagnostic control: definitions use symbolic heap atoms
    /// with the same deferred registration and scope lifecycle. Semantics agree.
    /// Set this before the first push/check.
    pub fn set_definition_simplification(&mut self, enabled: bool) -> Result<(), HeapError> {
        if self.closed {
            return Err(HeapError(
                "configure heap definitions before the first push or check",
            ));
        }
        self.invalidate();
        self.simplify_definitions = enabled;
        Ok(())
    }

    /// Retain redundant comparisons between non-anchor heaplets for diagnostics.
    /// The default is false. Both settings use the same forced positive heap
    /// as an anchor; retaining its implied pair constraints is a performance
    /// control with identical semantics. Set before the first push/check.
    pub fn set_anchor_redundancy(&mut self, retain: bool) -> Result<(), HeapError> {
        if self.closed {
            return Err(HeapError(
                "configure heap definitions before the first push or check",
            ));
        }
        self.invalidate();
        self.retain_anchor_redundancy = retain;
        Ok(())
    }

    /// Select exact optimizations or their diagnostic controls before push/check.
    pub fn set_optimizations(&mut self, options: HeapOptimizations) -> Result<(), HeapError> {
        if self.closed {
            return Err(HeapError(
                "configure heap definitions before the first push or check",
            ));
        }
        self.invalidate();
        self.optimizations = options;
        Ok(())
    }

    // Extract only literal consequences justified by Boolean syntax. In
    // particular Or(true) and And(false) do not force any particular child.
    // The two-bit visited set bounds work on DAGs with shared subformulas.
    fn forced_literals(&self) -> Result<Vec<(usize, bool)>, HeapError> {
        let mut literals = Vec::new();
        let mut visited = vec![[false; 2]; self.nodes.len()];
        let mut stack: Vec<_> = self.assertions.iter().map(|&i| (i, true)).collect();
        while let Some((index, polarity)) = stack.pop() {
            let seen = visited
                .get_mut(index)
                .ok_or(HeapError("invalid Boolean node"))?;
            if seen[usize::from(polarity)] {
                continue;
            }
            seen[usize::from(polarity)] = true;
            match self
                .nodes
                .get(index)
                .ok_or(HeapError("invalid Boolean node"))?
            {
                Node::Not(child) => stack.push((*child, !polarity)),
                Node::And(children) if polarity => {
                    stack.extend(children.iter().map(|&i| (i, true)));
                }
                Node::Or(children) if !polarity => {
                    stack.extend(children.iter().map(|&i| (i, false)));
                }
                Node::Heap(_) | Node::Eq(_, _) | Node::Le(_, _) => {
                    literals.push((index, polarity));
                }
                Node::And(_) | Node::Or(_) | Node::Boolean(_) | Node::BoolVar(_) => {}
                Node::Integer(_)
                | Node::IntVar(_)
                | Node::Add(_, _)
                | Node::Sub(_, _)
                | Node::Scale(_, _) => {
                    return Err(HeapError("integer node in Boolean assertion"));
                }
            }
        }
        Ok(literals)
    }

    fn forced_heap_atoms(&self, literals: &[(usize, bool)]) -> Vec<Option<bool>> {
        let mut forced = vec![None; self.spatial.len()];
        for &(index, polarity) in literals {
            if let Node::Heap(i) = self.nodes[index] {
                if forced[i].is_some_and(|previous| previous != polarity) {
                    // Let the original contradictory assertions reach the backend.
                    return vec![None; self.spatial.len()];
                }
                forced[i] = Some(polarity);
            }
        }
        forced
    }

    fn close_definition_scope(&mut self) {
        if self.definition_scope_open {
            self.backend.pop();
            self.definition_scope_open = false;
            self.definition_assertions = 0;
            self.heap_comparisons = 0;
            self.definition_terms.clear();
            self.integer_rewrites = 0;
            self.lazy_rows = None;
            self.refinement_rounds = 0;
        }
    }

    fn assert_definition(&mut self, term: TermId) {
        if term != self.tm.true_id {
            self.backend.assert(term, &mut self.tm);
            self.definition_assertions += 1;
        }
    }

    fn assert_heap_pair(&mut self, i: usize, j: usize, atoms: &[TermId], validity: &[TermId]) {
        if atoms[i] == self.tm.false_id && atoms[j] == self.tm.false_id {
            return;
        }
        let same = self.same_heap(i, j);
        let other_matches = self.tm.mk_and([validity[j], same]);
        let equivalence = self.tm.mk_eq(atoms[j], other_matches);
        let forward = self.tm.mk_implies(atoms[i], equivalence);
        self.assert_definition(forward);
        let this_matches = self.tm.mk_and([validity[i], same]);
        let equivalence = self.tm.mk_eq(atoms[i], this_matches);
        let backward = self.tm.mk_implies(atoms[j], equivalence);
        self.assert_definition(backward);
    }

    fn define_from_anchor(&mut self, anchor: usize, atoms: &[TermId]) {
        let anchor_valid = self.heap_validity(anchor);
        self.assert_definition(anchor_valid);
        let mut validity = Vec::with_capacity(self.spatial.len());
        for (i, &atom) in atoms.iter().enumerate() {
            if i == anchor {
                validity.push(anchor_valid);
                continue;
            }
            let same = self.same_heap(anchor, i);
            let matches = if self.optimizations.anchor_coverage {
                // Va and equal-sized coverage FROM the distinct anchor cells
                // force every other cell to participate exactly once. Thus Vi
                // follows; coverage in the opposite direction would not suffice.
                if self.retain_anchor_redundancy {
                    validity.push(self.heap_validity(i));
                }
                same
            } else {
                let valid = self.heap_validity(i);
                validity.push(valid);
                self.tm.mk_and([valid, same])
            };
            let equivalence = self.tm.mk_eq(atom, matches);
            self.assert_definition(equivalence);
        }
        // All maps are compared to the very same valid, asserted heap.
        // Equality of those maps entails every omitted pair constraint.
        // Keep exactly those constraints in the diagnostic control, after
        // the common anchor definitions, to isolate their removal.
        if self.retain_anchor_redundancy {
            for i in 0..atoms.len() {
                if i == anchor {
                    continue;
                }
                for j in 0..i {
                    if j != anchor {
                        self.assert_heap_pair(i, j, atoms, &validity);
                    }
                }
            }
        }
    }

    fn prepare_definitions(&mut self) -> Result<(), HeapError> {
        if self.definition_scope_open {
            return Ok(());
        }
        // Also scan units in the diagnostic control, isolating substitution
        // from changes in staging and from the cost of discovering the units.
        let literals = self.forced_literals()?;
        let forced = self.forced_heap_atoms(&literals);
        let atoms: Vec<_> = self
            .spatial
            .iter()
            .zip(forced)
            .map(|(heap, value)| match (self.simplify_definitions, value) {
                (true, Some(true)) => self.tm.true_id,
                (true, Some(false)) => self.tm.false_id,
                _ => heap.atom,
            })
            .collect();
        self.backend.push();
        self.definition_scope_open = true;
        if atoms.iter().all(|&atom| atom == self.tm.false_id) {
            // Every definition has a false antecedent. A finite heap larger
            // than every registered heaplet supplies the concrete witness.
            return Ok(());
        }
        // Discover substitutions in both treatment and identity controls. Keep
        // original assertions intact; only the private definitions are rewritten.
        let rewritten = self.propagated_terms(&literals)?;
        self.integer_rewrites = rewritten
            .iter()
            .zip(&self.terms)
            .filter(|(a, b)| a != b)
            .count();
        self.definition_terms = if self.optimizations.equality_propagation {
            rewritten
        } else {
            self.terms.clone()
        };
        // A syntactically entailed positive heap fixes the entire current
        // finite map. Never choose an arbitrary disjunct or a model guess.
        if let Some(anchor) = atoms.iter().position(|&atom| atom == self.tm.true_id) {
            self.define_from_anchor(anchor, &atoms);
            return Ok(());
        }
        if self.optimizations.lazy_boolean {
            self.lazy_rows = Some(vec![false; self.spatial.len()]);
            return Ok(());
        }
        if self.optimizations.anchor_coverage {
            // Eager control: install exactly the guarded rows that lazy
            // refinement can select, with the same directional coverage.
            self.lazy_rows = Some(vec![false; self.spatial.len()]);
            for index in 0..self.spatial.len() {
                self.refine_heap_row(index)?;
            }
            self.lazy_rows = None;
            self.refinement_rounds = 0;
            return Ok(());
        }
        // No forced positive heap: retain the general Boolean-context encoding
        // and its original interleaving of validity and pair constraints.
        let mut validity = Vec::with_capacity(self.spatial.len());
        for i in 0..self.spatial.len() {
            validity.push(self.heap_validity(i));
            let implication = self.tm.mk_implies(atoms[i], validity[i]);
            self.assert_definition(implication);
            for j in 0..i {
                self.assert_heap_pair(i, j, &atoms, &validity);
            }
        }
        Ok(())
    }

    // A model-chosen heap is never an unconditional anchor. These implications
    // are valid for every concrete heap, irrespective of the current candidate.
    fn refine_heap_row(&mut self, source: usize) -> Result<(), HeapError> {
        let rows = self
            .lazy_rows
            .as_mut()
            .ok_or(HeapError("missing lazy definition scope"))?;
        let row = rows
            .get_mut(source)
            .ok_or(HeapError("invalid refinement heaplet"))?;
        if *row {
            return Err(HeapError(
                "heap candidate violates an already installed definition",
            ));
        }
        *row = true;
        self.refinement_rounds += 1;
        let guard = self.spatial[source].atom;
        let valid = self.heap_validity(source);
        let implication = self.tm.mk_implies(guard, valid);
        self.assert_definition(implication);
        for index in 0..self.spatial.len() {
            if index == source {
                continue;
            }
            let matches = if self.optimizations.anchor_coverage {
                self.same_heap(source, index)
            } else {
                let valid = self.heap_validity(index);
                let coverage = self.same_heap(source, index);
                self.tm.mk_and([valid, coverage])
            };
            let equivalence = self.tm.mk_eq(self.spatial[index].atom, matches);
            let implication = self.tm.mk_implies(guard, equivalence);
            self.assert_definition(implication);
        }
        Ok(())
    }

    /// Assert a Boolean formula about the single current heap.
    pub fn assert(&mut self, formula: &Formula) -> Result<(), HeapError> {
        let index = self.index(&formula.0)?;
        self.invalidate();
        self.close_definition_scope();
        self.backend.assert(self.terms[index], &mut self.tm);
        self.assertions.push(index);
        Ok(())
    }

    /// Start an assertion scope and invalidate the previous model.
    pub fn push(&mut self) {
        self.invalidate();
        self.closed = true;
        self.close_definition_scope();
        self.scopes.push(self.assertions.len());
        self.backend.push();
    }

    /// Pop one assertion scope. Underflow is an error, never a silent no-op.
    pub fn pop(&mut self) -> Result<(), HeapError> {
        self.invalidate();
        let size = self
            .scopes
            .pop()
            .ok_or(HeapError("heap assertion scope underflow"))?;
        self.close_definition_scope();
        self.assertions.truncate(size);
        self.backend.pop();
        Ok(())
    }

    /// Check satisfiability. Resource limits, unsupported proof requests, or a
    /// model that cannot be concretely validated produce `Unknown`.
    pub fn check(&mut self) -> SolverResult {
        self.invalidate();
        self.closed = true;
        if self.proof_requested {
            self.reason = Some("heap reduction has no checked proof translation");
            return SolverResult::Unknown;
        }
        if let Err(error) = self.prepare_definitions() {
            self.reason = Some(error.0);
            return SolverResult::Unknown;
        }
        let timeout = self.backend.config().timeout_ms;
        let started = (timeout != 0).then(nixie_time::Instant::now);
        loop {
            // This is only a user resource deadline, never a refinement policy.
            // Conflict/decision statistics and their limits already accumulate
            // across backend calls; do not reset them between refinements.
            if let Some(started) = started {
                let elapsed = started.elapsed().as_millis();
                if elapsed >= u128::from(timeout) {
                    self.reason = Some("heap refinement timeout");
                    return SolverResult::Unknown;
                }
                let remaining = u64::try_from(u128::from(timeout) - elapsed).unwrap_or(timeout);
                self.backend
                    .set_timeout(std::time::Duration::from_millis(remaining));
            }
            let result = self.backend.check(&mut self.tm);
            if started.is_some() {
                self.backend
                    .set_timeout(std::time::Duration::from_millis(timeout));
            }
            if result != SolverResult::Sat {
                if result == SolverResult::Unknown {
                    self.reason = Some("underlying QF_LIA solver returned Unknown");
                }
                return result;
            }
            let candidate = self.extract_model().and_then(|model| {
                self.validate_model(&model)?;
                Ok(model)
            });
            match candidate {
                Ok(model) => {
                    self.model = Some(model);
                    return SolverResult::Sat;
                }
                Err(error) => {
                    if self.lazy_rows.is_none() {
                        self.reason = Some(error.0);
                        return SolverResult::Unknown;
                    }
                    // At most one new guarded row per registered heaplet. Once
                    // a row is installed, a repeat failure is an honest Unknown,
                    // not an invented conflict or an unbounded retry loop.
                    match self.selected_heap() {
                        Ok(Some(index)) => {
                            if let Err(refinement) = self.refine_heap_row(index) {
                                self.reason = Some(refinement.0);
                                return SolverResult::Unknown;
                            }
                        }
                        Ok(None) => {
                            self.reason = Some(error.0);
                            return SolverResult::Unknown;
                        }
                        Err(error) => {
                            self.reason = Some(error.0);
                            return SolverResult::Unknown;
                        }
                    }
                }
            }
        }
    }

    /// Model from the most recent successful check, until the next mutation.
    pub fn model(&self) -> Option<&HeapModel> {
        self.model.as_ref()
    }

    /// Why the most recent check declined to give a verdict, if it did.
    pub fn reason_unknown(&self) -> Option<&'static str> {
        self.reason
    }

    /// Set the backend's reproducible search seed and invalidate the model.
    /// Zero restores the ordinary default seed; heap semantics are unchanged.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.invalidate();
        self.backend.set_random_seed(seed);
    }

    /// Inspect encoding sizes and the backend's accumulated search counters.
    pub fn statistics(&self) -> HeapStatistics {
        let backend = self.backend.get_statistics();
        HeapStatistics {
            heaplets: self.spatial.len(),
            original_nodes: self.nodes.len(),
            backend_terms: self.tm.len(),
            definition_assertions: self.definition_assertions,
            heap_comparisons: self.heap_comparisons,
            template_builds: self.templates.builds,
            template_hits: self.templates.hits,
            integer_rewrites: self.integer_rewrites,
            refinement_rounds: self.refinement_rounds,
            conflicts: backend.conflicts,
            decisions: backend.decisions,
            propagations: backend.propagations,
        }
    }
}
