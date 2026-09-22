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
    /// Finite-map comparisons constructed in the current private scope.
    pub heap_comparisons: usize,
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

    // Extract only literal consequences justified by Boolean syntax. In
    // particular Or(true) and And(false) do not force any particular child.
    // The two-bit visited set bounds work on DAGs with shared subformulas.
    fn forced_heap_atoms(&self) -> Result<Vec<Option<bool>>, HeapError> {
        let mut forced = vec![None; self.spatial.len()];
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
                Node::Heap(i) => {
                    let slot = forced.get_mut(*i).ok_or(HeapError("invalid heap atom"))?;
                    if slot.is_some_and(|previous| previous != polarity) {
                        // Original assertions are contradictory. Leave definitions
                        // symbolic and let the backend establish the conflict.
                        return Ok(vec![None; self.spatial.len()]);
                    }
                    *slot = Some(polarity);
                }
                Node::And(_)
                | Node::Or(_)
                | Node::Boolean(_)
                | Node::BoolVar(_)
                | Node::Eq(_, _)
                | Node::Le(_, _) => {}
                Node::Integer(_)
                | Node::IntVar(_)
                | Node::Add(_, _)
                | Node::Sub(_, _)
                | Node::Scale(_, _) => {
                    return Err(HeapError("integer node in Boolean assertion"));
                }
            }
        }
        Ok(forced)
    }

    fn close_definition_scope(&mut self) {
        if self.definition_scope_open {
            self.backend.pop();
            self.definition_scope_open = false;
            self.definition_assertions = 0;
            self.heap_comparisons = 0;
        }
    }

    fn assert_definition(&mut self, term: TermId) {
        if term != self.tm.true_id {
            self.backend.assert(term, &mut self.tm);
            self.definition_assertions += 1;
        }
    }

    fn heap_validity(&mut self, index: usize) -> TermId {
        let zero = self.tm.mk_int(0);
        let cells = &self.spatial[index].cells;
        let mut valid = Vec::new();
        for (j, &(l, _)) in cells.iter().enumerate() {
            let nil = self.tm.mk_eq(self.terms[l], zero);
            valid.push(self.tm.mk_not(nil));
            for &(r, _) in &cells[..j] {
                let alias = self.tm.mk_eq(self.terms[l], self.terms[r]);
                valid.push(self.tm.mk_not(alias));
            }
        }
        self.tm.mk_and(valid)
    }

    // With both validity conditions, equal cardinality and membership of
    // every cell is equality of finite maps. This is not equality of lists.
    fn same_heap(&mut self, i: usize, j: usize) -> TermId {
        self.heap_comparisons += 1;
        let cells = &self.spatial[i].cells;
        let other = &self.spatial[j].cells;
        if cells.len() != other.len() {
            return self.tm.false_id;
        }
        let mut matches = Vec::new();
        for &(l, v) in cells {
            let mut choices = Vec::new();
            for &(r, w) in other {
                let address = self.tm.mk_eq(self.terms[l], self.terms[r]);
                let value = self.tm.mk_eq(self.terms[v], self.terms[w]);
                choices.push(self.tm.mk_and([address, value]));
            }
            matches.push(self.tm.mk_or(choices));
        }
        self.tm.mk_and(matches)
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
            let valid = self.heap_validity(i);
            validity.push(valid);
            let same = self.same_heap(i, anchor);
            let matches = self.tm.mk_and([valid, same]);
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
        let forced = self.forced_heap_atoms()?;
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
        // A syntactically entailed positive heap fixes the entire current
        // finite map. Never choose an arbitrary disjunct or a model guess.
        if let Some(anchor) = atoms.iter().position(|&atom| atom == self.tm.true_id) {
            self.define_from_anchor(anchor, &atoms);
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
        let result = self.backend.check(&mut self.tm);
        if result != SolverResult::Sat {
            if result == SolverResult::Unknown {
                self.reason = Some("underlying QF_LIA solver returned Unknown");
            }
            return result;
        }
        match self.extract_model().and_then(|model| {
            self.validate_model(&model)?;
            Ok(model)
        }) {
            Ok(model) => {
                self.model = Some(model);
                SolverResult::Sat
            }
            Err(error) => {
                self.reason = Some(error.0);
                SolverResult::Unknown
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
            conflicts: backend.conflicts,
            decisions: backend.decisions,
            propagations: backend.propagations,
        }
    }
}
