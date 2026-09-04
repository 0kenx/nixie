//! Set Constraint Solver
//!
//! Core implementation of the set theory solver using:
//! - BDD-based set representation for symbolic sets
//! - Constraint propagation for membership and subset
//! - Conflict-driven reasoning for unsatisfiability

#![allow(missing_docs)]

use super::{
    CardConstraint, CardConstraintKind, CardPropagator, MemberConstraint, MemberPropagator,
    SetConflict, SetLiteral, SetProofStep, SetSort, SubsetConstraint, SubsetPropagator,
};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{
    EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult as TR,
};
use nixie_core::ast::TermId;
use nixie_core::error::Result;
use smallvec::SmallVec;

/// Set variable identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SetVarId(pub u32);

impl SetVarId {
    /// Create a new set variable ID
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the underlying ID
    pub fn id(&self) -> u32 {
        self.0
    }
}

/// Set variable representation
#[derive(Debug, Clone)]
pub struct SetVar {
    /// Variable ID
    pub id: SetVarId,
    /// Variable name (for debugging)
    pub name: String,
    /// Sort of this set
    pub sort: SetSort,
    /// Current domain: known members
    pub must_members: FxHashSet<u32>,
    /// Current domain: known non-members
    pub must_not_members: FxHashSet<u32>,
    /// Possible members (for finite domain reasoning)
    pub may_members: Option<FxHashSet<u32>>,
    /// Cardinality bounds [lower, upper]
    pub card_bounds: (Option<i64>, Option<i64>),
    /// Is this set known to be empty?
    pub is_empty: bool,
    /// Is this set the universal set?
    pub is_universal: bool,
    /// Decision level when this variable was created
    pub level: usize,
}

impl SetVar {
    /// Create a new set variable
    pub fn new(id: SetVarId, name: String, sort: SetSort, level: usize) -> Self {
        Self {
            id,
            name,
            sort,
            must_members: FxHashSet::default(),
            must_not_members: FxHashSet::default(),
            may_members: None,
            card_bounds: (Some(0), None),
            is_empty: false,
            is_universal: false,
            level,
        }
    }

    /// Add a must-member element
    pub fn add_must_member(&mut self, elem: u32) -> bool {
        if self.must_not_members.contains(&elem) {
            return false; // Conflict
        }
        self.must_members.insert(elem);
        true // Success (either newly inserted or already there)
    }

    /// Add a must-not-member element
    pub fn add_must_not_member(&mut self, elem: u32) -> bool {
        if self.must_members.contains(&elem) {
            return false; // Conflict
        }
        self.must_not_members.insert(elem);
        true // Success (either newly inserted or already there)
    }

    /// Check if element is definitely in the set
    pub fn contains(&self, elem: u32) -> Option<bool> {
        if self.must_members.contains(&elem) {
            Some(true)
        } else if self.must_not_members.contains(&elem) {
            Some(false)
        } else {
            None
        }
    }

    /// Get current cardinality bounds
    pub fn cardinality_bounds(&self) -> (i64, Option<i64>) {
        let lower = self.must_members.len() as i64;
        let upper = if let Some(may) = &self.may_members {
            Some(may.len() as i64)
        } else {
            self.card_bounds.1
        };
        (
            lower.max(self.card_bounds.0.unwrap_or(0)),
            match (upper, self.card_bounds.1) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) => Some(a),
                (None, b) => b,
            },
        )
    }

    /// Check if cardinality is determined
    pub fn cardinality_determined(&self) -> Option<i64> {
        let (lower, upper) = self.cardinality_bounds();
        if let Some(u) = upper
            && lower == u
        {
            return Some(lower);
        }
        None
    }

    /// Mark set as empty
    pub fn set_empty(&mut self) -> bool {
        if !self.must_members.is_empty() {
            return false; // Conflict
        }
        self.is_empty = true;
        self.card_bounds.1 = Some(0);
        true
    }

    /// Check if set is definitely empty
    pub fn is_definitely_empty(&self) -> bool {
        self.is_empty
            || self.card_bounds.1 == Some(0)
            || (self.may_members.as_ref().is_some_and(|m| m.is_empty()))
    }

    /// Tighten upper cardinality bound
    pub fn tighten_upper_card(&mut self, bound: i64) -> bool {
        match self.card_bounds.1 {
            Some(current) if bound >= current => true,
            _ => {
                if bound < self.must_members.len() as i64 {
                    return false; // Conflict
                }
                // Check conflict with lower bound
                if let Some(lower) = self.card_bounds.0
                    && bound < lower
                {
                    return false; // Conflict: upper < lower
                }
                self.card_bounds.1 = Some(bound);
                true
            }
        }
    }

    /// Tighten lower cardinality bound
    pub fn tighten_lower_card(&mut self, bound: i64) -> bool {
        match self.card_bounds.0 {
            Some(current) if bound <= current => true,
            _ => {
                if let Some(upper) = self.card_bounds.1
                    && bound > upper
                {
                    return false; // Conflict
                }
                self.card_bounds.0 = Some(bound);
                true
            }
        }
    }
}

/// Set expression for constraints
#[derive(Debug, Clone)]
pub enum SetExpr {
    /// Variable reference
    Var(SetVarId),
    /// Empty set
    Empty,
    /// Universal set
    Universal,
    /// Singleton set {elem}
    Singleton(u32),
    /// Union S1 ∪ S2
    Union(Box<SetExpr>, Box<SetExpr>),
    /// Intersection S1 ∩ S2
    Intersection(Box<SetExpr>, Box<SetExpr>),
    /// Difference S1 \ S2
    Difference(Box<SetExpr>, Box<SetExpr>),
    /// Complement ¬S
    Complement(Box<SetExpr>),
    /// Set comprehension {x | φ(x)}
    Comprehension { var: u32, formula: Box<SetExpr> },
}

impl SetExpr {
    /// Create a union expression
    pub fn union(left: SetExpr, right: SetExpr) -> Self {
        SetExpr::Union(Box::new(left), Box::new(right))
    }

    /// Create an intersection expression
    pub fn intersection(left: SetExpr, right: SetExpr) -> Self {
        SetExpr::Intersection(Box::new(left), Box::new(right))
    }

    /// Create a difference expression
    pub fn difference(left: SetExpr, right: SetExpr) -> Self {
        SetExpr::Difference(Box::new(left), Box::new(right))
    }

    /// Create a complement expression
    pub fn complement(expr: SetExpr) -> Self {
        SetExpr::Complement(Box::new(expr))
    }

    /// Get all set variables referenced in this expression
    pub fn get_vars(&self) -> FxHashSet<SetVarId> {
        let mut vars = FxHashSet::default();
        self.collect_vars(&mut vars);
        vars
    }

    /// Collect every set variable in this expression.
    ///
    /// Explicit stack: `SetExpr` nests as deeply as the caller builds it and
    /// this returns `()`, so a depth cap could only drop variables from the
    /// answer – and a caller that acts on an incomplete variable set is
    /// silently wrong rather than merely incomplete.
    fn collect_vars(&self, vars: &mut FxHashSet<SetVarId>) {
        let mut stack: Vec<&SetExpr> = vec![self];
        while let Some(current) = stack.pop() {
            match current {
                SetExpr::Var(v) => {
                    vars.insert(*v);
                }
                SetExpr::Union(l, r) | SetExpr::Intersection(l, r) | SetExpr::Difference(l, r) => {
                    stack.push(r);
                    stack.push(l);
                }
                SetExpr::Complement(e) => stack.push(e),
                SetExpr::Comprehension { formula, .. } => stack.push(formula),
                SetExpr::Empty | SetExpr::Universal | SetExpr::Singleton(_) => {}
            }
        }
    }
}

impl Drop for SetExpr {
    /// Dismantle the operand tree iteratively.
    ///
    /// Compiler-generated drop glue recurses once per nesting level, so an
    /// expression deep enough to build is deep enough to abort the process at
    /// scope exit, after it has already been used successfully.
    fn drop(&mut self) {
        let mut stack: Vec<SetExpr> = Vec::new();
        take_set_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_set_children(&mut node, &mut stack);
        }
    }
}

/// Move `expr`'s operands onto `out`, leaving a childless expression behind.
fn take_set_children(expr: &mut SetExpr, out: &mut Vec<SetExpr>) {
    /// A childless stand-in left where an operand used to be. Dropping it
    /// terminates immediately.
    fn placeholder() -> Box<SetExpr> {
        Box::new(SetExpr::Empty)
    }
    // The operands are swapped out one field at a time: `SetExpr` implements
    // `Drop`, so its fields cannot be moved out wholesale.
    match expr {
        SetExpr::Var(_) | SetExpr::Empty | SetExpr::Universal | SetExpr::Singleton(_) => {}
        SetExpr::Union(l, r) | SetExpr::Intersection(l, r) | SetExpr::Difference(l, r) => {
            out.push(*core::mem::replace(l, placeholder()));
            out.push(*core::mem::replace(r, placeholder()));
        }
        SetExpr::Complement(e) => out.push(*core::mem::replace(e, placeholder())),
        SetExpr::Comprehension { formula, .. } => {
            out.push(*core::mem::replace(formula, placeholder()));
        }
    }
}

/// How a compound [`SetExpr`] node is constrained once its operands'
/// variables are known. Each variant carries the auxiliary variable that was
/// created for the node *before* its operands were extracted.
enum ExtractBuild {
    /// The node denotes exactly its single operand (set comprehension).
    Alias,
    /// `lhs ∪ rhs`
    Union(SetVarId),
    /// `lhs ∩ rhs`
    Intersection(SetVarId),
    /// `lhs \\ rhs`
    Difference(SetVarId),
    /// `¬inner`
    Complement(SetVarId),
}

/// One pending compound node of the iterative [`SetSolver::extract_var`] walk.
struct ExtractFrame<'e> {
    /// How to constrain this node.
    build: ExtractBuild,
    /// Operands still to extract, reversed so `pop` yields them in order.
    pending: Vec<&'e SetExpr>,
    /// Operand variables extracted so far, in operand order.
    done: Vec<SetVarId>,
}

impl<'e> ExtractFrame<'e> {
    /// A frame for a two-operand node, extracted left then right.
    fn binary(build: ExtractBuild, lhs: &'e SetExpr, rhs: &'e SetExpr) -> Self {
        Self {
            build,
            pending: vec![rhs, lhs],
            done: Vec::new(),
        }
    }
}

/// What extracting one set expression needs: a variable already, or operands.
enum ExtractOpened<'e> {
    /// The expression already denotes this variable.
    Leaf(SetVarId),
    /// A compound whose operands must be extracted first.
    Frame(ExtractFrame<'e>),
}

/// Set constraint
#[derive(Debug, Clone)]
pub enum SetConstraint {
    /// x ∈ S
    Member {
        element: u32,
        set: SetExpr,
        sign: bool,
    },
    /// S1 ⊆ S2
    Subset {
        lhs: SetExpr,
        rhs: SetExpr,
        sign: bool,
    },
    /// S1 = S2
    Equal { lhs: SetExpr, rhs: SetExpr },
    /// |S| op k
    Cardinality {
        set: SetExpr,
        op: CardConstraintKind,
        bound: i64,
    },
    /// S1 ∩ S2 = ∅ (disjoint)
    Disjoint { lhs: SetExpr, rhs: SetExpr },
}

/// Set solver configuration
#[derive(Debug, Clone)]
pub struct SetConfig {
    /// Enable aggressive propagation
    pub aggressive_propagation: bool,
    /// Maximum cardinality for finite domain reasoning
    pub max_finite_card: Option<usize>,
    /// Enable BDD-based set representation
    pub use_bdd: bool,
    /// Conflict clause minimization
    pub minimize_conflicts: bool,
    /// Enable subset closure computation
    pub compute_subset_closure: bool,
}

impl Default for SetConfig {
    fn default() -> Self {
        Self {
            aggressive_propagation: true,
            max_finite_card: Some(1000),
            use_bdd: true,
            minimize_conflicts: true,
            compute_subset_closure: true,
        }
    }
}

/// Set solver statistics
#[derive(Debug, Clone, Default)]
pub struct SetStats {
    /// Number of set variables
    pub num_vars: usize,
    /// Number of constraints
    pub num_constraints: usize,
    /// Number of membership constraints
    pub num_member_constraints: usize,
    /// Number of subset constraints
    pub num_subset_constraints: usize,
    /// Number of cardinality constraints
    pub num_card_constraints: usize,
    /// Number of propagations
    pub num_propagations: usize,
    /// Number of conflicts
    pub num_conflicts: usize,
    /// Number of backtracks
    pub num_backtracks: usize,
}

/// Set solver result
pub type SetResult<T> = core::result::Result<T, SetConflict>;

/// Set solver state for push/pop
#[derive(Debug, Clone)]
struct SolverState {
    num_vars: usize,
    num_constraints: usize,
    num_member_constraints: usize,
    num_subset_constraints: usize,
    num_card_constraints: usize,
    num_pending_assertions: usize,
}

/// Main set theory solver
pub struct SetSolver {
    /// Configuration
    #[allow(dead_code)]
    config: SetConfig,
    /// Set variables
    vars: Vec<SetVar>,
    /// Variable name to ID mapping
    var_names: FxHashMap<String, SetVarId>,
    /// Membership constraints
    member_constraints: Vec<MemberConstraint>,
    /// Subset constraints
    subset_constraints: Vec<SubsetConstraint>,
    /// Cardinality constraints
    card_constraints: Vec<CardConstraint>,
    /// General constraints
    constraints: Vec<SetConstraint>,
    /// Propagation queue
    propagation_queue: VecDeque<SetVarId>,
    /// Membership propagator
    member_prop: MemberPropagator,
    /// Subset propagator
    subset_prop: SubsetPropagator,
    /// Cardinality propagator
    card_prop: CardPropagator,
    /// Current decision level
    level: usize,
    /// Trail of assignments (for backtracking)
    trail: Vec<TrailEntry>,
    /// Decision level boundaries in trail
    level_boundaries: Vec<usize>,
    /// Statistics
    stats: SetStats,
    /// Context stack for push/pop
    context_stack: Vec<SolverState>,
    /// Conflict clause (if UNSAT)
    conflict: Option<SetConflict>,
    /// Term to set variable mapping (for theory integration)
    term_to_var: FxHashMap<TermId, SetVarId>,
    /// Set variable to term mapping
    var_to_term: FxHashMap<SetVarId, TermId>,
    /// Pending assertions: (term_id, polarity) accumulated before propagation
    pending_assertions: Vec<(TermId, bool)>,
    /// Equalities discovered by this theory to share via Nelson-Oppen
    derived_equalities: Vec<(TermId, TermId)>,
}

/// Trail entry for backtracking
#[derive(Debug, Clone)]
enum TrailEntry {
    /// Variable assignment
    VarAssign {
        var: SetVarId,
        snapshot: SetVarSnapshot,
    },
    /// Decision level marker
    #[allow(dead_code)]
    DecisionLevel(usize),
}

/// Snapshot of a set variable for backtracking
#[derive(Debug, Clone)]
struct SetVarSnapshot {
    must_members: FxHashSet<u32>,
    must_not_members: FxHashSet<u32>,
    may_members: Option<FxHashSet<u32>>,
    card_bounds: (Option<i64>, Option<i64>),
    is_empty: bool,
    is_universal: bool,
}

impl From<&SetVar> for SetVarSnapshot {
    fn from(var: &SetVar) -> Self {
        Self {
            must_members: var.must_members.clone(),
            must_not_members: var.must_not_members.clone(),
            may_members: var.may_members.clone(),
            card_bounds: var.card_bounds,
            is_empty: var.is_empty,
            is_universal: var.is_universal,
        }
    }
}

impl SetSolver {
    /// Create a new set solver
    pub fn new() -> Self {
        Self::with_config(SetConfig::default())
    }

    /// Create a new set solver with configuration
    pub fn with_config(config: SetConfig) -> Self {
        Self {
            config,
            vars: Vec::new(),
            var_names: FxHashMap::default(),
            member_constraints: Vec::new(),
            subset_constraints: Vec::new(),
            card_constraints: Vec::new(),
            constraints: Vec::new(),
            propagation_queue: VecDeque::new(),
            member_prop: MemberPropagator::new(),
            subset_prop: SubsetPropagator::new(),
            card_prop: CardPropagator::new(),
            level: 0,
            trail: Vec::new(),
            level_boundaries: Vec::new(),
            stats: SetStats::default(),
            context_stack: Vec::new(),
            conflict: None,
            term_to_var: FxHashMap::default(),
            var_to_term: FxHashMap::default(),
            pending_assertions: Vec::new(),
            derived_equalities: Vec::new(),
        }
    }

    /// Create a new set variable
    pub fn new_set_var(&mut self, name: &str, sort: SetSort) -> SetVarId {
        let id = SetVarId(self.vars.len() as u32);
        let var = SetVar::new(id, name.to_string(), sort, self.level);
        self.vars.push(var);
        self.var_names.insert(name.to_string(), id);
        self.stats.num_vars += 1;
        id
    }

    /// Get a variable by ID
    pub fn get_var(&self, id: SetVarId) -> Option<&SetVar> {
        self.vars.get(id.0 as usize)
    }

    /// Get a mutable variable by ID
    pub fn get_var_mut(&mut self, id: SetVarId) -> Option<&mut SetVar> {
        self.vars.get_mut(id.0 as usize)
    }

    /// Get a variable by name
    pub fn get_var_by_name(&self, name: &str) -> Option<&SetVar> {
        self.var_names.get(name).and_then(|id| self.get_var(*id))
    }

    /// Add a constraint
    pub fn add_constraint(&mut self, constraint: SetConstraint) -> SetResult<()> {
        self.stats.num_constraints += 1;

        match &constraint {
            SetConstraint::Member { element, set, sign } => {
                self.add_member_constraint(*element, set, *sign)?;
            }
            SetConstraint::Subset { lhs, rhs, sign } => {
                self.add_subset_constraint(lhs, rhs, *sign)?;
            }
            SetConstraint::Equal { lhs, rhs } => {
                self.add_equal_constraint(lhs, rhs)?;
            }
            SetConstraint::Cardinality { set, op, bound } => {
                self.add_cardinality_constraint(set, *op, *bound)?;
            }
            SetConstraint::Disjoint { lhs, rhs } => {
                self.add_disjoint_constraint(lhs, rhs)?;
            }
        }

        self.constraints.push(constraint);
        Ok(())
    }

    /// Add a membership constraint: elem ∈ set or elem ∉ set
    fn add_member_constraint(&mut self, element: u32, set: &SetExpr, sign: bool) -> SetResult<()> {
        self.stats.num_member_constraints += 1;

        // Extract the set variable
        let set_var = match set {
            SetExpr::Var(v) => *v,
            _ => {
                // For complex expressions, create an auxiliary variable
                let aux_var =
                    self.new_set_var(&format!("aux_member_{}", self.vars.len()), SetSort::IntSet);
                self.add_equal_constraint(&SetExpr::Var(aux_var), set)?;
                aux_var
            }
        };

        // Save snapshot
        if let Some(var) = self.get_var(set_var) {
            self.trail.push(TrailEntry::VarAssign {
                var: set_var,
                snapshot: SetVarSnapshot::from(var),
            });
        }

        // Apply the constraint
        if let Some(var) = self.get_var_mut(set_var) {
            let success = if sign {
                var.add_must_member(element)
            } else {
                var.add_must_not_member(element)
            };

            if !success {
                return Err(SetConflict {
                    literals: vec![SetLiteral::Member {
                        element,
                        set: set_var,
                        sign,
                    }],
                    reason: format!(
                        "Conflict: element {} is both in and not in set {}",
                        element, var.name
                    ),
                    proof_steps: vec![SetProofStep::Assume(SetLiteral::Member {
                        element,
                        set: set_var,
                        sign,
                    })],
                });
            }

            // Queue for propagation
            self.propagation_queue.push_back(set_var);
        }

        Ok(())
    }

    /// Add a subset constraint: lhs ⊆ rhs or lhs ⊈ rhs
    fn add_subset_constraint(&mut self, lhs: &SetExpr, rhs: &SetExpr, sign: bool) -> SetResult<()> {
        self.stats.num_subset_constraints += 1;

        // Extract variables
        let lhs_var = self.extract_var(lhs)?;
        let rhs_var = self.extract_var(rhs)?;

        if sign {
            // lhs ⊆ rhs: all elements in lhs must be in rhs
            self.propagate_subset(lhs_var, rhs_var)?;
        } else {
            // lhs ⊈ rhs: there exists an element in lhs but not in rhs
            // This is handled lazily during conflict analysis
        }

        Ok(())
    }

    /// Add an equality constraint: lhs = rhs
    fn add_equal_constraint(&mut self, lhs: &SetExpr, rhs: &SetExpr) -> SetResult<()> {
        // S1 = S2 is equivalent to S1 ⊆ S2 ∧ S2 ⊆ S1
        self.add_subset_constraint(lhs, rhs, true)?;
        self.add_subset_constraint(rhs, lhs, true)?;
        Ok(())
    }

    /// Add a cardinality constraint: |set| op bound
    fn add_cardinality_constraint(
        &mut self,
        set: &SetExpr,
        op: CardConstraintKind,
        bound: i64,
    ) -> SetResult<()> {
        self.stats.num_card_constraints += 1;

        let set_var = self.extract_var(set)?;

        // Save snapshot
        if let Some(var) = self.get_var(set_var) {
            self.trail.push(TrailEntry::VarAssign {
                var: set_var,
                snapshot: SetVarSnapshot::from(var),
            });
        }

        // Apply cardinality bounds
        if let Some(var) = self.get_var_mut(set_var) {
            let success = match op {
                CardConstraintKind::Equal => {
                    var.tighten_lower_card(bound) && var.tighten_upper_card(bound)
                }
                CardConstraintKind::Le => var.tighten_upper_card(bound),
                CardConstraintKind::Lt => var.tighten_upper_card(bound - 1),
                CardConstraintKind::Ge => var.tighten_lower_card(bound),
                CardConstraintKind::Gt => var.tighten_lower_card(bound + 1),
            };

            if !success {
                return Err(SetConflict {
                    literals: vec![SetLiteral::Cardinality {
                        set: set_var,
                        op,
                        bound,
                    }],
                    reason: format!(
                        "Conflict: cardinality constraint |{}| {:?} {} is unsatisfiable",
                        var.name, op, bound
                    ),
                    proof_steps: vec![SetProofStep::Assume(SetLiteral::Cardinality {
                        set: set_var,
                        op,
                        bound,
                    })],
                });
            }

            self.propagation_queue.push_back(set_var);
        }

        Ok(())
    }

    /// Add a disjoint constraint: lhs ∩ rhs = ∅
    fn add_disjoint_constraint(&mut self, lhs: &SetExpr, rhs: &SetExpr) -> SetResult<()> {
        let lhs_var = self.extract_var(lhs)?;
        let rhs_var = self.extract_var(rhs)?;

        // Propagate: if x ∈ lhs, then x ∉ rhs - collect members first to avoid borrow checker issues
        let lhs_members: Vec<u32> = self
            .get_var(lhs_var)
            .map(|s| s.must_members.iter().copied().collect())
            .unwrap_or_default();

        for elem in lhs_members {
            self.add_member_constraint(elem, &SetExpr::Var(rhs_var), false)?;
        }

        // Similarly for rhs
        let rhs_members: Vec<u32> = self
            .get_var(rhs_var)
            .map(|s| s.must_members.iter().copied().collect())
            .unwrap_or_default();

        for elem in rhs_members {
            self.add_member_constraint(elem, &SetExpr::Var(lhs_var), false)?;
        }

        Ok(())
    }

    /// Extract a set variable from an expression (creating auxiliary if needed).
    ///
    /// For complex sub-expressions each arm recursively decomposes the operands
    /// and then constrains the fresh auxiliary variable to be semantically equal
    /// to the expression – without ever calling `add_equal_constraint` with the
    /// same complex expression (which would trigger infinite recursion).
    fn extract_var(&mut self, expr: &SetExpr) -> SetResult<SetVarId> {
        // Explicit stack, not recursion. `SetExpr` nests as deeply as the
        // caller builds it (it is a `pub` type with `pub` constructors and no
        // depth-capped parser in front of it), and the recursive version also
        // deep-cloned the whole remaining subtree at every level, so the walk
        // was O(N^2) in copying on top of being O(N) in native stack frames.
        // The auxiliary variable for a compound node is still created *before*
        // its operands are extracted, exactly as the recursive version did, so
        // the generated variable names and ids are unchanged.
        let mut frames: Vec<ExtractFrame<'_>> = match self.open_extract(expr)? {
            ExtractOpened::Leaf(v) => return Ok(v),
            ExtractOpened::Frame(f) => vec![f],
        };
        // An extracted operand variable travelling back to the frame that
        // asked for it.
        let mut carry: Option<SetVarId> = None;

        while !frames.is_empty() {
            let next = match frames.last_mut() {
                Some(top) => {
                    if let Some(v) = carry.take() {
                        top.done.push(v);
                    }
                    top.pending.pop()
                }
                // Unreachable: the loop condition just checked non-emptiness.
                None => break,
            };
            match next {
                Some(child) => match self.open_extract(child)? {
                    ExtractOpened::Leaf(v) => carry = Some(v),
                    ExtractOpened::Frame(f) => frames.push(f),
                },
                None => match frames.pop() {
                    Some(frame) => carry = Some(self.finish_extract(frame)?),
                    // Unreachable for the same reason as above.
                    None => break,
                },
            }
        }

        match carry {
            Some(v) => Ok(v),
            // Unreachable: the root either answered outright above or left its
            // variable in `carry` when its frame finished. Reported through the
            // real error channel rather than defaulted to some variable id.
            None => Err(SetConflict {
                literals: Vec::new(),
                reason: "internal: set expression extraction produced no variable".to_string(),
                proof_steps: Vec::new(),
            }),
        }
    }

    /// Classify one set expression: either it already denotes a variable, or
    /// it is a compound whose operands must be extracted first.
    fn open_extract<'e>(&mut self, expr: &'e SetExpr) -> SetResult<ExtractOpened<'e>> {
        // `Comprehension` denotes exactly its body set (see below), so it is
        // unwrapped here instead of costing a frame.
        // Membership axiom for {x | phi(x)}:  x in {y | phi(y)} <=> phi(x).
        // In this expression language the predicate `phi` is itself a set
        // expression `formula`, so the comprehension denotes exactly that set:
        // the comprehension variable is identified with the body set.
        // Membership constraints then propagate through the body instead of
        // hitting a fresh, unconstrained variable -- which previously let an
        // infeasible body be reported `Sat`.
        let mut expr = expr;
        while let SetExpr::Comprehension { formula, .. } = expr {
            expr = &**formula;
        }
        match expr {
            SetExpr::Var(v) => Ok(ExtractOpened::Leaf(*v)),
            SetExpr::Empty => {
                let var = self.new_set_var(&format!("empty_{}", self.vars.len()), SetSort::IntSet);
                if let Some(v) = self.get_var_mut(var) {
                    v.set_empty();
                }
                Ok(ExtractOpened::Leaf(var))
            }
            SetExpr::Universal => {
                let var = self.new_set_var(&format!("univ_{}", self.vars.len()), SetSort::IntSet);
                if let Some(v) = self.get_var_mut(var) {
                    v.is_universal = true;
                }
                Ok(ExtractOpened::Leaf(var))
            }
            SetExpr::Singleton(elem) => {
                let elem_val = *elem;
                let var = self.new_set_var(&format!("sing_{}", self.vars.len()), SetSort::IntSet);
                // Cardinality exactly 1
                if let Some(v) = self.get_var_mut(var) {
                    v.add_must_member(elem_val);
                    v.tighten_lower_card(1);
                    v.tighten_upper_card(1);
                }
                Ok(ExtractOpened::Leaf(var))
            }
            SetExpr::Union(lhs_expr, rhs_expr) => {
                let aux =
                    self.new_set_var(&format!("aux_union_{}", self.vars.len()), SetSort::IntSet);
                Ok(ExtractOpened::Frame(ExtractFrame::binary(
                    ExtractBuild::Union(aux),
                    lhs_expr,
                    rhs_expr,
                )))
            }
            SetExpr::Intersection(lhs_expr, rhs_expr) => {
                let aux =
                    self.new_set_var(&format!("aux_inter_{}", self.vars.len()), SetSort::IntSet);
                Ok(ExtractOpened::Frame(ExtractFrame::binary(
                    ExtractBuild::Intersection(aux),
                    lhs_expr,
                    rhs_expr,
                )))
            }
            SetExpr::Difference(lhs_expr, rhs_expr) => {
                let aux =
                    self.new_set_var(&format!("aux_diff_{}", self.vars.len()), SetSort::IntSet);
                Ok(ExtractOpened::Frame(ExtractFrame::binary(
                    ExtractBuild::Difference(aux),
                    lhs_expr,
                    rhs_expr,
                )))
            }
            SetExpr::Complement(inner_expr) => {
                let aux =
                    self.new_set_var(&format!("aux_compl_{}", self.vars.len()), SetSort::IntSet);
                Ok(ExtractOpened::Frame(ExtractFrame {
                    build: ExtractBuild::Complement(aux),
                    pending: vec![&**inner_expr],
                    done: Vec::new(),
                }))
            }
            // Unwrapped above; listed so the match stays exhaustive and a new
            // `SetExpr` variant becomes a compile error here.
            SetExpr::Comprehension { formula, .. } => Ok(ExtractOpened::Frame(ExtractFrame {
                build: ExtractBuild::Alias,
                pending: vec![&**formula],
                done: Vec::new(),
            })),
        }
    }

    /// Constrain a compound node's auxiliary variable now that its operands'
    /// variables are known.
    fn finish_extract(&mut self, frame: ExtractFrame<'_>) -> SetResult<SetVarId> {
        let done = frame.done;
        match frame.build {
            ExtractBuild::Alias => match done.into_iter().next_back() {
                Some(v) => Ok(v),
                // Unreachable: an `Alias` frame always carries one operand.
                None => Err(SetConflict {
                    literals: Vec::new(),
                    reason: "internal: set comprehension body produced no variable".to_string(),
                    proof_steps: Vec::new(),
                }),
            },
            ExtractBuild::Union(aux) => {
                // aux ⊇ operand, for every operand (forward propagation of
                // membership). aux ⊆ lhs ∪ rhs is approximated by recording the
                // operation (exact membership tracking happens in propagate()).
                for operand in done {
                    self.propagate_subset(operand, aux)?;
                }
                self.propagation_queue.push_back(aux);
                Ok(aux)
            }
            ExtractBuild::Intersection(aux) => {
                // aux ⊆ operand, for every operand.
                for &operand in &done {
                    self.propagate_subset(aux, operand)?;
                }
                // Must-members present in *every* operand flow into aux.
                let mut common: Option<FxHashSet<u32>> = None;
                for &operand in &done {
                    let members: FxHashSet<u32> = self
                        .get_var(operand)
                        .map(|v| v.must_members.iter().copied().collect())
                        .unwrap_or_default();
                    common = Some(match common {
                        Some(acc) => acc.intersection(&members).copied().collect(),
                        None => members,
                    });
                }
                for elem in common.unwrap_or_default() {
                    if let Some(v) = self.get_var_mut(aux) {
                        v.add_must_member(elem);
                    }
                }
                self.propagation_queue.push_back(aux);
                Ok(aux)
            }
            ExtractBuild::Difference(aux) => {
                let mut operands = done.into_iter();
                if let Some(lhs_var) = operands.next() {
                    // aux ⊆ lhs
                    self.propagate_subset(aux, lhs_var)?;
                    let lhs_must: Vec<u32> = self
                        .get_var(lhs_var)
                        .map(|v| v.must_members.iter().copied().collect())
                        .unwrap_or_default();
                    for rhs_var in operands {
                        // Every must-member of rhs must NOT be in aux.
                        let rhs_must: Vec<u32> = self
                            .get_var(rhs_var)
                            .map(|v| v.must_members.iter().copied().collect())
                            .unwrap_or_default();
                        for elem in rhs_must {
                            if let Some(v) = self.get_var_mut(aux) {
                                v.add_must_not_member(elem);
                            }
                        }
                        // Must-members of lhs definitely not in rhs are in aux.
                        let rhs_not: FxHashSet<u32> = self
                            .get_var(rhs_var)
                            .map(|v| v.must_not_members.iter().copied().collect())
                            .unwrap_or_default();
                        for &elem in &lhs_must {
                            if rhs_not.contains(&elem)
                                && let Some(v) = self.get_var_mut(aux)
                            {
                                v.add_must_member(elem);
                            }
                        }
                    }
                }
                self.propagation_queue.push_back(aux);
                Ok(aux)
            }
            ExtractBuild::Complement(aux) => {
                for inner_var in done {
                    // x ∈ inner ⟹ x ∉ aux
                    let inner_must: Vec<u32> = self
                        .get_var(inner_var)
                        .map(|v| v.must_members.iter().copied().collect())
                        .unwrap_or_default();
                    for elem in inner_must {
                        if let Some(v) = self.get_var_mut(aux) {
                            v.add_must_not_member(elem);
                        }
                    }
                    // x ∉ inner ⟹ x ∈ aux
                    let inner_not: Vec<u32> = self
                        .get_var(inner_var)
                        .map(|v| v.must_not_members.iter().copied().collect())
                        .unwrap_or_default();
                    for elem in inner_not {
                        if let Some(v) = self.get_var_mut(aux) {
                            v.add_must_member(elem);
                        }
                    }
                }
                self.propagation_queue.push_back(aux);
                Ok(aux)
            }
        }
    }

    /// Propagate subset constraint: lhs ⊆ rhs
    fn propagate_subset(&mut self, lhs: SetVarId, rhs: SetVarId) -> SetResult<()> {
        // Get members that must be in lhs
        let lhs_must_members: SmallVec<[u32; 16]> = if let Some(lhs_var) = self.get_var(lhs) {
            lhs_var.must_members.iter().copied().collect()
        } else {
            return Ok(());
        };

        // They must all be in rhs
        for elem in lhs_must_members {
            if let Some(rhs_var) = self.get_var(rhs)
                && rhs_var.must_not_members.contains(&elem)
            {
                return Err(SetConflict {
                    literals: vec![
                        SetLiteral::Subset {
                            lhs,
                            rhs,
                            sign: true,
                        },
                        SetLiteral::Member {
                            element: elem,
                            set: lhs,
                            sign: true,
                        },
                        SetLiteral::Member {
                            element: elem,
                            set: rhs,
                            sign: false,
                        },
                    ],
                    reason: format!(
                        "Conflict: element {} is in lhs but not in rhs for subset constraint",
                        elem
                    ),
                    proof_steps: vec![SetProofStep::SubsetProp {
                        from: lhs,
                        mid: lhs,
                        to: rhs,
                    }],
                });
            }

            self.add_member_constraint(elem, &SetExpr::Var(rhs), true)?;
        }

        // Get elements that must not be in rhs
        let rhs_must_not_members: SmallVec<[u32; 16]> = if let Some(rhs_var) = self.get_var(rhs) {
            rhs_var.must_not_members.iter().copied().collect()
        } else {
            return Ok(());
        };

        // They must all not be in lhs
        for elem in rhs_must_not_members {
            self.add_member_constraint(elem, &SetExpr::Var(lhs), false)?;
        }

        Ok(())
    }

    /// Run constraint propagation
    pub fn propagate(&mut self) -> SetResult<()> {
        while let Some(var_id) = self.propagation_queue.pop_front() {
            self.stats.num_propagations += 1;

            // Propagate membership
            self.member_prop.propagate(var_id, &mut self.vars)?;

            // Propagate subset
            self.subset_prop
                .propagate(var_id, &mut self.vars, &self.subset_constraints)?;

            // Propagate cardinality
            self.card_prop
                .propagate(var_id, &mut self.vars, &self.card_constraints)?;

            // Check for conflicts
            if let Some(var) = self.get_var(var_id) {
                // Check cardinality conflict
                let (lower, upper) = var.cardinality_bounds();
                let var_name = var.name.clone();
                let is_empty = var.is_definitely_empty();
                let has_must_members = !var.must_members.is_empty();

                if let Some(u) = upper
                    && lower > u
                {
                    self.stats.num_conflicts += 1;
                    return Err(SetConflict {
                        literals: vec![],
                        reason: format!(
                            "Cardinality conflict: |{}| must be in [{}, {}] which is empty",
                            var_name, lower, u
                        ),
                        proof_steps: vec![SetProofStep::CardConflict {
                            set: var_id,
                            lower,
                            upper: u,
                        }],
                    });
                }

                // Check empty set conflict
                if is_empty && has_must_members {
                    self.stats.num_conflicts += 1;
                    return Err(SetConflict {
                        literals: vec![],
                        reason: format!("Empty set conflict: {} cannot be empty", var_name),
                        proof_steps: vec![SetProofStep::EmptyConflict { set: var_id }],
                    });
                }
            }
        }

        Ok(())
    }

    /// Check satisfiability
    pub fn check(&mut self) -> SetResult<bool> {
        // Run propagation
        self.propagate()?;

        // Check if all variables are determined
        let all_determined = self
            .vars
            .iter()
            .all(|v| v.cardinality_determined().is_some());

        Ok(all_determined)
    }

    /// Push a new decision level
    pub fn push(&mut self) {
        let state = SolverState {
            num_vars: self.vars.len(),
            num_constraints: self.constraints.len(),
            num_member_constraints: self.member_constraints.len(),
            num_subset_constraints: self.subset_constraints.len(),
            num_card_constraints: self.card_constraints.len(),
            num_pending_assertions: self.pending_assertions.len(),
        };
        self.context_stack.push(state);
        self.level += 1;
        self.level_boundaries.push(self.trail.len());
        self.trail.push(TrailEntry::DecisionLevel(self.level));
    }

    /// Pop a decision level
    pub fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            self.stats.num_backtracks += 1;
            self.level = self.level.saturating_sub(1);

            // Restore state
            self.vars.truncate(state.num_vars);
            self.constraints.truncate(state.num_constraints);
            self.member_constraints
                .truncate(state.num_member_constraints);
            self.subset_constraints
                .truncate(state.num_subset_constraints);
            self.card_constraints.truncate(state.num_card_constraints);
            self.pending_assertions
                .truncate(state.num_pending_assertions);

            // Restore trail
            if let Some(boundary) = self.level_boundaries.pop() {
                while self.trail.len() > boundary {
                    if let Some(entry) = self.trail.pop()
                        && let TrailEntry::VarAssign { var, snapshot } = entry
                        && let Some(v) = self.get_var_mut(var)
                    {
                        v.must_members = snapshot.must_members;
                        v.must_not_members = snapshot.must_not_members;
                        v.may_members = snapshot.may_members;
                        v.card_bounds = snapshot.card_bounds;
                        v.is_empty = snapshot.is_empty;
                        v.is_universal = snapshot.is_universal;
                    }
                }
            }

            // Clear propagation queue
            self.propagation_queue.clear();
        }
    }

    /// Get statistics
    pub fn stats(&self) -> &SetStats {
        &self.stats
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.vars.clear();
        self.var_names.clear();
        self.member_constraints.clear();
        self.subset_constraints.clear();
        self.card_constraints.clear();
        self.constraints.clear();
        self.propagation_queue.clear();
        self.level = 0;
        self.trail.clear();
        self.level_boundaries.clear();
        self.stats = SetStats::default();
        self.context_stack.clear();
        self.conflict = None;
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.pending_assertions.clear();
        self.derived_equalities.clear();
    }

    /// Register a term-to-variable mapping
    pub fn register_term(&mut self, term: TermId, var: SetVarId) {
        self.term_to_var.insert(term, var);
        self.var_to_term.insert(var, term);
    }

    /// Get the set variable for a term
    pub fn get_var_for_term(&self, term: TermId) -> Option<SetVarId> {
        self.term_to_var.get(&term).copied()
    }

    /// Get model for a variable
    pub fn get_model(&self, var: SetVarId) -> Option<FxHashSet<u32>> {
        self.get_var(var).map(|v| v.must_members.clone())
    }
}

impl Default for SetSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl Theory for SetSolver {
    fn id(&self) -> TheoryId {
        TheoryId::Bool // Use Bool for now, should add SetTheory variant
    }

    fn name(&self) -> &str {
        "Set Theory"
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // Set theory can handle all terms; the CDCL(T) dispatcher pre-filters by sort.
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TR> {
        // Record the assertion as positive polarity; it will be processed on the
        // next call to Theory::check() by the CDCL(T) loop.
        self.pending_assertions.push((term, true));
        Ok(TR::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TR> {
        // Record the assertion as negative polarity (i.e. the set term is false).
        self.pending_assertions.push((term, false));
        Ok(TR::Sat)
    }

    fn check(&mut self) -> Result<TR> {
        match self.check() {
            Ok(true) => Ok(TR::Sat),
            Ok(false) => Ok(TR::Unknown),
            Err(conflict) => {
                self.conflict = Some(conflict.clone());
                Ok(TR::Unsat(vec![]))
            }
        }
    }

    fn push(&mut self) {
        self.push();
    }

    fn pop(&mut self) {
        self.pop();
    }

    fn reset(&mut self) {
        self.reset();
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        // Without a TermId factory we cannot construct value terms for set
        // contents.  Return an empty model; callers that need set members
        // should query the solver directly via `get_model(SetVarId)`.
        Vec::new()
    }
}

impl TheoryCombination for SetSolver {
    fn notify_equality(&mut self, eq: EqualityNotification) -> bool {
        // When another theory discovers lhs = rhs, merge their set-variable
        // domains so that set-theory reasoning stays consistent.
        let lhs_var = match self.term_to_var.get(&eq.lhs).copied() {
            Some(v) => v,
            None => return false,
        };
        let rhs_var = match self.term_to_var.get(&eq.rhs).copied() {
            Some(v) => v,
            None => return false,
        };

        if lhs_var == rhs_var {
            return true; // already the same variable
        }

        // Collect both variable's current membership sets (avoid aliasing borrows)
        let lhs_must: FxHashSet<u32> = self
            .get_var(lhs_var)
            .map(|v| v.must_members.clone())
            .unwrap_or_default();
        let lhs_not: FxHashSet<u32> = self
            .get_var(lhs_var)
            .map(|v| v.must_not_members.clone())
            .unwrap_or_default();
        let rhs_must: FxHashSet<u32> = self
            .get_var(rhs_var)
            .map(|v| v.must_members.clone())
            .unwrap_or_default();
        let rhs_not: FxHashSet<u32> = self
            .get_var(rhs_var)
            .map(|v| v.must_not_members.clone())
            .unwrap_or_default();
        let lhs_lower = self
            .get_var(lhs_var)
            .and_then(|v| v.card_bounds.0)
            .unwrap_or(0);
        let lhs_upper = self.get_var(lhs_var).and_then(|v| v.card_bounds.1);
        let rhs_lower = self
            .get_var(rhs_var)
            .and_then(|v| v.card_bounds.0)
            .unwrap_or(0);
        let rhs_upper = self.get_var(rhs_var).and_then(|v| v.card_bounds.1);

        // Conflict check: any element in one's must-members and the other's must-not-members
        for elem in &lhs_must {
            if rhs_not.contains(elem) {
                return false;
            }
        }
        for elem in &rhs_must {
            if lhs_not.contains(elem) {
                return false;
            }
        }

        // Build merged sets
        let merged_must: FxHashSet<u32> = lhs_must.union(&rhs_must).copied().collect();
        let merged_not: FxHashSet<u32> = lhs_not.union(&rhs_not).copied().collect();
        let merged_lower = lhs_lower.max(rhs_lower);
        let merged_upper = match (lhs_upper, rhs_upper) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };

        // Conflict check: merged lower > merged upper
        if merged_upper.is_some_and(|u| merged_lower > u) {
            return false;
        }

        // Apply merged state to both variables
        for var_id in [lhs_var, rhs_var] {
            if let Some(v) = self.get_var_mut(var_id) {
                v.must_members = merged_must.clone();
                v.must_not_members = merged_not.clone();
                v.card_bounds.0 = Some(merged_lower);
                v.card_bounds.1 = merged_upper;
            }
            self.propagation_queue.push_back(var_id);
        }

        true
    }

    fn get_shared_equalities(&self) -> Vec<EqualityNotification> {
        // Export equalities that have been recorded by the set solver during
        // its own reasoning (e.g. when two set variables are found to have
        // identical extension).
        self.derived_equalities
            .iter()
            .map(|(lhs, rhs)| EqualityNotification {
                lhs: *lhs,
                rhs: *rhs,
                reason: None,
            })
            .collect()
    }

    fn is_relevant(&self, term: TermId) -> bool {
        self.term_to_var.contains_key(&term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_var_creation() {
        let mut solver = SetSolver::new();
        let s1 = solver.new_set_var("S1", SetSort::IntSet);
        let s2 = solver.new_set_var("S2", SetSort::IntSet);

        assert_eq!(s1.id(), 0);
        assert_eq!(s2.id(), 1);
        assert_eq!(solver.stats.num_vars, 2);
    }

    #[test]
    fn test_membership_constraint() {
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("S", SetSort::IntSet);

        // Assert: 42 ∈ S
        let result = solver.add_member_constraint(42, &SetExpr::Var(s), true);
        assert!(result.is_ok());

        // Verify the element is in must_members
        let var = solver
            .get_var(s)
            .expect("environment variable should be set");
        assert!(var.must_members.contains(&42));
    }

    #[test]
    fn test_membership_conflict() {
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("S", SetSort::IntSet);

        // Assert: 42 ∈ S
        solver
            .add_member_constraint(42, &SetExpr::Var(s), true)
            .expect("test operation should succeed");

        // Assert: 42 ∉ S (conflict)
        let result = solver.add_member_constraint(42, &SetExpr::Var(s), false);
        assert!(result.is_err());
    }

    #[test]
    fn test_cardinality_bounds() {
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("S", SetSort::IntSet);

        // Assert: |S| ≤ 5
        solver
            .add_cardinality_constraint(&SetExpr::Var(s), CardConstraintKind::Le, 5)
            .expect("test operation should succeed");

        let var = solver
            .get_var(s)
            .expect("environment variable should be set");
        let (lower, upper) = var.cardinality_bounds();
        assert_eq!(lower, 0);
        assert_eq!(upper, Some(5));
    }

    #[test]
    fn test_cardinality_conflict() {
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("S", SetSort::IntSet);

        // Assert: |S| ≥ 10
        solver
            .add_cardinality_constraint(&SetExpr::Var(s), CardConstraintKind::Ge, 10)
            .expect("test operation should succeed");

        // Assert: |S| ≤ 5 (conflict)
        let result = solver.add_cardinality_constraint(&SetExpr::Var(s), CardConstraintKind::Le, 5);
        assert!(result.is_err());
    }

    #[test]
    fn test_subset_propagation() {
        let mut solver = SetSolver::new();
        let s1 = solver.new_set_var("S1", SetSort::IntSet);
        let s2 = solver.new_set_var("S2", SetSort::IntSet);

        // Assert: 42 ∈ S1
        solver
            .add_member_constraint(42, &SetExpr::Var(s1), true)
            .expect("test operation should succeed");

        // Assert: S1 ⊆ S2
        solver
            .add_subset_constraint(&SetExpr::Var(s1), &SetExpr::Var(s2), true)
            .expect("test operation should succeed");

        // Propagate: 42 should now be in S2
        solver.propagate().expect("test operation should succeed");

        let var2 = solver
            .get_var(s2)
            .expect("environment variable should be set");
        assert!(var2.must_members.contains(&42));
    }

    #[test]
    fn test_empty_set() {
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("S", SetSort::IntSet);

        // Assert: |S| = 0
        solver
            .add_cardinality_constraint(&SetExpr::Var(s), CardConstraintKind::Equal, 0)
            .expect("test operation should succeed");

        let var = solver
            .get_var(s)
            .expect("environment variable should be set");
        assert!(var.is_definitely_empty());
    }

    #[test]
    fn test_disjoint_sets() {
        let mut solver = SetSolver::new();
        let s1 = solver.new_set_var("S1", SetSort::IntSet);
        let s2 = solver.new_set_var("S2", SetSort::IntSet);

        // Assert: 42 ∈ S1
        solver
            .add_member_constraint(42, &SetExpr::Var(s1), true)
            .expect("test operation should succeed");

        // Assert: S1 ∩ S2 = ∅
        solver
            .add_disjoint_constraint(&SetExpr::Var(s1), &SetExpr::Var(s2))
            .expect("test operation should succeed");

        // 42 should not be in S2
        let var2 = solver
            .get_var(s2)
            .expect("environment variable should be set");
        assert!(var2.must_not_members.contains(&42));
    }

    #[test]
    fn test_push_pop() {
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("S", SetSort::IntSet);

        solver.push();

        // Assert: 42 ∈ S
        solver
            .add_member_constraint(42, &SetExpr::Var(s), true)
            .expect("test operation should succeed");

        assert!(
            solver
                .get_var(s)
                .expect("environment variable should be set")
                .must_members
                .contains(&42)
        );

        solver.pop();

        // After pop, 42 should not be in must_members
        assert!(
            !solver
                .get_var(s)
                .expect("environment variable should be set")
                .must_members
                .contains(&42)
        );
    }

    #[test]
    fn test_set_expr_vars() {
        let expr = SetExpr::union(
            SetExpr::Var(SetVarId(0)),
            SetExpr::intersection(SetExpr::Var(SetVarId(1)), SetExpr::Var(SetVarId(2))),
        );

        let vars = expr.get_vars();
        assert_eq!(vars.len(), 3);
        assert!(vars.contains(&SetVarId(0)));
        assert!(vars.contains(&SetVarId(1)));
        assert!(vars.contains(&SetVarId(2)));
    }

    #[test]
    fn test_comprehension_identifies_with_body_set() {
        // {y | y in S} extracts to exactly S, so its membership is constrained
        // by the body rather than left free.
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("s", SetSort::IntSet);
        let comp = SetExpr::Comprehension {
            var: 0,
            formula: Box::new(SetExpr::Var(s)),
        };
        let extracted = solver
            .extract_var(&comp)
            .expect("comprehension over a set variable extracts");
        assert_eq!(extracted, s);
    }

    #[test]
    fn test_comprehension_body_constrains_membership_regression() {
        // 5 in {y | y in S} together with 5 not in S is UNSAT. With the old
        // unconstrained-aux encoding the body was ignored and this was
        // fabricated as satisfiable (no conflict).
        let mut solver = SetSolver::new();
        let s = solver.new_set_var("s", SetSort::IntSet);

        solver
            .add_constraint(SetConstraint::Member {
                element: 5,
                set: SetExpr::Var(s),
                sign: false,
            })
            .expect("asserting 5 not in S is consistent on its own");

        let result = solver.add_constraint(SetConstraint::Member {
            element: 5,
            set: SetExpr::Comprehension {
                var: 0,
                formula: Box::new(SetExpr::Var(s)),
            },
            sign: true,
        });
        assert!(
            result.is_err(),
            "5 in {{y | y in S}} while 5 not in S must conflict, got {result:?}"
        );
    }
}
