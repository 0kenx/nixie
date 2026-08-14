//! Set Operations Implementation
//!
//! Implements symbolic set operations:
//! - Union (∪)
//! - Intersection (∩)
//! - Difference (\)
//! - Complement (¬)
//! - Cartesian product (×)
//! - Symmetric difference (△)

#![allow(missing_docs)]
#![allow(dead_code)]

use super::{SetConflict, SetVarId};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Binary set operation kind
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SetBinOp {
    /// Union: S1 ∪ S2
    Union,
    /// Intersection: S1 ∩ S2
    Intersection,
    /// Difference: S1 \ S2
    Difference,
    /// Symmetric difference: S1 △ S2
    SymmetricDiff,
}

/// Set operation builder for complex expressions
#[derive(Debug, Clone)]
pub struct SetOpBuilder {
    /// Operations to apply
    ops: Vec<SetOp>,
    /// Intermediate results
    intermediates: Vec<SetVarId>,
}

impl SetOpBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            ops: Vec::new(),
            intermediates: Vec::new(),
        }
    }

    /// Add a union operation
    pub fn union(mut self, lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        self.ops.push(SetOp::Binary {
            op: SetBinOp::Union,
            lhs,
            rhs,
            result,
        });
        self
    }

    /// Add an intersection operation
    pub fn intersection(mut self, lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        self.ops.push(SetOp::Binary {
            op: SetBinOp::Intersection,
            lhs,
            rhs,
            result,
        });
        self
    }

    /// Add a difference operation
    pub fn difference(mut self, lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        self.ops.push(SetOp::Binary {
            op: SetBinOp::Difference,
            lhs,
            rhs,
            result,
        });
        self
    }

    /// Add a complement operation
    pub fn complement(mut self, set: SetVarId, result: SetVarId) -> Self {
        self.ops.push(SetOp::Complement { set, result });
        self
    }

    /// Build the operation sequence
    pub fn build(self) -> Vec<SetOp> {
        self.ops
    }
}

impl Default for SetOpBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Set operation
#[derive(Debug, Clone)]
pub enum SetOp {
    /// Binary operation: result = lhs op rhs
    Binary {
        op: SetBinOp,
        lhs: SetVarId,
        rhs: SetVarId,
        result: SetVarId,
    },
    /// Complement: result = ¬set
    Complement { set: SetVarId, result: SetVarId },
}

/// Set union implementation
#[derive(Debug, Clone)]
pub struct SetUnion {
    /// Left operand
    pub lhs: SetVarId,
    /// Right operand
    pub rhs: SetVarId,
    /// Result variable
    pub result: SetVarId,
}

impl SetUnion {
    /// Create a new union operation
    pub fn new(lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        Self { lhs, rhs, result }
    }

    /// Propagate union constraints
    ///
    /// For result = lhs ∪ rhs:
    /// - x ∈ result ⟺ x ∈ lhs ∨ x ∈ rhs
    /// - x ∉ result ⟹ x ∉ lhs ∧ x ∉ rhs
    /// - x ∈ lhs ⟹ x ∈ result
    /// - x ∈ rhs ⟹ x ∈ result
    pub fn propagate(
        &self,
        lhs_members: &FxHashSet<u32>,
        lhs_non_members: &FxHashSet<u32>,
        rhs_members: &FxHashSet<u32>,
        rhs_non_members: &FxHashSet<u32>,
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut result_must = FxHashSet::default();
        let mut result_must_not = FxHashSet::default();

        // x ∈ lhs ⟹ x ∈ result
        for &elem in lhs_members {
            result_must.insert(elem);
        }

        // x ∈ rhs ⟹ x ∈ result
        for &elem in rhs_members {
            result_must.insert(elem);
        }

        // x ∉ lhs ∧ x ∉ rhs ⟹ x ∉ result
        for &elem in lhs_non_members {
            if rhs_non_members.contains(&elem) {
                result_must_not.insert(elem);
            }
        }

        (result_must, result_must_not)
    }

    /// Backward propagation from result to operands
    pub fn propagate_backward(
        &self,
        _result_members: &FxHashSet<u32>,
        result_non_members: &FxHashSet<u32>,
    ) -> (
        FxHashSet<u32>,
        FxHashSet<u32>,
        FxHashSet<u32>,
        FxHashSet<u32>,
    ) {
        let mut lhs_must_not = FxHashSet::default();
        let mut rhs_must_not = FxHashSet::default();
        let lhs_must = FxHashSet::default();
        let rhs_must = FxHashSet::default();

        // x ∉ result ⟹ x ∉ lhs ∧ x ∉ rhs
        for &elem in result_non_members {
            lhs_must_not.insert(elem);
            rhs_must_not.insert(elem);
        }

        (lhs_must, lhs_must_not, rhs_must, rhs_must_not)
    }

    /// Compute cardinality bounds for union
    ///
    /// max(|lhs|, |rhs|) ≤ |result| ≤ |lhs| + |rhs|
    pub fn cardinality_bounds(
        &self,
        lhs_card: (i64, Option<i64>),
        rhs_card: (i64, Option<i64>),
    ) -> (i64, Option<i64>) {
        let lower = lhs_card.0.max(rhs_card.0);
        let upper = match (lhs_card.1, rhs_card.1) {
            (Some(l), Some(r)) => Some(l + r),
            _ => None,
        };
        (lower, upper)
    }
}

/// Set intersection implementation
#[derive(Debug, Clone)]
pub struct SetIntersection {
    /// Left operand
    pub lhs: SetVarId,
    /// Right operand
    pub rhs: SetVarId,
    /// Result variable
    pub result: SetVarId,
}

impl SetIntersection {
    /// Create a new intersection operation
    pub fn new(lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        Self { lhs, rhs, result }
    }

    /// Propagate intersection constraints
    ///
    /// For result = lhs ∩ rhs:
    /// - x ∈ result ⟺ x ∈ lhs ∧ x ∈ rhs
    /// - x ∉ result ⟹ x ∉ lhs ∨ x ∉ rhs
    /// - x ∈ result ⟹ x ∈ lhs ∧ x ∈ rhs
    /// - x ∉ lhs ⟹ x ∉ result
    /// - x ∉ rhs ⟹ x ∉ result
    pub fn propagate(
        &self,
        lhs_members: &FxHashSet<u32>,
        lhs_non_members: &FxHashSet<u32>,
        rhs_members: &FxHashSet<u32>,
        rhs_non_members: &FxHashSet<u32>,
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut result_must = FxHashSet::default();
        let mut result_must_not = FxHashSet::default();

        // x ∈ lhs ∧ x ∈ rhs ⟹ x ∈ result
        for &elem in lhs_members {
            if rhs_members.contains(&elem) {
                result_must.insert(elem);
            }
        }

        // x ∉ lhs ⟹ x ∉ result
        for &elem in lhs_non_members {
            result_must_not.insert(elem);
        }

        // x ∉ rhs ⟹ x ∉ result
        for &elem in rhs_non_members {
            result_must_not.insert(elem);
        }

        (result_must, result_must_not)
    }

    /// Backward propagation from result to operands
    pub fn propagate_backward(
        &self,
        result_members: &FxHashSet<u32>,
        _result_non_members: &FxHashSet<u32>,
    ) -> (
        FxHashSet<u32>,
        FxHashSet<u32>,
        FxHashSet<u32>,
        FxHashSet<u32>,
    ) {
        let mut lhs_must = FxHashSet::default();
        let mut rhs_must = FxHashSet::default();
        let lhs_must_not = FxHashSet::default();
        let rhs_must_not = FxHashSet::default();

        // x ∈ result ⟹ x ∈ lhs ∧ x ∈ rhs
        for &elem in result_members {
            lhs_must.insert(elem);
            rhs_must.insert(elem);
        }

        (lhs_must, lhs_must_not, rhs_must, rhs_must_not)
    }

    /// Compute cardinality bounds for intersection
    ///
    /// 0 ≤ |result| ≤ min(|lhs|, |rhs|)
    pub fn cardinality_bounds(
        &self,
        lhs_card: (i64, Option<i64>),
        rhs_card: (i64, Option<i64>),
    ) -> (i64, Option<i64>) {
        let lower = 0;
        let upper = match (lhs_card.1, rhs_card.1) {
            (Some(l), Some(r)) => Some(l.min(r)),
            (Some(l), None) => Some(l),
            (None, Some(r)) => Some(r),
            _ => None,
        };
        (lower, upper)
    }
}

/// Set difference implementation
#[derive(Debug, Clone)]
pub struct SetDifference {
    /// Left operand
    pub lhs: SetVarId,
    /// Right operand
    pub rhs: SetVarId,
    /// Result variable
    pub result: SetVarId,
}

impl SetDifference {
    /// Create a new difference operation
    pub fn new(lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        Self { lhs, rhs, result }
    }

    /// Propagate difference constraints
    ///
    /// For result = lhs \ rhs:
    /// - x ∈ result ⟺ x ∈ lhs ∧ x ∉ rhs
    /// - x ∈ result ⟹ x ∈ lhs
    /// - x ∈ result ⟹ x ∉ rhs
    /// - x ∉ lhs ⟹ x ∉ result
    /// - x ∈ rhs ⟹ x ∉ result
    pub fn propagate(
        &self,
        lhs_members: &FxHashSet<u32>,
        lhs_non_members: &FxHashSet<u32>,
        rhs_members: &FxHashSet<u32>,
        rhs_non_members: &FxHashSet<u32>,
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut result_must = FxHashSet::default();
        let mut result_must_not = FxHashSet::default();

        // x ∈ lhs ∧ x ∉ rhs ⟹ x ∈ result
        for &elem in lhs_members {
            if rhs_non_members.contains(&elem) {
                result_must.insert(elem);
            }
        }

        // x ∉ lhs ⟹ x ∉ result
        for &elem in lhs_non_members {
            result_must_not.insert(elem);
        }

        // x ∈ rhs ⟹ x ∉ result
        for &elem in rhs_members {
            result_must_not.insert(elem);
        }

        (result_must, result_must_not)
    }

    /// Backward propagation from result to operands
    pub fn propagate_backward(
        &self,
        result_members: &FxHashSet<u32>,
        _result_non_members: &FxHashSet<u32>,
    ) -> (
        FxHashSet<u32>,
        FxHashSet<u32>,
        FxHashSet<u32>,
        FxHashSet<u32>,
    ) {
        let mut lhs_must = FxHashSet::default();
        let mut rhs_must_not = FxHashSet::default();
        let lhs_must_not = FxHashSet::default();
        let rhs_must = FxHashSet::default();

        // x ∈ result ⟹ x ∈ lhs
        for &elem in result_members {
            lhs_must.insert(elem);
            rhs_must_not.insert(elem);
        }

        // x ∉ result ∧ x ∈ lhs ⟹ x ∈ rhs
        // (This is weaker, we don't propagate it here)

        (lhs_must, lhs_must_not, rhs_must, rhs_must_not)
    }

    /// Compute cardinality bounds for difference
    ///
    /// 0 ≤ |result| ≤ |lhs|
    pub fn cardinality_bounds(
        &self,
        lhs_card: (i64, Option<i64>),
        _rhs_card: (i64, Option<i64>),
    ) -> (i64, Option<i64>) {
        let lower = 0;
        let upper = lhs_card.1;
        (lower, upper)
    }
}

/// Set complement implementation
#[derive(Debug, Clone)]
pub struct SetComplement {
    /// Set to complement
    pub set: SetVarId,
    /// Result variable
    pub result: SetVarId,
    /// Universe (if known)
    pub universe: Option<FxHashSet<u32>>,
}

impl SetComplement {
    /// Create a new complement operation
    pub fn new(set: SetVarId, result: SetVarId, universe: Option<FxHashSet<u32>>) -> Self {
        Self {
            set,
            result,
            universe,
        }
    }

    /// Propagate complement constraints
    ///
    /// For result = ¬set:
    /// - x ∈ result ⟺ x ∉ set
    /// - x ∉ result ⟺ x ∈ set
    pub fn propagate(
        &self,
        set_members: &FxHashSet<u32>,
        set_non_members: &FxHashSet<u32>,
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut result_must = FxHashSet::default();
        let mut result_must_not = FxHashSet::default();

        // x ∉ set ⟹ x ∈ result
        for &elem in set_non_members {
            result_must.insert(elem);
        }

        // x ∈ set ⟹ x ∉ result
        for &elem in set_members {
            result_must_not.insert(elem);
        }

        // If universe is known, we can be more precise
        if let Some(univ) = &self.universe {
            for &elem in univ {
                if !set_members.contains(&elem) && !set_non_members.contains(&elem) {
                    // Element is unknown in set, so unknown in result
                } else if set_members.contains(&elem) {
                    result_must_not.insert(elem);
                } else {
                    result_must.insert(elem);
                }
            }
        }

        (result_must, result_must_not)
    }

    /// Backward propagation from result to set
    pub fn propagate_backward(
        &self,
        result_members: &FxHashSet<u32>,
        result_non_members: &FxHashSet<u32>,
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut set_must = FxHashSet::default();
        let mut set_must_not = FxHashSet::default();

        // x ∈ result ⟹ x ∉ set
        for &elem in result_members {
            set_must_not.insert(elem);
        }

        // x ∉ result ⟹ x ∈ set
        for &elem in result_non_members {
            set_must.insert(elem);
        }

        (set_must, set_must_not)
    }

    /// Compute cardinality bounds for complement
    ///
    /// If universe size is known: |result| = |universe| - |set|
    pub fn cardinality_bounds(
        &self,
        set_card: (i64, Option<i64>),
        universe_card: Option<i64>,
    ) -> (i64, Option<i64>) {
        if let Some(univ_size) = universe_card {
            match set_card.1 {
                Some(set_upper) => {
                    let lower = (univ_size - set_upper).max(0);
                    let upper = Some(univ_size - set_card.0);
                    (lower, upper)
                }
                None => (0, Some(univ_size - set_card.0)),
            }
        } else {
            // Universe is infinite or unknown
            (0, None)
        }
    }
}

/// Set operation result
pub type SetOpResult<T> = core::result::Result<T, SetConflict>;

/// Set operation statistics
#[derive(Debug, Clone, Default)]
pub struct SetOpStats {
    /// Number of union operations
    pub num_unions: usize,
    /// Number of intersection operations
    pub num_intersections: usize,
    /// Number of difference operations
    pub num_differences: usize,
    /// Number of complement operations
    pub num_complements: usize,
    /// Number of propagations
    pub num_propagations: usize,
}

/// Set operation manager
#[derive(Debug)]
pub struct SetOpManager {
    /// Union operations
    unions: Vec<SetUnion>,
    /// Intersection operations
    intersections: Vec<SetIntersection>,
    /// Difference operations
    differences: Vec<SetDifference>,
    /// Complement operations
    complements: Vec<SetComplement>,
    /// Statistics
    stats: SetOpStats,
}

impl SetOpManager {
    /// Create a new operation manager
    pub fn new() -> Self {
        Self {
            unions: Vec::new(),
            intersections: Vec::new(),
            differences: Vec::new(),
            complements: Vec::new(),
            stats: SetOpStats::default(),
        }
    }

    /// Add a union operation
    pub fn add_union(&mut self, lhs: SetVarId, rhs: SetVarId, result: SetVarId) {
        self.unions.push(SetUnion::new(lhs, rhs, result));
        self.stats.num_unions += 1;
    }

    /// Add an intersection operation
    pub fn add_intersection(&mut self, lhs: SetVarId, rhs: SetVarId, result: SetVarId) {
        self.intersections
            .push(SetIntersection::new(lhs, rhs, result));
        self.stats.num_intersections += 1;
    }

    /// Add a difference operation
    pub fn add_difference(&mut self, lhs: SetVarId, rhs: SetVarId, result: SetVarId) {
        self.differences.push(SetDifference::new(lhs, rhs, result));
        self.stats.num_differences += 1;
    }

    /// Add a complement operation
    pub fn add_complement(
        &mut self,
        set: SetVarId,
        result: SetVarId,
        universe: Option<FxHashSet<u32>>,
    ) {
        self.complements
            .push(SetComplement::new(set, result, universe));
        self.stats.num_complements += 1;
    }

    /// Get statistics
    pub fn stats(&self) -> &SetOpStats {
        &self.stats
    }

    /// Reset the manager
    pub fn reset(&mut self) {
        self.unions.clear();
        self.intersections.clear();
        self.differences.clear();
        self.complements.clear();
        self.stats = SetOpStats::default();
    }
}

impl Default for SetOpManager {
    fn default() -> Self {
        Self::new()
    }
}

/// Symbolic set expression evaluator
#[derive(Debug)]
pub struct SetExprEvaluator {
    /// Cache of evaluated subexpressions
    cache: FxHashMap<SetVarId, (FxHashSet<u32>, FxHashSet<u32>)>,
}

impl SetExprEvaluator {
    /// Create a new evaluator
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    /// Evaluate a union expression
    pub fn eval_union(
        &mut self,
        lhs: SetVarId,
        rhs: SetVarId,
        lhs_val: (FxHashSet<u32>, FxHashSet<u32>),
        rhs_val: (FxHashSet<u32>, FxHashSet<u32>),
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let union_op = SetUnion::new(lhs, rhs, SetVarId(0));
        union_op.propagate(&lhs_val.0, &lhs_val.1, &rhs_val.0, &rhs_val.1)
    }

    /// Evaluate an intersection expression
    pub fn eval_intersection(
        &mut self,
        lhs: SetVarId,
        rhs: SetVarId,
        lhs_val: (FxHashSet<u32>, FxHashSet<u32>),
        rhs_val: (FxHashSet<u32>, FxHashSet<u32>),
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let inter_op = SetIntersection::new(lhs, rhs, SetVarId(0));
        inter_op.propagate(&lhs_val.0, &lhs_val.1, &rhs_val.0, &rhs_val.1)
    }

    /// Evaluate a difference expression
    pub fn eval_difference(
        &mut self,
        lhs: SetVarId,
        rhs: SetVarId,
        lhs_val: (FxHashSet<u32>, FxHashSet<u32>),
        rhs_val: (FxHashSet<u32>, FxHashSet<u32>),
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let diff_op = SetDifference::new(lhs, rhs, SetVarId(0));
        diff_op.propagate(&lhs_val.0, &lhs_val.1, &rhs_val.0, &rhs_val.1)
    }

    /// Evaluate a complement expression
    pub fn eval_complement(
        &mut self,
        set: SetVarId,
        set_val: (FxHashSet<u32>, FxHashSet<u32>),
        universe: Option<FxHashSet<u32>>,
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let comp_op = SetComplement::new(set, SetVarId(0), universe);
        comp_op.propagate(&set_val.0, &set_val.1)
    }

    /// Clear the cache
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }
}

impl Default for SetExprEvaluator {
    fn default() -> Self {
        Self::new()
    }
}

/// N-ary set operations for optimization
#[derive(Debug)]
pub struct NarySetOp {
    /// Operation kind
    pub op: SetBinOp,
    /// Operands
    pub operands: SmallVec<[SetVarId; 8]>,
    /// Result
    pub result: SetVarId,
}

impl NarySetOp {
    /// Create a new n-ary operation
    pub fn new(op: SetBinOp, operands: SmallVec<[SetVarId; 8]>, result: SetVarId) -> Self {
        Self {
            op,
            operands,
            result,
        }
    }

    /// Flatten a sequence of binary `SetOp`s into `NarySetOp`s by absorbing
    /// same-kind children into their parent.
    ///
    /// Only `Union` and `Intersection` are associative; `Difference` and
    /// `SymmetricDiff` are left as 2-operand n-ary operations.
    /// `Complement` (unary) is skipped entirely.
    pub fn flatten(ops: Vec<SetOp>) -> Vec<NarySetOp> {
        if ops.is_empty() {
            return Vec::new();
        }

        // Build a map: result SetVarId -> index into `ops`
        let mut result_to_idx: FxHashMap<SetVarId, usize> = FxHashMap::default();
        for (idx, op) in ops.iter().enumerate() {
            if let SetOp::Binary { result, .. } = op {
                result_to_idx.insert(*result, idx);
            }
        }

        // Determine which result vars are consumed as operands of another op
        let mut consumed: FxHashSet<SetVarId> = FxHashSet::default();
        for op in &ops {
            if let SetOp::Binary { lhs, rhs, .. } = op {
                consumed.insert(*lhs);
                consumed.insert(*rhs);
            }
        }

        // Iterative helper: collect all leaf operands for a root binary op,
        // flattening same-kind children in-place.
        //
        // `ops` is caller-supplied data (this is a `pub fn`'s internals),
        // and nothing prevents a `result_to_idx` chain from being cyclic --
        // e.g. two `SetOp::Binary` entries whose `result`s feed back into
        // each other's operands. A plain recursive walk of "is this var
        // itself produced by a same-kind op, then recurse into its
        // operands" would revisit such a cycle forever. This walks the
        // same tree with an explicit work-stack and an `on_path` set: a var
        // already being expanded on the current path is a back-edge, and is
        // emitted as an un-flattened (opaque) leaf instead of absorbed
        // again. That is a sound fallback, not a fabrication -- declining
        // to inline a variable's definition further never changes what it
        // denotes, it only leaves that part of the expression less
        // flattened, exactly as already happens for non-associative ops and
        // for vars that are not produced by any op at all.
        fn collect_leaves(
            var: SetVarId,
            root_op: SetBinOp,
            ops: &[SetOp],
            result_to_idx: &FxHashMap<SetVarId, usize>,
            leaves: &mut SmallVec<[SetVarId; 8]>,
        ) {
            // A flat stack of "still need to resolve this var" work items is
            // enough for the leaf-emitting steps (each pops, absorbs its
            // operands, or emits a leaf, no result to combine afterward);
            // `Leave` markers below are pushed under a var's operands so
            // they are only popped once that var's whole subtree is done,
            // which is when its `on_path` entry must be released.
            enum Work {
                Visit(SetVarId),
                Leave(SetVarId),
            }

            let mut on_path: FxHashSet<SetVarId> = FxHashSet::default();
            let mut work: Vec<Work> = vec![Work::Visit(var)];

            while let Some(item) = work.pop() {
                let v = match item {
                    Work::Leave(v) => {
                        on_path.remove(&v);
                        continue;
                    }
                    Work::Visit(v) => v,
                };

                if on_path.contains(&v) {
                    // Back-edge: `v` is already being expanded higher up
                    // this path. Stop absorbing and reference it directly.
                    leaves.push(v);
                    continue;
                }

                let Some(&idx) = result_to_idx.get(&v) else {
                    leaves.push(v);
                    continue;
                };
                let SetOp::Binary { op, lhs, rhs, .. } = &ops[idx] else {
                    leaves.push(v);
                    continue;
                };
                let absorb =
                    *op == root_op && matches!(root_op, SetBinOp::Union | SetBinOp::Intersection);
                if !absorb {
                    leaves.push(v);
                    continue;
                }

                // Absorb: push a `Leave` marker beneath this var's operands
                // so it pops (releasing `on_path`) only after both operands
                // -- and everything they in turn absorb -- are resolved.
                on_path.insert(v);
                work.push(Work::Leave(v));
                work.push(Work::Visit(*rhs));
                work.push(Work::Visit(*lhs));
            }
        }

        let mut nary_ops: Vec<NarySetOp> = Vec::new();

        for op in &ops {
            let SetOp::Binary {
                op: bin_op,
                lhs,
                rhs,
                result,
            } = op
            else {
                // Skip Complement (unary)
                continue;
            };

            // Only emit a root NarySetOp for ops whose result is NOT consumed by
            // another op (i.e. they are tree roots).
            if consumed.contains(result) {
                continue;
            }

            let mut leaves: SmallVec<[SetVarId; 8]> = SmallVec::new();
            // For associative ops, recursively absorb children
            if matches!(bin_op, SetBinOp::Union | SetBinOp::Intersection) {
                collect_leaves(*lhs, *bin_op, &ops, &result_to_idx, &mut leaves);
                collect_leaves(*rhs, *bin_op, &ops, &result_to_idx, &mut leaves);
            } else {
                // Non-associative: keep as 2-operand n-ary
                leaves.push(*lhs);
                leaves.push(*rhs);
            }

            nary_ops.push(NarySetOp::new(*bin_op, leaves, *result));
        }

        nary_ops
    }

    /// Propagate n-ary union
    pub fn propagate_nary_union(
        &self,
        operand_vals: &[(FxHashSet<u32>, FxHashSet<u32>)],
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut result_must = FxHashSet::default();
        let mut result_must_not = FxHashSet::default();

        // Collect all must-members from all operands
        for (must, _) in operand_vals {
            for &elem in must {
                result_must.insert(elem);
            }
        }

        // Element is must-not if it's must-not in all operands
        if !operand_vals.is_empty() {
            let first_must_not = &operand_vals[0].1;
            for &elem in first_must_not {
                if operand_vals
                    .iter()
                    .all(|(_, must_not)| must_not.contains(&elem))
                {
                    result_must_not.insert(elem);
                }
            }
        }

        (result_must, result_must_not)
    }

    /// Propagate n-ary intersection
    pub fn propagate_nary_intersection(
        &self,
        operand_vals: &[(FxHashSet<u32>, FxHashSet<u32>)],
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut result_must = FxHashSet::default();
        let mut result_must_not = FxHashSet::default();

        // Element is must if it's must in all operands
        if !operand_vals.is_empty() {
            let first_must = &operand_vals[0].0;
            for &elem in first_must {
                if operand_vals.iter().all(|(must, _)| must.contains(&elem)) {
                    result_must.insert(elem);
                }
            }
        }

        // Collect all must-not-members from any operand
        for (_, must_not) in operand_vals {
            for &elem in must_not {
                result_must_not.insert(elem);
            }
        }

        (result_must, result_must_not)
    }
}

/// Cartesian product operation
#[derive(Debug, Clone)]
pub struct CartesianProduct {
    /// First set
    #[allow(dead_code)]
    pub lhs: SetVarId,
    /// Second set
    #[allow(dead_code)]
    pub rhs: SetVarId,
    /// Result set (of pairs)
    #[allow(dead_code)]
    pub result: SetVarId,
}

impl CartesianProduct {
    /// Create a new cartesian product
    pub fn new(lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        Self { lhs, rhs, result }
    }

    /// Compute cardinality of cartesian product
    ///
    /// |lhs × rhs| = |lhs| * |rhs|
    pub fn cardinality_bounds(
        &self,
        lhs_card: (i64, Option<i64>),
        rhs_card: (i64, Option<i64>),
    ) -> (i64, Option<i64>) {
        let lower = lhs_card.0 * rhs_card.0;
        let upper = match (lhs_card.1, rhs_card.1) {
            (Some(l), Some(r)) => Some(l * r),
            _ => None,
        };
        (lower, upper)
    }

    /// Check if a pair is in the cartesian product
    #[allow(dead_code)]
    pub fn contains_pair(
        &self,
        pair: (u32, u32),
        lhs_members: &FxHashSet<u32>,
        rhs_members: &FxHashSet<u32>,
    ) -> Option<bool> {
        let lhs_contains = lhs_members.contains(&pair.0);
        let rhs_contains = rhs_members.contains(&pair.1);

        if lhs_contains && rhs_contains {
            Some(true)
        } else if !lhs_contains || !rhs_contains {
            Some(false)
        } else {
            None
        }
    }
}

/// Symmetric difference operation
#[derive(Debug, Clone)]
pub struct SymmetricDifference {
    /// Left operand
    #[allow(dead_code)]
    pub lhs: SetVarId,
    /// Right operand
    #[allow(dead_code)]
    pub rhs: SetVarId,
    /// Result variable
    #[allow(dead_code)]
    pub result: SetVarId,
}

impl SymmetricDifference {
    /// Create a new symmetric difference operation
    pub fn new(lhs: SetVarId, rhs: SetVarId, result: SetVarId) -> Self {
        Self { lhs, rhs, result }
    }

    /// Propagate symmetric difference constraints
    ///
    /// For result = lhs △ rhs = (lhs \ rhs) ∪ (rhs \ lhs):
    /// - x ∈ result ⟺ (x ∈ lhs ∧ x ∉ rhs) ∨ (x ∈ rhs ∧ x ∉ lhs)
    /// - x ∈ result ⟺ x ∈ lhs ⊕ x ∈ rhs
    pub fn propagate(
        &self,
        lhs_members: &FxHashSet<u32>,
        lhs_non_members: &FxHashSet<u32>,
        rhs_members: &FxHashSet<u32>,
        rhs_non_members: &FxHashSet<u32>,
    ) -> (FxHashSet<u32>, FxHashSet<u32>) {
        let mut result_must = FxHashSet::default();
        let mut result_must_not = FxHashSet::default();

        // x ∈ lhs ∧ x ∉ rhs ⟹ x ∈ result
        for &elem in lhs_members {
            if rhs_non_members.contains(&elem) {
                result_must.insert(elem);
            }
        }

        // x ∈ rhs ∧ x ∉ lhs ⟹ x ∈ result
        for &elem in rhs_members {
            if lhs_non_members.contains(&elem) {
                result_must.insert(elem);
            }
        }

        // x ∈ lhs ∧ x ∈ rhs ⟹ x ∉ result
        for &elem in lhs_members {
            if rhs_members.contains(&elem) {
                result_must_not.insert(elem);
            }
        }

        // x ∉ lhs ∧ x ∉ rhs ⟹ x ∉ result
        for &elem in lhs_non_members {
            if rhs_non_members.contains(&elem) {
                result_must_not.insert(elem);
            }
        }

        (result_must, result_must_not)
    }

    /// Compute cardinality bounds for symmetric difference
    ///
    /// |result| = |lhs| + |rhs| - 2|lhs ∩ rhs|
    #[allow(dead_code)]
    pub fn cardinality_bounds(
        &self,
        lhs_card: (i64, Option<i64>),
        rhs_card: (i64, Option<i64>),
        intersection_card: (i64, Option<i64>),
    ) -> (i64, Option<i64>) {
        let lower = (lhs_card.0 + rhs_card.0 - 2 * intersection_card.1.unwrap_or(0)).max(0);
        let upper = match (lhs_card.1, rhs_card.1) {
            (Some(l), Some(r)) => Some(l + r - 2 * intersection_card.0),
            _ => None,
        };
        (lower, upper)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union_propagation() {
        let lhs = SetVarId(0);
        let rhs = SetVarId(1);
        let result = SetVarId(2);
        let union = SetUnion::new(lhs, rhs, result);

        let mut lhs_members = FxHashSet::default();
        lhs_members.insert(1);
        lhs_members.insert(2);

        let mut rhs_members = FxHashSet::default();
        rhs_members.insert(3);

        let lhs_non = FxHashSet::default();
        let rhs_non = FxHashSet::default();

        let (result_must, _) = union.propagate(&lhs_members, &lhs_non, &rhs_members, &rhs_non);

        assert!(result_must.contains(&1));
        assert!(result_must.contains(&2));
        assert!(result_must.contains(&3));
        assert_eq!(result_must.len(), 3);
    }

    #[test]
    fn test_intersection_propagation() {
        let lhs = SetVarId(0);
        let rhs = SetVarId(1);
        let result = SetVarId(2);
        let intersection = SetIntersection::new(lhs, rhs, result);

        let mut lhs_members = FxHashSet::default();
        lhs_members.insert(1);
        lhs_members.insert(2);
        lhs_members.insert(3);

        let mut rhs_members = FxHashSet::default();
        rhs_members.insert(2);
        rhs_members.insert(3);
        rhs_members.insert(4);

        let lhs_non = FxHashSet::default();
        let rhs_non = FxHashSet::default();

        let (result_must, _) =
            intersection.propagate(&lhs_members, &lhs_non, &rhs_members, &rhs_non);

        assert!(!result_must.contains(&1));
        assert!(result_must.contains(&2));
        assert!(result_must.contains(&3));
        assert!(!result_must.contains(&4));
        assert_eq!(result_must.len(), 2);
    }

    #[test]
    fn test_difference_propagation() {
        let lhs = SetVarId(0);
        let rhs = SetVarId(1);
        let result = SetVarId(2);
        let difference = SetDifference::new(lhs, rhs, result);

        let mut lhs_members = FxHashSet::default();
        lhs_members.insert(1);
        lhs_members.insert(2);
        lhs_members.insert(3);

        let mut rhs_members = FxHashSet::default();
        rhs_members.insert(2);
        rhs_members.insert(4);

        let mut rhs_non = FxHashSet::default();
        rhs_non.insert(1);
        rhs_non.insert(3);

        let lhs_non = FxHashSet::default();

        let (result_must, result_must_not) =
            difference.propagate(&lhs_members, &lhs_non, &rhs_members, &rhs_non);

        // 1 ∈ lhs and 1 ∉ rhs, so 1 ∈ result
        assert!(result_must.contains(&1));
        // 3 ∈ lhs and 3 ∉ rhs, so 3 ∈ result
        assert!(result_must.contains(&3));
        // 2 ∈ rhs, so 2 ∉ result
        assert!(result_must_not.contains(&2));
    }

    #[test]
    fn test_complement_propagation() {
        let set = SetVarId(0);
        let result = SetVarId(1);

        let mut universe = FxHashSet::default();
        for i in 1..=5 {
            universe.insert(i);
        }

        let complement = SetComplement::new(set, result, Some(universe));

        let mut set_members = FxHashSet::default();
        set_members.insert(1);
        set_members.insert(2);

        let mut set_non = FxHashSet::default();
        set_non.insert(4);
        set_non.insert(5);

        let (result_must, result_must_not) = complement.propagate(&set_members, &set_non);

        // 4, 5 ∉ set, so they ∈ result
        assert!(result_must.contains(&4));
        assert!(result_must.contains(&5));
        // 1, 2 ∈ set, so they ∉ result
        assert!(result_must_not.contains(&1));
        assert!(result_must_not.contains(&2));
    }

    #[test]
    fn test_symmetric_difference() {
        let lhs = SetVarId(0);
        let rhs = SetVarId(1);
        let result = SetVarId(2);
        let symdiff = SymmetricDifference::new(lhs, rhs, result);

        let mut lhs_members = FxHashSet::default();
        lhs_members.insert(1);
        lhs_members.insert(2);
        lhs_members.insert(3);

        let mut rhs_members = FxHashSet::default();
        rhs_members.insert(2);
        rhs_members.insert(3);
        rhs_members.insert(4);

        let mut lhs_non = FxHashSet::default();
        lhs_non.insert(4);
        lhs_non.insert(5);

        let mut rhs_non = FxHashSet::default();
        rhs_non.insert(1);
        rhs_non.insert(5);

        let (result_must, result_must_not) =
            symdiff.propagate(&lhs_members, &lhs_non, &rhs_members, &rhs_non);

        // 1 ∈ lhs, 1 ∉ rhs => 1 ∈ result
        assert!(result_must.contains(&1));
        // 4 ∈ rhs, 4 ∉ lhs => 4 ∈ result
        assert!(result_must.contains(&4));
        // 2 ∈ lhs, 2 ∈ rhs => 2 ∉ result
        assert!(result_must_not.contains(&2));
        // 3 ∈ lhs, 3 ∈ rhs => 3 ∉ result
        assert!(result_must_not.contains(&3));
        // 5 ∉ lhs, 5 ∉ rhs => 5 ∉ result
        assert!(result_must_not.contains(&5));
    }

    #[test]
    fn test_union_cardinality_bounds() {
        let union = SetUnion::new(SetVarId(0), SetVarId(1), SetVarId(2));

        let lhs_card = (2, Some(5));
        let rhs_card = (3, Some(4));

        let (lower, upper) = union.cardinality_bounds(lhs_card, rhs_card);

        assert_eq!(lower, 3); // max(2, 3)
        assert_eq!(upper, Some(9)); // 5 + 4
    }

    #[test]
    fn test_intersection_cardinality_bounds() {
        let intersection = SetIntersection::new(SetVarId(0), SetVarId(1), SetVarId(2));

        let lhs_card = (2, Some(5));
        let rhs_card = (3, Some(4));

        let (lower, upper) = intersection.cardinality_bounds(lhs_card, rhs_card);

        assert_eq!(lower, 0);
        assert_eq!(upper, Some(4)); // min(5, 4)
    }

    #[test]
    fn test_cartesian_product_cardinality() {
        let product = CartesianProduct::new(SetVarId(0), SetVarId(1), SetVarId(2));

        let lhs_card = (2, Some(3));
        let rhs_card = (4, Some(5));

        let (lower, upper) = product.cardinality_bounds(lhs_card, rhs_card);

        assert_eq!(lower, 8); // 2 * 4
        assert_eq!(upper, Some(15)); // 3 * 5
    }

    #[test]
    fn test_set_op_builder() {
        let builder = SetOpBuilder::new()
            .union(SetVarId(0), SetVarId(1), SetVarId(2))
            .intersection(SetVarId(2), SetVarId(3), SetVarId(4));

        let ops = builder.build();
        assert_eq!(ops.len(), 2);
    }

    #[test]
    fn test_nary_union_propagation() {
        let op = NarySetOp::new(
            SetBinOp::Union,
            SmallVec::from_vec(vec![SetVarId(0), SetVarId(1), SetVarId(2)]),
            SetVarId(3),
        );

        let mut operand_vals = Vec::new();

        let mut set1 = (FxHashSet::default(), FxHashSet::default());
        set1.0.insert(1);
        operand_vals.push(set1);

        let mut set2 = (FxHashSet::default(), FxHashSet::default());
        set2.0.insert(2);
        operand_vals.push(set2);

        let mut set3 = (FxHashSet::default(), FxHashSet::default());
        set3.0.insert(3);
        operand_vals.push(set3);

        let (result_must, _) = op.propagate_nary_union(&operand_vals);

        assert!(result_must.contains(&1));
        assert!(result_must.contains(&2));
        assert!(result_must.contains(&3));
        assert_eq!(result_must.len(), 3);
    }

    #[test]
    fn test_nary_intersection_propagation() {
        let op = NarySetOp::new(
            SetBinOp::Intersection,
            SmallVec::from_vec(vec![SetVarId(0), SetVarId(1), SetVarId(2)]),
            SetVarId(3),
        );

        let mut operand_vals = Vec::new();

        let mut set1 = (FxHashSet::default(), FxHashSet::default());
        set1.0.insert(1);
        set1.0.insert(2);
        operand_vals.push(set1);

        let mut set2 = (FxHashSet::default(), FxHashSet::default());
        set2.0.insert(2);
        set2.0.insert(3);
        operand_vals.push(set2);

        let mut set3 = (FxHashSet::default(), FxHashSet::default());
        set3.0.insert(2);
        set3.0.insert(4);
        operand_vals.push(set3);

        let (result_must, _) = op.propagate_nary_intersection(&operand_vals);

        assert!(!result_must.contains(&1));
        assert!(result_must.contains(&2)); // 2 is in all three sets
        assert!(!result_must.contains(&3));
        assert!(!result_must.contains(&4));
        assert_eq!(result_must.len(), 1);
    }

    // ========  ========
    // `NarySetOp::flatten` / `collect_leaves` cycle-safety regression tests
    // (audit: a cyclic `result_to_idx` chain made the leaf-collecting
    // recursion loop forever; `flatten` itself had no prior test coverage).
    // ========  ========

    #[test]
    fn test_flatten_normal_nested_union() {
        // Basic behaviour-preservation smoke test (flatten had zero prior
        // coverage): result = (a ∪ b) ∪ c must flatten into one n-ary op
        // over [a, b, c].
        let a = SetVarId(0);
        let b = SetVarId(1);
        let c = SetVarId(2);
        let ab = SetVarId(3);
        let root = SetVarId(4);
        let ops = vec![
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: a,
                rhs: b,
                result: ab,
            },
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: ab,
                rhs: c,
                result: root,
            },
        ];
        let nary = NarySetOp::flatten(ops);
        assert_eq!(nary.len(), 1);
        assert_eq!(nary[0].result, root);
        assert_eq!(nary[0].op, SetBinOp::Union);
        assert_eq!(nary[0].operands.to_vec(), vec![a, b, c]);
    }

    #[test]
    fn test_flatten_diamond_shared_substructure_matches_expansion_order() {
        // X = A ∪ B is shared by P = X ∪ Y and Q = X ∪ Z; root = P ∪ Q.
        // Flattening does not memoize/dedupe shared subterms (each
        // consuming branch expands its own copy), so X's operands appear
        // twice -- pinning this exact order guards against the iterative
        // conversion silently changing it (e.g. by adding memoization that
        // would be wrong here, unlike the sibling fixes in this module
        // where memoizing a *pure* per-call computation is safe).
        let a = SetVarId(0);
        let b = SetVarId(1);
        let x = SetVarId(2);
        let y = SetVarId(3);
        let z = SetVarId(4);
        let p = SetVarId(5);
        let q = SetVarId(6);
        let root = SetVarId(7);
        let ops = vec![
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: a,
                rhs: b,
                result: x,
            },
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: x,
                rhs: y,
                result: p,
            },
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: x,
                rhs: z,
                result: q,
            },
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: p,
                rhs: q,
                result: root,
            },
        ];
        let nary = NarySetOp::flatten(ops);
        assert_eq!(nary.len(), 1, "only `root` is not consumed by another op");
        assert_eq!(
            nary[0].operands.to_vec(),
            vec![a, b, y, a, b, z],
            "X = A ∪ B is expanded independently under both P and Q"
        );
    }

    #[test]
    fn test_flatten_cyclic_result_to_idx_terminates_with_defensible_leaves() {
        // V1 = V0 ∪ V2 and V0 = V1 ∪ V3 mutually depend on each other's
        // result (never producible via `SetOpBuilder`, but nothing in the
        // public `SetOp`/`flatten` API rules it out). V5 = V0 ∪ V4 is a
        // root reaching into the cycle through V0. Neither V0 nor V1 is a
        // root itself (each is consumed by the other), so the only work
        // `flatten` has to do is collect_leaves(V0) / collect_leaves(V4)
        // for V5's op -- and collect_leaves(V0) is exactly where the
        // recursion used to loop forever (V0 -> absorbs via V1's op -> V1
        // -> absorbs via V0's op -> V0 -> ...).
        let v0 = SetVarId(0);
        let v1 = SetVarId(1);
        let v2 = SetVarId(2);
        let v3 = SetVarId(3);
        let v4 = SetVarId(4);
        let v5 = SetVarId(5);
        let ops = vec![
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: v0,
                rhs: v2,
                result: v1,
            },
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: v1,
                rhs: v3,
                result: v0,
            },
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: v0,
                rhs: v4,
                result: v5,
            },
        ];

        // The primary assertion is that this call returns at all.
        let nary = NarySetOp::flatten(ops);

        assert_eq!(nary.len(), 1, "only v5's op is a root");
        assert_eq!(nary[0].result, v5);
        assert_eq!(nary[0].op, SetBinOp::Union);
        // The back-edge to v0 is emitted as an opaque (un-flattened) leaf
        // rather than absorbed again, alongside the ordinary leaves v2..v4.
        let mut operands: Vec<SetVarId> = nary[0].operands.to_vec();
        operands.sort();
        assert_eq!(operands, vec![v0, v2, v3, v4]);
    }

    #[test]
    fn test_flatten_self_referential_op_terminates() {
        // An op whose result is also (directly) one of its own operands:
        // V0 = V0 ∪ V1. Also never producible via `SetOpBuilder`, but a
        // caller-constructed `SetOp` list is not prevented from shaping it
        // this way.
        let v0 = SetVarId(0);
        let v1 = SetVarId(1);
        let v5 = SetVarId(5);
        let v4 = SetVarId(4);
        let ops = vec![
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: v0,
                rhs: v1,
                result: v0,
            },
            SetOp::Binary {
                op: SetBinOp::Union,
                lhs: v0,
                rhs: v4,
                result: v5,
            },
        ];
        let nary = NarySetOp::flatten(ops);
        assert_eq!(nary.len(), 1);
        let mut operands: Vec<SetVarId> = nary[0].operands.to_vec();
        operands.sort();
        assert_eq!(operands, vec![v0, v1, v4]);
    }

    #[test]
    fn test_flatten_deep_associative_chain_small_stack() {
        // Build (iteratively) a long left-leaning chain
        // (((leaf_0 ∪ leaf_1) ∪ leaf_2) ∪ ... ∪ leaf_n) and flatten it from
        // inside a thread with a deliberately small (128 KiB) stack. A stack
        // overflow aborts the whole process, so "the thread returned at
        // all" is itself part of the assertion. The stack size and `depth` are
        // scaled together and only their ratio (~21 bytes per level) matters --
        // never raise one without the other.
        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let depth: u32 = 12_500;
                let mut ops = Vec::with_capacity(depth as usize);
                // Leaves use even ids, intermediate results use odd ids, so
                // neither range collides with the other.
                let mut prev_result = SetVarId(0); // leaf_0, not itself a result
                for i in 1..=depth {
                    let leaf = SetVarId(2 * i);
                    let result = SetVarId(2 * i + 1);
                    ops.push(SetOp::Binary {
                        op: SetBinOp::Union,
                        lhs: prev_result,
                        rhs: leaf,
                        result,
                    });
                    prev_result = result;
                }
                let nary = NarySetOp::flatten(ops);
                assert_eq!(nary.len(), 1);
                assert_eq!(nary[0].operands.len() as u32, depth + 1);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deep but acyclic associative chain must not overflow a 128 KiB stack");
    }
}
