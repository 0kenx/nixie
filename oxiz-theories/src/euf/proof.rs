//! Proof Generation for Congruence Closure
//!
//! Generates proofs (explanations) for equalities and conflicts in the EUF theory.
//! This is crucial for:
//! - UNSAT core extraction
//! - Theory propagation explanations
//! - Interpolation

#[allow(unused_imports)]
use crate::prelude::*;
use core::fmt;
use oxiz_core::ast::TermId;
use smallvec::SmallVec;

/// A proof step in the congruence closure
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStep {
    /// Given equality (axiom): a = b
    Given {
        /// Left term
        left: TermId,
        /// Right term
        right: TermId,
        /// Reason (e.g., literal ID)
        reason: u32,
    },

    /// Reflexivity: a = a
    Refl {
        /// The term
        term: TermId,
    },

    /// Symmetry: a = b → b = a
    Symm {
        /// Original proof
        proof: Box<ProofStep>,
    },

    /// Transitivity: a = b ∧ b = c → a = c
    Trans {
        /// Left proof (a = b)
        left: Box<ProofStep>,
        /// Right proof (b = c)
        right: Box<ProofStep>,
    },

    /// Congruence: f(a₁,...,aₙ) = f(b₁,...,bₙ) if aᵢ = bᵢ for all i
    Cong {
        /// Function symbol
        func: TermId,
        /// Proofs for argument equalities
        arg_proofs: Vec<ProofStep>,
    },
}

impl ProofStep {
    /// Extract the left and right terms from a proof
    pub fn terms(&self) -> (TermId, TermId) {
        (self.endpoint(false), self.endpoint(true))
    }

    /// Follow the proof to one of its two endpoints.
    ///
    /// A plain loop rather than recursion: `Symm`/`Trans`/`Cong` nesting is
    /// the proof's own depth, which is caller-controlled through the public
    /// constructors, and the return type is `TermId` — a depth cap could only
    /// name the wrong term as the equality's endpoint.
    fn endpoint(&self, want_right: bool) -> TermId {
        let mut node = self;
        let mut want_right = want_right;
        loop {
            match node {
                ProofStep::Given { left, right, .. } => {
                    return if want_right { *right } else { *left };
                }
                ProofStep::Refl { term } => return *term,
                ProofStep::Symm { proof } => {
                    // a = b becomes b = a: the endpoints swap.
                    node = proof;
                    want_right = !want_right;
                }
                ProofStep::Trans { left, right } => {
                    node = if want_right { right } else { left };
                }
                ProofStep::Cong { func, .. } => return *func, // Simplified
            }
        }
    }

    /// Get the reasons (axioms) used in this proof
    pub fn reasons(&self) -> Vec<u32> {
        let mut reasons = Vec::new();
        self.collect_reasons(&mut reasons);
        reasons
    }

    /// Explicit stack, not recursion; sub-proofs are pushed in reverse so the
    /// reasons come out in the same order the recursive descent produced.
    fn collect_reasons(&self, reasons: &mut Vec<u32>) {
        let mut stack: Vec<&ProofStep> = vec![self];
        while let Some(node) = stack.pop() {
            match node {
                ProofStep::Given { reason, .. } => reasons.push(*reason),
                ProofStep::Refl { .. } => {}
                ProofStep::Symm { proof } => stack.push(proof),
                ProofStep::Trans { left, right } => {
                    stack.push(right);
                    stack.push(left);
                }
                ProofStep::Cong { arg_proofs, .. } => stack.extend(arg_proofs.iter().rev()),
            }
        }
    }

    /// Compute the size of the proof (number of steps)
    ///
    /// Explicit stack: the count has no error channel, so a depth cap could
    /// only report a proof as smaller than it is.
    #[must_use]
    pub fn size(&self) -> usize {
        let mut total = 0usize;
        let mut stack: Vec<&ProofStep> = vec![self];
        while let Some(node) = stack.pop() {
            total += 1;
            match node {
                ProofStep::Given { .. } | ProofStep::Refl { .. } => {}
                ProofStep::Symm { proof } => stack.push(proof),
                ProofStep::Trans { left, right } => {
                    stack.push(left);
                    stack.push(right);
                }
                ProofStep::Cong { arg_proofs, .. } => stack.extend(arg_proofs.iter()),
            }
        }
        total
    }
}

/// One item of [`ProofStep`]'s iterative `Display` output.
enum ProofToken<'a> {
    /// A sub-proof still to be rendered.
    Node(&'a ProofStep),
    /// Literal text to emit at this point.
    Text(&'static str),
}

impl fmt::Display for ProofStep {
    /// Explicit output stack, not recursion: `fmt` is reached from `{}` in
    /// error and log messages, where a second stack overflow is least
    /// recoverable, and the proof's depth is caller-controlled.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut stack: Vec<ProofToken<'_>> = vec![ProofToken::Node(self)];
        while let Some(item) = stack.pop() {
            let node = match item {
                ProofToken::Text(text) => {
                    f.write_str(text)?;
                    continue;
                }
                ProofToken::Node(node) => node,
            };
            match node {
                ProofStep::Given {
                    left,
                    right,
                    reason,
                } => write!(f, "Given({:?} = {:?}, reason={})", left, right, reason)?,
                ProofStep::Refl { term } => write!(f, "Refl({:?})", term)?,
                ProofStep::Symm { proof } => {
                    write!(f, "Symm(")?;
                    stack.push(ProofToken::Text(")"));
                    stack.push(ProofToken::Node(proof));
                }
                ProofStep::Trans { left, right } => {
                    write!(f, "Trans(")?;
                    stack.push(ProofToken::Text(")"));
                    stack.push(ProofToken::Node(right));
                    stack.push(ProofToken::Text(", "));
                    stack.push(ProofToken::Node(left));
                }
                ProofStep::Cong { func, arg_proofs } => {
                    write!(f, "Cong({:?}, [", func)?;
                    stack.push(ProofToken::Text("])"));
                    for (i, proof) in arg_proofs.iter().enumerate().rev() {
                        stack.push(ProofToken::Node(proof));
                        if i > 0 {
                            stack.push(ProofToken::Text(", "));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

impl Drop for ProofStep {
    /// Dismantle the sub-proof tree iteratively.
    ///
    /// Compiler-generated drop glue recurses once per proof level, so a proof
    /// deep enough to build is deep enough to abort the process at scope exit,
    /// after it has already been used successfully.
    fn drop(&mut self) {
        let mut stack: Vec<ProofStep> = Vec::new();
        take_proof_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_proof_children(&mut node, &mut stack);
        }
    }
}

/// Move `step`'s sub-proofs onto `out`, leaving a childless step behind.
fn take_proof_children(step: &mut ProofStep, out: &mut Vec<ProofStep>) {
    /// A childless stand-in left where a sub-proof used to be. It is dropped
    /// immediately and never observed.
    fn placeholder() -> Box<ProofStep> {
        Box::new(ProofStep::Refl {
            term: TermId::new(0),
        })
    }
    // Sub-proofs are swapped out one field at a time: `ProofStep` implements
    // `Drop`, so its fields cannot be moved out wholesale.
    match step {
        ProofStep::Given { .. } | ProofStep::Refl { .. } => {}
        ProofStep::Symm { proof } => out.push(*core::mem::replace(proof, placeholder())),
        ProofStep::Trans { left, right } => {
            out.push(*core::mem::replace(left, placeholder()));
            out.push(*core::mem::replace(right, placeholder()));
        }
        ProofStep::Cong { arg_proofs, .. } => out.append(arg_proofs),
    }
}

/// Proof forest for efficient proof construction
///
/// Stores parent pointers with proof annotations.
#[derive(Debug)]
pub struct ProofForest {
    /// Parent of each term (for union-find)
    parent: FxHashMap<TermId, TermId>,
    /// Proof from term to its parent
    proof_to_parent: FxHashMap<TermId, ProofStep>,
    /// Rank for union-by-rank
    rank: FxHashMap<TermId, u32>,
}

impl Default for ProofForest {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofForest {
    /// Create a new proof forest
    #[must_use]
    pub fn new() -> Self {
        Self {
            parent: FxHashMap::default(),
            proof_to_parent: FxHashMap::default(),
            rank: FxHashMap::default(),
        }
    }

    /// Make a term (ensure it exists)
    pub fn make(&mut self, term: TermId) {
        if let crate::prelude::hash_map::Entry::Vacant(e) = self.parent.entry(term) {
            e.insert(term);
            self.rank.insert(term, 0);
        }
    }

    /// Find the representative of a term
    #[must_use]
    pub fn find(&self, term: TermId) -> TermId {
        let mut current = term;
        while let Some(&parent) = self.parent.get(&current) {
            if parent == current {
                return current;
            }
            current = parent;
        }
        term
    }

    /// Union two terms with a proof
    pub fn union(&mut self, a: TermId, b: TermId, proof: ProofStep) {
        let root_a = self.find(a);
        let root_b = self.find(b);

        if root_a == root_b {
            return;
        }

        let rank_a = self.rank.get(&root_a).copied().unwrap_or(0);
        let rank_b = self.rank.get(&root_b).copied().unwrap_or(0);

        match rank_a.cmp(&rank_b) {
            core::cmp::Ordering::Less => {
                self.parent.insert(root_a, root_b);
                self.proof_to_parent.insert(root_a, proof);
            }
            core::cmp::Ordering::Greater => {
                self.parent.insert(root_b, root_a);
                self.proof_to_parent.insert(root_b, proof);
            }
            core::cmp::Ordering::Equal => {
                self.parent.insert(root_b, root_a);
                self.proof_to_parent.insert(root_b, proof);
                self.rank.insert(root_a, rank_a + 1);
            }
        }
    }

    /// Explain why two terms are equal
    pub fn explain(&self, a: TermId, b: TermId) -> Option<ProofStep> {
        if a == b {
            return Some(ProofStep::Refl { term: a });
        }

        // Find paths from a and b to their common root
        let path_a = self.path_to_root(a);
        let path_b = self.path_to_root(b);

        if path_a.is_empty() || path_b.is_empty() {
            return None;
        }

        // Check if they have the same root
        if path_a.last() != path_b.last() {
            return None;
        }

        // Build proof: a →* root ←* b
        let proof_a_to_root = self.build_proof_path(&path_a)?;
        let proof_b_to_root = self.build_proof_path(&path_b)?;

        // Combine: a = root ∧ b = root → a = b
        Some(ProofStep::Trans {
            left: Box::new(proof_a_to_root),
            right: Box::new(ProofStep::Symm {
                proof: Box::new(proof_b_to_root),
            }),
        })
    }

    /// Find path from term to root
    fn path_to_root(&self, term: TermId) -> Vec<TermId> {
        let mut path = vec![term];
        let mut current = term;

        while let Some(&parent) = self.parent.get(&current) {
            if parent == current {
                break;
            }
            path.push(parent);
            current = parent;
        }

        path
    }

    /// Build proof for a path
    fn build_proof_path(&self, path: &[TermId]) -> Option<ProofStep> {
        if path.len() == 1 {
            return Some(ProofStep::Refl { term: path[0] });
        }

        let mut current_proof = self.proof_to_parent.get(&path[0])?.clone();

        for &term in path.iter().take(path.len() - 1).skip(1) {
            let next_proof = self.proof_to_parent.get(&term)?.clone();
            current_proof = ProofStep::Trans {
                left: Box::new(current_proof),
                right: Box::new(next_proof),
            };
        }

        Some(current_proof)
    }

    /// Reset the forest
    pub fn reset(&mut self) {
        self.parent.clear();
        self.proof_to_parent.clear();
        self.rank.clear();
    }
}

/// Conflict explanation
///
/// When a conflict is detected (e.g., a ≠ b asserted but a = b derived),
/// we need to explain why a = b.
#[derive(Debug, Clone)]
pub struct Conflict {
    /// The two terms that are equal but asserted to be disequal
    pub left: TermId,
    /// The right term in the conflict
    pub right: TermId,
    /// Proof of equality
    pub proof: ProofStep,
    /// Disequality reason
    pub diseq_reason: u32,
}

impl Conflict {
    /// Create a new conflict
    #[must_use]
    pub fn new(left: TermId, right: TermId, proof: ProofStep, diseq_reason: u32) -> Self {
        Self {
            left,
            right,
            proof,
            diseq_reason,
        }
    }

    /// Get all reasons involved in this conflict
    pub fn reasons(&self) -> Vec<u32> {
        let mut reasons = self.proof.reasons();
        reasons.push(self.diseq_reason);
        reasons
    }

    /// Get the conflict clause
    pub fn clause(&self) -> SmallVec<[u32; 8]> {
        let reasons = self.reasons();
        SmallVec::from_vec(reasons)
    }
}

impl fmt::Display for Conflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Conflict: {:?} != {:?} (diseq={}) but {:?} = {:?} (proof={})",
            self.left, self.right, self.diseq_reason, self.left, self.right, self.proof
        )
    }
}

/// Proof manager for EUF solver
#[derive(Debug)]
pub struct ProofManager {
    /// Proof forest
    forest: ProofForest,
    /// Conflicts detected
    conflicts: Vec<Conflict>,
}

impl Default for ProofManager {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofManager {
    /// Create a new proof manager
    #[must_use]
    pub fn new() -> Self {
        Self {
            forest: ProofForest::new(),
            conflicts: Vec::new(),
        }
    }

    /// Add a term
    pub fn add_term(&mut self, term: TermId) {
        self.forest.make(term);
    }

    /// Merge two terms with a proof
    pub fn merge(&mut self, a: TermId, b: TermId, proof: ProofStep) {
        self.forest.make(a);
        self.forest.make(b);
        self.forest.union(a, b, proof);
    }

    /// Check if two terms are equal
    #[must_use]
    pub fn are_equal(&self, a: TermId, b: TermId) -> bool {
        self.forest.find(a) == self.forest.find(b)
    }

    /// Explain why two terms are equal
    pub fn explain(&self, a: TermId, b: TermId) -> Option<ProofStep> {
        self.forest.explain(a, b)
    }

    /// Record a conflict
    pub fn add_conflict(&mut self, left: TermId, right: TermId, diseq_reason: u32) {
        if let Some(proof) = self.explain(left, right) {
            self.conflicts
                .push(Conflict::new(left, right, proof, diseq_reason));
        }
    }

    /// Get all conflicts
    #[must_use]
    pub fn conflicts(&self) -> &[Conflict] {
        &self.conflicts
    }

    /// Clear conflicts
    pub fn clear_conflicts(&mut self) {
        self.conflicts.clear();
    }

    /// Reset the manager
    pub fn reset(&mut self) {
        self.forest.reset();
        self.conflicts.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_reflexivity() {
        let a = TermId::new(1);
        let proof = ProofStep::Refl { term: a };

        assert_eq!(proof.terms(), (a, a));
        assert_eq!(proof.size(), 1);
    }

    #[test]
    fn test_proof_symmetry() {
        let a = TermId::new(1);
        let b = TermId::new(2);

        let given = ProofStep::Given {
            left: a,
            right: b,
            reason: 0,
        };

        let symm = ProofStep::Symm {
            proof: Box::new(given),
        };

        assert_eq!(symm.terms(), (b, a));
    }

    #[test]
    fn test_proof_transitivity() {
        let a = TermId::new(1);
        let b = TermId::new(2);
        let c = TermId::new(3);

        let ab = ProofStep::Given {
            left: a,
            right: b,
            reason: 0,
        };

        let bc = ProofStep::Given {
            left: b,
            right: c,
            reason: 1,
        };

        let trans = ProofStep::Trans {
            left: Box::new(ab),
            right: Box::new(bc),
        };

        assert_eq!(trans.terms(), (a, c));
        assert_eq!(trans.reasons(), vec![0, 1]);
    }

    #[test]
    fn test_proof_forest() {
        let mut forest = ProofForest::new();

        let a = TermId::new(1);
        let b = TermId::new(2);
        let c = TermId::new(3);

        forest.make(a);
        forest.make(b);
        forest.make(c);

        let proof_ab = ProofStep::Given {
            left: a,
            right: b,
            reason: 0,
        };

        let proof_bc = ProofStep::Given {
            left: b,
            right: c,
            reason: 1,
        };

        forest.union(a, b, proof_ab);
        forest.union(b, c, proof_bc);

        assert_eq!(forest.find(a), forest.find(c));
    }

    #[test]
    fn test_proof_manager() {
        let mut manager = ProofManager::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        manager.add_term(a);
        manager.add_term(b);

        assert!(!manager.are_equal(a, b));

        let proof = ProofStep::Given {
            left: a,
            right: b,
            reason: 0,
        };

        manager.merge(a, b, proof);

        assert!(manager.are_equal(a, b));
    }
}
