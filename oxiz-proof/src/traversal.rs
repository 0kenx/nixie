//! Proof traversal and transformation utilities.
//!
//! This module provides various ways to traverse and transform proof trees,
//! including visitors, iterators, and transformation passes.

use crate::proof::{Proof, ProofNode, ProofNodeId, ProofStep};
use std::collections::{HashSet, VecDeque};

/// Visitor trait for proof tree traversal.
pub trait ProofVisitor {
    /// Visit a proof node.
    fn visit_node(&mut self, proof: &Proof, node: &ProofNode);

    /// Visit an axiom node.
    fn visit_axiom(&mut self, _proof: &Proof, _id: ProofNodeId, _conclusion: &str) {}

    /// Visit an inference node.
    fn visit_inference(
        &mut self,
        _proof: &Proof,
        _id: ProofNodeId,
        _rule: &str,
        _premises: &[ProofNodeId],
        _conclusion: &str,
    ) {
    }
}

/// Proof tree traversal order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraversalOrder {
    /// Pre-order: visit node before its children.
    PreOrder,
    /// Post-order: visit node after its children.
    PostOrder,
    /// Breadth-first: visit nodes level by level.
    BreadthFirst,
}

/// Traverse a proof tree with a visitor.
pub fn traverse<V: ProofVisitor>(proof: &Proof, visitor: &mut V, order: TraversalOrder) {
    if let Some(root) = proof.root() {
        let mut visited = HashSet::new();
        match order {
            TraversalOrder::PreOrder => traverse_pre_order(proof, root, visitor, &mut visited),
            TraversalOrder::PostOrder => traverse_post_order(proof, root, visitor, &mut visited),
            TraversalOrder::BreadthFirst => traverse_breadth_first(proof, visitor),
        }
    }
}

/// Work item for the explicit-stack depth-first walks below.
///
/// Proof DAGs produced by a solver are routinely 10^4-10^6 nodes deep, so every
/// depth-first walk in this module uses a heap stack rather than the call stack.
#[derive(Debug, Clone, Copy)]
enum DfsFrame {
    /// Node has not been expanded yet.
    Enter(ProofNodeId),
    /// All premises of the node have been processed.
    Exit(ProofNodeId),
}

/// Pre-order traversal (root, then children).
///
/// Iterative (explicit heap stack); semantics are identical to the natural
/// recursive formulation, including that a node is marked visited even when it
/// is not present in the proof.
fn traverse_pre_order<V: ProofVisitor>(
    proof: &Proof,
    node_id: ProofNodeId,
    visitor: &mut V,
    visited: &mut HashSet<ProofNodeId>,
) {
    let mut stack = vec![node_id];

    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }

        let Some(node) = proof.get_node(current) else {
            continue;
        };

        // Visit this node first
        visitor.visit_node(proof, node);

        match &node.step {
            ProofStep::Axiom { conclusion } => {
                visitor.visit_axiom(proof, current, conclusion);
            }
            ProofStep::Inference {
                rule,
                premises,
                conclusion,
                ..
            } => {
                visitor.visit_inference(proof, current, rule, premises, conclusion);

                // Then visit children, leftmost first (hence reversed pushes)
                stack.extend(premises.iter().rev().copied());
            }
        }
    }
}

/// Post-order traversal (children first, then root).
///
/// Iterative (explicit heap stack) with an `Enter`/`Exit` frame so the parent is
/// visited after all of its premises, exactly as the recursive formulation did.
fn traverse_post_order<V: ProofVisitor>(
    proof: &Proof,
    node_id: ProofNodeId,
    visitor: &mut V,
    visited: &mut HashSet<ProofNodeId>,
) {
    let mut stack = vec![DfsFrame::Enter(node_id)];

    while let Some(frame) = stack.pop() {
        match frame {
            DfsFrame::Enter(current) => {
                if !visited.insert(current) {
                    continue;
                }

                let Some(node) = proof.get_node(current) else {
                    continue;
                };

                stack.push(DfsFrame::Exit(current));

                // Visit children first
                if let ProofStep::Inference { premises, .. } = &node.step {
                    stack.extend(premises.iter().rev().copied().map(DfsFrame::Enter));
                }
            }
            DfsFrame::Exit(current) => {
                let Some(node) = proof.get_node(current) else {
                    continue;
                };

                // Then visit this node
                visitor.visit_node(proof, node);

                match &node.step {
                    ProofStep::Axiom { conclusion } => {
                        visitor.visit_axiom(proof, current, conclusion);
                    }
                    ProofStep::Inference {
                        rule,
                        premises,
                        conclusion,
                        ..
                    } => {
                        visitor.visit_inference(proof, current, rule, premises, conclusion);
                    }
                }
            }
        }
    }
}

/// Breadth-first traversal (level by level).
fn traverse_breadth_first<V: ProofVisitor>(proof: &Proof, visitor: &mut V) {
    if let Some(root) = proof.root() {
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();

        queue.push_back(root);
        visited.insert(root);

        while let Some(node_id) = queue.pop_front() {
            if let Some(node) = proof.get_node(node_id) {
                visitor.visit_node(proof, node);

                match &node.step {
                    ProofStep::Axiom { conclusion } => {
                        visitor.visit_axiom(proof, node_id, conclusion);
                    }
                    ProofStep::Inference {
                        rule,
                        premises,
                        conclusion,
                        ..
                    } => {
                        visitor.visit_inference(proof, node_id, rule, premises, conclusion);

                        for &premise in premises {
                            if !visited.contains(&premise) {
                                visited.insert(premise);
                                queue.push_back(premise);
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Collect all nodes in topological order (leaves first, root last).
#[must_use]
pub fn topological_order(proof: &Proof) -> Vec<ProofNodeId> {
    let mut order = Vec::new();
    if let Some(root) = proof.root() {
        let mut visited = HashSet::new();
        collect_topological(proof, root, &mut order, &mut visited);
    }
    order
}

/// Iterative post-order collection (explicit heap stack).
///
/// Note that, exactly as in the recursive formulation, a node that is not
/// present in the proof is still marked visited and still appended to `order`.
fn collect_topological(
    proof: &Proof,
    node_id: ProofNodeId,
    order: &mut Vec<ProofNodeId>,
    visited: &mut HashSet<ProofNodeId>,
) {
    let mut stack = vec![DfsFrame::Enter(node_id)];

    while let Some(frame) = stack.pop() {
        match frame {
            DfsFrame::Enter(current) => {
                if !visited.insert(current) {
                    continue;
                }

                stack.push(DfsFrame::Exit(current));

                if let Some(node) = proof.get_node(current)
                    && let ProofStep::Inference { premises, .. } = &node.step
                {
                    stack.extend(premises.iter().rev().copied().map(DfsFrame::Enter));
                }
            }
            DfsFrame::Exit(current) => order.push(current),
        }
    }
}

/// Find all root-to-leaf paths in the proof.
///
/// Only *simple* paths are enumerated: a node that already occurs on the current
/// path is not descended into again. On an acyclic proof (the documented shape —
/// see [`crate::validation`]) this is exactly "every root-to-axiom path"; on a
/// cyclic proof it terminates instead of looping forever.
///
/// The number of paths is the product of the premise counts along the DAG, so
/// this is inherently exponential in the proof size for a shared DAG. Prefer
/// [`topological_order`] unless every distinct path really is required.
#[must_use]
pub fn find_all_paths(proof: &Proof) -> Vec<Vec<ProofNodeId>> {
    let mut paths = Vec::new();
    if let Some(root) = proof.root() {
        let mut current_path = Vec::new();
        collect_paths(proof, root, &mut current_path, &mut paths);
    }
    paths
}

/// Frame for the iterative path enumeration.
#[derive(Debug, Clone, Copy)]
enum PathFrame {
    /// Extend the current path with this node.
    Enter(ProofNodeId),
    /// Drop the last node of the current path.
    Leave,
}

/// Iterative (explicit heap stack) enumeration of simple root-to-leaf paths.
fn collect_paths(
    proof: &Proof,
    node_id: ProofNodeId,
    current_path: &mut Vec<ProofNodeId>,
    all_paths: &mut Vec<Vec<ProofNodeId>>,
) {
    let mut stack = vec![PathFrame::Enter(node_id)];
    let mut on_path: HashSet<ProofNodeId> = HashSet::new();

    while let Some(frame) = stack.pop() {
        match frame {
            PathFrame::Enter(current) => {
                if !on_path.insert(current) {
                    // Cycle: the node is already on the current path.
                    continue;
                }
                current_path.push(current);
                stack.push(PathFrame::Leave);

                if let Some(node) = proof.get_node(current) {
                    match &node.step {
                        ProofStep::Axiom { .. } => {
                            // Reached a leaf - save the path
                            all_paths.push(current_path.clone());
                        }
                        ProofStep::Inference { premises, .. } => {
                            // Continue down each premise, leftmost first
                            stack.extend(premises.iter().rev().copied().map(PathFrame::Enter));
                        }
                    }
                }
            }
            PathFrame::Leave => {
                if let Some(popped) = current_path.pop() {
                    on_path.remove(&popped);
                }
            }
        }
    }
}

/// A visitor that counts nodes by type.

#[derive(Debug, Default)]
pub struct NodeCounter {
    /// Number of axiom nodes.
    pub axioms: usize,
    /// Number of inference nodes.
    pub inferences: usize,
}

impl ProofVisitor for NodeCounter {
    fn visit_node(&mut self, _proof: &Proof, node: &ProofNode) {
        match node.step {
            ProofStep::Axiom { .. } => self.axioms += 1,
            ProofStep::Inference { .. } => self.inferences += 1,
        }
    }
}

/// A visitor that collects all conclusions.

#[derive(Debug, Default)]
pub struct ConclusionCollector {
    /// All conclusions in the proof.
    pub conclusions: Vec<String>,
}

impl ProofVisitor for ConclusionCollector {
    fn visit_node(&mut self, _proof: &Proof, node: &ProofNode) {
        let conclusion = match &node.step {
            ProofStep::Axiom { conclusion } => conclusion.clone(),
            ProofStep::Inference { conclusion, .. } => conclusion.clone(),
        };
        self.conclusions.push(conclusion);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_node_counter() {
        let mut proof = Proof::new();
        let p1 = proof.add_axiom("p");
        let p2 = proof.add_axiom("q");
        let _p3 = proof.add_inference("and", vec![p1, p2], "(and p q)");

        let mut counter = NodeCounter::default();
        traverse(&proof, &mut counter, TraversalOrder::PreOrder);

        assert_eq!(counter.axioms, 2);
        assert_eq!(counter.inferences, 1);
    }

    #[test]
    fn test_conclusion_collector() {
        let mut proof = Proof::new();
        let p1 = proof.add_axiom("p");
        let p2 = proof.add_axiom("q");
        let _p3 = proof.add_inference("and", vec![p1, p2], "(and p q)");

        let mut collector = ConclusionCollector::default();
        traverse(&proof, &mut collector, TraversalOrder::PreOrder);

        assert_eq!(collector.conclusions.len(), 3);
        assert!(collector.conclusions.contains(&"p".to_string()));
        assert!(collector.conclusions.contains(&"q".to_string()));
        assert!(collector.conclusions.contains(&"(and p q)".to_string()));
    }

    #[test]
    fn test_topological_order() {
        let mut proof = Proof::new();
        let p1 = proof.add_axiom("p");
        let p2 = proof.add_axiom("q");
        let p3 = proof.add_inference("and", vec![p1, p2], "(and p q)");

        let order = topological_order(&proof);
        assert_eq!(order.len(), 3);

        // The root (p3) should come last in topological order
        assert_eq!(order[order.len() - 1], p3);
    }

    #[test]
    fn test_find_all_paths() {
        let mut proof = Proof::new();
        let p1 = proof.add_axiom("p");
        let p2 = proof.add_axiom("q");
        let _p3 = proof.add_inference("and", vec![p1, p2], "(and p q)");

        let paths = find_all_paths(&proof);
        assert_eq!(paths.len(), 2); // Two paths: one through p, one through q
    }

    #[test]
    fn test_traversal_orders() {
        let mut proof = Proof::new();
        let p1 = proof.add_axiom("p");
        let p2 = proof.add_axiom("q");
        let _p3 = proof.add_inference("and", vec![p1, p2], "(and p q)");

        // Test all traversal orders don't crash
        let mut counter = NodeCounter::default();
        traverse(&proof, &mut counter, TraversalOrder::PreOrder);
        assert_eq!(counter.axioms, 2);

        let mut counter = NodeCounter::default();
        traverse(&proof, &mut counter, TraversalOrder::PostOrder);
        assert_eq!(counter.axioms, 2);

        let mut counter = NodeCounter::default();
        traverse(&proof, &mut counter, TraversalOrder::BreadthFirst);
        assert_eq!(counter.axioms, 2);
    }
}
