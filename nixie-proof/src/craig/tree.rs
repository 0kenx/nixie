//! Tree interpolation for hierarchical formulas.

use super::config::{InterpolationAlgorithm, InterpolationConfig};
use super::error::InterpolationError;
use super::term::InterpolantTerm;
use rustc_hash::{FxHashMap, FxHashSet};

/// Tree interpolation for hierarchical formulas
///
/// Given a tree of formulas where leaves are UNSAT,
/// compute interpolants for internal nodes
#[derive(Debug)]
pub struct TreeInterpolator {
    config: InterpolationConfig,
}

/// Tree node for tree interpolation
#[derive(Debug, Clone)]
pub struct TreeNode {
    /// Node ID
    pub id: usize,
    /// Formula at this node (as term)
    pub formula: InterpolantTerm,
    /// Children node IDs
    pub children: Vec<usize>,
    /// Parent node ID (None for root)
    pub parent: Option<usize>,
}

impl TreeInterpolator {
    /// Create a new tree interpolator
    #[must_use]
    pub fn new(config: InterpolationConfig) -> Self {
        Self { config }
    }

    /// Compute tree interpolants
    ///
    /// Returns an interpolant for each non-leaf node
    pub fn interpolate_tree(
        &self,
        nodes: &[TreeNode],
    ) -> Result<FxHashMap<usize, InterpolantTerm>, InterpolationError> {
        let mut interpolants = FxHashMap::default();

        // Process nodes bottom-up (leaves first)
        let mut order = self.topological_order(nodes);
        order.reverse();

        for node_id in order {
            if let Some(node) = nodes.get(node_id) {
                if node.children.is_empty() {
                    // Leaf: interpolant is the formula itself
                    interpolants.insert(node_id, node.formula.clone());
                } else {
                    // Internal node: combine children interpolants
                    let child_interps: Vec<_> = node
                        .children
                        .iter()
                        .filter_map(|&c| interpolants.get(&c).cloned())
                        .collect();

                    let combined = if self.config.algorithm == InterpolationAlgorithm::McMillan {
                        InterpolantTerm::or(child_interps)
                    } else {
                        InterpolantTerm::and(child_interps)
                    };

                    let interp = InterpolantTerm::and(vec![node.formula.clone(), combined]);
                    interpolants.insert(node_id, interp.simplify());
                }
            }
        }

        Ok(interpolants)
    }

    /// Topological order of nodes (parents before children)
    fn topological_order(&self, nodes: &[TreeNode]) -> Vec<usize> {
        let mut order = Vec::new();
        let mut visited = FxHashSet::default();

        fn visit(
            node_id: usize,
            nodes: &[TreeNode],
            visited: &mut FxHashSet<usize>,
            order: &mut Vec<usize>,
        ) {
            if visited.contains(&node_id) {
                return;
            }
            visited.insert(node_id);

            if let Some(node) = nodes.get(node_id) {
                for &child in &node.children {
                    visit(child, nodes, visited, order);
                }
            }
            order.push(node_id);
        }

        // Find roots (nodes with no parent)
        for (i, node) in nodes.iter().enumerate() {
            if node.parent.is_none() {
                visit(i, nodes, &mut visited, &mut order);
            }
        }

        order
    }
}

impl Default for TreeInterpolator {
    fn default() -> Self {
        Self::new(InterpolationConfig::default())
    }
}
