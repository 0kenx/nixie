//! Recursive CHC support and analysis.
//!
//! This module provides utilities for detecting and handling recursive
//! predicates in CHC systems, which are common in verification of
//! recursive functions and data structures.
//!
//! Reference: Z3's recursive predicate handling in Spacer

use crate::chc::{ChcSystem, PredId, Rule};
use std::collections::{HashMap, HashSet};
use thiserror::Error;
use tracing::{debug, trace};

/// Errors in recursive CHC analysis
#[derive(Error, Debug)]
pub enum RecursiveError {
    /// Invalid recursion pattern
    #[error("invalid recursion pattern: {0}")]
    InvalidPattern(String),
    /// Cyclic dependency detected
    #[error("cyclic dependency in non-recursive context")]
    CyclicDependency,
}

/// Type of recursion in a predicate
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecursionKind {
    /// Not recursive
    NonRecursive,
    /// Directly recursive (predicate appears in its own rules)
    DirectRecursive,
    /// Mutually recursive with other predicates
    MutuallyRecursive,
    /// Nested recursion (recursive calls within recursive calls)
    NestedRecursive,
}

/// Information about a recursive predicate
#[derive(Debug, Clone)]
pub struct RecursiveInfo {
    /// The predicate ID
    pub pred: PredId,
    /// Kind of recursion
    pub kind: RecursionKind,
    /// Predicates this one depends on
    pub dependencies: HashSet<PredId>,
    /// Predicates that depend on this one
    pub dependents: HashSet<PredId>,
    /// Recursive rules (rules that contain the predicate in both head and body)
    pub recursive_rules: Vec<usize>, // Rule indices
    /// Base case rules (non-recursive rules)
    pub base_rules: Vec<usize>,
}

impl RecursiveInfo {
    /// Create new recursive info
    pub fn new(pred: PredId) -> Self {
        Self {
            pred,
            kind: RecursionKind::NonRecursive,
            dependencies: HashSet::new(),
            dependents: HashSet::new(),
            recursive_rules: Vec::new(),
            base_rules: Vec::new(),
        }
    }

    /// Check if predicate is recursive
    pub fn is_recursive(&self) -> bool {
        self.kind != RecursionKind::NonRecursive
    }

    /// Check if predicate has base cases
    pub fn has_base_cases(&self) -> bool {
        !self.base_rules.is_empty()
    }

    /// Get recursion depth (number of predicates in mutual recursion)
    pub fn recursion_depth(&self) -> usize {
        match self.kind {
            RecursionKind::NonRecursive => 0,
            RecursionKind::DirectRecursive => 1,
            RecursionKind::MutuallyRecursive => self.dependencies.len(),
            RecursionKind::NestedRecursive => self.dependencies.len() + 1,
        }
    }
}

/// Analyzer for recursive CHC systems
pub struct RecursiveAnalyzer<'a> {
    /// The CHC system to analyze
    system: &'a ChcSystem,
    /// Recursive information for each predicate
    info: HashMap<PredId, RecursiveInfo>,
}

impl<'a> RecursiveAnalyzer<'a> {
    /// Create a new recursive analyzer
    pub fn new(system: &'a ChcSystem) -> Self {
        Self {
            system,
            info: HashMap::new(),
        }
    }

    /// Analyze the CHC system for recursion
    pub fn analyze(&mut self) -> Result<(), RecursiveError> {
        debug!("Analyzing CHC system for recursion");

        // Initialize info for all predicates
        for pred in self.system.predicates() {
            self.info.insert(pred.id, RecursiveInfo::new(pred.id));
        }

        // Build dependency graph
        self.build_dependency_graph()?;

        // Detect recursion kinds
        self.detect_recursion_kinds()?;

        // Classify rules
        self.classify_rules()?;

        debug!(
            "Found {} recursive predicates",
            self.info
                .values()
                .filter(|info| info.is_recursive())
                .count()
        );

        Ok(())
    }

    /// Build the dependency graph between predicates
    fn build_dependency_graph(&mut self) -> Result<(), RecursiveError> {
        for rule in self.system.rules() {
            if let Some(head_pred) = rule.head_predicate() {
                // Collect body predicates first
                let body_preds: Vec<PredId> =
                    rule.body.predicates.iter().map(|app| app.pred).collect();

                // Get or create info for head predicate
                let head_info = self
                    .info
                    .entry(head_pred)
                    .or_insert_with(|| RecursiveInfo::new(head_pred));

                // Add dependencies from body predicates
                for body_pred in &body_preds {
                    head_info.dependencies.insert(*body_pred);
                }

                // Now update body predicates (separate borrow)
                for body_pred in body_preds {
                    let body_info = self
                        .info
                        .entry(body_pred)
                        .or_insert_with(|| RecursiveInfo::new(body_pred));
                    body_info.dependents.insert(head_pred);
                }
            }
        }

        Ok(())
    }

    /// Detect recursion kinds for each predicate
    fn detect_recursion_kinds(&mut self) -> Result<(), RecursiveError> {
        // Clone the info to avoid borrow issues
        let pred_ids: Vec<PredId> = self.info.keys().copied().collect();

        for pred_id in pred_ids {
            let kind = self.detect_predicate_recursion(pred_id)?;

            if let Some(info) = self.info.get_mut(&pred_id) {
                info.kind = kind;
                trace!("Predicate {:?} has recursion kind {:?}", pred_id, kind);
            }
        }

        Ok(())
    }

    /// Detect recursion kind for a specific predicate
    fn detect_predicate_recursion(&self, pred: PredId) -> Result<RecursionKind, RecursiveError> {
        let info = self
            .info
            .get(&pred)
            .ok_or_else(|| RecursiveError::InvalidPattern("predicate not found".to_string()))?;

        // Check for direct recursion
        if info.dependencies.contains(&pred) {
            // Check for nested recursion (depends on other recursive predicates)
            let has_recursive_deps = info.dependencies.iter().any(|dep| {
                if let Some(dep_info) = self.info.get(dep) {
                    dep_info.dependencies.contains(&pred) || dep_info.dependencies.contains(dep)
                } else {
                    false
                }
            });

            if has_recursive_deps {
                return Ok(RecursionKind::NestedRecursive);
            } else {
                return Ok(RecursionKind::DirectRecursive);
            }
        }

        // Check for mutual recursion
        for dep in &info.dependencies {
            if let Some(dep_info) = self.info.get(dep)
                && dep_info.dependencies.contains(&pred)
            {
                return Ok(RecursionKind::MutuallyRecursive);
            }
        }

        Ok(RecursionKind::NonRecursive)
    }

    /// Classify rules as recursive or base cases
    fn classify_rules(&mut self) -> Result<(), RecursiveError> {
        for (rule_idx, rule) in self.system.rules().enumerate() {
            if let Some(head_pred) = rule.head_predicate() {
                let is_recursive = self.is_rule_recursive(rule);

                if let Some(info) = self.info.get_mut(&head_pred) {
                    if is_recursive {
                        info.recursive_rules.push(rule_idx);
                    } else {
                        info.base_rules.push(rule_idx);
                    }
                }
            }
        }

        Ok(())
    }

    /// Check if a rule is recursive
    fn is_rule_recursive(&self, rule: &Rule) -> bool {
        if let Some(head_pred) = rule.head_predicate() {
            // Check if head predicate appears in body
            rule.body
                .predicates
                .iter()
                .any(|body_app| body_app.pred == head_pred)
        } else {
            false
        }
    }

    /// Get recursive info for a predicate
    pub fn get_info(&self, pred: PredId) -> Option<&RecursiveInfo> {
        self.info.get(&pred)
    }

    /// Get all recursive predicates
    pub fn recursive_predicates(&self) -> impl Iterator<Item = &RecursiveInfo> {
        self.info.values().filter(|info| info.is_recursive())
    }

    /// Get strongly connected components (mutual recursion groups).
    ///
    /// Tarjan's algorithm, run iteratively over an explicit heap stack.
    ///
    /// Three defects in the previous version are fixed here:
    ///
    /// * **Unbounded recursion.** `strongconnect` recursed once per graph
    ///   edge followed, and the graph is the CHC predicate-dependency graph
    ///   whose size comes from the input file, so a long predicate chain
    ///   overflowed the stack. The procedure produced its result through a
    ///   `&mut Vec`, i.e. no error channel, so a depth cap could only have
    ///   returned silently wrong SCCs.
    /// * **Wrong lowlink.** The tree-edge case took `min` against the
    ///   successor's *index* instead of its *lowlink*, so a cycle closed
    ///   below a successor did not propagate upwards and mutually recursive
    ///   predicate groups were split apart. Spacer uses these groups to
    ///   decide which predicates need joint treatment, so mis-grouping is a
    ///   correctness bug, not just a performance one.
    /// * **`stack.contains(&dep)` linear scan** on every edge, making the
    ///   walk `O(V·E)`; membership is a hash set now.
    pub fn strongly_connected_components(&self) -> Vec<Vec<PredId>> {
        /// One suspended `strongconnect` activation.
        struct Frame {
            /// The node being explored.
            node: PredId,
            /// Its successors, in a stable order.
            successors: Vec<PredId>,
            /// How many successors have been consumed.
            next: usize,
            /// The node's Tarjan lowlink.
            lowlink: usize,
            /// The node's Tarjan index.
            index: usize,
        }

        /// What the current frame asks the driver loop to do next.
        enum Step {
            /// Start exploring this unvisited successor.
            Descend(PredId),
            /// Nothing to do; re-enter the loop.
            Continue,
            /// The current frame is exhausted.
            Finish,
        }

        let mut sccs: Vec<Vec<PredId>> = Vec::new();
        let mut indices: HashMap<PredId, usize> = HashMap::new();
        let mut counter: usize = 0;
        let mut scc_stack: Vec<PredId> = Vec::new();
        let mut on_stack: HashSet<PredId> = HashSet::new();

        let successors_of = |pred: PredId| -> Vec<PredId> {
            self.info
                .get(&pred)
                .map(|info| info.dependencies.iter().copied().collect())
                .unwrap_or_default()
        };

        let mut roots: Vec<PredId> = self.info.keys().copied().collect();
        roots.sort_unstable();

        for root in roots {
            if indices.contains_key(&root) {
                continue;
            }

            let mut frames: Vec<Frame> = vec![{
                indices.insert(root, counter);
                scc_stack.push(root);
                on_stack.insert(root);
                let frame = Frame {
                    node: root,
                    successors: successors_of(root),
                    next: 0,
                    lowlink: counter,
                    index: counter,
                };
                counter = counter.saturating_add(1);
                frame
            }];

            while !frames.is_empty() {
                let step = match frames.last_mut() {
                    Some(frame) => match frame.successors.get(frame.next).copied() {
                        Some(dep) => {
                            frame.next += 1;
                            match indices.get(&dep) {
                                Some(&dep_index) => {
                                    if on_stack.contains(&dep) {
                                        frame.lowlink = frame.lowlink.min(dep_index);
                                    }
                                    Step::Continue
                                }
                                None => Step::Descend(dep),
                            }
                        }
                        None => Step::Finish,
                    },
                    None => break,
                };

                match step {
                    Step::Continue => {}
                    Step::Descend(dep) => {
                        indices.insert(dep, counter);
                        scc_stack.push(dep);
                        on_stack.insert(dep);
                        frames.push(Frame {
                            node: dep,
                            successors: successors_of(dep),
                            next: 0,
                            lowlink: counter,
                            index: counter,
                        });
                        counter = counter.saturating_add(1);
                    }
                    Step::Finish => {
                        let Some(frame) = frames.pop() else {
                            break;
                        };

                        if frame.lowlink == frame.index {
                            let mut scc = Vec::new();
                            while let Some(node) = scc_stack.pop() {
                                on_stack.remove(&node);
                                scc.push(node);
                                if node == frame.node {
                                    break;
                                }
                            }
                            // Keep genuine mutual-recursion groups and
                            // self-recursive singletons only.
                            let keep = scc.len() > 1
                                || scc.first().is_some_and(|first| {
                                    self.info
                                        .get(first)
                                        .is_some_and(|i| i.dependencies.contains(first))
                                });
                            if keep {
                                sccs.push(scc);
                            }
                        }

                        // Returning from the recursive call propagated the
                        // callee's *lowlink* -- not its index -- upwards.
                        if let Some(parent) = frames.last_mut() {
                            parent.lowlink = parent.lowlink.min(frame.lowlink);
                        }
                    }
                }
            }
        }

        sccs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::TermManager;

    /// Stack size and chain length for the long-chain Tarjan test below.
    ///
    /// The two are scaled together on purpose: the DFS depth equals the chain
    /// length, so what the test actually pins is the *ratio* -- about
    /// 10 bytes of stack per graph node (128 KiB / 12_500). A natively
    /// recursive Tarjan needs far more than that per frame and still
    /// overflows, so the regression keeps every bit of its detection power.
    /// The pair used to be 1 MiB / 100_000 -- the same 10 bytes -- and was
    /// scaled down together with the rest of the crate's deep-nesting tests
    /// to keep the suite's peak memory in check. Never raise `DEEP_DEPTH`
    /// without raising `DEEP_STACK` by the same factor.
    const DEEP_STACK: usize = 1 << 17;
    const DEEP_DEPTH: u32 = 12_500;

    #[test]
    fn test_recursion_kind() {
        let info = RecursiveInfo::new(PredId(0));
        assert_eq!(info.kind, RecursionKind::NonRecursive);
        assert!(!info.is_recursive());
    }

    #[test]
    fn test_recursive_info() {
        let mut info = RecursiveInfo::new(PredId(0));
        info.kind = RecursionKind::DirectRecursive;
        info.dependencies.insert(PredId(0));
        info.recursive_rules.push(0);
        info.base_rules.push(1);

        assert!(info.is_recursive());
        assert!(info.has_base_cases());
        assert_eq!(info.recursion_depth(), 1);
    }

    #[test]
    fn test_analyzer_empty_system() {
        let system = ChcSystem::new();
        let mut analyzer = RecursiveAnalyzer::new(&system);
        assert!(analyzer.analyze().is_ok());
    }

    #[test]
    fn test_analyzer_simple_system() {
        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();

        // Create a simple non-recursive system
        let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);
        let x = terms.mk_var("x", terms.sorts.int_sort);
        let zero = terms.mk_int(0);
        let init_constraint = terms.mk_eq(x, zero);

        system.add_init_rule(
            [("x".to_string(), terms.sorts.int_sort)],
            init_constraint,
            inv,
            [x],
        );

        let mut analyzer = RecursiveAnalyzer::new(&system);
        assert!(analyzer.analyze().is_ok());

        // Check that predicate is non-recursive
        let info = analyzer.get_info(inv);
        assert!(info.is_some());
        let info = info.expect("test operation should succeed");
        assert_eq!(info.kind, RecursionKind::NonRecursive);
    }

    #[test]
    fn test_scc_computation() {
        let system = ChcSystem::new();
        let analyzer = RecursiveAnalyzer::new(&system);
        let sccs = analyzer.strongly_connected_components();
        assert!(sccs.is_empty());
    }

    /// Regression: the previous Tarjan took `min` against the successor's
    /// *index* rather than its *lowlink* on a tree edge, so the cycle closed
    /// at `c -> a` did not propagate up to `a` and the mutually recursive
    /// group `{a, b, c}` was split. All three predicates must land in one
    /// SCC.
    #[test]
    fn scc_groups_the_whole_cycle() {
        let system = ChcSystem::new();
        let mut analyzer = RecursiveAnalyzer::new(&system);
        let (a, b, c) = (PredId(0), PredId(1), PredId(2));
        for (pred, dep) in [(a, b), (b, c), (c, a)] {
            let entry = analyzer
                .info
                .entry(pred)
                .or_insert_with(|| RecursiveInfo::new(pred));
            entry.dependencies.insert(dep);
        }

        let sccs = analyzer.strongly_connected_components();
        assert_eq!(sccs.len(), 1, "the 3-cycle is a single SCC");
        let scc = &sccs[0];
        assert_eq!(scc.len(), 3, "all three predicates belong to it");
        assert!(scc.contains(&a) && scc.contains(&b) && scc.contains(&c));
    }

    /// A [`DEEP_DEPTH`]-long dependency chain must not overflow the stack.
    #[test]
    fn scc_survives_long_dependency_chain() {
        let handle = std::thread::Builder::new()
            .stack_size(DEEP_STACK)
            .spawn(|| {
                let system = ChcSystem::new();
                let mut analyzer = RecursiveAnalyzer::new(&system);
                for i in 0..DEEP_DEPTH {
                    let pred = PredId(i);
                    let entry = analyzer
                        .info
                        .entry(pred)
                        .or_insert_with(|| RecursiveInfo::new(pred));
                    entry.dependencies.insert(PredId(i + 1));
                }
                // No cycle and no self-loop, so nothing is reported.
                assert!(analyzer.strongly_connected_components().is_empty());
            })
            .expect("thread spawn should succeed");
        handle.join().expect("long-chain Tarjan must return");
    }
}
