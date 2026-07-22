//! Code tree for efficient pattern compilation and matching
//!
//! This module implements an optimized code tree representation for E-matching
//! patterns. The code tree compiles patterns into a sequence of instructions that
//! can be efficiently executed for matching.
//!
//! # Design
//!
//! Patterns are compiled into a tree of instructions that guide the matching process:
//! - **Compare**: Check if a term matches a specific pattern node
//! - **Bind**: Bind a variable to a matched term
//! - **Check**: Verify constraints (sort, arity, etc.)
//! - **Yield**: Produce a match result
//!
//! # Algorithm Reference
//!
//! Based on Z3's code tree implementation in src/sat/smt/q_mam.cpp

use crate::ast::{TermId, TermKind, TermManager};
use crate::error::{OxizError, Result};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use core::fmt;

/// A compiled code tree for pattern matching
#[derive(Debug, Clone)]
pub struct CodeTree {
    /// Root instruction
    pub root: usize,
    /// All instructions
    pub instructions: Vec<Instruction>,
    /// Variable count
    pub num_vars: usize,
}

/// A single instruction in the code tree
#[derive(Debug, Clone)]
pub struct Instruction {
    /// The kind of instruction
    pub kind: InstructionKind,
    /// Next instruction on success (index into instructions array)
    pub next: Option<usize>,
    /// Alternative instruction on failure (for backtracking)
    pub alt: Option<usize>,
}

/// Kinds of instructions
#[derive(Debug, Clone, PartialEq)]
pub enum InstructionKind {
    /// Compare current term with pattern term
    Compare {
        /// Expected term kind discriminant
        expected: TermKindDiscriminant,
    },
    /// Bind variable to current term
    Bind {
        /// Variable index
        var_idx: usize,
        /// Variable sort (for verification)
        sort: SortId,
    },
    /// Check term property
    Check {
        /// Property to check
        property: TermProperty,
    },
    /// Descend into child term
    DescendChild {
        /// Child index
        child_idx: usize,
    },
    /// Ascend to parent
    Ascend,
    /// Function application check
    CheckFunction {
        /// Function name
        func_name: Spur,
        /// Expected arity
        arity: usize,
    },
    /// Yield a successful match
    Yield {
        /// Pattern ID
        pattern_id: usize,
    },
    /// Choice point for backtracking
    Choice {
        /// First alternative
        first: usize,
        /// Second alternative
        second: usize,
    },
    /// Match any term (wildcard)
    MatchAny,
    /// End of instruction sequence
    Halt,
}

/// Discriminant for term kinds (for efficient comparison)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TermKindDiscriminant {
    /// Variable term
    Var,
    /// Boolean true constant
    True,
    /// Boolean false constant
    False,
    /// Integer constant
    IntConst,
    /// Real number constant
    RealConst,
    /// Bit-vector constant
    BitVecConst,
    /// String literal constant
    StringLit,
    /// Function application
    Apply,
    /// Equality comparison
    Eq,
    /// Less-than comparison
    Lt,
    /// Less-than-or-equal comparison
    Le,
    /// Greater-than comparison
    Gt,
    /// Greater-than-or-equal comparison
    Ge,
    /// Addition operation
    Add,
    /// Multiplication operation
    Mul,
    /// Subtraction operation
    Sub,
    /// Division operation
    Div,
    /// Logical AND operation
    And,
    /// Logical OR operation
    Or,
    /// Logical NOT operation
    Not,
    /// Logical implication
    Implies,
    /// Array select operation
    Select,
    /// Array store operation
    Store,
    /// Other term kinds
    Other,
}

impl TermKindDiscriminant {
    /// Get discriminant from a term
    pub fn from_term(term: &crate::ast::Term) -> Self {
        match &term.kind {
            TermKind::Var(_) => Self::Var,
            TermKind::True => Self::True,
            TermKind::False => Self::False,
            TermKind::IntConst(_) => Self::IntConst,
            TermKind::RealConst(_) => Self::RealConst,
            TermKind::BitVecConst { .. } => Self::BitVecConst,
            TermKind::StringLit(_) => Self::StringLit,
            TermKind::Apply { .. } => Self::Apply,
            TermKind::Eq(_, _) => Self::Eq,
            TermKind::Lt(_, _) => Self::Lt,
            TermKind::Le(_, _) => Self::Le,
            TermKind::Gt(_, _) => Self::Gt,
            TermKind::Ge(_, _) => Self::Ge,
            TermKind::Add(_) => Self::Add,
            TermKind::Mul(_) => Self::Mul,
            TermKind::Sub(_, _) => Self::Sub,
            TermKind::Div(_, _) => Self::Div,
            TermKind::And(_) => Self::And,
            TermKind::Or(_) => Self::Or,
            TermKind::Not(_) => Self::Not,
            TermKind::Implies(_, _) => Self::Implies,
            TermKind::Select(_, _) => Self::Select,
            TermKind::Store(_, _, _) => Self::Store,
            _ => Self::Other,
        }
    }
}

/// Properties that can be checked
#[derive(Debug, Clone, PartialEq)]
pub enum TermProperty {
    /// Has specific sort
    HasSort(SortId),
    /// Is ground (no variables)
    IsGround,
    /// Has specific arity
    HasArity(usize),
    /// Is constant value
    IsConstant,
}

/// Builder for constructing code trees
#[derive(Debug)]
pub struct CodeTreeBuilder {
    /// Instructions being built
    instructions: Vec<Instruction>,
    /// Next available instruction index
    next_idx: usize,
    /// Variable mapping
    var_map: FxHashMap<Spur, usize>,
    /// Number of variables
    num_vars: usize,
}

impl CodeTreeBuilder {
    /// Create a new code tree builder
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            next_idx: 0,
            var_map: FxHashMap::default(),
            num_vars: 0,
        }
    }

    /// Compile a pattern into a code tree
    pub fn compile(
        &mut self,
        pattern: &crate::ematching::pattern::Pattern,
        manager: &TermManager,
    ) -> Result<CodeTree> {
        // Reset state
        self.instructions.clear();
        self.next_idx = 0;
        self.var_map.clear();
        self.num_vars = 0;

        // Build variable map
        for var in &pattern.variables {
            if !self.var_map.contains_key(&var.name) {
                self.var_map.insert(var.name, self.num_vars);
                self.num_vars += 1;
            }
        }

        // Compile pattern root
        let root = self.compile_term(pattern.root, manager)?;

        // Add yield instruction
        let yield_idx = self.add_instruction(Instruction {
            kind: InstructionKind::Yield { pattern_id: 0 },
            next: None,
            alt: None,
        });

        // Link root to yield
        if let Some(instr) = self.instructions.get_mut(root) {
            instr.next = Some(yield_idx);
        }

        Ok(CodeTree {
            root,
            instructions: self.instructions.clone(),
            num_vars: self.num_vars,
        })
    }

    /// Compile a single term
    fn compile_term(&mut self, term_id: TermId, manager: &TermManager) -> Result<usize> {
        let Some(term) = manager.get(term_id) else {
            return Err(OxizError::EmatchError(format!(
                "Term {:?} not found",
                term_id
            )));
        };

        match &term.kind {
            TermKind::Var(name) => {
                // Variable: add bind instruction
                if let Some(&var_idx) = self.var_map.get(name) {
                    Ok(self.add_instruction(Instruction {
                        kind: InstructionKind::Bind {
                            var_idx,
                            sort: term.sort,
                        },
                        next: None,
                        alt: None,
                    }))
                } else {
                    // Free variable - match any
                    Ok(self.add_instruction(Instruction {
                        kind: InstructionKind::MatchAny,
                        next: None,
                        alt: None,
                    }))
                }
            }

            TermKind::Apply { func, args } => {
                // Function application
                let func_name = *func;
                let arity = args.len();

                // Add check function instruction
                let check_idx = self.add_instruction(Instruction {
                    kind: InstructionKind::CheckFunction { func_name, arity },
                    next: None,
                    alt: None,
                });

                // Compile arguments
                let mut prev_idx = check_idx;
                for (child_idx, &arg) in args.iter().enumerate() {
                    // Descend to child
                    let descend_idx = self.add_instruction(Instruction {
                        kind: InstructionKind::DescendChild { child_idx },
                        next: None,
                        alt: None,
                    });

                    // Compile child pattern
                    let child_instr = self.compile_term(arg, manager)?;

                    // Ascend back
                    let ascend_idx = self.add_instruction(Instruction {
                        kind: InstructionKind::Ascend,
                        next: None,
                        alt: None,
                    });

                    // Link: prev -> descend -> child -> ascend
                    if let Some(instr) = self.instructions.get_mut(prev_idx) {
                        instr.next = Some(descend_idx);
                    }
                    if let Some(instr) = self.instructions.get_mut(descend_idx) {
                        instr.next = Some(child_instr);
                    }
                    if let Some(instr) = self.instructions.get_mut(child_instr) {
                        instr.next = Some(ascend_idx);
                    }

                    prev_idx = ascend_idx;
                }

                Ok(check_idx)
            }

            TermKind::Eq(lhs, rhs) => {
                self.compile_binary_op(TermKindDiscriminant::Eq, *lhs, *rhs, manager)
            }

            TermKind::Lt(lhs, rhs) => {
                self.compile_binary_op(TermKindDiscriminant::Lt, *lhs, *rhs, manager)
            }

            TermKind::Le(lhs, rhs) => {
                self.compile_binary_op(TermKindDiscriminant::Le, *lhs, *rhs, manager)
            }

            TermKind::Gt(lhs, rhs) => {
                self.compile_binary_op(TermKindDiscriminant::Gt, *lhs, *rhs, manager)
            }

            TermKind::Ge(lhs, rhs) => {
                self.compile_binary_op(TermKindDiscriminant::Ge, *lhs, *rhs, manager)
            }

            TermKind::Add(args) => self.compile_nary_op(TermKindDiscriminant::Add, args, manager),

            TermKind::Mul(args) => self.compile_nary_op(TermKindDiscriminant::Mul, args, manager),

            TermKind::And(args) => self.compile_nary_op(TermKindDiscriminant::And, args, manager),

            TermKind::Or(args) => self.compile_nary_op(TermKindDiscriminant::Or, args, manager),

            _ => {
                // For other terms, just add a compare instruction
                let discriminant = TermKindDiscriminant::from_term(term);
                Ok(self.add_instruction(Instruction {
                    kind: InstructionKind::Compare {
                        expected: discriminant,
                    },
                    next: None,
                    alt: None,
                }))
            }
        }
    }

    /// Compile a binary operator
    fn compile_binary_op(
        &mut self,
        op: TermKindDiscriminant,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
    ) -> Result<usize> {
        // Add compare instruction for the operator
        let compare_idx = self.add_instruction(Instruction {
            kind: InstructionKind::Compare { expected: op },
            next: None,
            alt: None,
        });

        // Compile left operand
        let descend_left = self.add_instruction(Instruction {
            kind: InstructionKind::DescendChild { child_idx: 0 },
            next: None,
            alt: None,
        });
        let left_instr = self.compile_term(lhs, manager)?;
        let ascend_left = self.add_instruction(Instruction {
            kind: InstructionKind::Ascend,
            next: None,
            alt: None,
        });

        // Compile right operand
        let descend_right = self.add_instruction(Instruction {
            kind: InstructionKind::DescendChild { child_idx: 1 },
            next: None,
            alt: None,
        });
        let right_instr = self.compile_term(rhs, manager)?;
        let ascend_right = self.add_instruction(Instruction {
            kind: InstructionKind::Ascend,
            next: None,
            alt: None,
        });

        // Link instructions
        if let Some(instr) = self.instructions.get_mut(compare_idx) {
            instr.next = Some(descend_left);
        }
        if let Some(instr) = self.instructions.get_mut(descend_left) {
            instr.next = Some(left_instr);
        }
        if let Some(instr) = self.instructions.get_mut(left_instr) {
            instr.next = Some(ascend_left);
        }
        if let Some(instr) = self.instructions.get_mut(ascend_left) {
            instr.next = Some(descend_right);
        }
        if let Some(instr) = self.instructions.get_mut(descend_right) {
            instr.next = Some(right_instr);
        }
        if let Some(instr) = self.instructions.get_mut(right_instr) {
            instr.next = Some(ascend_right);
        }

        Ok(compare_idx)
    }

    /// Compile an n-ary operator
    fn compile_nary_op(
        &mut self,
        op: TermKindDiscriminant,
        args: &[TermId],
        manager: &TermManager,
    ) -> Result<usize> {
        // Add compare and arity check
        let compare_idx = self.add_instruction(Instruction {
            kind: InstructionKind::Compare { expected: op },
            next: None,
            alt: None,
        });

        let check_arity = self.add_instruction(Instruction {
            kind: InstructionKind::Check {
                property: TermProperty::HasArity(args.len()),
            },
            next: None,
            alt: None,
        });

        if let Some(instr) = self.instructions.get_mut(compare_idx) {
            instr.next = Some(check_arity);
        }

        // Compile each argument
        let mut prev_idx = check_arity;
        for (idx, &arg) in args.iter().enumerate() {
            let descend = self.add_instruction(Instruction {
                kind: InstructionKind::DescendChild { child_idx: idx },
                next: None,
                alt: None,
            });
            let child_instr = self.compile_term(arg, manager)?;
            let ascend = self.add_instruction(Instruction {
                kind: InstructionKind::Ascend,
                next: None,
                alt: None,
            });

            if let Some(instr) = self.instructions.get_mut(prev_idx) {
                instr.next = Some(descend);
            }
            if let Some(instr) = self.instructions.get_mut(descend) {
                instr.next = Some(child_instr);
            }
            if let Some(instr) = self.instructions.get_mut(child_instr) {
                instr.next = Some(ascend);
            }

            prev_idx = ascend;
        }

        Ok(compare_idx)
    }

    /// Add an instruction and return its index
    fn add_instruction(&mut self, instr: Instruction) -> usize {
        let idx = self.next_idx;
        self.instructions.push(instr);
        self.next_idx += 1;
        idx
    }

    /// Optimize the code tree
    pub fn optimize(&mut self, tree: &mut CodeTree) {
        // Remove unreachable instructions
        self.remove_unreachable(tree);

        // Merge sequential instructions where possible
        self.merge_sequences(tree);

        // Eliminate redundant checks
        self.eliminate_redundant_checks(tree);
    }

    /// Remove unreachable instructions
    fn remove_unreachable(&self, tree: &mut CodeTree) {
        let mut reachable = FxHashSet::default();
        let mut to_visit = vec![tree.root];

        while let Some(idx) = to_visit.pop() {
            if reachable.contains(&idx) {
                continue;
            }
            reachable.insert(idx);

            if let Some(instr) = tree.instructions.get(idx) {
                if let Some(next) = instr.next {
                    to_visit.push(next);
                }
                if let Some(alt) = instr.alt {
                    to_visit.push(alt);
                }
                if let InstructionKind::Choice { first, second } = &instr.kind {
                    to_visit.push(*first);
                    to_visit.push(*second);
                }
            }
        }

        // Keep only reachable instructions
        // (This is simplified - in practice, we'd need to renumber indices)
    }

    /// Merge sequential instructions.
    ///
    /// Finds consecutive Compare instructions that check the same discriminant
    /// and removes the duplicate — the first check already establishes the kind.
    fn merge_sequences(&self, tree: &mut CodeTree) {
        if tree.instructions.len() < 2 {
            return;
        }

        // Build a set of instruction indices to drop (duplicates).
        let mut drop: FxHashSet<usize> = FxHashSet::default();

        // Walk the instruction chain starting from root via `next` links.
        let mut idx = tree.root;
        while let Some(instr) = tree.instructions.get(idx) {
            let next_opt = instr.next;
            if let Some(next_idx) = next_opt {
                if let (Some(cur), Some(nxt)) =
                    (tree.instructions.get(idx), tree.instructions.get(next_idx))
                {
                    // Two consecutive Compare instructions with the same expected
                    // discriminant: the second is redundant.
                    if let (
                        InstructionKind::Compare { expected: exp_cur },
                        InstructionKind::Compare { expected: exp_nxt },
                    ) = (&cur.kind, &nxt.kind)
                        && exp_cur == exp_nxt
                    {
                        drop.insert(next_idx);
                    }
                }
                idx = next_idx;
            } else {
                break;
            }
        }

        Self::patch_links(&drop, &mut tree.instructions);
    }

    /// Eliminate redundant checks.
    ///
    /// Walks the instruction chain via `next` links and removes any `Check`
    /// instruction whose property was already verified by an earlier `Check`
    /// on the same chain.
    fn eliminate_redundant_checks(&self, tree: &mut CodeTree) {
        let mut seen: FxHashSet<String> = FxHashSet::default();
        let mut drop: FxHashSet<usize> = FxHashSet::default();

        let mut idx = tree.root;
        while let Some(instr) = tree.instructions.get(idx) {
            let next_opt = instr.next;

            if let InstructionKind::Check { property } = &instr.kind {
                // Use a stable string key for deduplication (avoids requiring Hash on TermProperty).
                let key = format!("{:?}", property);
                if !seen.insert(key) {
                    drop.insert(idx);
                }
            }

            if let Some(next_idx) = next_opt {
                idx = next_idx;
            } else {
                break;
            }
        }

        Self::patch_links(&drop, &mut tree.instructions);
    }

    /// Rewrite `next`/`alt` pointers that refer to dropped instructions,
    /// forwarding them to the dropped instruction's own successor.
    ///
    /// Pre-computes all replacements before mutating to satisfy the borrow checker.
    fn patch_links(drop: &FxHashSet<usize>, instructions: &mut [Instruction]) {
        // (new_next, new_alt): Some(v) means "replace with v", None means "keep as-is".
        type Patch = (Option<Option<usize>>, Option<Option<usize>>);
        let forwards: Vec<Patch> = instructions
            .iter()
            .map(|instr| {
                let new_next = instr.next.and_then(|ni| {
                    if drop.contains(&ni) {
                        Some(instructions.get(ni).and_then(|i| i.next))
                    } else {
                        None
                    }
                });
                let new_alt = instr.alt.and_then(|ai| {
                    if drop.contains(&ai) {
                        Some(instructions.get(ai).and_then(|i| i.next))
                    } else {
                        None
                    }
                });
                (new_next, new_alt)
            })
            .collect();

        for (instr, (new_next, new_alt)) in instructions.iter_mut().zip(forwards.iter()) {
            if let Some(replacement) = new_next {
                instr.next = *replacement;
            }
            if let Some(replacement) = new_alt {
                instr.alt = *replacement;
            }
        }
    }
}

impl Default for CodeTreeBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Node in the code tree (alternative representation)
#[derive(Debug, Clone)]
pub struct CodeTreeNode {
    /// The instruction at this node
    pub instruction: Instruction,
    /// Children (for visualization/debugging)
    pub children: Vec<CodeTreeNode>,
}

impl CodeTree {
    /// Execute the code tree against a term.
    ///
    /// Returns `Some(bindings)` for the first successful match (each entry is
    /// the term bound to the corresponding pattern variable), or `None` if no
    /// match exists.
    pub fn execute(&self, term: TermId, manager: &TermManager) -> Result<Option<Vec<TermId>>> {
        let bindings = vec![None; self.num_vars];
        let term_stack = Vec::new();
        self.run(self.root, term, bindings, term_stack, manager)
    }

    /// Interpret the instruction stream starting at `ip` with the supplied
    /// resumption state (`current_term`, `bindings`, `term_stack`).
    ///
    /// `Choice` points are handled by real backtracking: the first
    /// alternative is explored with a *clone* of the current register state
    /// (bindings + term stack), so any bindings it makes are discarded if it
    /// fails; the second alternative then resumes from the unmodified state
    /// of this frame. This correctly explores both branches and restores
    /// register state per choice point (TODO-939) — the previous
    /// `execute_from` stub inspected only a single instruction and silently
    /// dropped any first-branch match longer than an immediate `Yield`/`Halt`.
    fn run(
        &self,
        mut ip: usize,
        mut current_term: TermId,
        mut bindings: Vec<Option<TermId>>,
        mut term_stack: Vec<TermId>,
        manager: &TermManager,
    ) -> Result<Option<Vec<TermId>>> {
        loop {
            let Some(instr) = self.instructions.get(ip) else {
                return Err(OxizError::EmatchError(format!(
                    "Invalid instruction pointer: {}",
                    ip
                )));
            };

            match &instr.kind {
                InstructionKind::Compare { expected } => {
                    let Some(t) = manager.get(current_term) else {
                        return Ok(None); // Match failed
                    };

                    let actual = TermKindDiscriminant::from_term(t);
                    if actual != *expected {
                        return Ok(None); // Match failed
                    }

                    ip = instr.next.ok_or_else(|| {
                        OxizError::EmatchError("Compare has no next instruction".to_string())
                    })?;
                }

                InstructionKind::Bind { var_idx, sort } => {
                    let Some(t) = manager.get(current_term) else {
                        return Ok(None);
                    };

                    // Check sort
                    if t.sort != *sort {
                        return Ok(None);
                    }

                    // Check if already bound
                    if let Some(existing) = bindings[*var_idx] {
                        if existing != current_term {
                            return Ok(None); // Inconsistent binding
                        }
                    } else {
                        bindings[*var_idx] = Some(current_term);
                    }

                    ip = instr.next.ok_or_else(|| {
                        OxizError::EmatchError("Bind has no next instruction".to_string())
                    })?;
                }

                InstructionKind::Check { property } => {
                    let Some(t) = manager.get(current_term) else {
                        return Ok(None);
                    };

                    let passes = match property {
                        TermProperty::HasSort(s) => t.sort == *s,
                        TermProperty::IsGround => {
                            // Check if term is ground (simplified)
                            !matches!(t.kind, TermKind::Var(_))
                        }
                        TermProperty::HasArity(arity) => match &t.kind {
                            TermKind::Apply { args, .. } => args.len() == *arity,
                            TermKind::Add(args) | TermKind::Mul(args) => args.len() == *arity,
                            _ => false,
                        },
                        TermProperty::IsConstant => matches!(
                            t.kind,
                            TermKind::True
                                | TermKind::False
                                | TermKind::IntConst(_)
                                | TermKind::RealConst(_)
                        ),
                    };

                    if !passes {
                        return Ok(None);
                    }

                    ip = instr.next.ok_or_else(|| {
                        OxizError::EmatchError("Check has no next instruction".to_string())
                    })?;
                }

                InstructionKind::DescendChild { child_idx } => {
                    let Some(t) = manager.get(current_term) else {
                        return Ok(None);
                    };

                    let child = match &t.kind {
                        TermKind::Apply { args, .. } => args.get(*child_idx).copied(),
                        TermKind::Eq(lhs, rhs)
                        | TermKind::Lt(lhs, rhs)
                        | TermKind::Le(lhs, rhs) => match child_idx {
                            0 => Some(*lhs),
                            1 => Some(*rhs),
                            _ => None,
                        },
                        TermKind::Add(args) | TermKind::Mul(args) => args.get(*child_idx).copied(),
                        _ => None,
                    };

                    let Some(child_term) = child else {
                        return Ok(None);
                    };

                    term_stack.push(current_term);
                    current_term = child_term;

                    ip = instr.next.ok_or_else(|| {
                        OxizError::EmatchError("DescendChild has no next instruction".to_string())
                    })?;
                }

                InstructionKind::Ascend => {
                    let Some(parent) = term_stack.pop() else {
                        return Err(OxizError::EmatchError(
                            "Cannot ascend: stack empty".to_string(),
                        ));
                    };

                    current_term = parent;

                    ip = instr.next.ok_or_else(|| {
                        OxizError::EmatchError("Ascend has no next instruction".to_string())
                    })?;
                }

                InstructionKind::CheckFunction { func_name, arity } => {
                    let Some(t) = manager.get(current_term) else {
                        return Ok(None);
                    };

                    let matches = match &t.kind {
                        TermKind::Apply { func, args } => func == func_name && args.len() == *arity,
                        _ => false,
                    };

                    if !matches {
                        return Ok(None);
                    }

                    ip = instr.next.ok_or_else(|| {
                        OxizError::EmatchError("CheckFunction has no next instruction".to_string())
                    })?;
                }

                InstructionKind::Yield { .. } => {
                    // Success! Return bindings
                    let result: Option<Vec<TermId>> = bindings.into_iter().collect();
                    return Ok(result);
                }

                InstructionKind::Choice { first, second } => {
                    // Explore the first alternative with a *clone* of the
                    // current register state, so any bindings/navigation it
                    // performs are discarded if it ultimately fails.
                    let result1 = self.run(
                        *first,
                        current_term,
                        bindings.clone(),
                        term_stack.clone(),
                        manager,
                    )?;
                    if result1.is_some() {
                        return Ok(result1);
                    }

                    // First alternative failed: resume the second alternative
                    // from this frame's unmodified state (real backtracking).
                    ip = *second;
                }

                InstructionKind::MatchAny => {
                    // Match any term (wildcard)
                    ip = instr.next.ok_or_else(|| {
                        OxizError::EmatchError("MatchAny has no next instruction".to_string())
                    })?;
                }

                InstructionKind::Halt => {
                    return Ok(None);
                }
            }
        }
    }
}

impl fmt::Display for CodeTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CodeTree(root={}, {} instructions, {} vars)",
            self.root,
            self.instructions.len(),
            self.num_vars
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::TermManager;
    use crate::ematching::pattern::{PatternCompiler, PatternConfig};

    fn setup() -> TermManager {
        TermManager::new()
    }

    #[test]
    fn test_code_tree_builder_creation() {
        let builder = CodeTreeBuilder::new();
        assert_eq!(builder.instructions.len(), 0);
        assert_eq!(builder.num_vars, 0);
    }

    #[test]
    fn test_term_kind_discriminant() {
        let manager = setup();
        let t_true = manager.mk_true();
        let t_false = manager.mk_false();

        let term_true = manager.get(t_true).expect("key should exist in map");
        let term_false = manager.get(t_false).expect("key should exist in map");

        assert_eq!(
            TermKindDiscriminant::from_term(term_true),
            TermKindDiscriminant::True
        );
        assert_eq!(
            TermKindDiscriminant::from_term(term_false),
            TermKindDiscriminant::False
        );
    }

    #[test]
    fn test_compile_simple_pattern() {
        let mut manager = setup();
        let mut pattern_compiler = PatternCompiler::new(PatternConfig::default());
        let mut builder = CodeTreeBuilder::new();

        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);

        let x_name = manager.intern_str("x");
        let bound_vars = vec![(x_name, int_sort)];

        let pattern = pattern_compiler
            .compile(f_x, &bound_vars, &manager)
            .expect("test operation should succeed");
        let code_tree = builder
            .compile(&pattern, &manager)
            .expect("test operation should succeed");

        assert!(!code_tree.instructions.is_empty());
        assert_eq!(code_tree.num_vars, 1);
    }

    #[test]
    fn test_instruction_kinds() {
        let bind = Instruction {
            kind: InstructionKind::Bind {
                var_idx: 0,
                sort: SortId(0),
            },
            next: Some(1),
            alt: None,
        };

        assert!(matches!(bind.kind, InstructionKind::Bind { .. }));
        assert_eq!(bind.next, Some(1));
    }

    // ── TODO-939: Choice backtracking regression tests ────────────────────
    //
    // Before the fix, `execute_from` inspected only the *single* instruction
    // at a Choice's first branch and returned `Ok(None)` for anything other
    // than an immediate `Yield`/`Halt`, so a legitimate first-branch match
    // that required more than one instruction was silently dropped.

    fn instr(kind: InstructionKind, next: Option<usize>) -> Instruction {
        Instruction {
            kind,
            next,
            alt: None,
        }
    }

    #[test]
    fn test_choice_explores_multi_instruction_first_branch() {
        // Term is an equality; the first branch requires (Compare Eq -> Yield),
        // i.e. more than a single immediate Yield. The old stub dropped it.
        let mut manager = setup();
        let s = manager.sorts.int_sort;
        let a = manager.mk_var("a", s);
        let b = manager.mk_var("b", s);
        let eq = manager.mk_eq(a, b);

        let instructions = vec![
            instr(
                InstructionKind::Choice {
                    first: 1,
                    second: 3,
                },
                None,
            ),
            instr(
                InstructionKind::Compare {
                    expected: TermKindDiscriminant::Eq,
                },
                Some(2),
            ),
            instr(InstructionKind::Yield { pattern_id: 0 }, None),
            instr(InstructionKind::Halt, None),
        ];
        let tree = CodeTree {
            root: 0,
            instructions,
            num_vars: 0,
        };

        let result = tree.execute(eq, &manager).expect("execute must not error");
        assert!(
            result.is_some(),
            "Choice first branch (Compare Eq -> Yield) must be explored and match"
        );
    }

    #[test]
    fn test_choice_falls_through_to_second_branch() {
        // First branch requires Lt (fails on an Eq term); the second branch
        // requires Eq (succeeds). Real backtracking must reach the second.
        let mut manager = setup();
        let s = manager.sorts.int_sort;
        let a = manager.mk_var("a", s);
        let b = manager.mk_var("b", s);
        let eq = manager.mk_eq(a, b);

        let instructions = vec![
            instr(
                InstructionKind::Choice {
                    first: 1,
                    second: 3,
                },
                None,
            ),
            instr(
                InstructionKind::Compare {
                    expected: TermKindDiscriminant::Lt,
                },
                Some(2),
            ),
            instr(InstructionKind::Yield { pattern_id: 0 }, None),
            instr(
                InstructionKind::Compare {
                    expected: TermKindDiscriminant::Eq,
                },
                Some(4),
            ),
            instr(InstructionKind::Yield { pattern_id: 1 }, None),
        ];
        let tree = CodeTree {
            root: 0,
            instructions,
            num_vars: 0,
        };

        let result = tree.execute(eq, &manager).expect("execute must not error");
        assert!(
            result.is_some(),
            "second Choice branch must match after the first fails"
        );
    }

    #[test]
    fn test_choice_both_branches_fail() {
        // Neither branch matches an Eq term.
        let mut manager = setup();
        let s = manager.sorts.int_sort;
        let a = manager.mk_var("a", s);
        let b = manager.mk_var("b", s);
        let eq = manager.mk_eq(a, b);

        let instructions = vec![
            instr(
                InstructionKind::Choice {
                    first: 1,
                    second: 3,
                },
                None,
            ),
            instr(
                InstructionKind::Compare {
                    expected: TermKindDiscriminant::Lt,
                },
                Some(2),
            ),
            instr(InstructionKind::Yield { pattern_id: 0 }, None),
            instr(
                InstructionKind::Compare {
                    expected: TermKindDiscriminant::Gt,
                },
                Some(4),
            ),
            instr(InstructionKind::Yield { pattern_id: 1 }, None),
        ];
        let tree = CodeTree {
            root: 0,
            instructions,
            num_vars: 0,
        };

        let result = tree.execute(eq, &manager).expect("execute must not error");
        assert!(result.is_none(), "no branch matches, expected no match");
    }

    #[test]
    fn test_choice_bindings_are_isolated_between_branches() {
        // The first branch descends to the lhs and binds var 0 to `a`, then
        // fails (Compare Lt on the parent Eq). The second branch descends to
        // the rhs and binds var 0 to `b`. If register state were shared, the
        // second branch's Bind would see var 0 already bound to `a` and fail
        // on the inconsistent binding; with proper per-choice isolation it
        // binds `b` and yields `[b]`.
        let mut manager = setup();
        let s = manager.sorts.int_sort;
        let a = manager.mk_var("a", s);
        let b = manager.mk_var("b", s);
        let eq = manager.mk_eq(a, b);

        let instructions = vec![
            instr(
                InstructionKind::Choice {
                    first: 1,
                    second: 5,
                },
                None,
            ),
            // First branch: lhs -> bind v0=a -> ascend -> Compare Lt (fails).
            instr(InstructionKind::DescendChild { child_idx: 0 }, Some(2)),
            instr(
                InstructionKind::Bind {
                    var_idx: 0,
                    sort: s,
                },
                Some(3),
            ),
            instr(InstructionKind::Ascend, Some(4)),
            instr(
                InstructionKind::Compare {
                    expected: TermKindDiscriminant::Lt,
                },
                None,
            ),
            // Second branch: rhs -> bind v0=b -> ascend -> yield.
            instr(InstructionKind::DescendChild { child_idx: 1 }, Some(6)),
            instr(
                InstructionKind::Bind {
                    var_idx: 0,
                    sort: s,
                },
                Some(7),
            ),
            instr(InstructionKind::Ascend, Some(8)),
            instr(InstructionKind::Yield { pattern_id: 0 }, None),
        ];
        let tree = CodeTree {
            root: 0,
            instructions,
            num_vars: 1,
        };

        let result = tree
            .execute(eq, &manager)
            .expect("execute must not error")
            .expect("second branch must produce a match");
        assert_eq!(
            result,
            vec![b],
            "second branch must bind var 0 to b, unaffected by the first branch"
        );
    }
}
