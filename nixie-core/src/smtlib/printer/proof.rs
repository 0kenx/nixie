//! Proof printing functionality
//!
//! [`Printer::write_proof_node`] walks the proof iteratively -- an explicit
//! `(ProofId, indent)` stack, never native recursion -- and prints each node
//! at most once even though a [`Proof`] is a DAG, not a tree. See that
//! method's doc comment for why both of those matter.

use crate::ast::{proof::Proof, proof::ProofRule};
#[allow(unused_imports)]
use crate::prelude::*;
use core::fmt::Write;

use super::basic::Printer;
use super::format_string_literal;

impl<'a> Printer<'a> {
    /// Print a proof in SMT-LIB2 format
    pub fn print_proof(&self, proof: &Proof) -> String {
        let mut buf = String::new();
        self.write_proof(&mut buf, proof);
        buf
    }

    /// Write a proof in SMT-LIB2 format
    ///
    /// This outputs the proof as a DAG of inference steps in a readable format.
    pub fn write_proof(&self, w: &mut impl Write, proof: &Proof) {
        let _ = writeln!(w, "(proof");

        // Get the root node and iteratively write the proof DAG.
        let root_id = proof.root();
        self.write_proof_node(w, proof, root_id, 1);

        let _ = writeln!(w, ")");
    }

    /// Write a proof node and, transitively, every node reachable from it
    /// through `:premises`.
    ///
    /// **Iterative.** An explicit `(ProofId, indent)` stack stands in for the
    /// native call stack, so this function's native stack usage is constant
    /// regardless of how deep the proof is. [`Proof::add_node`] places no
    /// bound on how many steps a caller chains together through
    /// [`ProofNode::premises`](crate::ast::proof::ProofNode::premises), so an
    /// embedder assembling a large synthesized or replayed proof could hand
    /// this a chain deep enough to overflow a worker thread's native stack --
    /// a fatal process abort, not a catchable error -- under the old
    /// recursive version.
    ///
    /// **Deduplicating.** A [`Proof`] is a DAG, not a tree: the same node can
    /// be a premise of more than one other node (a shared lemma reused at
    /// several resolution steps, for instance). The old recursive version
    /// re-wrote a shared node's entire subtree once per parent that reaches
    /// it, which is exponential in the depth of the sharing; independent of
    /// that cost, it also emitted more than one `(step @pN ...)` declaration
    /// for the same `@pN`, which is already malformed relative to this
    /// format's own contract -- a step id is declared exactly once and
    /// referenced by id thereafter, which is exactly what the existing
    /// `:premises (@pN ...)` list already does for every node, shared or not.
    /// A `visited` set makes each node's `(step ...)` print exactly once, at
    /// the position it is first reached in the same left-to-right,
    /// premise-order traversal the recursive version used; a later reference
    /// to it is already covered by the referencing node's own `:premises`
    /// list, so nothing is lost.
    fn write_proof_node(
        &self,
        w: &mut impl Write,
        proof: &Proof,
        node_id: crate::ast::proof::ProofId,
        indent: usize,
    ) {
        let mut visited: FxHashSet<crate::ast::proof::ProofId> = FxHashSet::default();
        let mut stack: Vec<(crate::ast::proof::ProofId, usize)> = vec![(node_id, indent)];

        while let Some((node_id, indent)) = stack.pop() {
            if !visited.insert(node_id) {
                // Already printed via another parent; the referencing node's
                // `:premises (@pN ...)` list already records this edge, and a
                // cycle (which should not occur in a well-formed proof; see
                // `Proof::validate_structure`) simply stops here instead of
                // looping forever.
                continue;
            }

            let Some(node) = proof.get_node(node_id) else {
                continue;
            };

            let indent_str = "  ".repeat(indent);

            // Write the proof step
            let _ = write!(w, "{}", indent_str);
            let _ = write!(w, "(step @p{} ", node_id.0);

            // Write the rule
            self.write_proof_rule(w, &node.rule);

            // Write the conclusion
            let _ = write!(w, "\n{}  :conclusion ", indent_str);
            self.write_term(w, node.conclusion);

            // Write premises if any
            if !node.premises.is_empty() {
                let _ = write!(w, "\n{}  :premises (", indent_str);
                for (i, premise_id) in node.premises.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(w, " ");
                    }
                    let _ = write!(w, "@p{}", premise_id.0);
                }
                let _ = write!(w, ")");
            }

            // Write metadata if any
            if !node.metadata.is_empty() {
                let _ = write!(w, "\n{}  :metadata (", indent_str);
                for (i, (key, value)) in node.metadata.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(w, " ");
                    }
                    let _ = write!(w, ":{} {}", key, format_string_literal(value));
                }
                let _ = write!(w, ")");
            }

            let _ = writeln!(w, ")");

            // Push premises in reverse so the first premise is processed
            // next, matching the original recursion's left-to-right order.
            for premise_id in node.premises.iter().rev() {
                stack.push((*premise_id, indent + 1));
            }
        }
    }

    /// Write a proof rule
    fn write_proof_rule(&self, w: &mut impl Write, rule: &ProofRule) {
        match rule {
            ProofRule::Assume { name } => {
                if let Some(n) = name {
                    let _ = write!(w, ":rule assume :name {}", format_string_literal(n));
                } else {
                    let _ = write!(w, ":rule assume");
                }
            }
            ProofRule::Resolution { pivot } => {
                let _ = write!(w, ":rule resolution :pivot ");
                self.write_term(w, *pivot);
            }
            ProofRule::ModusPonens => {
                let _ = write!(w, ":rule modus-ponens");
            }
            ProofRule::Tautology => {
                let _ = write!(w, ":rule tautology");
            }
            ProofRule::ArithInequality => {
                let _ = write!(w, ":rule arith-inequality");
            }
            ProofRule::TheoryLemma { theory } => {
                let _ = write!(
                    w,
                    ":rule theory-lemma :theory {}",
                    format_string_literal(theory)
                );
            }
            ProofRule::Contradiction => {
                let _ = write!(w, ":rule contradiction");
            }
            ProofRule::Rewrite => {
                let _ = write!(w, ":rule rewrite");
            }
            ProofRule::Substitution => {
                let _ = write!(w, ":rule substitution");
            }
            ProofRule::Symmetry => {
                let _ = write!(w, ":rule symmetry");
            }
            ProofRule::Transitivity => {
                let _ = write!(w, ":rule transitivity");
            }
            ProofRule::Congruence => {
                let _ = write!(w, ":rule congruence");
            }
            ProofRule::Reflexivity => {
                let _ = write!(w, ":rule reflexivity");
            }
            ProofRule::Instantiation { terms } => {
                let _ = write!(w, ":rule instantiation :terms (");
                for (i, term_id) in terms.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(w, " ");
                    }
                    self.write_term(w, *term_id);
                }
                let _ = write!(w, ")");
            }
            ProofRule::Custom { name } => {
                let _ = write!(w, ":rule custom :name {}", format_string_literal(name));
            }
        }
    }
}
