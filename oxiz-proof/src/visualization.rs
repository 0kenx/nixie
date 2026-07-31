//! Proof visualization utilities.
//!
//! This module provides tools for visualizing proof trees in various formats,
//! including DOT (Graphviz), ASCII art, and structured text.

use crate::proof::{Proof, ProofNode, ProofNodeId, ProofStep};
use std::collections::HashSet;
use std::fmt::Write as FmtWrite;
use std::io::{self, Write};

/// Visualization format for proofs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisualizationFormat {
    /// DOT format for Graphviz.
    Dot,
    /// ASCII tree format.
    AsciiTree,
    /// Indented text format.
    IndentedText,
    /// JSON format.
    Json,
}

/// Work item for the iterative JSON writer.
#[derive(Debug)]
enum JsonFrame {
    /// Render the node's object body at the given indent/depth.
    Node {
        /// Node to render.
        id: ProofNodeId,
        /// Indentation level for the node's keys.
        indent: usize,
        /// Distance from the visualization root (for `max_depth`).
        depth: usize,
    },
    /// Emit a pre-rendered structural line (brace, bracket, separator).
    Literal(String),
}

/// Proof visualizer.
#[derive(Debug)]
pub struct ProofVisualizer {
    /// Maximum depth to visualize (None = unlimited).
    max_depth: Option<usize>,
    /// Whether to show node IDs.
    show_ids: bool,
    /// Whether to show full conclusions (or truncate).
    show_full_conclusions: bool,
    /// Maximum conclusion length (if not showing full).
    max_conclusion_length: usize,
}

impl ProofVisualizer {
    /// Create a new proof visualizer with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self {
            max_depth: None,
            show_ids: true,
            show_full_conclusions: false,
            max_conclusion_length: 40,
        }
    }

    /// Set the maximum depth to visualize.
    pub fn with_max_depth(mut self, depth: usize) -> Self {
        self.max_depth = Some(depth);
        self
    }

    /// Set whether to show node IDs.
    pub fn with_show_ids(mut self, show: bool) -> Self {
        self.show_ids = show;
        self
    }

    /// Set whether to show full conclusions.
    pub fn with_full_conclusions(mut self, show: bool) -> Self {
        self.show_full_conclusions = show;
        self
    }

    /// Visualize a proof in the specified format.
    pub fn visualize<W: Write>(
        &self,
        proof: &Proof,
        format: VisualizationFormat,
        writer: &mut W,
    ) -> io::Result<()> {
        match format {
            VisualizationFormat::Dot => self.visualize_dot(proof, writer),
            VisualizationFormat::AsciiTree => self.visualize_ascii_tree(proof, writer),
            VisualizationFormat::IndentedText => self.visualize_indented(proof, writer),
            VisualizationFormat::Json => self.visualize_json(proof, writer),
        }
    }

    /// Visualize proof as DOT format for Graphviz.
    fn visualize_dot<W: Write>(&self, proof: &Proof, writer: &mut W) -> io::Result<()> {
        writeln!(writer, "digraph Proof {{")?;
        writeln!(writer, "  rankdir=BT;")?;
        writeln!(writer, "  node [shape=box];")?;

        // Write nodes
        let mut visited = HashSet::new();
        if let Some(root) = proof.root() {
            self.write_dot_nodes(proof, root, writer, &mut visited, 0)?;
        }

        writeln!(writer, "}}")?;
        Ok(())
    }

    /// Emit the DOT node/edge lines for the sub-DAG rooted at `node_id`.
    ///
    /// Iterative (explicit heap stack): proof DAGs are routinely far deeper than
    /// the call stack can accommodate, and the `max_depth` cap is `None` by
    /// default so it cannot be relied on as a bound.
    fn write_dot_nodes<W: Write>(
        &self,
        proof: &Proof,
        node_id: ProofNodeId,
        writer: &mut W,
        visited: &mut HashSet<ProofNodeId>,
        depth: usize,
    ) -> io::Result<()> {
        // (node, node it is a premise of, depth)
        let mut stack: Vec<(ProofNodeId, Option<ProofNodeId>, usize)> =
            vec![(node_id, None, depth)];

        while let Some((current, parent, current_depth)) = stack.pop() {
            // The edge is written before the child is expanded, and regardless
            // of whether the child turns out to be already-visited or capped.
            if let Some(parent_id) = parent {
                writeln!(writer, "  {} -> {};", current.0, parent_id.0)?;
            }

            if visited.contains(&current) {
                continue;
            }
            if let Some(max_depth) = self.max_depth
                && current_depth >= max_depth
            {
                continue;
            }

            visited.insert(current);

            let Some(node) = proof.get_node(current) else {
                continue;
            };

            let label = escape_dot_label(&self.format_node_label(node));
            let color = match &node.step {
                ProofStep::Axiom { .. } => "lightblue",
                ProofStep::Inference { .. } => "lightgreen",
            };

            writeln!(
                writer,
                "  {} [label=\"{}\", fillcolor={}, style=filled];",
                current.0, label, color
            )?;

            // Write edges to premises, leftmost first (hence reversed pushes)
            if let ProofStep::Inference { premises, .. } = &node.step {
                stack.extend(
                    premises
                        .iter()
                        .rev()
                        .map(|&premise_id| (premise_id, Some(current), current_depth + 1)),
                );
            }
        }

        Ok(())
    }

    /// Visualize proof as ASCII tree.
    ///
    /// This is a *tree* rendering: a premise shared by several inferences is
    /// printed once under each of them, exactly as the recursive version did.
    /// On a heavily shared proof DAG that output is exponentially large — use
    /// [`VisualizationFormat::Dot`], which renders the DAG itself, instead.
    fn visualize_ascii_tree<W: Write>(&self, proof: &Proof, writer: &mut W) -> io::Result<()> {
        if let Some(root) = proof.root() {
            self.write_ascii_node(proof, root, writer, String::new(), true, 0)?;
        }
        Ok(())
    }

    /// Iterative (explicit heap stack) ASCII-tree rendering.
    fn write_ascii_node<W: Write>(
        &self,
        proof: &Proof,
        node_id: ProofNodeId,
        writer: &mut W,
        prefix: String,
        is_last: bool,
        depth: usize,
    ) -> io::Result<()> {
        // (node, prefix for that node's own line, is_last, depth)
        let mut stack: Vec<(ProofNodeId, String, bool, usize)> =
            vec![(node_id, prefix, is_last, depth)];

        while let Some((current, current_prefix, current_is_last, current_depth)) = stack.pop() {
            if let Some(max_depth) = self.max_depth
                && current_depth >= max_depth
            {
                continue;
            }

            let Some(node) = proof.get_node(current) else {
                continue;
            };

            let connector = if current_is_last { "└─" } else { "├─" };
            let label = self.format_node_label(node);

            writeln!(writer, "{}{} {}", current_prefix, connector, label)?;

            if let ProofStep::Inference { premises, .. } = &node.step {
                let new_prefix = format!(
                    "{}{}  ",
                    current_prefix,
                    if current_is_last { " " } else { "│" }
                );

                let last_index = premises.len().saturating_sub(1);
                stack.extend(premises.iter().enumerate().rev().map(|(i, &premise_id)| {
                    (
                        premise_id,
                        new_prefix.clone(),
                        i == last_index,
                        current_depth + 1,
                    )
                }));
            }
        }

        Ok(())
    }

    /// Visualize proof as indented text.
    ///
    /// Like the ASCII tree, this is a tree rendering and repeats shared premises.
    fn visualize_indented<W: Write>(&self, proof: &Proof, writer: &mut W) -> io::Result<()> {
        if let Some(root) = proof.root() {
            self.write_indented_node(proof, root, writer, 0, 0)?;
        }
        Ok(())
    }

    /// Iterative (explicit heap stack) indented-text rendering.
    fn write_indented_node<W: Write>(
        &self,
        proof: &Proof,
        node_id: ProofNodeId,
        writer: &mut W,
        indent: usize,
        depth: usize,
    ) -> io::Result<()> {
        // (node, indent level, depth)
        let mut stack: Vec<(ProofNodeId, usize, usize)> = vec![(node_id, indent, depth)];

        while let Some((current, current_indent, current_depth)) = stack.pop() {
            if let Some(max_depth) = self.max_depth
                && current_depth >= max_depth
            {
                continue;
            }

            let Some(node) = proof.get_node(current) else {
                continue;
            };

            let indent_str = "  ".repeat(current_indent);
            let label = self.format_node_label(node);

            writeln!(writer, "{}{}", indent_str, label)?;

            if let ProofStep::Inference { premises, .. } = &node.step {
                stack.extend(
                    premises
                        .iter()
                        .rev()
                        .map(|&premise_id| (premise_id, current_indent + 1, current_depth + 1)),
                );
            }
        }

        Ok(())
    }

    /// Visualize proof as JSON.
    fn visualize_json<W: Write>(&self, proof: &Proof, writer: &mut W) -> io::Result<()> {
        writeln!(writer, "{{")?;
        writeln!(writer, "  \"type\": \"proof\",")?;
        writeln!(writer, "  \"node_count\": {},", proof.node_count())?;
        writeln!(writer, "  \"depth\": {},", proof.depth())?;
        writeln!(writer, "  \"root\": {{")?;

        if let Some(root) = proof.root() {
            self.write_json_node(proof, root, writer, 2, 0)?;
        }

        writeln!(writer, "  }}")?;
        writeln!(writer, "}}")?;
        Ok(())
    }

    /// Iterative (explicit heap stack) JSON rendering.
    ///
    /// Depth truncation and dangling premises are both reported *in* the JSON
    /// rather than by silently emitting a partial object: a node cut off by
    /// `max_depth` becomes `{"truncated": true}`, and the trailing-comma
    /// bookkeeping counts only the premises actually emitted, so the output is
    /// always parseable.
    fn write_json_node<W: Write>(
        &self,
        proof: &Proof,
        node_id: ProofNodeId,
        writer: &mut W,
        indent: usize,
        depth: usize,
    ) -> io::Result<()> {
        let mut stack = vec![JsonFrame::Node {
            id: node_id,
            indent,
            depth,
        }];

        while let Some(frame) = stack.pop() {
            let (current, current_indent, current_depth) = match frame {
                JsonFrame::Literal(line) => {
                    writeln!(writer, "{}", line)?;
                    continue;
                }
                JsonFrame::Node { id, indent, depth } => (id, indent, depth),
            };

            let indent_str = "  ".repeat(current_indent);

            if let Some(max_depth) = self.max_depth
                && current_depth >= max_depth
            {
                writeln!(writer, "{}\"truncated\": true", indent_str)?;
                continue;
            }

            let Some(node) = proof.get_node(current) else {
                writeln!(writer, "{}\"missing\": true", indent_str)?;
                continue;
            };

            if self.show_ids {
                writeln!(writer, "{}\"id\": \"{}\",", indent_str, node.id)?;
            }

            match &node.step {
                ProofStep::Axiom { conclusion } => {
                    writeln!(writer, "{}\"type\": \"axiom\",", indent_str)?;
                    writeln!(
                        writer,
                        "{}\"conclusion\": \"{}\"",
                        indent_str,
                        escape_json(conclusion)
                    )?;
                }
                ProofStep::Inference {
                    rule,
                    premises,
                    conclusion,
                    ..
                } => {
                    writeln!(writer, "{}\"type\": \"inference\",", indent_str)?;
                    writeln!(writer, "{}\"rule\": \"{}\",", indent_str, escape_json(rule))?;
                    writeln!(
                        writer,
                        "{}\"conclusion\": \"{}\",",
                        indent_str,
                        escape_json(conclusion)
                    )?;

                    // Only premises that resolve to a node are emitted, and the
                    // comma bookkeeping is over that emitted set.
                    let present: Vec<ProofNodeId> = premises
                        .iter()
                        .copied()
                        .filter(|&id| proof.get_node(id).is_some())
                        .collect();

                    if !present.is_empty() {
                        writeln!(writer, "{}\"premises\": [", indent_str)?;
                        let last_index = present.len().saturating_sub(1);
                        stack.push(JsonFrame::Literal(format!("{}]", indent_str)));
                        for (i, &premise_id) in present.iter().enumerate().rev() {
                            let close = if i < last_index {
                                format!("{}  }},", indent_str)
                            } else {
                                format!("{}  }}", indent_str)
                            };
                            stack.push(JsonFrame::Literal(close));
                            stack.push(JsonFrame::Node {
                                id: premise_id,
                                indent: current_indent + 2,
                                depth: current_depth + 1,
                            });
                            stack.push(JsonFrame::Literal(format!("{}  {{", indent_str)));
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Format a node label for display.
    fn format_node_label(&self, node: &ProofNode) -> String {
        let mut label = String::new();

        if self.show_ids {
            let _ = write!(label, "{}: ", node.id);
        }

        match &node.step {
            ProofStep::Axiom { conclusion } => {
                let _ = write!(label, "axiom ");
                label.push_str(&self.format_conclusion(conclusion));
            }
            ProofStep::Inference {
                rule, conclusion, ..
            } => {
                let _ = write!(label, "{} ", rule);
                label.push_str(&self.format_conclusion(conclusion));
            }
        }

        label
    }

    /// Format a conclusion, possibly truncating it.
    fn format_conclusion(&self, conclusion: &str) -> String {
        if self.show_full_conclusions || conclusion.len() <= self.max_conclusion_length {
            conclusion.to_string()
        } else {
            format!("{}...", &conclusion[..self.max_conclusion_length])
        }
    }
}

impl Default for ProofVisualizer {
    fn default() -> Self {
        Self::new()
    }
}

/// Escape a string for JSON output.
fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Escape a string for use inside a double-quoted DOT (Graphviz) label.
///
/// A DOT quoted string ends at the first unescaped `"`, and `\` is itself
/// the escape introducer that would otherwise change the meaning of the
/// character after it. `write_dot_nodes` embeds free-form proof text (a
/// conclusion or a rule name, neither validated against DOT's grammar)
/// directly into `label="..."`; without this, a `"` in that text ended the
/// attribute early and corrupted the rest of the graph description (and any
/// premises/edges written after it).
fn escape_dot_label(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_visualizer_new() {
        let viz = ProofVisualizer::new();
        assert!(viz.show_ids);
        assert!(!viz.show_full_conclusions);
        assert_eq!(viz.max_conclusion_length, 40);
        assert!(viz.max_depth.is_none());
    }

    #[test]
    fn test_visualizer_with_options() {
        let viz = ProofVisualizer::new()
            .with_max_depth(5)
            .with_show_ids(false)
            .with_full_conclusions(true);

        assert_eq!(viz.max_depth, Some(5));
        assert!(!viz.show_ids);
        assert!(viz.show_full_conclusions);
    }

    #[test]
    fn test_visualize_dot() {
        let mut proof = Proof::new();
        proof.add_axiom("test");
        let viz = ProofVisualizer::new();

        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::Dot, &mut output)
            .expect("test operation should succeed");

        let dot = String::from_utf8(output).expect("test operation should succeed");
        assert!(dot.contains("digraph Proof"));
        assert!(dot.contains("axiom"));
        assert!(dot.contains("test"));
    }

    /// Direct unit test of the DOT label escaper: `\` and `"` are escaped
    /// (they are DOT's own escape introducer and quoted-string terminator);
    /// non-ASCII and control characters are left alone since they are not
    /// special to DOT's quoted-string grammar.
    #[test]
    fn test_escape_dot_label() {
        assert_eq!(escape_dot_label("hello"), "hello");
        assert_eq!(escape_dot_label("a\"b"), "a\\\"b");
        assert_eq!(escape_dot_label("a\\b"), "a\\\\b");
        assert_eq!(escape_dot_label("caf\u{e9}"), "caf\u{e9}");
        assert_eq!(escape_dot_label("a\u{0}b"), "a\u{0}b");
    }

    /// Regression: `write_dot_nodes` used to interpolate the node label
    /// (built from the free-form conclusion/rule text) straight into
    /// `label="..."` with no escaping at all, so a `"` in a conclusion ended
    /// the DOT attribute early and corrupted the rest of the graph
    /// (dangling text, unbalanced brackets, or a truncated file depending on
    /// what followed). Every `label="..."` attribute must now be a properly
    /// terminated, balanced quoted string even when the conclusion contains
    /// a quote and a backslash.
    #[test]
    fn test_visualize_dot_conclusion_with_quote_and_backslash_is_escaped() {
        let mut proof = Proof::new();
        proof.add_axiom("has \"quote\" and \\backslash");
        let viz = ProofVisualizer::new();

        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::Dot, &mut output)
            .expect("test operation should succeed");
        let dot = String::from_utf8(output).expect("test operation should succeed");

        assert!(
            dot.contains(r#"\"quote\""#),
            "the quote must be escaped, not raw, in: {dot}"
        );
        assert!(
            dot.contains(r"\\backslash"),
            "the backslash must be escaped, not raw, in: {dot}"
        );

        // Every `label="..."` attribute must terminate at an *unescaped*
        // quote before the line ends (i.e. escaping did not leave a bare
        // `"` that ends the attribute early).
        for line in dot.lines().filter(|l| l.contains("label=\"")) {
            let after_label = line
                .split_once("label=\"")
                .expect("filtered line contains label=\"")
                .1;
            let mut chars = after_label.chars();
            let mut terminated = false;
            while let Some(c) = chars.next() {
                if c == '\\' {
                    chars.next(); // escaped character: does not terminate.
                    continue;
                }
                if c == '"' {
                    terminated = true;
                    break;
                }
            }
            assert!(
                terminated,
                "label attribute never reaches an unescaped closing quote in: {line}"
            );
        }
    }

    /// Control: a conclusion with no special characters renders in the DOT
    /// label completely unchanged.
    #[test]
    fn test_visualize_dot_plain_conclusion_unchanged() {
        let mut proof = Proof::new();
        proof.add_axiom("plain conclusion with no special chars");
        let viz = ProofVisualizer::new();

        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::Dot, &mut output)
            .expect("test operation should succeed");
        let dot = String::from_utf8(output).expect("test operation should succeed");

        assert!(dot.contains("plain conclusion with no special chars"));
        assert!(!dot.contains('\\'), "no character here needed escaping");
    }

    #[test]
    fn test_visualize_ascii_tree() {
        let mut proof = Proof::new();
        let p = proof.add_axiom("p");
        let q = proof.add_axiom("q");
        let _and_node = proof.add_inference("and", vec![p, q], "(and p q)");

        let viz = ProofVisualizer::new();
        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::AsciiTree, &mut output)
            .expect("test operation should succeed");

        let tree = String::from_utf8(output).expect("test operation should succeed");
        assert!(tree.contains("and"));
        assert!(tree.contains("axiom"));
    }

    #[test]
    fn test_visualize_indented() {
        let mut proof = Proof::new();
        proof.add_axiom("test");
        let viz = ProofVisualizer::new();

        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::IndentedText, &mut output)
            .expect("test operation should succeed");

        let text = String::from_utf8(output).expect("test operation should succeed");
        assert!(text.contains("axiom"));
        assert!(text.contains("test"));
    }

    #[test]
    fn test_visualize_json() {
        let mut proof = Proof::new();
        proof.add_axiom("test");
        let viz = ProofVisualizer::new();

        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::Json, &mut output)
            .expect("test operation should succeed");

        let json = String::from_utf8(output).expect("test operation should succeed");
        assert!(json.contains("\"type\": \"proof\""));
        assert!(json.contains("\"type\": \"axiom\""));
        assert!(json.contains("test"));
    }

    #[test]
    fn test_escape_json() {
        assert_eq!(escape_json("hello"), "hello");
        assert_eq!(escape_json("hello\"world"), "hello\\\"world");
        assert_eq!(escape_json("line1\nline2"), "line1\\nline2");
        assert_eq!(escape_json("path\\to\\file"), "path\\\\to\\\\file");
        // Non-ASCII passes through raw (valid inside a JSON string as-is);
        // a control character below 0x20 is not one of the five characters
        // `escape_json` special-cases, so it also passes through unescaped
        // here -- JSON's grammar technically requires *some* escape for
        // control characters, but that gap is pre-existing and out of scope
        // for this fix (this test exists to pin current behaviour, not
        // claim strict JSON conformance).
        assert_eq!(escape_json("caf\u{e9}"), "caf\u{e9}");
    }

    /// Confirmation (not a fix): `visualize_json` already routes `rule` and
    /// `conclusion` through `escape_json` (unlike the DOT path, which did
    /// not route its label through any escaper at all). A `"` in a
    /// conclusion must not break the surrounding `"conclusion": "..."` JSON
    /// string value.
    #[test]
    fn test_visualize_json_conclusion_with_quote_is_escaped() {
        let mut proof = Proof::new();
        proof.add_axiom("has \"quote\" inside");
        let viz = ProofVisualizer::new();

        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::Json, &mut output)
            .expect("test operation should succeed");
        let json = String::from_utf8(output).expect("test operation should succeed");

        assert!(
            json.contains(r#"has \"quote\" inside"#),
            "the quote must be escaped, not raw, in: {json}"
        );
        assert!(
            !json.contains("\"conclusion\": \"has \"quote\""),
            "a raw quote must not end the conclusion string value early in: {json}"
        );
    }

    #[test]
    fn test_visualize_with_max_depth() {
        let mut proof = Proof::new();
        let p = proof.add_axiom("p");
        let q = proof.add_axiom("q");
        let r = proof.add_axiom("r");
        let and1 = proof.add_inference("and", vec![q, r], "(and q r)");
        let _and2 = proof.add_inference("and", vec![p, and1], "(and p (and q r))");

        let viz = ProofVisualizer::new().with_max_depth(1);
        let mut output = Vec::new();
        viz.visualize(&proof, VisualizationFormat::IndentedText, &mut output)
            .expect("test operation should succeed");

        let text = String::from_utf8(output).expect("test operation should succeed");
        // Should only show root and its immediate children
        assert!(text.contains("and"));
    }

    #[test]
    fn test_format_conclusion_truncate() {
        let viz = ProofVisualizer::new();

        let short = "short";
        assert_eq!(viz.format_conclusion(short), "short");

        let long = "a".repeat(50);
        let formatted = viz.format_conclusion(&long);
        assert!(formatted.ends_with("..."));
        assert!(formatted.len() < long.len());
    }

    #[test]
    fn test_format_conclusion_full() {
        let viz = ProofVisualizer::new().with_full_conclusions(true);

        let long = "a".repeat(50);
        let formatted = viz.format_conclusion(&long);
        assert_eq!(formatted, long);
        assert!(!formatted.contains("..."));
    }
}
