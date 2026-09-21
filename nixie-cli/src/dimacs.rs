//! DIMACS CNF format parser and writer
//!
//! DIMACS is a standard format for representing SAT problems in CNF (Conjunctive Normal Form).
//! Format specification:
//! - Comments start with 'c'
//! - Problem line: "p cnf <num_vars> <num_clauses>"
//! - Clauses: space-separated literals ending with 0
//! - Literals: positive integers for positive literals, negative for negated

use std::collections::HashMap;
use std::io::{BufRead, Write};

/// Represents a DIMACS CNF problem
#[derive(Debug, Clone)]
pub struct DimacsCnf {
    /// Number of variables
    pub num_vars: usize,
    /// Clauses (each clause is a vector of literals)
    pub clauses: Vec<Vec<i32>>,
    /// Comments from the file
    #[allow(dead_code)]
    pub comments: Vec<String>,
}

impl DimacsCnf {
    /// Create a new empty DIMACS CNF problem
    #[allow(dead_code)]
    pub fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            clauses: Vec::new(),
            comments: Vec::new(),
        }
    }

    /// Parse DIMACS CNF from a reader
    ///
    /// DIMACS clauses are terminated by a literal `0` and may legally span
    /// multiple lines; a clause is not necessarily "one line". This parser
    /// therefore tokenizes the whole clause body as a single literal stream
    /// (not line-by-line) and splits it into clauses on `0` terminators, so:
    /// - a clause split across several lines is reassembled correctly,
    /// - an empty clause (`0` immediately, i.e. two terminators back-to-back
    ///   or a lone `0` line) is preserved as the empty clause (falsum),
    ///   which `to_smtlib2` renders as `(assert false)` -- an immediate
    ///   UNSAT witness, matching the DIMACS semantics -- rather than being
    ///   silently dropped, and
    /// - a `0` appearing mid-line is always treated as a terminator, never
    ///   misread as a reference to "variable 0".
    pub fn parse<R: BufRead>(reader: R) -> Result<Self, String> {
        let mut num_vars = 0usize;
        let mut num_clauses_expected = 0usize;
        let mut comments = Vec::new();
        let mut problem_line_found = false;
        let mut body_tokens: Vec<i32> = Vec::new();

        for line in reader.lines() {
            let line = line.map_err(|e| format!("Failed to read line: {}", e))?;
            let trimmed = line.trim();

            if trimmed.is_empty() {
                continue;
            }

            if let Some(stripped) = trimmed.strip_prefix('c') {
                // Comment line
                comments.push(stripped.trim().to_string());
                continue;
            }

            if trimmed.starts_with("p cnf") {
                // Problem line: p cnf <num_vars> <num_clauses>
                let parts: Vec<&str> = trimmed.split_whitespace().collect();
                if parts.len() != 4 {
                    return Err(format!("Invalid problem line: {}", trimmed));
                }

                num_vars = parts[2]
                    .parse()
                    .map_err(|_| format!("Invalid number of variables: {}", parts[2]))?;
                num_clauses_expected = parts[3]
                    .parse()
                    .map_err(|_| format!("Invalid number of clauses: {}", parts[3]))?;
                problem_line_found = true;
                continue;
            }

            // Clause body line: accumulate its tokens into the literal
            // stream; clause boundaries are resolved afterwards by `0`
            // terminators, not by line breaks.
            if !problem_line_found {
                return Err(
                    "Clause found before problem line. Problem line must come first.".to_string(),
                );
            }

            for tok in trimmed.split_whitespace() {
                let lit: i32 = tok
                    .parse()
                    .map_err(|_| format!("Invalid literal in clause: {}", tok))?;
                body_tokens.push(lit);
            }
        }

        if !problem_line_found {
            return Err("No problem line found in DIMACS file".to_string());
        }

        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let mut current: Vec<i32> = Vec::new();
        for tok in body_tokens {
            if tok == 0 {
                clauses.push(std::mem::take(&mut current));
            } else {
                let var = tok.unsigned_abs() as usize;
                if var > num_vars {
                    return Err(format!(
                        "Literal {} refers to variable {}, but only {} variables declared",
                        tok, var, num_vars
                    ));
                }
                current.push(tok);
            }
        }
        if !current.is_empty() {
            return Err(format!(
                "Unterminated clause: literals {:?} are missing a trailing 0",
                current
            ));
        }

        if clauses.len() != num_clauses_expected {
            return Err(format!(
                "Expected {} clauses but found {}",
                num_clauses_expected,
                clauses.len()
            ));
        }

        Ok(Self {
            num_vars,
            clauses,
            comments,
        })
    }

    /// Write DIMACS CNF to a writer
    #[allow(dead_code)]
    pub fn write<W: Write>(&self, mut writer: W) -> Result<(), String> {
        // Write comments
        for comment in &self.comments {
            writeln!(writer, "c {}", comment)
                .map_err(|e| format!("Failed to write comment: {}", e))?;
        }

        // Write problem line
        writeln!(writer, "p cnf {} {}", self.num_vars, self.clauses.len())
            .map_err(|e| format!("Failed to write problem line: {}", e))?;

        // Write clauses
        for clause in &self.clauses {
            for &lit in clause {
                write!(writer, "{} ", lit)
                    .map_err(|e| format!("Failed to write literal: {}", e))?;
            }
            writeln!(writer, "0").map_err(|e| format!("Failed to write clause end: {}", e))?;
        }

        Ok(())
    }

    /// Convert to SMT-LIB2 format
    pub fn to_smtlib2(&self) -> String {
        let mut result = String::new();

        result.push_str("(set-logic QF_UF)\n");

        // Declare variables as Boolean
        for i in 1..=self.num_vars {
            result.push_str(&format!("(declare-const v{} Bool)\n", i));
        }

        // Add clauses as assertions
        for clause in &self.clauses {
            if clause.is_empty() {
                // The empty clause (falsum): DIMACS files may legitimately
                // contain a bare "0" clause, which is unsatisfiable by
                // definition. Assert `false` directly instead of emitting
                // `(or)` (vacuously true) or silently dropping the clause.
                result.push_str("(assert false)\n");
            } else if clause.len() == 1 {
                // Unit clause
                let lit = clause[0];
                if lit > 0 {
                    result.push_str(&format!("(assert v{})\n", lit));
                } else {
                    result.push_str(&format!("(assert (not v{}))\n", lit.abs()));
                }
            } else {
                // Multi-literal clause
                result.push_str("(assert (or");
                for &lit in clause {
                    if lit > 0 {
                        result.push_str(&format!(" v{}", lit));
                    } else {
                        result.push_str(&format!(" (not v{})", lit.abs()));
                    }
                }
                result.push_str("))\n");
            }
        }

        result.push_str("(check-sat)\n");
        result
    }

    /// Convert SMT-LIB2 model to DIMACS assignment
    pub fn model_from_smtlib2(model: &str, num_vars: usize) -> Vec<i32> {
        let mut assignment = Vec::new();
        let lines: Vec<&str> = model.lines().collect();

        // Parse model from SMT-LIB2 format
        let mut var_values: HashMap<usize, bool> = HashMap::new();

        for line in lines {
            let trimmed = line.trim();
            // Look for patterns like: (define-fun v1 () Bool true)
            if trimmed.contains("define-fun")
                && trimmed.contains("Bool")
                && let Some(var_start) = trimmed.find("v")
            {
                let after_v = &trimmed[var_start + 1..];
                if let Some(space_idx) = after_v.find(char::is_whitespace)
                    && let Ok(var_num) = after_v[..space_idx].parse::<usize>()
                {
                    let is_true = trimmed.contains("true");
                    var_values.insert(var_num, is_true);
                }
            }
        }

        // Build DIMACS assignment
        for i in 1..=num_vars {
            if let Some(&value) = var_values.get(&i) {
                assignment.push(if value { i as i32 } else { -(i as i32) });
            }
        }

        assignment
    }

    /// Write DIMACS satisfying assignment
    #[allow(dead_code)]
    pub fn write_sat_assignment<W: Write>(assignment: &[i32], mut writer: W) -> Result<(), String> {
        writeln!(writer, "s SATISFIABLE")
            .map_err(|e| format!("Failed to write SAT line: {}", e))?;
        write!(writer, "v ").map_err(|e| format!("Failed to write assignment prefix: {}", e))?;

        for &lit in assignment {
            write!(writer, "{} ", lit).map_err(|e| format!("Failed to write literal: {}", e))?;
        }

        writeln!(writer, "0").map_err(|e| format!("Failed to write assignment end: {}", e))?;

        Ok(())
    }

    /// Write DIMACS unsatisfiable result
    #[allow(dead_code)]
    pub fn write_unsat<W: Write>(mut writer: W) -> Result<(), String> {
        writeln!(writer, "s UNSATISFIABLE")
            .map_err(|e| format!("Failed to write UNSAT line: {}", e))?;
        Ok(())
    }
}

/// Quantifier type for QDIMACS
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    /// Universal quantifier (forall)
    Universal,
    /// Existential quantifier (exists)
    Existential,
}

/// Quantifier prefix entry
#[derive(Debug, Clone)]
pub struct QuantifierBlock {
    /// Type of quantifier
    pub quantifier: Quantifier,
    /// Variables in this quantifier block
    pub variables: Vec<usize>,
}

/// Represents a QDIMACS (Quantified Boolean Formula) problem
#[derive(Debug, Clone)]
pub struct QDimacsCnf {
    /// Number of variables
    pub num_vars: usize,
    /// Quantifier prefix (alternating quantifiers)
    pub quantifiers: Vec<QuantifierBlock>,
    /// Clauses (each clause is a vector of literals)
    pub clauses: Vec<Vec<i32>>,
    /// Comments from the file
    pub comments: Vec<String>,
}

impl QDimacsCnf {
    /// Create a new empty QDIMACS CNF problem
    #[allow(dead_code)]
    pub fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            quantifiers: Vec::new(),
            clauses: Vec::new(),
            comments: Vec::new(),
        }
    }

    /// Parse QDIMACS from a reader
    ///
    /// Quantifier blocks (`a ...`/`e ...`) are always exactly one line per
    /// the QDIMACS spec, so those are still parsed line-by-line. Clauses,
    /// however, are 0-terminated and may span multiple lines just like in
    /// plain DIMACS (see [`DimacsCnf::parse`]), so the clause body is
    /// tokenized as a single literal stream and split on `0` terminators
    /// rather than treated as one clause per line.
    pub fn parse<R: BufRead>(reader: R) -> Result<Self, String> {
        let mut num_vars = 0usize;
        let mut num_clauses_expected = 0usize;
        let mut quantifiers = Vec::new();
        let mut comments = Vec::new();
        let mut problem_line_found = false;
        let mut body_tokens: Vec<i32> = Vec::new();

        for line in reader.lines() {
            let line = line.map_err(|e| format!("Failed to read line: {}", e))?;
            let trimmed = line.trim();

            if trimmed.is_empty() {
                continue;
            }

            if let Some(stripped) = trimmed.strip_prefix('c') {
                // Comment line
                comments.push(stripped.trim().to_string());
                continue;
            }

            if trimmed.starts_with("p cnf") {
                // Problem line: p cnf <num_vars> <num_clauses>
                let parts: Vec<&str> = trimmed.split_whitespace().collect();
                if parts.len() != 4 {
                    return Err(format!("Invalid problem line: {}", trimmed));
                }

                num_vars = parts[2]
                    .parse()
                    .map_err(|_| format!("Invalid number of variables: {}", parts[2]))?;
                num_clauses_expected = parts[3]
                    .parse()
                    .map_err(|_| format!("Invalid number of clauses: {}", parts[3]))?;
                problem_line_found = true;
                continue;
            }

            if !problem_line_found {
                return Err("Quantifier or clause found before problem line".to_string());
            }

            // Check for quantifier lines (a or e)
            if trimmed.starts_with('a') || trimmed.starts_with('e') {
                let quantifier = if trimmed.starts_with('a') {
                    Quantifier::Universal
                } else {
                    Quantifier::Existential
                };

                let vars: Result<Vec<i32>, _> = trimmed[1..]
                    .split_whitespace()
                    .map(|s| s.parse::<i32>())
                    .collect();

                let mut vars =
                    vars.map_err(|e| format!("Invalid variable in quantifier line: {}", e))?;

                // Remove trailing zero if present
                if vars.last() == Some(&0) {
                    vars.pop();
                }

                // Convert to usize and validate
                let variables: Result<Vec<usize>, String> = vars
                    .into_iter()
                    .map(|v| {
                        if v <= 0 {
                            Err(format!("Invalid variable in quantifier: {}", v))
                        } else {
                            let var = v as usize;
                            if var > num_vars {
                                Err(format!("Variable {} exceeds num_vars {}", var, num_vars))
                            } else {
                                Ok(var)
                            }
                        }
                    })
                    .collect();

                quantifiers.push(QuantifierBlock {
                    quantifier,
                    variables: variables?,
                });
                continue;
            }

            // Clause body line: accumulate tokens; clause boundaries are
            // resolved after the loop by `0` terminators, not line breaks.
            for tok in trimmed.split_whitespace() {
                let lit: i32 = tok
                    .parse()
                    .map_err(|_| format!("Invalid literal in clause: {}", tok))?;
                body_tokens.push(lit);
            }
        }

        if !problem_line_found {
            return Err("No problem line found in QDIMACS file".to_string());
        }

        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let mut current: Vec<i32> = Vec::new();
        for tok in body_tokens {
            if tok == 0 {
                clauses.push(std::mem::take(&mut current));
            } else {
                let var = tok.unsigned_abs() as usize;
                if var > num_vars {
                    return Err(format!(
                        "Literal {} refers to variable {}, but only {} variables declared",
                        tok, var, num_vars
                    ));
                }
                current.push(tok);
            }
        }
        if !current.is_empty() {
            return Err(format!(
                "Unterminated clause: literals {:?} are missing a trailing 0",
                current
            ));
        }

        if clauses.len() != num_clauses_expected {
            return Err(format!(
                "Expected {} clauses but found {}",
                num_clauses_expected,
                clauses.len()
            ));
        }

        Ok(Self {
            num_vars,
            quantifiers,
            clauses,
            comments,
        })
    }

    /// Write QDIMACS to a writer
    #[allow(dead_code)]
    pub fn write<W: Write>(&self, mut writer: W) -> Result<(), String> {
        // Write comments
        for comment in &self.comments {
            writeln!(writer, "c {}", comment)
                .map_err(|e| format!("Failed to write comment: {}", e))?;
        }

        // Write problem line
        writeln!(writer, "p cnf {} {}", self.num_vars, self.clauses.len())
            .map_err(|e| format!("Failed to write problem line: {}", e))?;

        // Write quantifiers
        for block in &self.quantifiers {
            let prefix = match block.quantifier {
                Quantifier::Universal => 'a',
                Quantifier::Existential => 'e',
            };

            write!(writer, "{}", prefix)
                .map_err(|e| format!("Failed to write quantifier: {}", e))?;

            for &var in &block.variables {
                write!(writer, " {}", var)
                    .map_err(|e| format!("Failed to write variable: {}", e))?;
            }
            writeln!(writer, " 0").map_err(|e| format!("Failed to write quantifier end: {}", e))?;
        }

        // Write clauses
        for clause in &self.clauses {
            for &lit in clause {
                write!(writer, "{} ", lit)
                    .map_err(|e| format!("Failed to write literal: {}", e))?;
            }
            writeln!(writer, "0").map_err(|e| format!("Failed to write clause end: {}", e))?;
        }

        Ok(())
    }

    /// Convert QDIMACS to SMT-LIB2 format
    pub fn to_smtlib2(&self) -> String {
        let mut output = String::new();

        // Set logic
        output.push_str("(set-logic UF)\n\n");

        // Comments
        for comment in &self.comments {
            output.push_str(&format!("; {}\n", comment));
        }
        if !self.comments.is_empty() {
            output.push('\n');
        }

        // Declare all variables as Bool
        for i in 1..=self.num_vars {
            output.push_str(&format!("(declare-const v{} Bool)\n", i));
        }
        output.push('\n');

        // Build the formula with quantifiers
        let matrix = self.clauses_to_smtlib2();

        // Wrap with quantifiers (outermost first)
        let mut formula = matrix;
        for block in self.quantifiers.iter().rev() {
            let quant_str = match block.quantifier {
                Quantifier::Universal => "forall",
                Quantifier::Existential => "exists",
            };

            let vars: Vec<String> = block
                .variables
                .iter()
                .map(|&v| format!("(v{} Bool)", v))
                .collect();

            formula = format!("({} ({}) {})", quant_str, vars.join(" "), formula);
        }

        output.push_str(&format!("(assert {})\n\n", formula));
        output.push_str("(check-sat)\n");

        output
    }

    /// Convert clauses to SMT-LIB2 (without quantifiers)
    fn clauses_to_smtlib2(&self) -> String {
        if self.clauses.is_empty() {
            return "true".to_string();
        }

        let clause_strs: Vec<String> = self
            .clauses
            .iter()
            .map(|clause| {
                if clause.is_empty() {
                    "false".to_string()
                } else if clause.len() == 1 {
                    let lit = clause[0];
                    if lit > 0 {
                        format!("v{}", lit)
                    } else {
                        format!("(not v{})", -lit)
                    }
                } else {
                    let literals: Vec<String> = clause
                        .iter()
                        .map(|&lit| {
                            if lit > 0 {
                                format!("v{}", lit)
                            } else {
                                format!("(not v{})", -lit)
                            }
                        })
                        .collect();
                    format!("(or {})", literals.join(" "))
                }
            })
            .collect();

        if clause_strs.len() == 1 {
            clause_strs[0].clone()
        } else {
            format!("(and {})", clause_strs.join(" "))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_parse_simple_dimacs() {
        let input = "c Simple SAT problem\np cnf 3 2\n1 -2 0\n2 3 -1 0\n";
        let cursor = Cursor::new(input);
        let cnf = DimacsCnf::parse(cursor).expect("test operation should succeed");

        assert_eq!(cnf.num_vars, 3);
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.clauses[0], vec![1, -2]);
        assert_eq!(cnf.clauses[1], vec![2, 3, -1]);
        assert_eq!(cnf.comments.len(), 1);
    }

    #[test]
    fn test_write_dimacs() {
        let mut cnf = DimacsCnf::new(2);
        cnf.clauses.push(vec![1, -2]);
        cnf.clauses.push(vec![2]);
        cnf.comments.push("Test problem".to_string());

        let mut output = Vec::new();
        cnf.write(&mut output)
            .expect("test operation should succeed");

        let output_str = String::from_utf8(output).expect("test operation should succeed");
        assert!(output_str.contains("c Test problem"));
        assert!(output_str.contains("p cnf 2 2"));
        assert!(output_str.contains("1 -2 0"));
        assert!(output_str.contains("2 0"));
    }

    #[test]
    fn test_to_smtlib2() {
        let mut cnf = DimacsCnf::new(2);
        cnf.clauses.push(vec![1, -2]);
        cnf.clauses.push(vec![2]);

        let smtlib2 = cnf.to_smtlib2();
        assert!(smtlib2.contains("(set-logic QF_UF)"));
        assert!(smtlib2.contains("(declare-const v1 Bool)"));
        assert!(smtlib2.contains("(declare-const v2 Bool)"));
        assert!(smtlib2.contains("(assert (or v1 (not v2)))"));
        assert!(smtlib2.contains("(assert v2)"));
        assert!(smtlib2.contains("(check-sat)"));
    }

    #[test]
    fn test_invalid_dimacs() {
        // Missing problem line
        let input = "1 -2 0\n";
        let cursor = Cursor::new(input);
        assert!(DimacsCnf::parse(cursor).is_err());

        // Invalid variable number
        let input = "p cnf 2 1\n1 -3 0\n";
        let cursor = Cursor::new(input);
        assert!(DimacsCnf::parse(cursor).is_err());

        // Wrong number of clauses
        let input = "p cnf 2 2\n1 -2 0\n";
        let cursor = Cursor::new(input);
        assert!(DimacsCnf::parse(cursor).is_err());
    }

    #[test]
    fn test_clause_spanning_multiple_lines_is_one_clause() {
        // A single clause whose literals are split across several lines
        // must be parsed as ONE clause, not several.
        let input = "p cnf 3 1\n1 -2\n3 0\n";
        let cursor = Cursor::new(input);
        let cnf = DimacsCnf::parse(cursor).expect("multi-line clause should parse");
        assert_eq!(cnf.clauses.len(), 1);
        assert_eq!(cnf.clauses[0], vec![1, -2, 3]);
    }

    #[test]
    fn test_multiple_clauses_spanning_lines() {
        // Two clauses, each spanning two lines.
        let input = "p cnf 4 2\n1 -2\n3 0\n-4 1\n2 0\n";
        let cursor = Cursor::new(input);
        let cnf = DimacsCnf::parse(cursor).expect("test should parse");
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.clauses[0], vec![1, -2, 3]);
        assert_eq!(cnf.clauses[1], vec![-4, 1, 2]);
    }

    #[test]
    fn test_empty_clause_is_falsum_not_dropped() {
        // A bare "0" clause means UNSAT (the empty clause / falsum) per the
        // DIMACS spec -- it must survive parsing rather than being silently
        // discarded.
        let input = "p cnf 1 1\n0\n";
        let cursor = Cursor::new(input);
        let cnf = DimacsCnf::parse(cursor).expect("empty clause should parse, not error");
        assert_eq!(cnf.clauses.len(), 1);
        assert!(cnf.clauses[0].is_empty());

        // And it must render as an explicit contradiction, not a vacuous
        // `(or)` or a dropped assertion.
        let smtlib2 = cnf.to_smtlib2();
        assert!(smtlib2.contains("(assert false)"));
        assert!(!smtlib2.contains("(assert (or))"));
    }

    #[test]
    fn test_empty_clause_among_others() {
        let input = "p cnf 2 2\n1 2 0\n0\n";
        let cursor = Cursor::new(input);
        let cnf = DimacsCnf::parse(cursor).expect("test should parse");
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.clauses[0], vec![1, 2]);
        assert!(cnf.clauses[1].is_empty());
    }

    #[test]
    fn test_mid_line_zero_terminates_clause_not_treated_as_variable() {
        // "1 2 0 3 0" on one physical line is two clauses: [1, 2] and [3],
        // not a single clause containing a bogus "variable 0" literal.
        let input = "p cnf 3 2\n1 2 0 3 0\n";
        let cursor = Cursor::new(input);
        let cnf = DimacsCnf::parse(cursor).expect("test should parse");
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.clauses[0], vec![1, 2]);
        assert_eq!(cnf.clauses[1], vec![3]);
    }

    #[test]
    fn test_unterminated_clause_is_an_error() {
        // A trailing clause with no terminating 0 is malformed.
        let input = "p cnf 2 1\n1 2\n";
        let cursor = Cursor::new(input);
        let err = DimacsCnf::parse(cursor).expect_err("missing terminator should error");
        assert!(err.contains("Unterminated clause"));
    }

    #[test]
    fn test_qdimacs_clause_spanning_multiple_lines() {
        let input = "p cnf 3 1\ne 1 2 0\na 3 0\n1 -2\n3 0\n";
        let cursor = Cursor::new(input);
        let qcnf = QDimacsCnf::parse(cursor).expect("test should parse");
        assert_eq!(qcnf.clauses.len(), 1);
        assert_eq!(qcnf.clauses[0], vec![1, -2, 3]);
    }

    #[test]
    fn test_qdimacs_empty_clause_preserved() {
        let input = "p cnf 1 1\ne 1 0\n0\n";
        let cursor = Cursor::new(input);
        let qcnf = QDimacsCnf::parse(cursor).expect("test should parse");
        assert_eq!(qcnf.clauses.len(), 1);
        assert!(qcnf.clauses[0].is_empty());
        assert!(qcnf.to_smtlib2().contains("false"));
    }

    #[test]
    fn test_parse_qdimacs() {
        let input = "c QBF example\np cnf 4 2\na 1 2 0\ne 3 4 0\n1 -2 3 0\n-1 2 -4 0\n";
        let cursor = Cursor::new(input);
        let qcnf = QDimacsCnf::parse(cursor).expect("test operation should succeed");

        assert_eq!(qcnf.num_vars, 4);
        assert_eq!(qcnf.quantifiers.len(), 2);
        assert_eq!(qcnf.quantifiers[0].quantifier, Quantifier::Universal);
        assert_eq!(qcnf.quantifiers[0].variables, vec![1, 2]);
        assert_eq!(qcnf.quantifiers[1].quantifier, Quantifier::Existential);
        assert_eq!(qcnf.quantifiers[1].variables, vec![3, 4]);
        assert_eq!(qcnf.clauses.len(), 2);
    }

    #[test]
    fn test_write_qdimacs() {
        let mut qcnf = QDimacsCnf::new(3);
        qcnf.quantifiers.push(QuantifierBlock {
            quantifier: Quantifier::Existential,
            variables: vec![1, 2],
        });
        qcnf.quantifiers.push(QuantifierBlock {
            quantifier: Quantifier::Universal,
            variables: vec![3],
        });
        qcnf.clauses.push(vec![1, -2]);
        qcnf.clauses.push(vec![2, 3]);

        let mut output = Vec::new();
        qcnf.write(&mut output)
            .expect("test operation should succeed");

        let output_str = String::from_utf8(output).expect("test operation should succeed");
        assert!(output_str.contains("p cnf 3 2"));
        assert!(output_str.contains("e 1 2 0"));
        assert!(output_str.contains("a 3 0"));
        assert!(output_str.contains("1 -2 0"));
        assert!(output_str.contains("2 3 0"));
    }

    #[test]
    fn test_qdimacs_to_smtlib2() {
        let mut qcnf = QDimacsCnf::new(2);
        qcnf.quantifiers.push(QuantifierBlock {
            quantifier: Quantifier::Universal,
            variables: vec![1],
        });
        qcnf.quantifiers.push(QuantifierBlock {
            quantifier: Quantifier::Existential,
            variables: vec![2],
        });
        qcnf.clauses.push(vec![1, -2]);

        let smtlib2 = qcnf.to_smtlib2();
        assert!(smtlib2.contains("(set-logic UF)"));
        assert!(smtlib2.contains("(declare-const v1 Bool)"));
        assert!(smtlib2.contains("(declare-const v2 Bool)"));
        assert!(smtlib2.contains("forall"));
        assert!(smtlib2.contains("exists"));
        assert!(smtlib2.contains("(or v1 (not v2))"));
    }
}

/// A flat, scanned DIMACS body: `(num_vars, lits)` where `lits` is the
/// clause stream in file order, clauses separated (terminated) by `0` —
/// the same representation the file itself uses, with none of the
/// per-clause `Vec` materialization.
///
/// Built by [`FlatCnf::scan`], a byte-level scanner with the same token
/// semantics as [`DimacsCnf::parse`] (comment lines skipped whole,
/// clause boundaries at `0` regardless of line breaks, non-`i32` tokens
/// error naming the token, unterminated trailing clause an error).  It
/// exists because the line-based UTF-8 parse plus the `Vec<Vec<i32>>`
/// intermediate cost ~70 % of whole-run wall on the 544 MB parse anatomy
/// (`hwmcc-6s299`, zero search on both sides) — see
/// `docs/studies/2026-09-15-env-probe-regression.md`.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct FlatCnf {
    pub num_vars: usize,
    pub num_clauses: usize,
    pub lits: Vec<i32>,
}

impl FlatCnf {
    /// Byte-level scan of a whole DIMACS CNF body.
    ///
    /// Uses the AVX2 boundary kernels (32-byte blockwise whitespace/digit
    /// runs, direct integer assembly) when the CPU has AVX2 and
    /// `NIXIE_NO_SIMD` is unset; otherwise the scalar byte loops.  The two
    /// Byte-level scan of a whole DIMACS CNF body, with a byte-size hint
    /// for the input buffer (the caller's file length when known).
    ///
    /// `read_to_end` otherwise grows the buffer by amortized doubling —
    /// on half-gigabyte inputs that is a second full read's worth of
    /// copying through the page cache; an exact reservation reads once.
    /// The AVX2 boundary kernels and the fused blockwise token walk run
    /// when the CPU has AVX2 and `NIXIE_NO_SIMD` is unset; both produce
    /// byte-identical `lits` streams and identical error messages —
    /// pinned by the differential tests in `scan_tests`.
    ///
    /// # Errors
    ///
    /// Same error conditions as [`DimacsCnf::parse`], with analogous
    /// messages (missing problem line, invalid literal, variable exceeding
    /// the declared count, unterminated clause, clause count mismatch).
    pub fn scan_sized<R: BufRead>(mut reader: R, size_hint: u64) -> Result<Self, String> {
        // One whole-file buffer: for CNF inputs (hundreds of MB at most)
        // a single allocation beats chunk-carry machinery, and unlike the
        // solver-side parser this scan builds no solver state mid-read.
        let mut raw = Vec::new();
        if size_hint > 0 {
            // +1 slack: `reserve_exact` at the exact length leaves the
            // vector zero-capacity-margin, and any metadata/file-length
            // disagreement then falls straight back to doubling.
            raw.reserve_exact(size_hint as usize + 1);
        }
        reader
            .read_to_end(&mut raw)
            .map_err(|e| format!("Failed to read DIMACS: {}", e))?;
        Self::scan_body(&raw, simd_scan_enabled())
    }

    /// The scan driver over an in-memory buffer.
    ///
    /// `simd == true` is a caller contract: AVX2 was runtime-detected
    /// ([`simd_scan_enabled`] or the equivalent test-side check) — the
    /// AVX2 kernels below are `#[target_feature]` and must not be called
    /// otherwise.  Both kernel choices walk the identical token stream;
    /// the output and every error message are path-independent.
    fn scan_body(raw: &[u8], simd: bool) -> Result<Self, String> {
        let mut num_vars = 0usize;
        let mut num_clauses_expected = 0usize;
        let mut problem_line_found = false;
        // ABLATION: exact upper bound measured +3% instructions on the
        // load cells vs this heuristic (mimalloc's large-alloc path
        // costs more than the doubling regrows it saves); see the study.
        let mut lits: Vec<i32> = Vec::with_capacity(raw.len() / 8);
        let mut clauses_found = 0usize;

        let mut i = 0usize;
        let n = raw.len();
        while i < n {
            // Fused blockwise walk: advances whole 32-byte blocks of
            // tokens at one load + two masks each, stopping at line
            // bytes, block-edge tokens, or the tail for this scalar
            // body (which handles the stop reason; the loop then
            // re-enters fused mode — the scalar body is the reference
            // semantics and owns every non-fast path).
            if simd && i + 32 <= n {
                i = scan_tokens_fused_fast(
                    raw,
                    i,
                    num_vars,
                    problem_line_found,
                    &mut lits,
                    &mut clauses_found,
                )?;
            }
            // The fused walk can consume THROUGH the final block and
            // land exactly on `n` (its block loop exits with `i == n`
            // when the buffer ends on a block boundary reached from the
            // re-entry position): hand control back to the loop head,
            // whose `i < n` is the exit.
            if i >= n {
                continue;
            }
            let b = raw[i];
            // Line classification mirrors `DimacsCnf::parse`: a line whose
            // first non-space byte is 'c' is a comment (skipped whole);
            // 'p' opens the problem line; anything else is body.
            if b == b'c' || b == b'p' {
                // Capture the whole line, then classify.
                let start = i;
                while i < n && raw[i] != b'\n' {
                    i += 1;
                }
                let line = std::str::from_utf8(&raw[start..i])
                    .map_err(|_| "Invalid UTF-8 in DIMACS".to_string())?;
                let trimmed = line.trim();
                if trimmed.starts_with('c') {
                    continue; // comment
                }
                if trimmed.starts_with("p cnf") {
                    let parts: Vec<&str> = trimmed.split_whitespace().collect();
                    if parts.len() != 4 {
                        return Err(format!("Invalid problem line: {}", trimmed));
                    }
                    num_vars = parts[2]
                        .parse()
                        .map_err(|_| format!("Invalid number of variables: {}", parts[2]))?;
                    num_clauses_expected = parts[3]
                        .parse()
                        .map_err(|_| format!("Invalid number of clauses: {}", parts[3]))?;
                    problem_line_found = true;
                }
                continue;
            }
            if b.is_ascii_whitespace() {
                i = skip_ws(raw, i, simd);
                continue;
            }
            if !problem_line_found {
                return Err(
                    "Clause found before problem line. Problem line must come first.".to_string(),
                );
            }
            // Literal token: [+-]?digits
            let start = i;
            if b == b'+' || b == b'-' {
                i += 1;
            }
            let ds = i;
            i = scan_digits(raw, i, simd);
            if i == ds {
                let end = (start + 16).min(n);
                return Err(format!(
                    "Invalid literal in clause: {}",
                    String::from_utf8_lossy(&raw[start..end])
                ));
            }
            // Digits are ASCII by the kernel contract, so the token is
            // valid UTF-8; assemble the i32 directly (no from_utf8/
            // str::parse round trip).  `None` is exactly the `str::parse`
            // failure case (magnitude beyond i32 range) — pinned against
            // `str::parse` by `scan_tests::parse_lit_matches_str_parse`.
            let lit = match parse_lit(raw, start, ds, i) {
                Some(lit) => lit,
                None => {
                    return Err(format!(
                        "Invalid literal in clause: {}",
                        String::from_utf8_lossy(&raw[start..i])
                    ));
                }
            };
            if lit == 0 {
                clauses_found += 1;
            } else if lit.unsigned_abs() as usize > num_vars {
                return Err(format!(
                    "Literal {} refers to variable {}, but only {} variables declared",
                    lit,
                    lit.unsigned_abs(),
                    num_vars
                ));
            }
            lits.push(lit);
        }
        if !problem_line_found {
            return Err("No problem line found in DIMACS file".to_string());
        }
        // Unterminated trailing clause: the stream ends with literals but
        // no 0. `lits` being empty or ending in 0 means every literal was
        // terminated.
        if lits.last().is_some_and(|&l| l != 0) {
            return Err("Unterminated clause: literals are missing a trailing 0".to_string());
        }
        if clauses_found != num_clauses_expected {
            return Err(format!(
                "Expected {} clauses but found {}",
                num_clauses_expected, clauses_found
            ));
        }
        Ok(Self {
            num_vars,
            num_clauses: clauses_found,
            lits,
        })
    }
}

/// Runtime gate, cached once; `NIXIE_NO_SIMD=1` opts out (the same
/// pattern as `nixie-sat`'s list-kernel gate).
fn simd_scan_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    #[cfg(target_arch = "x86_64")]
    {
        *ON.get_or_init(|| {
            std::arch::is_x86_feature_detected!("avx2")
                && !std::env::var("NIXIE_NO_SIMD").is_ok_and(|v| v == "1")
        })
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        *ON.get_or_init(|| false)
    }
}

/// Advance `i` past the maximal ASCII-whitespace run starting at `i`
/// (byte-at-a-time reference kernel; exactly `u8::is_ascii_whitespace`:
/// space, `\t`, `\n`, `\x0C`, `\r` — *not* `\x0B`).
#[inline]
fn skip_ws_scalar(raw: &[u8], mut i: usize) -> usize {
    while i < raw.len() && raw[i].is_ascii_whitespace() {
        i += 1;
    }
    i
}

/// Advance `i` past the maximal ASCII-digit run starting at `i`
/// (byte-at-a-time reference kernel).
#[inline]
fn scan_digits_scalar(raw: &[u8], mut i: usize) -> usize {
    while i < raw.len() && raw[i].is_ascii_digit() {
        i += 1;
    }
    i
}

/// Kernel dispatch: `simd` selects the AVX2 boundary kernels when the
/// caller's runtime gate allows (see [`FlatCnf::scan_body`]'s contract).
#[inline]
fn skip_ws(raw: &[u8], i: usize, simd: bool) -> usize {
    if simd {
        skip_ws_fast(raw, i)
    } else {
        skip_ws_scalar(raw, i)
    }
}

/// Kernel dispatch (digits), mirroring [`skip_ws`].
#[inline]
fn scan_digits(raw: &[u8], i: usize, simd: bool) -> usize {
    if simd {
        scan_digits_fast(raw, i)
    } else {
        scan_digits_scalar(raw, i)
    }
}

/// AVX2 whitespace skip: classify 32-byte blocks, jump to the first
/// non-whitespace byte (one load + one tzcnt for typical short gaps);
/// the trailing partial block falls back to the scalar kernel.
///
/// # Safety (caller contract)
///
/// AVX2 must be available at runtime (`is_x86_feature_detected!("avx2")`);
/// the `#[target_feature]` body below must not execute otherwise.
#[cfg(target_arch = "x86_64")]
#[inline]
fn skip_ws_fast(raw: &[u8], i: usize) -> usize {
    // SAFETY: only reached with `simd == true`, which the callers gate on
    // AVX2 runtime detection (the `simd_scan_enabled` OnceLock, or the
    // differential test's own detection check).
    unsafe { skip_ws_avx2(raw, i) }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn skip_ws_avx2(raw: &[u8], mut i: usize) -> usize {
    // SAFETY: AVX2 is caller-contracted (see `skip_ws_fast`); every load is
    // in-bounds by the `i + 32 <= n` cursor bound.
    unsafe {
        use core::arch::x86_64::*;
        while i + 32 <= raw.len() {
            let v = _mm256_loadu_si256(raw.as_ptr().add(i) as *const __m256i);
            // bit set = whitespace byte (the five `is_ascii_whitespace`
            // members — the mask set must match `skip_ws_scalar` exactly).
            let ws = _mm256_or_si256(
                _mm256_or_si256(
                    _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b' ' as i8)),
                    _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b'\t' as i8)),
                ),
                _mm256_or_si256(
                    _mm256_or_si256(
                        _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b'\n' as i8)),
                        _mm256_cmpeq_epi8(v, _mm256_set1_epi8(0x0c)),
                    ),
                    _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b'\r' as i8)),
                ),
            );
            // movemask covers exactly the 32 lanes (a full i32), so `!m`
            // sets a bit precisely at non-whitespace bytes.
            let non_ws = !_mm256_movemask_epi8(ws);
            if non_ws != 0 {
                return i + non_ws.trailing_zeros() as usize;
            }
            i += 32;
        }
    }
    skip_ws_scalar(raw, i)
}

/// Fused-block dispatch (see [`scan_tokens_fused`]); `true`-gated on the
/// same runtime detection as the boundary kernels.
#[cfg(target_arch = "x86_64")]
#[inline]
fn scan_tokens_fused_fast(
    raw: &[u8],
    i: usize,
    num_vars: usize,
    problem_line_found: bool,
    lits: &mut Vec<i32>,
    clauses_found: &mut usize,
) -> Result<usize, String> {
    // SAFETY: only reached with `simd == true` (runtime-gated on AVX2).
    unsafe { scan_tokens_fused(raw, i, num_vars, problem_line_found, lits, clauses_found) }
}

#[cfg(not(target_arch = "x86_64"))]
#[inline]
fn scan_tokens_fused_fast(
    raw: &[u8],
    i: usize,
    _num_vars: usize,
    _problem_line_found: bool,
    _lits: &mut Vec<i32>,
    _clauses_found: &mut usize,
) -> Result<usize, String> {
    Ok(i)
}

/// AVX2 digit-run scan: same blockwise shape as [`skip_ws_fast`]; a byte
/// is a digit iff `v - b'0'` is unsigned `<= 9` (the sub/min/cmpeq trick —
/// wrapping bytes below `b'0'` become large unsigned values and fail).
///
/// # Safety (caller contract)
///
/// AVX2 must be available at runtime, as for [`skip_ws_fast`].
#[cfg(target_arch = "x86_64")]
#[inline]
fn scan_digits_fast(raw: &[u8], i: usize) -> usize {
    // SAFETY: only reached with `simd == true` (runtime-gated on AVX2).
    unsafe { scan_digits_avx2(raw, i) }
}

/// The fused blockwise token walk (the load path's remaining headroom:
/// `FlatCnf::scan_sized` + the two per-token kernels were 57 % of the
/// 531 MB anatomy run; this collapses them to one load + two masks per
/// 32 *bytes*).
///
/// Processes whole 32-byte blocks from `i` while they are fully inside
/// `raw`, walking tokens with mask arithmetic only (no per-token kernel
/// calls, no per-token loads): per block one whitespace mask and one
/// digit mask; per token a `tzcnt` to its start, a `tzcnt` of the
/// inverted digit mask for its run, the shared `parse_lit`, and the same
/// clause/var bookkeeping as the scalar driver.
///
/// Stops (returning that absolute byte position for the scalar driver,
/// which handles the reason and re-enters fused mode on the next loop
/// iteration — progress is guaranteed in every case):
/// * a token whose first byte is `c`/`p` (the line path),
/// * a token touching the block end (its digit run may continue into
///   the next block — the scalar walk finishes it),
/// * the problem line not yet seen (the scalar driver owns that error),
/// * fewer than 32 bytes remaining (the scalar tail).
///
/// # Safety (caller contract)
///
/// AVX2 must be available at runtime, as for the boundary kernels.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn scan_tokens_fused(
    raw: &[u8],
    mut i: usize,
    num_vars: usize,
    problem_line_found: bool,
    lits: &mut Vec<i32>,
    clauses_found: &mut usize,
) -> Result<usize, String> {
    if !problem_line_found {
        return Ok(i);
    }
    let n = raw.len();
    // SAFETY: AVX2 is caller-contracted (see `skip_ws_fast`); every load
    // is in-bounds by the `i + 32 <= n` block bound, every byte access
    // by the same bound plus the in-block positions from 32-bit masks.
    unsafe {
        use core::arch::x86_64::*;
        'blocks: while i + 32 <= n {
            let v = _mm256_loadu_si256(raw.as_ptr().add(i) as *const __m256i);
            let ws = _mm256_or_si256(
                _mm256_or_si256(
                    _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b' ' as i8)),
                    _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b'\t' as i8)),
                ),
                _mm256_or_si256(
                    _mm256_or_si256(
                        _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b'\n' as i8)),
                        _mm256_cmpeq_epi8(v, _mm256_set1_epi8(0x0c)),
                    ),
                    _mm256_cmpeq_epi8(v, _mm256_set1_epi8(b'\r' as i8)),
                ),
            );
            let t = _mm256_sub_epi8(v, _mm256_set1_epi8(b'0' as i8));
            let digits = _mm256_cmpeq_epi8(t, _mm256_min_epu8(t, _mm256_set1_epi8(9)));
            let ws_m = _mm256_movemask_epi8(ws) as u32;
            let digit_m = _mm256_movemask_epi8(digits) as u32;
            // Bit b set: byte b of the block is a non-whitespace token
            // start candidate.  Walked destructively: after each token,
            // the mask shifts past it (separator bits are clear).
            // Both masks live in ONE walked frame: after each token the
            // pair shifts past it in lockstep (a block-relative digit
            // mask under a frame-relative position was the first draft's
            // divergence — every token after the first in a block read
            // the wrong digit bits; caught by the differential harness
            // at randomized iteration 2).
            let mut non_ws = !ws_m;
            let mut digits_m = digit_m;
            if non_ws == 0 {
                i += 32;
                continue 'blocks;
            }
            // `off` accumulates the consumed prefix so token positions
            // stay block-relative in `non_ws`.
            let mut off = 0u32;
            while non_ws != 0 {
                let pos = non_ws.trailing_zeros();
                let abs_start = i + (off + pos) as usize;
                let b = raw[abs_start];
                if b == b'c' || b == b'p' {
                    return Ok(abs_start);
                }
                let has_sign = (b == b'+' || b == b'-') as u32;
                let dstart_rel = pos + has_sign;
                if off + dstart_rel >= 32 {
                    // Sign at the block edge: the digits live in the next
                    // block; let the scalar walk finish this token.
                    return Ok(abs_start);
                }
                let rest = digits_m >> dstart_rel;
                let run = (!rest).trailing_zeros();
                if run == 0 {
                    // Not a digit after the sign/byte: the scalar error,
                    // byte-identical (16-byte context window).
                    let end = (abs_start + 16).min(n);
                    return Err(format!(
                        "Invalid literal in clause: {}",
                        String::from_utf8_lossy(&raw[abs_start..end])
                    ));
                }
                if run == 32 || off + dstart_rel + run >= 32 {
                    // The digit run touches the block end and may
                    // continue into the next block.
                    return Ok(abs_start);
                }
                let ds_abs = i + (off + dstart_rel) as usize;
                let end_abs = ds_abs + run as usize;
                let lit = match parse_lit(raw, abs_start, ds_abs, end_abs) {
                    Some(lit) => lit,
                    None => {
                        return Err(format!(
                            "Invalid literal in clause: {}",
                            String::from_utf8_lossy(&raw[abs_start..end_abs])
                        ));
                    }
                };
                if lit == 0 {
                    *clauses_found += 1;
                } else if lit.unsigned_abs() as usize > num_vars {
                    return Err(format!(
                        "Literal {} refers to variable {}, but only {} variables declared",
                        lit,
                        lit.unsigned_abs(),
                        num_vars
                    ));
                }
                lits.push(lit);
                // Consume the token (sign + digits) from BOTH masks;
                // separator bits between tokens are already clear.
                let shift = dstart_rel + run;
                non_ws >>= shift;
                digits_m >>= shift;
                off += shift;
                if non_ws == 0 {
                    break;
                }
            }
            i += 32;
        }
    }
    Ok(i)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn scan_digits_avx2(raw: &[u8], mut i: usize) -> usize {
    // SAFETY: AVX2 is caller-contracted (see `scan_digits_fast`); every
    // load is in-bounds by the `i + 32 <= n` cursor bound.
    unsafe {
        use core::arch::x86_64::*;
        while i + 32 <= raw.len() {
            let v = _mm256_loadu_si256(raw.as_ptr().add(i) as *const __m256i);
            let t = _mm256_sub_epi8(v, _mm256_set1_epi8(b'0' as i8));
            let digits = _mm256_cmpeq_epi8(t, _mm256_min_epu8(t, _mm256_set1_epi8(9)));
            let non_digits = !_mm256_movemask_epi8(digits);
            if non_digits != 0 {
                return i + non_digits.trailing_zeros() as usize;
            }
            i += 32;
        }
    }
    scan_digits_scalar(raw, i)
}

/// Accumulator freeze point: once the running magnitude exceeds this,
/// one more digit proves the full magnitude exceeds `2_147_483_649`, i.e.
/// beyond every `i32` literal bound — `str::parse::<i32>` would reject the
/// token.  Clamping to the sentinel (kept on every later digit) therefore
/// preserves the accept/reject decision exactly while making unbounded
/// digit runs (arbitrary leading zeros) safe in `u64`.  While unclamped,
/// every accumulated value is exact (≤ `214_748_364 * 10 + 9`), so all
/// valid magnitudes up to `i32::MIN`'s `2147483648` stay exact.
const LIT_ACC_LIMIT: u64 = 214_748_364;
/// Sentinel magnitude: strictly above `2147483649` (the largest exact
/// accumulator value `LIT_ACC_LIMIT * 10 + 9`) and above every accepted
/// magnitude, so a clamped accumulator is always rejected and can never
/// be mistaken for an exact one.
const LIT_ACC_SENTINEL: u64 = 3_000_000_000;

/// Assemble a DIMACS literal from ASCII bytes: `raw[start..ds)` is the
/// optional `+`/`-` sign, `raw[ds..end)` a non-empty ASCII digit run.
///
/// Semantics are exactly `str::parse::<i32>` over the same token
/// (arbitrary leading zeros accepted; `+0`/`-0` are `0`; `i32::MIN`'s
/// magnitude is accepted only with `-`), returning `None` precisely
/// where the `str` parse fails.  Equivalence is pinned by
/// `scan_tests::parse_lit_matches_str_parse`.
#[inline]
fn parse_lit(raw: &[u8], start: usize, ds: usize, end: usize) -> Option<i32> {
    let neg = raw[start] == b'-';
    let mut acc: u64 = 0;
    for &d in &raw[ds..end] {
        if acc <= LIT_ACC_LIMIT {
            acc = acc * 10 + u64::from(d - b'0');
        } else {
            acc = LIT_ACC_SENTINEL;
        }
    }
    if neg {
        if acc > 2147483648 {
            return None;
        }
        if acc == 2147483648 {
            return Some(i32::MIN); // -2147483648: the one wide negative
        }
        Some(-(acc as i32))
    } else {
        if acc > i32::MAX as u64 {
            return None;
        }
        Some(acc as i32)
    }
}

#[cfg(test)]
mod scan_tests {
    use super::*;

    /// Test-side twin of `simd_scan_enabled`'s detection half: the
    /// differential harness compares the SIMD path against the scalar
    /// reference whenever the hardware can actually run it.
    fn have_avx2() -> bool {
        #[cfg(target_arch = "x86_64")]
        {
            std::arch::is_x86_feature_detected!("avx2")
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            false
        }
    }

    /// Differential oracle: scalar reference vs SIMD kernels must agree
    /// on the full result — including the exact error message.  On
    /// hardware without AVX2 the SIMD leg degenerates to the scalar path
    /// (the safety contract forbids executing the kernels undetected).
    fn assert_paths_agree(raw: &[u8]) {
        let scalar = FlatCnf::scan_body(raw, false);
        let simd = FlatCnf::scan_body(raw, have_avx2());
        assert_eq!(
            scalar, simd,
            "scalar and SIMD scan disagree on input {raw:?}"
        );
    }

    #[test]
    fn parse_lit_matches_str_parse() {
        // Deterministic boundary magnitudes (around i32::MAX, i32::MIN,
        // and the accumulator freeze point) plus arbitrary leading zeros.
        let magnitudes = [
            0u64,
            1,
            9,
            10,
            99,
            214748364,
            2147483646,
            2147483647,
            2147483648,
            2147483649,
            2147483650,
            3_000_000_000,
            4_294_967_295,
        ];
        let mut tokens: Vec<String> = Vec::new();
        for &m in &magnitudes {
            tokens.push(m.to_string());
            tokens.push(format!("+{m}"));
            tokens.push(format!("-{m}"));
            // Leading zeros must not change acceptance (str::parse skips
            // them; the accumulator must stay exact through them).
            tokens.push(format!("0{m}"));
            tokens.push(format!("-000{m}"));
            tokens.push(format!("00000000000000000000{m}"));
        }
        tokens.push("00000000000000000000000000000".to_string()); // all zeros
        tokens.push("99999999999999999999999999999".to_string()); // wide, nonzero
        tokens.push("-99999999999999999999999999999".to_string());
        for tok in &tokens {
            let bytes = tok.as_bytes();
            let start = 0;
            let ds = matches!(bytes[0], b'+' | b'-') as usize;
            let got = parse_lit(bytes, start, ds, bytes.len());
            let want = tok.parse::<i32>().ok();
            assert_eq!(
                got, want,
                "parse_lit({tok:?}) = {got:?} but str::parse = {want:?}"
            );
        }
    }

    #[test]
    fn scan_paths_agree_deterministic() {
        // Well-formed basics.
        assert_paths_agree(b"p cnf 2 2\n1 2 0\n-1 -2 0\n");
        assert_paths_agree(b"c comment\np cnf 1 1\n1 0\n");
        assert_paths_agree(b"p cnf 1 1\n0\n"); // empty clause
        assert_paths_agree(b"p cnf 3 1\n1 -2\n3 0\n"); // clause across lines
        assert_paths_agree(b"p cnf 3 2\n1 2 0 3 0\n"); // two clauses one line
        assert_paths_agree(b"p cnf 2 2\n+1 -0 0\n007 0\n"); // signs, -0, leading zeros
        // Every whitespace member (and the excluded \x0B) as separator.
        assert_paths_agree(b"p cnf 2 2\x201\x09-2\x0c0\x0a\x0d1 0\n");
        // Malformed: the error paths must stay reachable and identical.
        assert_paths_agree(b"1 -2 0\n"); // clause before problem line
        assert_paths_agree(b"p cnf 2 1\n1 3 0\n"); // var beyond declared count
        assert_paths_agree(b"p cnf 2 1\n1 2\n"); // unterminated
        assert_paths_agree(b"p cnf 2 2\n1 2 0\n"); // clause count mismatch
        assert_paths_agree(b"p cnf 2 1\nx 0\n"); // non-digit token
        assert_paths_agree(b"p cnf 2 1\n- 0\n"); // lone sign
        assert_paths_agree(b"p cnf 2 1\n--5 0\n");
        assert_paths_agree(b"p cnf 2 1\n999999999999 0\n"); // i32 overflow
        assert_paths_agree(b"p cnf 2 1\n-999999999999 0\n");
        assert_paths_agree(b"p cnf 2 1\n2147483648 0\n"); // i32::MAX + 1
        assert_paths_agree(b"p cnf 2 1\n-2147483648 0\n"); // i32::MIN, valid
        assert_paths_agree(b"p cnf 2 1\n2147483649 0\n");
        assert_paths_agree(b"p cnf\n"); // truncated problem line
        assert_paths_agree(b"p cnf x y\n1 0\n");
        assert_paths_agree(b""); // empty file
        assert_paths_agree(b"p cnf 2 1\n"); // declared but absent clause
        assert_paths_agree(b"p cnf 2 1\n1 2 c3 0\n"); // 'c' swallows rest of line
        assert_paths_agree(b"p cnf 2 1\n1 p 2 0\n"); // 'p' line skipped silently
        assert_paths_agree(b"p cnf 2 1\n1 2 0 c\xa0\n"); // invalid UTF-8 comment
        assert_paths_agree(b"p cnf 2 1\n1 2 0\nc"); // comment, no newline at EOF
        assert_paths_agree(b"p cnf 2 1\n1 2 0"); // no newline after last clause
        assert_paths_agree(b"p cnf 2 1\n1 2 0 \t \r \x0c \n"); // ws tail at EOF
    }

    #[test]
    fn scan_paths_agree_at_block_boundaries() {
        // The AVX2 kernels decide in 32-byte blocks; every token/whitespace
        // arrangement around a block edge must agree with the scalar walk.
        for pad in 0..96usize {
            // Token starting exactly at each offset near the edges.
            let body = format!(
                "p cnf 9 2\n{}1 -2 0\n{}34 0\n",
                " ".repeat(pad),
                " ".repeat(pad)
            );
            assert_paths_agree(body.as_bytes());
        }
        // Whitespace runs crossing block edges (length 30..=66).
        for ws_len in 28..=68usize {
            for ws in [" ", "\t", "\n", "\r\n", " \t\x0c "] {
                let sep = ws.repeat(ws_len / ws.len() + 1);
                let body = format!("p cnf 9 1\n1{sep}2{sep}3{sep}0\n");
                assert_paths_agree(body.as_bytes());
            }
        }
        // Digit runs crossing block edges: leading zeros make long runs.
        for zeros in [28usize, 29, 30, 31, 32, 33, 34, 63, 64, 65, 100] {
            let body = format!("p cnf 9 1\n{}5 0\n", "0".repeat(zeros));
            assert_paths_agree(body.as_bytes());
        }
        // Exact multiples of 32 for the whole buffer (tail-path coverage).
        for total in [0usize, 1, 31, 32, 33, 63, 64, 65, 95, 96, 97, 128, 160] {
            let mut body = String::from("p cnf 9 1\n1 0\n");
            while body.len() < total {
                body.push(' ');
            }
            body.truncate(total);
            assert_paths_agree(body.as_bytes());
        }
        // Digit run ending exactly at EOF (no terminator after it).
        for tail in [
            "5".to_string(),
            "55".to_string(),
            "0".repeat(31) + "5",
            "0".repeat(32) + "5",
        ] {
            let body = format!("p cnf 9 1\n1 0\n{tail}");
            assert_paths_agree(body.as_bytes());
        }
        // All-digit final block (the all-32-digits advance branch).
        let all_digits = "1".repeat(96);
        let body = format!("p cnf 9 1\n{all_digits}");
        assert_paths_agree(body.as_bytes());
        // All-whitespace tail blocks (the all-32-ws advance branch).
        assert_paths_agree(b"p cnf 9 1\n1 0\n                              \n");
    }

    #[test]
    fn scan_paths_agree_randomized() {
        // Deterministic xorshift64* — no external RNG so the corpus is
        // reproducible from the seed alone.
        let mut state: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let gen_case = |next: &mut dyn FnMut() -> u64| -> Vec<u8> {
            let mode = next() % 4;
            let mut out: Vec<u8> = Vec::new();
            match mode {
                0 => {
                    // Structured CNF: header, random small clauses.
                    out.extend_from_slice(b"p cnf 64 200\n");
                    for _ in 0..200 {
                        let len = next() % 5;
                        for _ in 0..=len {
                            let v = (next() % 64) as i64 + 1;
                            let lit = if next().is_multiple_of(2) { v } else { -v };
                            out.extend_from_slice(lit.to_string().as_bytes());
                            out.push(b' ');
                        }
                        out.extend_from_slice(b"0\n");
                    }
                }
                1 => {
                    // Header plus random byte soup (malformed-heavy).
                    out.extend_from_slice(b"p cnf 999 5\n");
                    for _ in 0..(next() % 4096) {
                        out.push((next() % 256) as u8);
                    }
                }
                2 => {
                    // Random tokens from a hostile alphabet.
                    let alphabet: Vec<u8> = b"0123456789-+ cpcnf\t\n\r\x0c[]%$@\xC3\xA0".to_vec();
                    out.extend_from_slice(b"p cnf 50 1\n");
                    for _ in 0..(next() % 512) {
                        out.push(alphabet[(next() % alphabet.len() as u64) as usize]);
                    }
                }
                _ => {
                    // No header at all (exercises the early-error paths).
                    for _ in 0..(next() % 256) {
                        out.push(b"0123456789 -+c\n"[(next() % 14) as usize]);
                    }
                }
            }
            out
        };
        for iter in 0..3000 {
            let case = gen_case(&mut next);
            let scalar = FlatCnf::scan_body(&case, false);
            let simd = FlatCnf::scan_body(&case, have_avx2());
            assert_eq!(scalar, simd, "iteration {iter} diverged on {case:?}");
        }
    }
}
