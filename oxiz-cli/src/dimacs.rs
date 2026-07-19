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
