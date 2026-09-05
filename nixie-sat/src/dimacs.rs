//! DIMACS CNF format parser and writer
//!
//! DIMACS CNF is the standard format for SAT problems.
//! Format:
//! - Comments start with 'c'
//! - Problem line: p cnf <num_vars> <num_clauses>
//! - Clause lines: space-separated literals ending with 0
//! - Positive literal i represents variable i, negative -i represents NOT i

use crate::literal::{Lit, Var};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::{Solver, SolverResult};
use core::fmt;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::Path;

/// Error type for DIMACS parsing
#[derive(Debug)]
pub enum DimacsError {
    /// I/O error
    Io(io::Error),
    /// Parse error
    Parse(String),
    /// Invalid problem line
    InvalidProblem,
    /// Literal out of range
    LiteralOutOfRange(i32),
}

impl fmt::Display for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => write!(f, "I/O error: {e}"),
            Self::Parse(msg) => write!(f, "Parse error: {msg}"),
            Self::InvalidProblem => write!(f, "Invalid problem line"),
            Self::LiteralOutOfRange(lit) => write!(f, "Literal out of range: {lit}"),
        }
    }
}

impl core::error::Error for DimacsError {}

impl From<io::Error> for DimacsError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

/// Default upper bound on the variable count accepted from a `p cnf` header.
///
/// The header value is attacker-controlled and is used to eagerly allocate
/// per-variable state (`Solver::ensure_vars`), so an unbounded value turns a
/// tiny file such as `p cnf 999999999999 1` into an effectively infinite loop
/// and OOM. `2^31` both fits the `u32` variable index space and caps the eager
/// allocation. Callers needing more can raise it with
/// [`DimacsParser::set_max_vars`].
pub const DEFAULT_MAX_VARS: usize = 1 << 31;

/// DIMACS CNF parser
pub struct DimacsParser {
    num_vars: usize,
    num_clauses: usize,
    max_vars: usize,
}

impl DimacsParser {
    /// Create a new DIMACS parser
    #[must_use]
    pub fn new() -> Self {
        Self {
            num_vars: 0,
            num_clauses: 0,
            max_vars: DEFAULT_MAX_VARS,
        }
    }

    /// Set the maximum accepted variable count from the `p cnf` header.
    ///
    /// A header declaring more than this many variables is rejected with
    /// [`DimacsError::InvalidProblem`] instead of triggering an unbounded
    /// allocation. Values above `u32::MAX` are clamped to `u32::MAX` because
    /// variable indices must fit in a `u32`.
    pub fn set_max_vars(&mut self, max_vars: usize) {
        self.max_vars = max_vars.min(u32::MAX as usize);
    }

    /// Parse a DIMACS file and load into solver
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or parsed
    pub fn parse_file<P: AsRef<Path>>(
        &mut self,
        path: P,
        solver: &mut Solver,
    ) -> Result<(), DimacsError> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        self.parse_reader(reader, solver)
    }

    /// Parse from a reader
    ///
    /// Byte-level scanning: the whole input is read once and tokens are
    /// parsed by hand (`[+-]?digits`) instead of `str::parse::<i32>` per
    /// whitespace-split token. Semantics are identical to the previous
    /// line/token version, including its quirks (a line whose first
    /// non-space character is `c` is skipped *entirely*, `%` ends parsing,
    /// a token that is not a valid `i32` is an error naming that token).
    ///
    /// # Errors
    ///
    /// Returns an error if parsing fails
    pub fn parse_reader<R: BufRead>(
        &mut self,
        mut reader: R,
        solver: &mut Solver,
    ) -> Result<(), DimacsError> {
        let mut current_clause = Vec::new();
        let mut _clauses_read = 0;

        // Chunked window (1 MiB reads + partial-line carry). Reading the
        // whole file into one buffer first (the previous shape) is faster
        // by a hair, but freeing that whole-file mmap raises glibc's
        // dynamic mmap threshold to the file size — every later
        // sub-file-size transient (walk rounds, occurrence lists, lucky
        // snapshots) then allocates from the main heap and stays resident
        // after free, which measured as a ~170 MB permanent RSS floor on
        // clause-dense instances. Scanning line-complete chunks keeps the
        // threshold at its 128 KiB default so those transients stay
        // mmap-backed and return on drop. Tokens never span lines, so
        // carrying the partial tail line to the next window preserves the
        // token stream exactly.
        const CHUNK: usize = 1 << 20;
        let mut window: Vec<u8> = Vec::with_capacity(2 * CHUNK);
        let mut chunk = vec![0u8; CHUNK];
        let mut eof = false;

        // Token scan state: `tok_start..i` is the pending token when
        // `in_token` is set. Tokens never span lines, so the line-oriented
        // classification below sees the same token stream as the previous
        // `split_whitespace` version.
        let mut in_token = false;
        let mut tok_start = 0usize;
        let mut line_has_content = false; // seen a non-whitespace byte this line

        #[inline]
        fn parse_i32(token: &str) -> Option<i32> {
            let neg = token.starts_with('-');
            let digits = token.strip_prefix(['+', '-']).unwrap_or(token);
            if digits.is_empty() {
                return None;
            }
            let mut acc: i64 = 0;
            for b in digits.bytes() {
                if !b.is_ascii_digit() {
                    return None;
                }
                acc = acc * 10 + i64::from(b - b'0');
                if acc > i32::MAX as i64 + 1 {
                    return None;
                }
            }
            let v = if neg { -acc } else { acc };
            if v < i32::MIN as i64 || v > i32::MAX as i64 {
                return None;
            }
            Some(v as i32)
        }

        let mut i = 0usize;
        // Prime the first window (short reads are fine — only line-complete
        // prefixes are scanned).
        {
            let n = reader.read(&mut chunk)?;
            if n == 0 {
                eof = true;
            } else {
                window.extend_from_slice(&chunk[..n]);
            }
        }
        let mut text: &str = core::str::from_utf8(&window)
            .map_err(|e| DimacsError::Io(io::Error::new(io::ErrorKind::InvalidData, e)))?;
        let mut bytes: &[u8] = text.as_bytes();
        let mut limit: usize = if eof {
            bytes.len()
        } else {
            bytes.iter().rposition(|&b| b == b'\n').map_or(0, |p| p + 1)
        };
        'chunks: while i <= limit {
            // End of the line-complete prefix (or an initially line-less
            // window): carry the partial tail forward and refill. At EOF
            // the whole window is scannable, with a synthetic final
            // newline for a trailing partial line — exactly the
            // whole-buffer version's end-of-input behaviour.
            if i == limit && !eof {
                window.copy_within(limit.., 0);
                window.truncate(window.len() - limit);
                let n = reader.read(&mut chunk)?;
                if n == 0 {
                    eof = true;
                } else {
                    window.extend_from_slice(&chunk[..n]);
                }
                text = core::str::from_utf8(&window)
                    .map_err(|e| DimacsError::Io(io::Error::new(io::ErrorKind::InvalidData, e)))?;
                bytes = text.as_bytes();
                limit = if eof {
                    bytes.len()
                } else {
                    match bytes.iter().rposition(|&b| b == b'\n') {
                        Some(p) => p + 1,
                        // No complete line in the window yet (>1 MiB line):
                        // keep reading.
                        None => 0,
                    }
                };
                i = 0;
                continue 'chunks;
            }
            let at_end = eof && i == limit;
            let b = if at_end { b'\n' } else { bytes[i] };

            if at_end || b == b'\n' {
                // End of line: flush any pending token first.
                if in_token {
                    let token = &text[tok_start..i];
                    match parse_i32(token) {
                        Some(0) => {
                            solver.add_clause(current_clause.iter().copied());
                            current_clause.clear();
                            _clauses_read += 1;
                        }
                        Some(v) => {
                            let lit = self.dimacs_to_lit(v)?;
                            current_clause.push(lit);
                        }
                        None => {
                            return Err(DimacsError::Parse(format!("Invalid literal: {token}")));
                        }
                    }
                    in_token = false;
                }
                if at_end {
                    break 'chunks;
                }
                // Line-level classification happens on the FIRST content byte
                // of a line; a directive byte consumed it already.
                if !line_has_content {
                    i += 1;
                    continue;
                }
                line_has_content = false;
                i += 1;
                continue;
            }

            let is_space = matches!(b, b' ' | b'\t' | b'\r' | b'\x0b' | b'\x0c');
            if is_space {
                if in_token {
                    let token = &text[tok_start..i];
                    match parse_i32(token) {
                        Some(0) => {
                            solver.add_clause(current_clause.iter().copied());
                            current_clause.clear();
                            _clauses_read += 1;
                        }
                        Some(v) => {
                            let lit = self.dimacs_to_lit(v)?;
                            current_clause.push(lit);
                        }
                        None => {
                            return Err(DimacsError::Parse(format!("Invalid literal: {token}")));
                        }
                    }
                    in_token = false;
                }
                i += 1;
                continue;
            }

            if !line_has_content && !in_token {
                // First non-space byte of a line: check the line directives
                // exactly like the line-based parser did.
                line_has_content = true;
                match b {
                    b'c' => {
                        // Skip the remainder of this line entirely.
                        while i < limit && bytes[i] != b'\n' {
                            i += 1;
                        }
                        line_has_content = false;
                        continue;
                    }
                    b'%' => break 'chunks,
                    b'p' => {
                        // Collect the rest of the line and hand it to the
                        // problem-line parser.
                        let start = i;
                        while i < limit && bytes[i] != b'\n' {
                            i += 1;
                        }
                        let line = &text[start..i];
                        self.parse_problem_line(line.trim_end())?;
                        solver.ensure_vars(self.num_vars);
                        line_has_content = false;
                        continue;
                    }
                    _ => {}
                }
            }

            if !in_token {
                in_token = true;
                tok_start = i;
            }
            i += 1;
        }

        // Handle case where last clause doesn't end with 0
        if !current_clause.is_empty() {
            solver.add_clause(current_clause.iter().copied());
            _clauses_read += 1;
        }

        // Verify we read the expected number of clauses
        #[cfg(feature = "analyze-debug")]
        if self.num_clauses > 0 && _clauses_read != self.num_clauses {
            eprintln!(
                "Warning: Expected {} clauses but read {}",
                self.num_clauses, _clauses_read
            );
        }

        Ok(())
    }

    /// Parse the problem line: p cnf <num_vars> <num_clauses>
    fn parse_problem_line(&mut self, line: &str) -> Result<(), DimacsError> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() != 4 || parts[0] != "p" || parts[1] != "cnf" {
            return Err(DimacsError::InvalidProblem);
        }

        self.num_vars = parts[2]
            .parse()
            .map_err(|_| DimacsError::Parse("Invalid number of variables".to_string()))?;
        self.num_clauses = parts[3]
            .parse()
            .map_err(|_| DimacsError::Parse("Invalid number of clauses".to_string()))?;

        // Reject an adversarial variable count before it is handed to
        // `Solver::ensure_vars`, which would otherwise allocate per-variable
        // state in a loop (hang / OOM). Variable indices must also fit in a
        // `u32`, so `max_vars` never exceeds `u32::MAX`.
        if self.num_vars > self.max_vars {
            return Err(DimacsError::InvalidProblem);
        }

        Ok(())
    }

    /// Convert DIMACS literal (1-indexed, negative for negation) to internal Lit
    fn dimacs_to_lit(&self, dimacs_lit: i32) -> Result<Lit, DimacsError> {
        if dimacs_lit == 0 {
            return Err(DimacsError::Parse("Literal cannot be 0".to_string()));
        }

        let abs_val = dimacs_lit.unsigned_abs();
        if abs_val as usize > self.num_vars {
            return Err(DimacsError::LiteralOutOfRange(dimacs_lit));
        }

        // DIMACS uses 1-indexed variables, we use 0-indexed
        let var = Var::new(abs_val - 1);
        Ok(if dimacs_lit > 0 {
            Lit::pos(var)
        } else {
            Lit::neg(var)
        })
    }

    /// Get number of variables
    #[must_use]
    pub const fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Get number of clauses
    #[must_use]
    pub const fn num_clauses(&self) -> usize {
        self.num_clauses
    }
}

impl Default for DimacsParser {
    fn default() -> Self {
        Self::new()
    }
}

/// DIMACS CNF writer
pub struct DimacsWriter;

impl DimacsWriter {
    /// Write a SAT problem to a file in DIMACS format
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be written
    pub fn write_cnf<P: AsRef<Path>>(
        path: P,
        num_vars: usize,
        clauses: &[Vec<Lit>],
    ) -> Result<(), DimacsError> {
        let mut file = File::create(path)?;
        Self::write_cnf_to(&mut file, num_vars, clauses)
    }

    /// Write CNF to a writer
    ///
    /// # Errors
    ///
    /// Returns an error if writing fails
    pub fn write_cnf_to<W: Write>(
        writer: &mut W,
        num_vars: usize,
        clauses: &[Vec<Lit>],
    ) -> Result<(), DimacsError> {
        // Write header
        writeln!(writer, "c DIMACS CNF")?;
        writeln!(writer, "p cnf {} {}", num_vars, clauses.len())?;

        // Write clauses
        for clause in clauses {
            for &lit in clause {
                write!(writer, "{} ", Self::lit_to_dimacs(lit))?;
            }
            writeln!(writer, "0")?;
        }

        Ok(())
    }

    /// Write a model (satisfying assignment) to a file
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be written
    pub fn write_model<P: AsRef<Path>>(
        path: P,
        solver: &Solver,
        result: SolverResult,
    ) -> Result<(), DimacsError> {
        let mut file = File::create(path)?;
        Self::write_model_to(&mut file, solver, result)
    }

    /// Write model to a writer
    ///
    /// # Errors
    ///
    /// Returns an error if writing fails
    pub fn write_model_to<W: Write>(
        writer: &mut W,
        solver: &Solver,
        result: SolverResult,
    ) -> Result<(), DimacsError> {
        use crate::literal::LBool;

        match result {
            SolverResult::Sat => {
                writeln!(writer, "s SATISFIABLE")?;
                write!(writer, "v ")?;
                for i in 0..solver.num_vars() {
                    let var = Var::new(i as u32);
                    let value = solver.model_value(var);
                    let dimacs_lit = if value == LBool::True {
                        (i + 1) as i32
                    } else {
                        -((i + 1) as i32)
                    };
                    write!(writer, "{dimacs_lit} ")?;
                }
                writeln!(writer, "0")?;
            }
            SolverResult::Unsat => {
                writeln!(writer, "s UNSATISFIABLE")?;
            }
            SolverResult::Unknown => {
                writeln!(writer, "s UNKNOWN")?;
            }
        }
        Ok(())
    }

    /// Convert internal Lit to DIMACS literal
    fn lit_to_dimacs(lit: Lit) -> i32 {
        let var_index = lit.var().index() as i32;
        if lit.is_pos() {
            var_index + 1
        } else {
            -(var_index + 1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_cnf() {
        let cnf = "c Simple test\n\
                   p cnf 3 2\n\
                   1 -3 0\n\
                   2 3 -1 0\n";

        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();

        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("test operation should succeed");

        assert_eq!(parser.num_vars(), 3);
        assert_eq!(parser.num_clauses(), 2);
    }

    #[test]
    fn test_parse_with_comments() {
        let cnf = "c This is a comment\n\
                   c Another comment\n\
                   p cnf 2 1\n\
                   c Comment in the middle\n\
                   1 2 0\n";

        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();

        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("test operation should succeed");

        assert_eq!(parser.num_vars(), 2);
        assert_eq!(parser.num_clauses(), 1);
    }

    #[test]
    fn test_write_cnf() {
        let mut buffer = Vec::new();
        let clauses = vec![
            vec![Lit::pos(Var::new(0)), Lit::neg(Var::new(2))],
            vec![
                Lit::pos(Var::new(1)),
                Lit::pos(Var::new(2)),
                Lit::neg(Var::new(0)),
            ],
        ];

        DimacsWriter::write_cnf_to(&mut buffer, 3, &clauses)
            .expect("test operation should succeed");

        let output = String::from_utf8(buffer).expect("test operation should succeed");
        assert!(output.contains("p cnf 3 2"));
        assert!(output.contains("1 -3 0"));
        assert!(output.contains("2 3 -1 0"));
    }

    #[test]
    fn test_roundtrip() {
        // Create a simple formula
        let original_clauses = vec![
            vec![Lit::pos(Var::new(0)), Lit::neg(Var::new(1))],
            vec![Lit::pos(Var::new(1)), Lit::neg(Var::new(2))],
            vec![Lit::pos(Var::new(2)), Lit::neg(Var::new(0))],
        ];

        // Write to buffer
        let mut buffer = Vec::new();
        DimacsWriter::write_cnf_to(&mut buffer, 3, &original_clauses)
            .expect("test operation should succeed");

        // Parse back
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(buffer.as_slice(), &mut solver)
            .expect("test operation should succeed");

        assert_eq!(parser.num_vars(), 3);
        assert_eq!(parser.num_clauses(), 3);
    }

    // Regression: an empty clause (a lone `0`, as in cadical's
    // test/cnf/false.cnf = `p cnf 0 1` / `0`) is the unsatisfiable unit and must
    // be handed to the solver. The parser previously guarded clause emission
    // with `!current_clause.is_empty()`, silently dropping empty clauses so
    // this file parsed as clause-free and solved as SAT instead of UNSAT.
    #[test]
    fn test_parse_empty_clause_is_unsat() {
        let cnf = "p cnf 0 1\n0\n";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("test operation should succeed");
        assert_eq!(solver.solve(), SolverResult::Unsat);
    }

    // An empty clause embedded among ordinary clauses must still flip a
    // satisfiable formula to UNSAT (guards against the parser only handling a
    // trailing empty clause).
    #[test]
    fn test_parse_empty_clause_in_middle_is_unsat() {
        // (x1) ∧ (empty) – satisfiable by x1=true except for the empty clause.
        let cnf = "p cnf 1 2\n1 0\n0\n";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("test operation should succeed");
        assert_eq!(solver.solve(), SolverResult::Unsat);
    }

    // Byte-scanner parity with the previous line/token parser on the awkward
    // shapes that motivated its quirks.
    #[test]
    fn test_parse_crlf_and_tabs() {
        let cnf = "c comment\r\np cnf 2 2\r\n1\t-2 0\r\n-1 2 0\r\n";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("CRLF input parses");
        assert_eq!(parser.num_clauses(), 2);
    }

    #[test]
    fn test_parse_no_trailing_newline() {
        let cnf = "p cnf 2 1\n1 2 0";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("input without final newline parses");
        assert_eq!(parser.num_clauses(), 1);
    }

    #[test]
    fn test_parse_percent_stops() {
        // SATLIB-style trailing garbage after `%` is ignored.
        let cnf = "p cnf 2 1\n1 2 0\n%\n0\n";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("% terminates parsing");
        assert_eq!(parser.num_clauses(), 1);
    }

    #[test]
    fn test_parse_plus_sign_literal() {
        let cnf = "p cnf 1 1\n+1 0";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("leading + accepted like i32::from_str");
        assert_eq!(parser.num_clauses(), 1);
    }

    #[test]
    fn test_parse_invalid_token_is_error() {
        let cnf = "p cnf 2 1\n1 x 0";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        let err = parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect_err("invalid token rejected");
        assert!(
            matches!(err, DimacsError::Parse(ref msg) if msg.contains('x')),
            "error names the offending token: {err:?}"
        );
    }

    #[test]
    fn test_parse_bare_digits_are_literals() {
        // Regression: an early draft of the byte scanner stripped a sign
        // prefix via `strip_prefix('+').or_else(|| strip_prefix('-'))`, whose
        // `None` fallthrough made every plain digit token fail to parse.
        let cnf = "p cnf 3 1\n1 -2 3 0";
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();
        parser
            .parse_reader(cnf.as_bytes(), &mut solver)
            .expect("plain digit tokens parse");
        assert_eq!(parser.num_vars(), 3);
    }
}
