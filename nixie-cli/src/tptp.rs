//! TPTP (Thousands of Problems for Theorem Provers) format parser and converter
//!
//! TPTP is a standard format for representing first-order logic problems.
//! This module supports the FOF (First-Order Formula) sublanguage.
//!
//! Format specification:
//! - fof declarations: `fof(name, role, formula).`
//! - Roles: axiom, hypothesis, conjecture, negated_conjecture
//! - Formulas: & (and), | (or), ~ (not), => (implies), <=> (iff), ! (forall), ? (exists)
//! - Terms: constants (lowercase), variables (uppercase), functions

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io::BufRead;

/// TPTP formula role
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TptpRole {
    /// Axiom - assumed to be true
    Axiom,
    /// Hypothesis - assumed for the problem
    Hypothesis,
    /// Conjecture - to be proven
    Conjecture,
    /// Negated conjecture - negation of conjecture (for refutation)
    NegatedConjecture,
    /// Lemma
    Lemma,
    /// Definition
    Definition,
    /// Type declaration
    Type,
    /// Unknown/other role
    Unknown,
}

impl TptpRole {
    /// Parse role from string
    fn from_str(s: &str) -> Self {
        match s.trim().to_lowercase().as_str() {
            "axiom" => TptpRole::Axiom,
            "hypothesis" => TptpRole::Hypothesis,
            "conjecture" => TptpRole::Conjecture,
            "negated_conjecture" => TptpRole::NegatedConjecture,
            "lemma" => TptpRole::Lemma,
            "definition" => TptpRole::Definition,
            "type" => TptpRole::Type,
            _ => TptpRole::Unknown,
        }
    }
}

impl fmt::Display for TptpRole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TptpRole::Axiom => write!(f, "axiom"),
            TptpRole::Hypothesis => write!(f, "hypothesis"),
            TptpRole::Conjecture => write!(f, "conjecture"),
            TptpRole::NegatedConjecture => write!(f, "negated_conjecture"),
            TptpRole::Lemma => write!(f, "lemma"),
            TptpRole::Definition => write!(f, "definition"),
            TptpRole::Type => write!(f, "type"),
            TptpRole::Unknown => write!(f, "unknown"),
        }
    }
}

/// TPTP term (constant, variable, or function application)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TptpTerm {
    /// Variable (uppercase identifier)
    Variable(String),
    /// Constant (lowercase identifier)
    Constant(String),
    /// Function application
    Function(String, Vec<TptpTerm>),
}

#[allow(dead_code)]
impl TptpTerm {
    /// Check if this term is a variable
    pub fn is_variable(&self) -> bool {
        matches!(self, TptpTerm::Variable(_))
    }

    /// Get all variables in this term.
    ///
    /// Iterative (explicit heap stack): `f(f(f(...)))` nesting comes straight
    /// from an attacker-supplied `.p` file, and `-> ()` leaves nowhere to report
    /// a truncated walk.
    fn collect_variables(&self, vars: &mut HashSet<String>) {
        let mut stack: Vec<&TptpTerm> = vec![self];

        while let Some(term) = stack.pop() {
            match term {
                TptpTerm::Variable(name) => {
                    vars.insert(name.clone());
                }
                TptpTerm::Constant(_) => {}
                TptpTerm::Function(_, args) => stack.extend(args.iter()),
            }
        }
    }

    /// Convert to SMT-LIB2 term.
    ///
    /// Iterative (explicit heap stack); output is byte-identical to the
    /// recursive formulation.
    fn to_smtlib2(&self) -> String {
        let mut out = String::new();
        let mut stack = vec![TermEmit::Term(self)];

        while let Some(task) = stack.pop() {
            let term = match task {
                TermEmit::Text(text) => {
                    out.push_str(text);
                    continue;
                }
                TermEmit::Term(term) => term,
            };

            match term {
                TptpTerm::Variable(name) | TptpTerm::Constant(name) => out.push_str(name),
                TptpTerm::Function(name, args) => {
                    if args.is_empty() {
                        out.push_str(name);
                    } else {
                        out.push('(');
                        out.push_str(name);
                        stack.push(TermEmit::Text(")"));
                        for arg in args.iter().rev() {
                            stack.push(TermEmit::Term(arg));
                            stack.push(TermEmit::Text(" "));
                        }
                    }
                }
            }
        }

        out
    }
}

/// Work item for the iterative [`TptpTerm::to_smtlib2`] serializer.
enum TermEmit<'a> {
    /// Serialize this subterm.
    Term(&'a TptpTerm),
    /// Emit a structural token verbatim.
    Text(&'static str),
}

/// Maximum nesting accepted by the TPTP formula and term parsers.
///
/// The parsers themselves are iterative, so this is not a stack guard for the
/// parse: it bounds the *depth of the resulting AST*, which is still walked
/// recursively by the compiler-generated `Drop`, `Clone`, `Debug` and
/// `PartialEq` impls of [`TptpFormula`] and [`TptpTerm`]. A `.p` file is
/// untrusted input auto-detected by extension, so the bound is enforced through
/// the parsers' existing `Result<_, String>` channel rather than left to
/// whichever of those walks runs first – a recursive drop firing after the
/// parse has already returned would abort the process with no diagnostic at
/// all. Matches `MAX_PARSE_DEPTH` in nixie-core's SMT-LIB term parser.
const MAX_TPTP_DEPTH: usize = 1024;

/// Continuation-stack budget corresponding to [`MAX_TPTP_DEPTH`].
///
/// The formula parser pushes up to four continuations per grammar level
/// (`iff -> implies -> or -> and`), plus one for each `~` or quantifier prefix.
const MAX_TPTP_CONTINUATIONS: usize = MAX_TPTP_DEPTH * 4;

/// A pending step of the iterative formula parser: what still has to happen
/// once the operand currently being read is complete.
///
/// Each variant corresponds to one rung of the recursive-descent ladder this
/// replaces (`iff -> implies -> or -> and -> unary -> atomic`), with its
/// partially-accumulated state carried explicitly instead of living in a call
/// frame.
enum FormulaCont {
    /// Iff chain (`<=>` / `<~>`), left-associative.
    Iff {
        /// Accumulated left side and whether the pending operator was `<~>`.
        pending: Option<(TptpFormula, bool)>,
    },
    /// Implication level: `None` while reading the left operand, `Some` while
    /// reading the right operand of `=>` (`reversed == false`) or `<=`
    /// (`reversed == true`).
    Implies {
        /// The already-parsed side, once an implication operator was seen.
        left: Option<(TptpFormula, bool)>,
    },
    /// Disjunction chain (`|`).
    Or {
        /// Operands read so far.
        operands: Vec<TptpFormula>,
    },
    /// Conjunction chain (`&`).
    And {
        /// Operands read so far.
        operands: Vec<TptpFormula>,
    },
    /// A `~` awaiting its operand.
    Not,
    /// A quantifier prefix awaiting its body.
    Quantify {
        /// True for `!` (forall), false for `?` (exists).
        universal: bool,
        /// The bound variables.
        vars: Vec<String>,
    },
    /// An open `(` at atomic level awaiting its `)`.
    CloseParen,
}

/// Work item for the iterative `TptpFormula::to_smtlib2` serializer.
enum FormulaEmit<'a> {
    /// Serialize this subformula.
    Formula(&'a TptpFormula),
    /// Emit a pre-rendered token verbatim.
    Text(String),
}

/// TPTP formula
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TptpFormula {
    /// Atomic formula (predicate application)
    Atom(String, Vec<TptpTerm>),
    /// Equality
    Equality(TptpTerm, TptpTerm),
    /// Inequality
    Inequality(TptpTerm, TptpTerm),
    /// Negation
    Not(Box<TptpFormula>),
    /// Conjunction
    And(Vec<TptpFormula>),
    /// Disjunction
    Or(Vec<TptpFormula>),
    /// Implication
    Implies(Box<TptpFormula>, Box<TptpFormula>),
    /// Equivalence (iff)
    Iff(Box<TptpFormula>, Box<TptpFormula>),
    /// Universal quantification
    Forall(Vec<String>, Box<TptpFormula>),
    /// Existential quantification
    Exists(Vec<String>, Box<TptpFormula>),
    /// True constant
    True,
    /// False constant
    False,
}

impl TptpFormula {
    /// Get all free variables in this formula
    fn free_variables(&self) -> HashSet<String> {
        let mut free = HashSet::new();
        self.collect_free_variables(&mut free, &HashSet::new());
        free
    }

    /// Iterative (explicit heap stack) free-variable collection.
    ///
    /// The set of bound variables in scope is kept in a side table indexed per
    /// frame, so it is cloned only where the recursive version cloned it: on
    /// entering a quantifier.
    fn collect_free_variables(&self, free: &mut HashSet<String>, bound: &HashSet<String>) {
        // Scope 0 is the caller's `bound` set; quantifiers append new scopes.
        let mut scopes: Vec<HashSet<String>> = vec![bound.clone()];
        let mut stack: Vec<(&TptpFormula, usize)> = vec![(self, 0)];

        while let Some((formula, scope)) = stack.pop() {
            match formula {
                TptpFormula::Atom(_, args) => {
                    for arg in args {
                        let mut term_vars = HashSet::new();
                        arg.collect_variables(&mut term_vars);
                        for v in term_vars {
                            if !scopes.get(scope).is_some_and(|s| s.contains(&v)) {
                                free.insert(v);
                            }
                        }
                    }
                }
                TptpFormula::Equality(t1, t2) | TptpFormula::Inequality(t1, t2) => {
                    let mut term_vars = HashSet::new();
                    t1.collect_variables(&mut term_vars);
                    t2.collect_variables(&mut term_vars);
                    for v in term_vars {
                        if !scopes.get(scope).is_some_and(|s| s.contains(&v)) {
                            free.insert(v);
                        }
                    }
                }
                TptpFormula::Not(f) => stack.push((f, scope)),
                TptpFormula::And(fs) | TptpFormula::Or(fs) => {
                    stack.extend(fs.iter().map(|f| (f, scope)));
                }
                TptpFormula::Implies(f1, f2) | TptpFormula::Iff(f1, f2) => {
                    stack.push((f1, scope));
                    stack.push((f2, scope));
                }
                TptpFormula::Forall(vars, f) | TptpFormula::Exists(vars, f) => {
                    let mut new_bound = scopes.get(scope).cloned().unwrap_or_default();
                    for v in vars {
                        new_bound.insert(v.clone());
                    }
                    scopes.push(new_bound);
                    let new_scope = scopes.len() - 1;
                    stack.push((f, new_scope));
                }
                TptpFormula::True | TptpFormula::False => {}
            }
        }
    }

    /// Get all predicates used in this formula with their arities.
    ///
    /// Iterative (explicit heap stack); see [`TptpTerm::collect_variables`].
    fn collect_predicates(&self, predicates: &mut HashMap<String, usize>) {
        let mut stack: Vec<&TptpFormula> = vec![self];

        while let Some(formula) = stack.pop() {
            match formula {
                TptpFormula::Atom(name, args) => {
                    predicates.insert(name.clone(), args.len());
                }
                TptpFormula::Equality(_, _) | TptpFormula::Inequality(_, _) => {}
                TptpFormula::Not(f) => stack.push(f),
                TptpFormula::And(fs) | TptpFormula::Or(fs) => stack.extend(fs.iter()),
                TptpFormula::Implies(f1, f2) | TptpFormula::Iff(f1, f2) => {
                    stack.push(f1);
                    stack.push(f2);
                }
                TptpFormula::Forall(_, f) | TptpFormula::Exists(_, f) => stack.push(f),
                TptpFormula::True | TptpFormula::False => {}
            }
        }
    }

    /// Get all functions used in this formula with their arities.
    ///
    /// Iterative (explicit heap stack); see [`TptpTerm::collect_variables`].
    fn collect_functions(&self, functions: &mut HashMap<String, usize>) {
        let mut stack: Vec<&TptpFormula> = vec![self];

        while let Some(formula) = stack.pop() {
            match formula {
                TptpFormula::Atom(_, args) => {
                    for arg in args {
                        Self::collect_functions_from_term(arg, functions);
                    }
                }
                TptpFormula::Equality(t1, t2) | TptpFormula::Inequality(t1, t2) => {
                    Self::collect_functions_from_term(t1, functions);
                    Self::collect_functions_from_term(t2, functions);
                }
                TptpFormula::Not(f) => stack.push(f),
                TptpFormula::And(fs) | TptpFormula::Or(fs) => stack.extend(fs.iter()),
                TptpFormula::Implies(f1, f2) | TptpFormula::Iff(f1, f2) => {
                    stack.push(f1);
                    stack.push(f2);
                }
                TptpFormula::Forall(_, f) | TptpFormula::Exists(_, f) => stack.push(f),
                TptpFormula::True | TptpFormula::False => {}
            }
        }
    }

    /// Iterative (explicit heap stack) function-symbol collection over a term.
    fn collect_functions_from_term(term: &TptpTerm, functions: &mut HashMap<String, usize>) {
        let mut stack: Vec<&TptpTerm> = vec![term];

        while let Some(current) = stack.pop() {
            match current {
                TptpTerm::Variable(_) => {}
                TptpTerm::Constant(name) => {
                    functions.entry(name.clone()).or_insert(0);
                }
                TptpTerm::Function(name, args) => {
                    functions.insert(name.clone(), args.len());
                    stack.extend(args.iter());
                }
            }
        }
    }

    /// Convert to SMT-LIB2 formula string.
    ///
    /// Iterative (explicit heap stack): formula nesting is fully controlled by
    /// the `.p` file and `-> String` has no channel through which a depth cap
    /// could report truncation – a truncated formula here would be handed to the
    /// solver as if it were the real problem. Output is byte-identical to the
    /// recursive formulation.
    fn to_smtlib2(&self) -> String {
        let mut out = String::new();
        let mut stack = vec![FormulaEmit::Formula(self)];

        while let Some(task) = stack.pop() {
            let formula = match task {
                FormulaEmit::Text(text) => {
                    out.push_str(&text);
                    continue;
                }
                FormulaEmit::Formula(formula) => formula,
            };

            match formula {
                TptpFormula::Atom(name, args) => {
                    if args.is_empty() {
                        out.push_str(name);
                    } else {
                        let args_str: Vec<String> = args.iter().map(TptpTerm::to_smtlib2).collect();
                        out.push_str(&format!("({} {})", name, args_str.join(" ")));
                    }
                }
                TptpFormula::Equality(t1, t2) => {
                    out.push_str(&format!("(= {} {})", t1.to_smtlib2(), t2.to_smtlib2()));
                }
                TptpFormula::Inequality(t1, t2) => {
                    out.push_str(&format!(
                        "(not (= {} {}))",
                        t1.to_smtlib2(),
                        t2.to_smtlib2()
                    ));
                }
                TptpFormula::Not(f) => {
                    out.push_str("(not ");
                    stack.push(FormulaEmit::Text(")".to_string()));
                    stack.push(FormulaEmit::Formula(f));
                }
                TptpFormula::And(fs) | TptpFormula::Or(fs) => {
                    let (empty, head) = if matches!(formula, TptpFormula::And(_)) {
                        ("true", "(and")
                    } else {
                        ("false", "(or")
                    };
                    match fs.split_first() {
                        None => out.push_str(empty),
                        Some((only, [])) => {
                            stack.push(FormulaEmit::Formula(only));
                        }
                        Some(_) => {
                            out.push_str(head);
                            stack.push(FormulaEmit::Text(")".to_string()));
                            for f in fs.iter().rev() {
                                stack.push(FormulaEmit::Formula(f));
                                stack.push(FormulaEmit::Text(" ".to_string()));
                            }
                        }
                    }
                }
                TptpFormula::Implies(f1, f2) | TptpFormula::Iff(f1, f2) => {
                    let head = if matches!(formula, TptpFormula::Implies(..)) {
                        "(=> "
                    } else {
                        "(= "
                    };
                    out.push_str(head);
                    stack.push(FormulaEmit::Text(")".to_string()));
                    stack.push(FormulaEmit::Formula(f2));
                    stack.push(FormulaEmit::Text(" ".to_string()));
                    stack.push(FormulaEmit::Formula(f1));
                }
                TptpFormula::Forall(vars, f) | TptpFormula::Exists(vars, f) => {
                    let head = if matches!(formula, TptpFormula::Forall(..)) {
                        "forall"
                    } else {
                        "exists"
                    };
                    let bindings: Vec<String> = vars.iter().map(|v| format!("({} U)", v)).collect();
                    out.push_str(&format!("({} ({}) ", head, bindings.join(" ")));
                    stack.push(FormulaEmit::Text(")".to_string()));
                    stack.push(FormulaEmit::Formula(f));
                }
                TptpFormula::True => out.push_str("true"),
                TptpFormula::False => out.push_str("false"),
            }
        }

        out
    }

    /// Convert to SMT-LIB2, universally closing over this formula's own
    /// free variables (`(forall ((V U) ...) <formula>)`).
    ///
    /// Per the TPTP standard, a variable free in an FOF formula is
    /// implicitly universally quantified from the outside -- `axiom(X):
    /// p(X)` means `axiom: forall X. p(X)`, not "p holds for some
    /// particular X". This must be used for every role except the
    /// (negated) conjecture, whose free variables are instead legitimately
    /// Skolemizable (see [`TptpProblem::to_smtlib2`]).
    fn to_smtlib2_closed(&self) -> String {
        let mut free: Vec<String> = self.free_variables().into_iter().collect();
        let body = self.to_smtlib2();
        if free.is_empty() {
            return body;
        }
        // Sort for deterministic output.
        free.sort();
        let bindings: Vec<String> = free.iter().map(|v| format!("({} U)", v)).collect();
        format!("(forall ({}) {})", bindings.join(" "), body)
    }
}

/// A single TPTP statement (fof declaration)
#[derive(Debug, Clone)]
pub struct TptpStatement {
    /// Name of the formula
    pub name: String,
    /// Role of the formula
    pub role: TptpRole,
    /// The formula itself
    pub formula: TptpFormula,
}

/// TPTP problem (collection of statements)
#[derive(Debug, Clone)]
pub struct TptpProblem {
    /// All statements in the problem
    pub statements: Vec<TptpStatement>,
    /// Comments from the file
    pub comments: Vec<String>,
}

/// TPTP parser
pub struct TptpParser {
    input: Vec<char>,
    pos: usize,
}

impl TptpParser {
    /// Create a new parser for the given input
    pub fn new(input: &str) -> Self {
        TptpParser {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    /// Parse a TPTP problem from a reader
    pub fn parse_reader<R: BufRead>(reader: R) -> Result<TptpProblem, String> {
        let mut input = String::new();
        for line in reader.lines() {
            let line = line.map_err(|e| format!("Failed to read line: {}", e))?;
            input.push_str(&line);
            input.push('\n');
        }
        let mut parser = TptpParser::new(&input);
        parser.parse_problem()
    }

    /// Parse the entire TPTP problem
    pub fn parse_problem(&mut self) -> Result<TptpProblem, String> {
        let mut statements = Vec::new();
        let mut comments = Vec::new();

        while self.pos < self.input.len() {
            self.skip_whitespace();
            if self.pos >= self.input.len() {
                break;
            }

            // Check for comment
            if self.peek() == Some('%') {
                let comment = self.parse_line_comment();
                comments.push(comment);
                continue;
            }

            // Check for block comment
            if self.peek() == Some('/') && self.peek_ahead(1) == Some('*') {
                let comment = self.parse_block_comment()?;
                comments.push(comment);
                continue;
            }

            // Try to parse an fof statement
            if self.try_consume("fof") || self.try_consume("cnf") {
                let stmt = self.parse_statement()?;
                statements.push(stmt);
            } else if self.try_consume("include") {
                // Skip include statements for now
                self.skip_until('.');
                self.consume_char('.')?;
            } else if self.pos < self.input.len() {
                // Unknown content, try to skip
                self.pos += 1;
            }
        }

        Ok(TptpProblem {
            statements,
            comments,
        })
    }

    /// Parse a single fof statement
    fn parse_statement(&mut self) -> Result<TptpStatement, String> {
        self.skip_whitespace();
        self.consume_char('(')?;
        self.skip_whitespace();

        // Parse name
        let name = self.parse_identifier()?;
        self.skip_whitespace();
        self.consume_char(',')?;
        self.skip_whitespace();

        // Parse role
        let role_str = self.parse_identifier()?;
        let role = TptpRole::from_str(&role_str);
        self.skip_whitespace();
        self.consume_char(',')?;
        self.skip_whitespace();

        // Parse formula
        let formula = self.parse_formula()?;
        self.skip_whitespace();

        // Optional annotations
        if self.peek() == Some(',') {
            self.consume_char(',')?;
            self.skip_annotations()?;
        }

        self.skip_whitespace();
        self.consume_char(')')?;
        self.skip_whitespace();
        self.consume_char('.')?;

        Ok(TptpStatement {
            name,
            role,
            formula,
        })
    }

    /// Parse a formula.
    ///
    /// Iterative pushdown parser (explicit heap stack of pending
    /// continuations). The recursive-descent ladder this replaces cost roughly
    /// seven call frames per parenthesis level and one per `~`, over input that
    /// is an untrusted `.p` file auto-detected by extension and parsed on a
    /// rayon worker thread with a ~2 MiB stack – so a depth cap large enough to
    /// be useful could never have fired there. Grammar, associativity and error
    /// messages are unchanged.
    fn parse_formula(&mut self) -> Result<TptpFormula, String> {
        let mut conts: Vec<FormulaCont> = Vec::new();
        Self::push_formula_levels(&mut conts);

        'descend: loop {
            if conts.len() > MAX_TPTP_CONTINUATIONS {
                return Err(format!(
                    "formula nesting exceeds the maximum supported depth of {MAX_TPTP_DEPTH}"
                ));
            }
            // ======== prefix operators, then an atomic formula ========
            let mut value = loop {
                // Checked here as well as at `'descend`: a run of `~` or
                // quantifier prefixes grows the continuation stack without
                // completing an operand.
                if conts.len() > MAX_TPTP_CONTINUATIONS {
                    return Err(format!(
                        "formula nesting exceeds the maximum supported depth of {MAX_TPTP_DEPTH}"
                    ));
                }

                self.skip_whitespace();

                // Negation
                if self.try_consume("~") {
                    self.skip_whitespace();
                    conts.push(FormulaCont::Not);
                    continue;
                }

                // Universal quantifier
                if self.try_consume("!") {
                    let vars = self.parse_quantifier_vars()?;
                    conts.push(FormulaCont::Quantify {
                        universal: true,
                        vars,
                    });
                    continue;
                }

                // Existential quantifier
                if self.try_consume("?") {
                    let vars = self.parse_quantifier_vars()?;
                    conts.push(FormulaCont::Quantify {
                        universal: false,
                        vars,
                    });
                    continue;
                }

                self.skip_whitespace();

                // Check for true/false
                if self.try_consume("$true") {
                    break TptpFormula::True;
                }
                if self.try_consume("$false") {
                    break TptpFormula::False;
                }

                // Check for parenthesized formula
                if self.peek() == Some('(') {
                    self.consume_char('(')?;
                    conts.push(FormulaCont::CloseParen);
                    Self::push_formula_levels(&mut conts);
                    continue;
                }

                break self.parse_atomic_relation()?;
            };

            // ======== fold the completed value through the pending continuations ========
            loop {
                let Some(cont) = conts.pop() else {
                    return Ok(value);
                };

                match cont {
                    FormulaCont::Not => value = TptpFormula::Not(Box::new(value)),
                    FormulaCont::Quantify { universal, vars } => {
                        value = if universal {
                            TptpFormula::Forall(vars, Box::new(value))
                        } else {
                            TptpFormula::Exists(vars, Box::new(value))
                        };
                    }
                    FormulaCont::CloseParen => {
                        self.skip_whitespace();
                        self.consume_char(')')?;
                    }
                    FormulaCont::And { mut operands } => {
                        operands.push(value);
                        self.skip_whitespace();
                        if self.try_consume("&") {
                            self.skip_whitespace();
                            conts.push(FormulaCont::And { operands });
                            continue 'descend;
                        }
                        value = Self::collapse(operands, TptpFormula::And);
                    }
                    FormulaCont::Or { mut operands } => {
                        operands.push(value);
                        self.skip_whitespace();
                        if self.try_consume("|") {
                            self.skip_whitespace();
                            conts.push(FormulaCont::Or { operands });
                            conts.push(FormulaCont::And {
                                operands: Vec::new(),
                            });
                            continue 'descend;
                        }
                        value = Self::collapse(operands, TptpFormula::Or);
                    }
                    FormulaCont::Implies { left: None } => {
                        let left = value;
                        self.skip_whitespace();

                        if self.try_consume("=>") {
                            self.skip_whitespace();
                            conts.push(FormulaCont::Implies {
                                left: Some((left, false)),
                            });
                            Self::push_implies_levels(&mut conts);
                            continue 'descend;
                        }

                        if self.peek() == Some('<') {
                            // Check for reverse implies (<=) but not <=> or <~>
                            let next_chars: String =
                                self.input[self.pos..].iter().take(3).collect();
                            if next_chars.starts_with("<=")
                                && !next_chars.starts_with("<=>")
                                && !next_chars.starts_with("<~>")
                            {
                                self.try_consume("<=");
                                self.skip_whitespace();
                                conts.push(FormulaCont::Implies {
                                    left: Some((left, true)),
                                });
                                Self::push_implies_levels(&mut conts);
                                continue 'descend;
                            }
                        }

                        value = left;
                    }
                    FormulaCont::Implies {
                        left: Some((left, reversed)),
                    } => {
                        value = if reversed {
                            TptpFormula::Implies(Box::new(value), Box::new(left))
                        } else {
                            TptpFormula::Implies(Box::new(left), Box::new(value))
                        };
                    }
                    FormulaCont::Iff { pending } => {
                        let combined = match pending {
                            None => value,
                            Some((left, xor)) => {
                                let iff = TptpFormula::Iff(Box::new(left), Box::new(value));
                                if xor {
                                    TptpFormula::Not(Box::new(iff))
                                } else {
                                    iff
                                }
                            }
                        };

                        self.skip_whitespace();
                        let next_xor = if self.try_consume("<=>") {
                            Some(false)
                        } else if self.try_consume("<~>") {
                            // XOR (not iff)
                            Some(true)
                        } else {
                            None
                        };

                        if let Some(xor) = next_xor {
                            self.skip_whitespace();
                            conts.push(FormulaCont::Iff {
                                pending: Some((combined, xor)),
                            });
                            Self::push_implies_levels(&mut conts);
                            continue 'descend;
                        }

                        value = combined;
                    }
                }
            }
        }
    }

    /// Schedule the full `iff -> implies -> or -> and` descent for the next
    /// operand.
    fn push_formula_levels(conts: &mut Vec<FormulaCont>) {
        conts.push(FormulaCont::Iff { pending: None });
        Self::push_implies_levels(conts);
    }

    /// Schedule an `implies -> or -> and` descent (the right-hand side of an
    /// implication, and each operand of an iff chain).
    fn push_implies_levels(conts: &mut Vec<FormulaCont>) {
        conts.push(FormulaCont::Implies { left: None });
        conts.push(FormulaCont::Or {
            operands: Vec::new(),
        });
        conts.push(FormulaCont::And {
            operands: Vec::new(),
        });
    }

    /// A single operand stays as-is; several become an n-ary connective.
    fn collapse(
        operands: Vec<TptpFormula>,
        build: fn(Vec<TptpFormula>) -> TptpFormula,
    ) -> TptpFormula {
        if operands.len() == 1 {
            // Safety: len() == 1 ensures next() succeeds, use into_iter for no-unwrap policy
            operands.into_iter().next().unwrap_or(TptpFormula::True)
        } else {
            build(operands)
        }
    }

    /// Parse the `[X, Y, ...]:` prefix of a quantified formula, returning the
    /// bound variables. The body is parsed by the caller's continuation.
    fn parse_quantifier_vars(&mut self) -> Result<Vec<String>, String> {
        self.skip_whitespace();
        self.consume_char('[')?;
        self.skip_whitespace();

        let mut vars = Vec::new();
        loop {
            let var = self.parse_variable()?;
            vars.push(var);
            self.skip_whitespace();

            // Optional type annotation - only if next char is ':' and not followed by ']'
            // This distinguishes between `[X:Type]` (typed) and `[X]` (untyped)
            if self.peek() == Some(':') && self.pos + 1 < self.input.len() {
                // Look ahead to check if this is a type annotation or body separator
                // Type annotation: [X:Type] or [X : Type]
                // Body separator: [X]: formula
                let next_non_ws = self.input[self.pos + 1..]
                    .iter()
                    .find(|&&c| !c.is_whitespace());
                if next_non_ws != Some(&']') && next_non_ws != Some(&'(') {
                    self.try_consume(":");
                    self.skip_whitespace();
                    let _type = self.parse_identifier()?;
                    self.skip_whitespace();
                }
            }

            if self.try_consume(",") {
                self.skip_whitespace();
            } else {
                break;
            }
        }

        self.consume_char(']')?;
        self.skip_whitespace();
        // Body separator - may or may not have ':'
        self.try_consume(":");
        self.skip_whitespace();

        Ok(vars)
    }

    /// Parse the term-level part of an atomic formula: a term, optionally
    /// followed by `=` or `!=` and a second term.
    fn parse_atomic_relation(&mut self) -> Result<TptpFormula, String> {
        // Parse term or predicate
        let first_term = self.parse_term()?;

        self.skip_whitespace();

        // Check for equality/inequality
        // Note: Must check != before =, and must not consume = if it's part of => or <=>
        if self.try_consume("!=") {
            self.skip_whitespace();
            let second_term = self.parse_term()?;
            return Ok(TptpFormula::Inequality(first_term, second_term));
        }

        // Check for = but not => or <=>
        if self.peek() == Some('=') {
            // Look ahead to make sure it's not => or part of <=>
            let next_char = if self.pos + 1 < self.input.len() {
                Some(self.input[self.pos + 1])
            } else {
                None
            };
            if next_char != Some('>') {
                self.try_consume("=");
                self.skip_whitespace();
                let second_term = self.parse_term()?;
                return Ok(TptpFormula::Equality(first_term, second_term));
            }
        }

        // Convert term to atom
        match first_term {
            TptpTerm::Function(name, args) => Ok(TptpFormula::Atom(name, args)),
            TptpTerm::Constant(name) | TptpTerm::Variable(name) => {
                Ok(TptpFormula::Atom(name, vec![]))
            }
        }
    }

    /// Parse a term.
    ///
    /// Iterative (explicit heap stack): `f(f(f(...)))` nesting is bounded only
    /// by the input file. Grammar and error messages are unchanged.
    fn parse_term(&mut self) -> Result<TptpTerm, String> {
        // Function applications whose argument list is still being read.
        let mut pending: Vec<(String, Vec<TptpTerm>)> = Vec::new();

        'read: loop {
            if pending.len() > MAX_TPTP_DEPTH {
                return Err(format!(
                    "term nesting exceeds the maximum supported depth of {MAX_TPTP_DEPTH}"
                ));
            }
            self.skip_whitespace();

            let name = self.parse_identifier()?;

            self.skip_whitespace();

            // Check for function application
            let mut value = if self.peek() == Some('(') {
                self.consume_char('(')?;
                self.skip_whitespace();

                if self.peek() != Some(')') {
                    pending.push((name, Vec::new()));
                    continue 'read;
                }

                self.consume_char(')')?;
                TptpTerm::Function(name, Vec::new())
            } else if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                // Variable (uppercase)
                TptpTerm::Variable(name)
            } else {
                // Constant (lowercase)
                TptpTerm::Constant(name)
            };

            loop {
                let Some((fn_name, mut args)) = pending.pop() else {
                    return Ok(value);
                };

                args.push(value);
                self.skip_whitespace();

                if self.try_consume(",") {
                    self.skip_whitespace();
                    pending.push((fn_name, args));
                    continue 'read;
                }

                self.consume_char(')')?;
                value = TptpTerm::Function(fn_name, args);
            }
        }
    }

    /// Parse a variable (must start with uppercase)
    fn parse_variable(&mut self) -> Result<String, String> {
        let name = self.parse_identifier()?;
        if name.chars().next().is_some_and(|c| c.is_uppercase()) {
            Ok(name)
        } else {
            Err(format!("Expected variable (uppercase), found '{}'", name))
        }
    }

    /// Parse an identifier
    fn parse_identifier(&mut self) -> Result<String, String> {
        self.skip_whitespace();

        let mut name = String::new();

        // Handle quoted identifiers
        if self.peek() == Some('\'') {
            self.consume_char('\'')?;
            while let Some(c) = self.peek() {
                if c == '\'' {
                    self.consume_char('\'')?;
                    break;
                }
                name.push(c);
                self.pos += 1;
            }
            return Ok(name);
        }

        // Handle regular identifiers
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' || c == '$' {
                name.push(c);
                self.pos += 1;
            } else {
                break;
            }
        }

        if name.is_empty() {
            Err(format!(
                "Expected identifier at position {}, found {:?}",
                self.pos,
                self.peek()
            ))
        } else {
            Ok(name)
        }
    }

    /// Parse a line comment (starting with %)
    fn parse_line_comment(&mut self) -> String {
        let mut comment = String::new();
        self.pos += 1; // Skip %

        while let Some(c) = self.peek() {
            if c == '\n' {
                self.pos += 1;
                break;
            }
            comment.push(c);
            self.pos += 1;
        }

        comment.trim().to_string()
    }

    /// Parse a block comment (/* ... */)
    fn parse_block_comment(&mut self) -> Result<String, String> {
        let mut comment = String::new();
        self.pos += 2; // Skip /*

        while self.pos + 1 < self.input.len() {
            if self.peek() == Some('*') && self.peek_ahead(1) == Some('/') {
                self.pos += 2;
                break;
            }
            if let Some(c) = self.peek() {
                comment.push(c);
            }
            self.pos += 1;
        }

        Ok(comment.trim().to_string())
    }

    /// Skip annotations (after formula in parentheses)
    fn skip_annotations(&mut self) -> Result<(), String> {
        let mut depth = 0;
        while let Some(c) = self.peek() {
            match c {
                '(' | '[' => {
                    depth += 1;
                    self.pos += 1;
                }
                ')' | ']' => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                    self.pos += 1;
                }
                _ => self.pos += 1,
            }
        }
        Ok(())
    }

    /// Skip until a specific character
    fn skip_until(&mut self, target: char) {
        while let Some(c) = self.peek() {
            if c == target {
                break;
            }
            self.pos += 1;
        }
    }

    /// Skip whitespace
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    /// Peek at current character
    fn peek(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    /// Peek ahead by n characters
    fn peek_ahead(&self, n: usize) -> Option<char> {
        self.input.get(self.pos + n).copied()
    }

    /// Try to consume a string
    fn try_consume(&mut self, s: &str) -> bool {
        let chars: Vec<char> = s.chars().collect();
        if self.pos + chars.len() <= self.input.len() {
            for (i, c) in chars.iter().enumerate() {
                if self.input[self.pos + i] != *c {
                    return false;
                }
            }
            self.pos += chars.len();
            true
        } else {
            false
        }
    }

    /// Consume a specific character
    fn consume_char(&mut self, expected: char) -> Result<(), String> {
        if self.peek() == Some(expected) {
            self.pos += 1;
            Ok(())
        } else {
            Err(format!(
                "Expected '{}' at position {}, found {:?}",
                expected,
                self.pos,
                self.peek()
            ))
        }
    }
}

#[allow(dead_code)]
impl TptpProblem {
    /// Parse a TPTP problem from a string
    pub fn parse(input: &str) -> Result<Self, String> {
        let mut parser = TptpParser::new(input);
        parser.parse_problem()
    }

    /// Convert the TPTP problem to SMT-LIB2 format
    ///
    /// # Free variables
    ///
    /// Per the TPTP standard, a variable free in an FOF formula is
    /// implicitly universally quantified: `axiom(ax1, axiom, p(X))` means
    /// `forall X. p(X)`, not "p holds for some particular X". Declaring `X`
    /// as a global constant and asserting the open formula `p(x0)` (as this
    /// function used to do for every role) is a *weaker* statement than the
    /// intended axiom -- a refutation that genuinely needs the universally
    /// quantified axiom can then come out satisfiable, so a `Theorem` could
    /// be misreported as `CounterSatisfiable`.
    ///
    /// The one legitimate exception is the (negated) conjecture: negating
    /// `forall X. P(X)` gives `exists X. not P(X)`, and Skolemizing that
    /// existential -- picking an arbitrary fresh witness constant for `X`
    /// -- is sound for a satisfiability-preserving refutation check. So
    /// only conjecture/negated-conjecture free variables are declared as
    /// constants; every other role's formula is closed with an explicit
    /// `forall` over its own free variables instead (see
    /// [`TptpFormula::to_smtlib2_closed`]).
    pub fn to_smtlib2(&self) -> String {
        let mut output = String::new();

        // Collect all predicates and functions
        let mut predicates: HashMap<String, usize> = HashMap::new();
        let mut functions: HashMap<String, usize> = HashMap::new();
        // Only the (negated) conjecture's free variables are Skolemized as
        // global constants; see the doc comment above.
        let mut skolem_vars: HashSet<String> = HashSet::new();

        for stmt in &self.statements {
            stmt.formula.collect_predicates(&mut predicates);
            stmt.formula.collect_functions(&mut functions);
            if matches!(
                stmt.role,
                TptpRole::Conjecture | TptpRole::NegatedConjecture
            ) {
                skolem_vars.extend(stmt.formula.free_variables());
            }
        }

        // Set logic (use UF for uninterpreted functions)
        output.push_str("(set-logic UF)\n\n");

        // Add comments
        for comment in &self.comments {
            output.push_str(&format!("; {}\n", comment));
        }
        if !self.comments.is_empty() {
            output.push('\n');
        }

        // Declare the universal sort U
        output.push_str("(declare-sort U 0)\n\n");

        // Declare all functions (constants have arity 0)
        for (name, arity) in &functions {
            if *arity == 0 {
                output.push_str(&format!("(declare-const {} U)\n", name));
            } else {
                let args: Vec<&str> = (0..*arity).map(|_| "U").collect();
                output.push_str(&format!("(declare-fun {} ({}) U)\n", name, args.join(" ")));
            }
        }

        // Declare the (negated) conjecture's free variables as Skolem
        // constants -- see the doc comment on `to_smtlib2` for why this is
        // only sound for that role.
        for var in &skolem_vars {
            output.push_str(&format!("(declare-const {} U)\n", var));
        }

        if !functions.is_empty() || !skolem_vars.is_empty() {
            output.push('\n');
        }

        // Declare all predicates
        for (name, arity) in &predicates {
            if *arity == 0 {
                output.push_str(&format!("(declare-const {} Bool)\n", name));
            } else {
                let args: Vec<&str> = (0..*arity).map(|_| "U").collect();
                output.push_str(&format!(
                    "(declare-fun {} ({}) Bool)\n",
                    name,
                    args.join(" ")
                ));
            }
        }

        if !predicates.is_empty() {
            output.push('\n');
        }

        // Add assertions
        let mut has_conjecture = false;

        for stmt in &self.statements {
            // Conjecture/negated-conjecture free variables are Skolem
            // constants declared above, so the formula is used as-is; every
            // other role's free variables must instead be universally
            // closed (see the doc comment on `to_smtlib2`).
            let formula_str = match stmt.role {
                TptpRole::Conjecture | TptpRole::NegatedConjecture => stmt.formula.to_smtlib2(),
                _ => stmt.formula.to_smtlib2_closed(),
            };

            match stmt.role {
                TptpRole::Conjecture => {
                    // For refutation-based proving, we negate the conjecture
                    output.push_str(&format!(
                        "; {} ({})\n(assert (not {}))\n\n",
                        stmt.name, stmt.role, formula_str
                    ));
                    has_conjecture = true;
                }
                TptpRole::NegatedConjecture => {
                    // Already negated
                    output.push_str(&format!(
                        "; {} ({})\n(assert {})\n\n",
                        stmt.name, stmt.role, formula_str
                    ));
                    has_conjecture = true;
                }
                _ => {
                    output.push_str(&format!(
                        "; {} ({})\n(assert {})\n\n",
                        stmt.name, stmt.role, formula_str
                    ));
                }
            }
        }

        // Add check-sat
        output.push_str("(check-sat)\n");

        // Add comment about interpretation
        if has_conjecture {
            output.push_str("; If unsat, the conjecture is a theorem\n");
            output.push_str("; If sat, the conjecture has a counter-example\n");
        }

        output
    }

    /// Check if the problem has a conjecture
    pub fn has_conjecture(&self) -> bool {
        self.statements
            .iter()
            .any(|s| matches!(s.role, TptpRole::Conjecture | TptpRole::NegatedConjecture))
    }
}

/// SZS status codes for TPTP output
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum SzsStatus {
    /// The conjecture is a theorem (proven)
    Theorem,
    /// The conjecture is not a theorem (counter-satisfiable)
    CounterSatisfiable,
    /// The problem is satisfiable (no conjecture)
    Satisfiable,
    /// The problem is unsatisfiable (no conjecture)
    Unsatisfiable,
    /// Unknown result
    Unknown,
    /// Timeout
    Timeout,
    /// Error
    Error,
    /// Resource out (memory, etc.)
    ResourceOut,
    /// Given up
    GaveUp,
}

impl fmt::Display for SzsStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SzsStatus::Theorem => write!(f, "Theorem"),
            SzsStatus::CounterSatisfiable => write!(f, "CounterSatisfiable"),
            SzsStatus::Satisfiable => write!(f, "Satisfiable"),
            SzsStatus::Unsatisfiable => write!(f, "Unsatisfiable"),
            SzsStatus::Unknown => write!(f, "Unknown"),
            SzsStatus::Timeout => write!(f, "Timeout"),
            SzsStatus::Error => write!(f, "Error"),
            SzsStatus::ResourceOut => write!(f, "ResourceOut"),
            SzsStatus::GaveUp => write!(f, "GaveUp"),
        }
    }
}

/// Format SMT-LIB2 result as TPTP SZS status
pub fn format_tptp_result(smtlib_result: &str, has_conjecture: bool) -> String {
    let status = if smtlib_result.contains("unsat") {
        if has_conjecture {
            SzsStatus::Theorem
        } else {
            SzsStatus::Unsatisfiable
        }
    } else if smtlib_result.contains("sat") && !smtlib_result.contains("unsat") {
        if has_conjecture {
            SzsStatus::CounterSatisfiable
        } else {
            SzsStatus::Satisfiable
        }
    } else if smtlib_result.contains("timeout") {
        SzsStatus::Timeout
    } else if smtlib_result.contains("error") {
        SzsStatus::Error
    } else {
        SzsStatus::Unknown
    };

    format!("% SZS status {}", status)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_fof() {
        let input = r#"
            fof(ax1, axiom, ![X]: (human(X) => mortal(X))).
            fof(ax2, axiom, human(socrates)).
            fof(conj, conjecture, mortal(socrates)).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        assert_eq!(problem.statements.len(), 3);
        assert_eq!(problem.statements[0].role, TptpRole::Axiom);
        assert_eq!(problem.statements[1].role, TptpRole::Axiom);
        assert_eq!(problem.statements[2].role, TptpRole::Conjecture);
    }

    #[test]
    fn test_parse_complex_formula() {
        let input = r#"
            fof(test, axiom, ![X,Y]: ((p(X) & q(Y)) => r(X,Y))).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        assert_eq!(problem.statements.len(), 1);
    }

    #[test]
    fn test_parse_equality() {
        let input = r#"
            fof(eq_test, axiom, ![X]: (X = X)).
            fof(neq_test, axiom, a != b).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        assert_eq!(problem.statements.len(), 2);
    }

    #[test]
    fn test_to_smtlib2() {
        let input = r#"
            fof(ax1, axiom, ![X]: (human(X) => mortal(X))).
            fof(ax2, axiom, human(socrates)).
            fof(conj, conjecture, mortal(socrates)).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        let smtlib = problem.to_smtlib2();

        assert!(smtlib.contains("(set-logic UF)"));
        assert!(smtlib.contains("(declare-sort U 0)"));
        assert!(smtlib.contains("(declare-fun human (U) Bool)"));
        assert!(smtlib.contains("(declare-fun mortal (U) Bool)"));
        assert!(smtlib.contains("(declare-const socrates U)"));
        assert!(smtlib.contains("(check-sat)"));
        // Conjecture should be negated
        assert!(smtlib.contains("(assert (not"));
    }

    #[test]
    fn test_szs_status_theorem() {
        let result = format_tptp_result("unsat", true);
        assert_eq!(result, "% SZS status Theorem");
    }

    #[test]
    fn test_szs_status_counter_satisfiable() {
        let result = format_tptp_result("sat", true);
        assert_eq!(result, "% SZS status CounterSatisfiable");
    }

    #[test]
    fn test_szs_status_satisfiable() {
        let result = format_tptp_result("sat", false);
        assert_eq!(result, "% SZS status Satisfiable");
    }

    #[test]
    fn test_szs_status_unsatisfiable() {
        let result = format_tptp_result("unsat", false);
        assert_eq!(result, "% SZS status Unsatisfiable");
    }

    #[test]
    fn test_parse_comments() {
        let input = r#"
            % This is a comment
            fof(ax1, axiom, p).
            /* Block comment */
            fof(ax2, axiom, q).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        assert_eq!(problem.statements.len(), 2);
        assert!(!problem.comments.is_empty());
    }

    #[test]
    fn test_parse_existential() {
        let input = r#"
            fof(ex_test, axiom, ?[X]: p(X)).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        assert_eq!(problem.statements.len(), 1);

        let smtlib = problem.to_smtlib2();
        assert!(smtlib.contains("exists"));
    }

    #[test]
    fn test_parse_iff() {
        let input = r#"
            fof(iff_test, axiom, p <=> q).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        assert_eq!(problem.statements.len(), 1);
    }

    #[test]
    fn test_parse_function_terms() {
        let input = r#"
            fof(func_test, axiom, p(f(a, g(b)))).
        "#;

        let problem = TptpProblem::parse(input).expect("test operation should succeed");
        assert_eq!(problem.statements.len(), 1);

        let smtlib = problem.to_smtlib2();
        assert!(smtlib.contains("(declare-fun f (U U) U)"));
        assert!(smtlib.contains("(declare-fun g (U) U)"));
    }

    #[test]
    fn test_axiom_free_variable_is_universally_closed() {
        // `X` is free in `p(X)` (no explicit `![X]:`), so per TPTP semantics
        // this axiom means `forall X. p(X)`. It must not be weakened to a
        // single arbitrary witness constant.
        let input = "fof(ax1, axiom, p(X)).\n";
        let problem = TptpProblem::parse(input).expect("should parse");
        let smtlib = problem.to_smtlib2();

        assert!(
            smtlib.contains("(forall ((X U)) (p X))"),
            "axiom free variable must be closed with forall: {smtlib}"
        );
        // The free variable must NOT be declared as a global witness
        // constant -- that would defeat the point of closing it.
        assert!(!smtlib.contains("(declare-const X U)"));
    }

    #[test]
    fn test_hypothesis_free_variable_is_universally_closed() {
        let input = "fof(h1, hypothesis, q(Y)).\n";
        let problem = TptpProblem::parse(input).expect("should parse");
        let smtlib = problem.to_smtlib2();
        assert!(smtlib.contains("(forall ((Y U)) (q Y))"));
    }

    #[test]
    fn test_conjecture_free_variable_is_still_skolemized() {
        // For the (negated) conjecture, Skolemizing the free variable as an
        // arbitrary fresh constant is sound (see module docs), so this case
        // must keep working as before -- no forall here.
        let input = "fof(conj, conjecture, p(X)).\n";
        let problem = TptpProblem::parse(input).expect("should parse");
        let smtlib = problem.to_smtlib2();

        assert!(smtlib.contains("(declare-const X U)"));
        assert!(smtlib.contains("(assert (not (p X)))"));
        assert!(!smtlib.contains("forall"));
    }

    #[test]
    fn test_negated_conjecture_free_variable_is_still_skolemized() {
        let input = "fof(nc, negated_conjecture, p(X)).\n";
        let problem = TptpProblem::parse(input).expect("should parse");
        let smtlib = problem.to_smtlib2();

        assert!(smtlib.contains("(declare-const X U)"));
        assert!(smtlib.contains("(assert (p X))"));
        assert!(!smtlib.contains("forall"));
    }

    #[test]
    fn test_free_variable_of_same_name_is_not_shared_across_axioms() {
        // Two independent axioms each use `X` as their own free variable.
        // Each occurrence must be closed locally; they must not collapse
        // onto one shared global witness (the old bug: both would resolve
        // to the same `(declare-const X U)`, incorrectly identifying two
        // logically unrelated variables).
        let input = "fof(ax1, axiom, p(X)).\nfof(ax2, axiom, q(X)).\n";
        let problem = TptpProblem::parse(input).expect("should parse");
        let smtlib = problem.to_smtlib2();

        assert!(smtlib.contains("(forall ((X U)) (p X))"));
        assert!(smtlib.contains("(forall ((X U)) (q X))"));
        assert!(!smtlib.contains("(declare-const X U)"));
    }

    #[test]
    fn test_already_quantified_axiom_is_unaffected() {
        // `X` is already explicitly bound by `![X]:`, so `free_variables()`
        // is empty and no extra forall wrapping should be added.
        let input = "fof(ax1, axiom, ![X]: p(X)).\n";
        let problem = TptpProblem::parse(input).expect("should parse");
        let smtlib = problem.to_smtlib2();

        assert!(smtlib.contains("(assert (forall ((X U)) (p X)))"));
        // Must not be double-wrapped in a second forall.
        assert!(!smtlib.contains("(forall ((X U)) (forall"));
    }

    /// Stack size for the deep-nesting regression tests below. A stack overflow
    /// aborts the process rather than failing a test, so *returning at all* is
    /// the assertion; the small stack makes a surviving recursion detectable.
    const SMALL_STACK: usize = 1 << 20;

    /// Run `body` on a thread with a deliberately small stack.
    fn on_small_stack<F>(name: &str, body: F)
    where
        F: FnOnce() + Send + 'static,
    {
        std::thread::Builder::new()
            .name(name.to_string())
            .stack_size(SMALL_STACK)
            .spawn(body)
            .expect("test thread should spawn")
            .join()
            .expect("test thread should not panic");
    }

    #[test]
    fn deep_negation_run_is_rejected_not_fatal() {
        on_small_stack("tptp_deep_not", || {
            // One recursive-descent frame per `~` in the old parser.
            let src = format!("fof(a, axiom, {}p).", "~".repeat(100_000));
            let mut parser = TptpParser::new(&src);
            let result = parser.parse_problem();
            // An honest error through the parser's existing channel, never an abort.
            assert!(result.is_err(), "expected a depth error, got {result:?}");
        });
    }

    #[test]
    fn deep_paren_nesting_is_rejected_not_fatal() {
        on_small_stack("tptp_deep_parens", || {
            // ~7 recursive-descent frames per parenthesis level in the old parser.
            let src = format!(
                "fof(a, axiom, {}p{}).",
                "(".repeat(50_000),
                ")".repeat(50_000)
            );
            let mut parser = TptpParser::new(&src);
            assert!(parser.parse_problem().is_err());
        });
    }

    #[test]
    fn deep_term_nesting_is_rejected_not_fatal() {
        on_small_stack("tptp_deep_terms", || {
            let depth = 50_000;
            let src = format!(
                "fof(a, axiom, p({}c{})).",
                "f(".repeat(depth),
                ")".repeat(depth)
            );
            let mut parser = TptpParser::new(&src);
            assert!(parser.parse_problem().is_err());
        });
    }

    #[test]
    fn nesting_just_under_the_cap_still_parses_and_converts() {
        on_small_stack("tptp_under_cap", || {
            // 1000 `~`s is under MAX_TPTP_DEPTH, so it must parse *and* survive
            // every post-parse walk (to_smtlib2, free_variables, ...).
            let depth = 1000;
            let src = format!("fof(a, axiom, {}p).", "~".repeat(depth));
            let mut parser = TptpParser::new(&src);
            let problem = parser.parse_problem().expect("should parse under the cap");
            let smtlib = problem.to_smtlib2();
            assert!(smtlib.contains(&"(not ".repeat(depth)));
        });
    }

    #[test]
    fn deep_term_walks_survive_under_the_cap() {
        on_small_stack("tptp_deep_walks", || {
            let depth = 1000;
            let src = format!(
                "fof(a, axiom, p(X, {}c{})).",
                "f(".repeat(depth),
                ")".repeat(depth)
            );
            let mut parser = TptpParser::new(&src);
            let problem = parser.parse_problem().expect("should parse under the cap");
            let smtlib = problem.to_smtlib2();
            // Free variable X is universally closed, and the nested term survives
            // collect_variables / collect_functions / to_smtlib2.
            assert!(smtlib.contains("(forall ((X U))"));
            assert!(smtlib.contains(&"(f ".repeat(depth)));
        });
    }

    #[test]
    fn smtlib2_conversion_output_is_unchanged() {
        // Semantic pins over the iterative serializers.
        let mut parser = TptpParser::new(
            "fof(a, axiom, ![X]: (p(X) & (q(X) | ~r(f(X)))) ).\n\
             fof(b, axiom, (p(c) <=> q(c)) => (a != b)).",
        );
        let problem = parser.parse_problem().expect("should parse");
        let smtlib = problem.to_smtlib2();
        assert!(
            smtlib.contains("(assert (forall ((X U)) (and (p X) (or (q X) (not (r (f X)))))))")
        );
        assert!(smtlib.contains("(assert (=> (= (p c) (q c)) (not (= a b))))"));
    }
}
