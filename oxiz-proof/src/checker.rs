//! Proof checking infrastructure.
//!
//! This module provides validation and verification of proof steps,
//! ensuring that proof derivations are sound.
//!
//! ## Features
//!
//! - **Syntactic checks**: Validate proof structure (premises exist, etc.)
//! - **Rule validation**: Check that rule applications are well-formed
//! - **Extensible**: Support for custom rule validators
//!
//! ## Example
//!
//! ```
//! use oxiz_proof::checker::{ProofChecker, CheckResult};
//! use oxiz_proof::theory::{TheoryProof, TheoryRule};
//!
//! let mut proof = TheoryProof::new();
//! proof.refl("x");
//!
//! let mut checker = ProofChecker::new();
//! let result = checker.check_theory_proof(&proof);
//! assert!(result.is_valid());
//! ```

use crate::alethe::{AletheProof, AletheRule, AletheStep, StepIndex, TermRef};
use crate::theory::{ProofTerm, TheoryProof, TheoryRule, TheoryStepId};
use std::collections::{HashMap, HashSet};
use std::fmt;

/// Result of checking a proof step
#[derive(Debug, Clone)]
pub enum CheckResult {
    /// The proof is valid
    Valid,
    /// The proof has an error at a specific step
    Invalid {
        /// Step index where the error occurred
        step: u32,
        /// Description of the error
        error: CheckError,
    },
    /// Multiple errors were found
    MultipleErrors(Vec<(u32, CheckError)>),
}

impl CheckResult {
    /// Check if the result indicates a valid proof
    #[must_use]
    pub fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    /// Get the error if there is one
    #[must_use]
    pub fn error(&self) -> Option<&CheckError> {
        match self {
            Self::Invalid { error, .. } => Some(error),
            _ => None,
        }
    }
}

impl fmt::Display for CheckResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Valid => write!(f, "✓ Proof is valid"),
            Self::Invalid { step, error } => {
                writeln!(f, "✗ Proof is invalid")?;
                writeln!(f, "  Step: {}", step)?;
                writeln!(f, "  [{:?}] {}", error.severity(), error)?;
                if let Some(suggestion) = error.suggestion() {
                    writeln!(f, "  Suggestion: {}", suggestion)?;
                }
                Ok(())
            }
            Self::MultipleErrors(errors) => {
                writeln!(f, "✗ Proof has {} error(s):", errors.len())?;
                for (step, error) in errors {
                    writeln!(f, "\n  Step {}:", step)?;
                    writeln!(f, "    [{:?}] {}", error.severity(), error)?;
                    if let Some(suggestion) = error.suggestion() {
                        writeln!(f, "    Suggestion: {}", suggestion)?;
                    }
                }
                Ok(())
            }
        }
    }
}

/// Types of proof checking errors
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    /// A referenced premise doesn't exist
    MissingPremise(u32),
    /// Wrong number of premises for the rule
    WrongPremiseCount { expected: usize, got: usize },
    /// Wrong number of arguments for the rule
    WrongArgumentCount { expected: usize, got: usize },
    /// Rule is not applicable
    RuleNotApplicable(String),
    /// Conclusion doesn't follow from premises
    InvalidConclusion(String),
    /// Cyclic dependency in proof
    CyclicDependency,
    /// Empty proof
    EmptyProof,
    /// Malformed term in proof
    MalformedTerm(String),
    /// Unknown rule
    UnknownRule(String),
    /// Custom error
    Custom(String),
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingPremise(id) => {
                write!(
                    f,
                    "Missing premise: step {} does not exist or has not been defined yet. \
                     Premises must be defined before they are referenced.",
                    id
                )
            }
            Self::WrongPremiseCount { expected, got } => {
                write!(
                    f,
                    "Wrong premise count: rule requires {} premise(s), but {} {} provided. \
                     Check the rule definition for the correct number of premises.",
                    expected,
                    got,
                    if *got == 1 { "was" } else { "were" }
                )
            }
            Self::WrongArgumentCount { expected, got } => {
                write!(
                    f,
                    "Wrong argument count: rule expects {} argument(s), but {} {} provided. \
                     Ensure all required arguments are supplied.",
                    expected,
                    got,
                    if *got == 1 { "was" } else { "were" }
                )
            }
            Self::RuleNotApplicable(msg) => {
                write!(
                    f,
                    "Rule not applicable: {}. \
                     Verify that the rule's preconditions are met.",
                    msg
                )
            }
            Self::InvalidConclusion(msg) => {
                write!(
                    f,
                    "Invalid conclusion: {}. \
                     The conclusion does not follow from the premises using the specified rule.",
                    msg
                )
            }
            Self::CyclicDependency => {
                write!(
                    f,
                    "Cyclic dependency detected in proof structure. \
                     A proof step cannot depend on itself (directly or indirectly). \
                     Check for circular references in premise chains."
                )
            }
            Self::EmptyProof => {
                write!(
                    f,
                    "Empty proof: no proof steps provided. \
                     A valid proof must contain at least one step."
                )
            }
            Self::MalformedTerm(msg) => {
                write!(
                    f,
                    "Malformed term: {}. \
                     Check for syntax errors or invalid term structure.",
                    msg
                )
            }
            Self::UnknownRule(name) => {
                write!(
                    f,
                    "Unknown rule: '{}'. \
                     This rule is not recognized by the proof checker. \
                     Verify the rule name is spelled correctly.",
                    name
                )
            }
            Self::Custom(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for CheckError {}

impl CheckError {
    /// Get a suggestion for fixing this error
    #[must_use]
    pub fn suggestion(&self) -> Option<&str> {
        match self {
            Self::MissingPremise(_) => {
                Some("Ensure all premise steps are added to the proof before referencing them.")
            }
            Self::WrongPremiseCount { .. } => {
                Some("Consult the rule documentation for the correct number of premises.")
            }
            Self::WrongArgumentCount { .. } => {
                Some("Review the rule definition to determine which arguments are required.")
            }
            Self::RuleNotApplicable(_) => {
                Some("Check that the premise types match what the rule expects.")
            }
            Self::InvalidConclusion(_) => {
                Some("Verify that the rule is being applied correctly to the given premises.")
            }
            Self::CyclicDependency => {
                Some("Reorganize proof steps to eliminate circular dependencies.")
            }
            Self::EmptyProof => Some("Add at least one axiom or assumption to the proof."),
            Self::MalformedTerm(_) => Some("Check the term syntax against the expected format."),
            Self::UnknownRule(_) => {
                Some("Use a standard proof rule or define a custom rule handler.")
            }
            Self::Custom(_) => None,
        }
    }

    /// Get the severity level of this error
    #[must_use]
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            Self::CyclicDependency | Self::EmptyProof => ErrorSeverity::Critical,
            Self::MissingPremise(_) | Self::InvalidConclusion(_) | Self::UnknownRule(_) => {
                ErrorSeverity::Error
            }
            Self::WrongPremiseCount { .. }
            | Self::WrongArgumentCount { .. }
            | Self::RuleNotApplicable(_)
            | Self::MalformedTerm(_) => ErrorSeverity::Warning,
            Self::Custom(_) => ErrorSeverity::Error,
        }
    }
}

/// Error severity level
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorSeverity {
    /// Warning - proof may be acceptable
    Warning,
    /// Error - proof is invalid
    Error,
    /// Critical - proof structure is fundamentally broken
    Critical,
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Warning => write!(f, "WARNING"),
            Self::Error => write!(f, "ERROR"),
            Self::Critical => write!(f, "CRITICAL"),
        }
    }
}

/// Configuration for proof checking
#[derive(Debug, Clone, Default)]
pub struct CheckerConfig {
    /// Whether to continue checking after the first error
    pub continue_on_error: bool,
    /// Whether to verify conclusion content (not just structure).
    ///
    /// When `true`, in addition to the structural checks that always run
    /// (premises exist, no cycles, premise/argument counts), the checker
    /// re-derives and checks the *semantics* of the conclusion for the rules
    /// it knows how to verify:
    ///
    /// - Theory proofs (see [`crate::theory::TheoryRule`]): `Refl`, `Symm`,
    ///   `Trans`, `Cong`, `ArrReadWrite1`.
    /// - Alethe proofs (see [`crate::alethe::AletheRule`]): `Refl`/`EqRefl`,
    ///   `Symm`/`EqSymm`, `Trans`/`EqTrans`, `Cong`/`EqCong`, and `Resolution`
    ///   (a necessary-condition check: every literal in the concluded clause
    ///   must appear in some premise clause).
    ///
    /// Rules outside this set (e.g. `LaGeneric`, quantifier rules, bit-vector
    /// rules) are *not* semantically verified even with this flag set --
    /// only the structural checks apply to them. This is a deliberate,
    /// honest scoping: the checker never fabricates a semantic verdict for a
    /// rule it cannot actually check.
    pub verify_conclusions: bool,
    /// Whether to allow cyclic dependencies (for some proof formats)
    pub allow_cycles: bool,
}

/// Work item for the iterative theory-step dependency walk.
#[derive(Debug, Clone, Copy)]
enum StepFrame {
    /// The step's premises have not been scheduled yet.
    Enter(TheoryStepId),
    /// All premises of the step have been validated.
    Exit(TheoryStepId),
}

/// Proof checker for verifying proof derivations
#[derive(Debug, Default)]
pub struct ProofChecker {
    /// Configuration
    config: CheckerConfig,
    /// Collected errors
    errors: Vec<(u32, CheckError)>,
    /// Validated step IDs (for cycle detection)
    validated: HashSet<u32>,
    /// Currently being validated (for cycle detection)
    in_progress: HashSet<u32>,
}

impl ProofChecker {
    /// Create a new proof checker with default configuration
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a proof checker with custom configuration
    #[must_use]
    pub fn with_config(config: CheckerConfig) -> Self {
        Self {
            config,
            errors: Vec::new(),
            validated: HashSet::new(),
            in_progress: HashSet::new(),
        }
    }

    /// Reset the checker state
    pub fn reset(&mut self) {
        self.errors.clear();
        self.validated.clear();
        self.in_progress.clear();
    }

    /// Check a theory proof
    pub fn check_theory_proof(&mut self, proof: &TheoryProof) -> CheckResult {
        self.reset();

        if proof.is_empty() {
            return CheckResult::Invalid {
                step: 0,
                error: CheckError::EmptyProof,
            };
        }

        // Check each step
        for step in proof.steps() {
            if let Err(error) = self.check_theory_step(proof, step.id) {
                if self.config.continue_on_error {
                    self.errors.push((step.id.0, error));
                } else {
                    return CheckResult::Invalid {
                        step: step.id.0,
                        error,
                    };
                }
            }
        }

        if self.errors.is_empty() {
            CheckResult::Valid
        } else {
            CheckResult::MultipleErrors(std::mem::take(&mut self.errors))
        }
    }

    /// Check a single theory proof step, and (unless cycles are allowed) every
    /// step it transitively depends on.
    ///
    /// Iterative (explicit heap stack): untrusted theory proofs from an
    /// external prover drive this directly, and their dependency chains are
    /// bounded only by the file. The `Enter`/`Exit` split keeps the original
    /// ordering — premises are validated before the rule and conclusion checks
    /// of the step that uses them — and the `in_progress`/`validated` sets keep
    /// the walk linear in the number of steps.
    fn check_theory_step(
        &mut self,
        proof: &TheoryProof,
        step_id: TheoryStepId,
    ) -> Result<(), CheckError> {
        let allow_cycles = self.config.allow_cycles;
        let mut stack = vec![StepFrame::Enter(step_id)];

        while let Some(frame) = stack.pop() {
            match frame {
                StepFrame::Enter(id) => {
                    // Cycle detection
                    if !allow_cycles {
                        if self.in_progress.contains(&id.0) {
                            return Err(CheckError::CyclicDependency);
                        }
                        if self.validated.contains(&id.0) {
                            continue;
                        }
                        self.in_progress.insert(id.0);
                    }

                    let step = proof.get_step(id).ok_or(CheckError::MissingPremise(id.0))?;

                    stack.push(StepFrame::Exit(id));

                    if allow_cycles {
                        // No descent: only check that the premises exist.
                        for premise_id in &step.premises {
                            if proof.get_step(*premise_id).is_none() {
                                return Err(CheckError::MissingPremise(premise_id.0));
                            }
                        }
                    } else {
                        // Descending into a premise reports a missing step with
                        // exactly the same error the inline check produced.
                        stack.extend(step.premises.iter().rev().copied().map(StepFrame::Enter));
                    }
                }
                StepFrame::Exit(id) => {
                    let step = proof.get_step(id).ok_or(CheckError::MissingPremise(id.0))?;

                    // Check rule-specific requirements
                    self.check_theory_rule(&step.rule, step.premises.len(), step.args.len())?;

                    // Check the semantic content of the conclusion, if requested.
                    if self.config.verify_conclusions {
                        let premise_terms: Vec<&ProofTerm> = step
                            .premises
                            .iter()
                            .filter_map(|premise_id| {
                                proof.get_step(*premise_id).map(|s| &s.conclusion)
                            })
                            .collect();
                        verify_theory_conclusion(&step.rule, &premise_terms, &step.conclusion)?;
                    }

                    // Mark as validated
                    if !allow_cycles {
                        self.in_progress.remove(&id.0);
                        self.validated.insert(id.0);
                    }
                }
            }
        }

        Ok(())
    }

    /// Check rule-specific requirements for theory proofs
    fn check_theory_rule(
        &self,
        rule: &TheoryRule,
        premise_count: usize,
        arg_count: usize,
    ) -> Result<(), CheckError> {
        match rule {
            // Rules with no premises
            TheoryRule::Refl if premise_count != 0 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 0,
                    got: premise_count,
                });
            }

            // Rules with exactly one premise
            TheoryRule::Symm if premise_count != 1 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 1,
                    got: premise_count,
                });
            }

            // Rules with exactly two premises
            TheoryRule::Trans if premise_count != 2 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 2,
                    got: premise_count,
                });
            }

            // Rules with at least one premise (congruence needs arg equalities)
            TheoryRule::Cong => {
                // Congruence can have zero premises for nullary functions
            }

            // Farkas lemma needs at least 2 premises
            TheoryRule::LaGeneric if premise_count < 2 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 2,
                    got: premise_count,
                });
            }

            // Array read-write-same is an axiom
            TheoryRule::ArrReadWrite1 if premise_count != 0 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 0,
                    got: premise_count,
                });
            }

            // Array read-write-different needs proof of i ≠ j
            TheoryRule::ArrReadWrite2 if premise_count != 1 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 1,
                    got: premise_count,
                });
            }

            // LaMult needs coefficient argument
            TheoryRule::LaMult if arg_count < 1 => {
                return Err(CheckError::WrongArgumentCount {
                    expected: 1,
                    got: arg_count,
                });
            }

            // Other rules - flexible checking
            _ => {}
        }

        Ok(())
    }

    /// Check an Alethe proof
    pub fn check_alethe_proof(&mut self, proof: &AletheProof) -> CheckResult {
        self.reset();

        if proof.is_empty() {
            return CheckResult::Invalid {
                step: 0,
                error: CheckError::EmptyProof,
            };
        }

        let steps = proof.steps();
        let mut step_indices: HashSet<u32> = HashSet::new();
        // Map from step index to its conclusion clause (literals), used for
        // semantic conclusion checking. `Assume` contributes a one-literal
        // "clause" (the assumed term); `Anchor`/`DefineFun` steps have no
        // clause and are simply absent from the map.
        let mut clause_by_index: HashMap<StepIndex, Vec<TermRef>> = HashMap::new();

        // First pass: collect all step indices
        for step in steps {
            match step {
                AletheStep::Assume { index, term } => {
                    step_indices.insert(*index);
                    clause_by_index.insert(*index, vec![term.clone()]);
                }
                AletheStep::Step { index, clause, .. } => {
                    step_indices.insert(*index);
                    clause_by_index.insert(*index, clause.clone());
                }
                AletheStep::Anchor { step: index, .. } => {
                    step_indices.insert(*index);
                }
                AletheStep::DefineFun { .. } => {}
            }
        }

        // Second pass: check each step
        for (idx, step) in steps.iter().enumerate() {
            if let Err(error) = self.check_alethe_step(step, &step_indices, &clause_by_index) {
                if self.config.continue_on_error {
                    self.errors.push((idx as u32, error));
                } else {
                    return CheckResult::Invalid {
                        step: idx as u32,
                        error,
                    };
                }
            }
        }

        if self.errors.is_empty() {
            CheckResult::Valid
        } else {
            CheckResult::MultipleErrors(std::mem::take(&mut self.errors))
        }
    }

    /// Check a single Alethe proof step
    fn check_alethe_step(
        &self,
        step: &AletheStep,
        step_indices: &HashSet<u32>,
        clause_by_index: &HashMap<StepIndex, Vec<TermRef>>,
    ) -> Result<(), CheckError> {
        match step {
            AletheStep::Assume { .. } => {
                // Assumptions don't need checking
                Ok(())
            }

            AletheStep::Step {
                clause,
                rule,
                premises,
                ..
            } => {
                // Check all premises exist
                for premise in premises {
                    if !step_indices.contains(premise) {
                        return Err(CheckError::MissingPremise(*premise));
                    }
                }

                // Check rule-specific requirements
                self.check_alethe_rule(rule, premises.len())?;

                // Check the semantic content of the conclusion, if requested.
                if self.config.verify_conclusions {
                    verify_alethe_conclusion(*rule, clause, premises, clause_by_index)?;
                }

                Ok(())
            }

            AletheStep::Anchor { .. } => {
                // Anchors don't need checking
                Ok(())
            }

            AletheStep::DefineFun { .. } => {
                // Definitions don't need checking
                Ok(())
            }
        }
    }

    /// Check rule-specific requirements for Alethe proofs
    fn check_alethe_rule(&self, rule: &AletheRule, premise_count: usize) -> Result<(), CheckError> {
        match rule {
            // Resolution needs at least 2 premises
            AletheRule::Resolution if premise_count < 2 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 2,
                    got: premise_count,
                });
            }

            // Reflexivity is an axiom
            AletheRule::Refl if premise_count != 0 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 0,
                    got: premise_count,
                });
            }

            // Transitivity needs at least 2 premises
            AletheRule::Trans if premise_count < 2 => {
                return Err(CheckError::WrongPremiseCount {
                    expected: 2,
                    got: premise_count,
                });
            }

            // Other rules - flexible checking
            _ => {}
        }

        Ok(())
    }
}

/// Trait for types that can be checked for validity
pub trait Checkable {
    /// Check if the proof is valid
    fn check(&self) -> CheckResult;

    /// Check using a custom checker configuration
    fn check_with_config(&self, config: CheckerConfig) -> CheckResult;
}

impl Checkable for TheoryProof {
    fn check(&self) -> CheckResult {
        ProofChecker::new().check_theory_proof(self)
    }

    fn check_with_config(&self, config: CheckerConfig) -> CheckResult {
        ProofChecker::with_config(config).check_theory_proof(self)
    }
}

impl Checkable for AletheProof {
    fn check(&self) -> CheckResult {
        ProofChecker::new().check_alethe_proof(self)
    }

    fn check_with_config(&self, config: CheckerConfig) -> CheckResult {
        ProofChecker::with_config(config).check_alethe_proof(self)
    }
}

// ============================================================================
// Semantic conclusion verification
// ============================================================================
//
// `ProofTerm`/`TermRef` values are opaque SMT-LIB-style s-expression strings
// (e.g. `"(= a b)"`, `"(f x y)"`). To check that a rule's conclusion actually
// follows from its premises we parse those strings into a tiny s-expression
// tree and compare subterms structurally. This is deliberately scoped to the
// handful of rules below (see [`CheckerConfig::verify_conclusions`]); rules
// we cannot verify are left alone rather than being given a fabricated pass
// or fail.

/// A minimal parsed s-expression: either an atom or a parenthesized list.
///
/// # Depth invariant
///
/// Every `SExpr` in this crate is at most [`MAX_SEXPR_DEPTH`] levels deep.
/// The type is private to this module and [`parse_sexpr`] (via
/// [`parse_sexpr_rec`], which enforces the bound) is its *only* construction
/// path -- [`as_binary`] and [`as_call`] merely borrow subterms, and nothing
/// here builds a node by hand or nests one parsed value inside another. That is
/// what makes the derives below safe: `Drop`, `Debug`, `Clone`, `PartialEq` and
/// `Hash` are all compiler-generated recursive walks, so any new construction
/// path must either respect the same bound or come with hand-written iterative
/// impls.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Maximum nesting accepted by [`parse_sexpr`].
///
/// The parser itself is iterative, so this is not a stack guard for the parse:
/// it bounds the *depth of the resulting tree*, which is still walked
/// recursively by the compiler-generated `Drop`, `Debug`, `Hash` and `PartialEq`
/// impls of [`SExpr`]. Conclusion strings reach this parser from externally
/// supplied proof files, so the bound is enforced through the parser's existing
/// error channel rather than left to whichever of those walks runs first.
/// Matches `MAX_PARSE_DEPTH` in oxiz-core's SMT-LIB term parser.
const MAX_SEXPR_DEPTH: usize = 1024;

/// Parse a single s-expression from `input`, requiring the whole string
/// (modulo surrounding whitespace) to be consumed.
fn parse_sexpr(input: &str) -> Result<SExpr, String> {
    let mut chars: std::iter::Peekable<std::str::Chars<'_>> = input.chars().peekable();
    let expr = parse_sexpr_rec(&mut chars)?;
    skip_ws(&mut chars);
    if chars.peek().is_some() {
        return Err(format!("trailing input after term: {input:?}"));
    }
    Ok(expr)
}

fn skip_ws(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
}

/// Parse one s-expression, leaving the iterator positioned after it.
///
/// Iterative: nesting here comes straight from an untrusted proof file, so the
/// open lists live on an explicit heap stack (`open`) instead of the call stack.
/// Depth is still bounded by [`MAX_SEXPR_DEPTH`] because the produced [`SExpr`]
/// tree is walked recursively by its derived impls — see that constant.
fn parse_sexpr_rec(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<SExpr, String> {
    let mut open: Vec<Vec<SExpr>> = Vec::new();

    loop {
        skip_ws(chars);

        let value = match chars.peek() {
            Some('(') => {
                chars.next();
                if open.len() >= MAX_SEXPR_DEPTH {
                    return Err(format!(
                        "s-expression nesting exceeds the maximum supported depth of \
                         {MAX_SEXPR_DEPTH}"
                    ));
                }
                open.push(Vec::new());
                continue;
            }
            Some(')') => {
                let Some(items) = open.pop() else {
                    return Err("unexpected ')'".to_string());
                };
                chars.next();
                SExpr::List(items)
            }
            Some(_) => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                if atom.is_empty() {
                    return Err("empty atom".to_string());
                }
                SExpr::Atom(atom)
            }
            None => {
                return Err(if open.is_empty() {
                    "unexpected end of input".to_string()
                } else {
                    "unexpected end of input inside a list".to_string()
                });
            }
        };

        match open.last_mut() {
            Some(items) => items.push(value),
            None => return Ok(value),
        }
    }
}

/// If `expr` is `(op lhs rhs)`, return `(lhs, rhs)`.
fn as_binary<'a>(op: &str, expr: &'a SExpr) -> Option<(&'a SExpr, &'a SExpr)> {
    if let SExpr::List(items) = expr
        && items.len() == 3
        && let SExpr::Atom(a) = &items[0]
        && a == op
    {
        return Some((&items[1], &items[2]));
    }
    None
}

/// If `expr` is a function application `(name arg1 .. argn)`, return
/// `(name, [arg1 .. argn])`.
fn as_call(expr: &SExpr) -> Option<(&str, &[SExpr])> {
    if let SExpr::List(items) = expr
        && let Some(SExpr::Atom(name)) = items.first()
    {
        return Some((name.as_str(), &items[1..]));
    }
    None
}

fn malformed(msg: impl Into<String>) -> CheckError {
    CheckError::MalformedTerm(msg.into())
}

fn invalid(msg: impl Into<String>) -> CheckError {
    CheckError::InvalidConclusion(msg.into())
}

/// Check whether the four "endpoints" of two premise equalities chain
/// together (in any orientation) into `(u, v)`, i.e. transitivity.
fn trans_chains_to<'a>(
    a1: &'a SExpr,
    b1: &'a SExpr,
    a2: &'a SExpr,
    b2: &'a SExpr,
    u: &SExpr,
    v: &SExpr,
) -> bool {
    let candidates = [
        (a1, b1, a2, b2),
        (a1, b1, b2, a2),
        (b1, a1, a2, b2),
        (b1, a1, b2, a2),
    ];
    for (x1, y1, x2, y2) in candidates {
        if y1 == x2 && ((u == x1 && v == y2) || (u == y2 && v == x1)) {
            return true;
        }
    }
    false
}

/// Semantically verify a theory-proof step's conclusion against its
/// premises' conclusions, for the subset of rules we can check. Rules not
/// covered here return `Ok(())` -- absence of a semantic error does not mean
/// the step was verified, only that it was not found to be wrong.
fn verify_theory_conclusion(
    rule: &TheoryRule,
    premises: &[&ProofTerm],
    conclusion: &ProofTerm,
) -> Result<(), CheckError> {
    match rule {
        TheoryRule::Refl => {
            let c = parse_sexpr(&conclusion.0).map_err(malformed)?;
            let (l, r) = as_binary("=", &c).ok_or_else(|| {
                invalid(format!(
                    "refl conclusion '{}' is not an equality",
                    conclusion.0
                ))
            })?;
            if l == r {
                Ok(())
            } else {
                Err(invalid(format!(
                    "refl conclusion '{}' does not equate identical terms",
                    conclusion.0
                )))
            }
        }
        TheoryRule::Symm => {
            let p = premises
                .first()
                .ok_or_else(|| invalid("symm requires one premise"))?;
            let pe = parse_sexpr(&p.0).map_err(malformed)?;
            let (a, b) = as_binary("=", &pe)
                .ok_or_else(|| invalid(format!("symm premise '{}' is not an equality", p.0)))?;
            let c = parse_sexpr(&conclusion.0).map_err(malformed)?;
            let (x, y) = as_binary("=", &c).ok_or_else(|| {
                invalid(format!(
                    "symm conclusion '{}' is not an equality",
                    conclusion.0
                ))
            })?;
            if x == b && y == a {
                Ok(())
            } else {
                Err(invalid(format!(
                    "symm conclusion '{}' is not the reverse of premise '{}'",
                    conclusion.0, p.0
                )))
            }
        }
        TheoryRule::Trans => {
            if premises.len() < 2 {
                return Err(invalid("trans requires two premises"));
            }
            let p1 = parse_sexpr(&premises[0].0).map_err(malformed)?;
            let p2 = parse_sexpr(&premises[1].0).map_err(malformed)?;
            let (a1, b1) = as_binary("=", &p1).ok_or_else(|| {
                invalid(format!(
                    "trans premise '{}' is not an equality",
                    premises[0].0
                ))
            })?;
            let (a2, b2) = as_binary("=", &p2).ok_or_else(|| {
                invalid(format!(
                    "trans premise '{}' is not an equality",
                    premises[1].0
                ))
            })?;
            let c = parse_sexpr(&conclusion.0).map_err(malformed)?;
            let (u, v) = as_binary("=", &c).ok_or_else(|| {
                invalid(format!(
                    "trans conclusion '{}' is not an equality",
                    conclusion.0
                ))
            })?;

            if trans_chains_to(a1, b1, a2, b2, u, v) {
                Ok(())
            } else {
                Err(invalid(format!(
                    "trans conclusion '{}' does not follow from premises '{}' and '{}'",
                    conclusion.0, premises[0].0, premises[1].0
                )))
            }
        }
        TheoryRule::Cong => {
            let c = parse_sexpr(&conclusion.0).map_err(malformed)?;
            let (l, r) = as_binary("=", &c).ok_or_else(|| {
                invalid(format!(
                    "cong conclusion '{}' is not an equality",
                    conclusion.0
                ))
            })?;
            match (as_call(l), as_call(r)) {
                (Some((lf, largs)), Some((rf, rargs))) => {
                    if lf != rf {
                        return Err(invalid(format!(
                            "cong conclusion '{}' uses different function symbols ({lf} vs {rf})",
                            conclusion.0
                        )));
                    }
                    if largs.len() != rargs.len() {
                        return Err(invalid(format!(
                            "cong conclusion '{}' has mismatched arity ({} vs {})",
                            conclusion.0,
                            largs.len(),
                            rargs.len()
                        )));
                    }
                    let mut premise_iter = premises.iter();
                    for i in 0..largs.len() {
                        if largs[i] == rargs[i] {
                            continue;
                        }
                        let premise = premise_iter.next().ok_or_else(|| {
                            invalid(format!(
                                "cong conclusion '{}' has no premise establishing argument {i} equal",
                                conclusion.0
                            ))
                        })?;
                        let p = parse_sexpr(&premise.0).map_err(malformed)?;
                        let (pa, pb) = as_binary("=", &p).ok_or_else(|| {
                            invalid(format!("cong premise '{}' is not an equality", premise.0))
                        })?;
                        if !((pa == &largs[i] && pb == &rargs[i])
                            || (pa == &rargs[i] && pb == &largs[i]))
                        {
                            return Err(invalid(format!(
                                "cong premise '{}' does not establish argument {i} equal",
                                premise.0
                            )));
                        }
                    }
                    Ok(())
                }
                (None, None) => {
                    // Nullary function symbols (or plain constants) render as bare atoms.
                    if l == r {
                        Ok(())
                    } else {
                        Err(invalid(format!(
                            "cong conclusion '{}' does not equate identical constants",
                            conclusion.0
                        )))
                    }
                }
                _ => Err(invalid(format!(
                    "cong conclusion '{}' has mismatched left/right shape",
                    conclusion.0
                ))),
            }
        }
        TheoryRule::ArrReadWrite1 => {
            // (= (select (store a i v) i) v)
            let c = parse_sexpr(&conclusion.0).map_err(malformed)?;
            let (l, r) = as_binary("=", &c).ok_or_else(|| {
                invalid(format!(
                    "arr_read_write_1 conclusion '{}' is not an equality",
                    conclusion.0
                ))
            })?;
            let (sel_fn, sel_args) = as_call(l).ok_or_else(|| {
                invalid(format!(
                    "arr_read_write_1 conclusion '{}' left side is not a function application",
                    conclusion.0
                ))
            })?;
            if sel_fn != "select" || sel_args.len() != 2 {
                return Err(invalid(format!(
                    "arr_read_write_1 conclusion '{}' left side is not a (select ...) of arity 2",
                    conclusion.0
                )));
            }
            let (store_fn, store_args) = as_call(&sel_args[0]).ok_or_else(|| {
                invalid(format!(
                    "arr_read_write_1 conclusion '{}' does not select from a store",
                    conclusion.0
                ))
            })?;
            if store_fn != "store" || store_args.len() != 3 {
                return Err(invalid(format!(
                    "arr_read_write_1 conclusion '{}' does not select from a (store ...) of arity 3",
                    conclusion.0
                )));
            }
            let select_index = &sel_args[1];
            let store_index = &store_args[1];
            let store_value = &store_args[2];
            if select_index != store_index {
                return Err(invalid(format!(
                    "arr_read_write_1 conclusion '{}' selects a different index than was stored",
                    conclusion.0
                )));
            }
            if store_value != r {
                return Err(invalid(format!(
                    "arr_read_write_1 conclusion '{}' does not conclude the stored value",
                    conclusion.0
                )));
            }
            Ok(())
        }
        // Other rules (arithmetic, bit-vector, quantifier, array extensionality, ...)
        // are not semantically re-derivable from their string conclusion alone
        // within this checker's scope; leave them to structural checking only.
        _ => Ok(()),
    }
}

/// Semantically verify an Alethe step's concluded clause against its
/// premises' clauses, for the subset of rules we can check.
fn verify_alethe_conclusion(
    rule: AletheRule,
    clause: &[TermRef],
    premises: &[StepIndex],
    clause_by_index: &HashMap<StepIndex, Vec<TermRef>>,
) -> Result<(), CheckError> {
    match rule {
        AletheRule::Refl | AletheRule::EqRefl => {
            if clause.len() != 1 {
                return Err(invalid("refl step must conclude exactly one literal"));
            }
            let e = parse_sexpr(&clause[0]).map_err(malformed)?;
            let (l, r) = as_binary("=", &e).ok_or_else(|| {
                invalid(format!(
                    "refl conclusion '{}' is not an equality",
                    clause[0]
                ))
            })?;
            if l == r {
                Ok(())
            } else {
                Err(invalid(format!(
                    "refl conclusion '{}' does not equate identical terms",
                    clause[0]
                )))
            }
        }
        AletheRule::Symm | AletheRule::EqSymm => {
            let Some(premise_clause) = premises.first().and_then(|idx| clause_by_index.get(idx))
            else {
                // Premise clause unavailable (e.g. references an anchor); out of scope.
                return Ok(());
            };
            let (Some(plit), true) = (premise_clause.first(), premise_clause.len() == 1) else {
                return Ok(());
            };
            if clause.len() != 1 {
                return Err(invalid("symm step must conclude exactly one literal"));
            }
            let pe = parse_sexpr(plit).map_err(malformed)?;
            let ce = parse_sexpr(&clause[0]).map_err(malformed)?;
            let (a, b) = as_binary("=", &pe)
                .ok_or_else(|| invalid(format!("symm premise '{plit}' is not an equality")))?;
            let (x, y) = as_binary("=", &ce).ok_or_else(|| {
                invalid(format!(
                    "symm conclusion '{}' is not an equality",
                    clause[0]
                ))
            })?;
            if x == b && y == a {
                Ok(())
            } else {
                Err(invalid(format!(
                    "symm conclusion '{}' is not the reverse of premise '{plit}'",
                    clause[0]
                )))
            }
        }
        AletheRule::Trans | AletheRule::EqTrans => {
            if premises.len() != 2 {
                // Chained (>2 premise) transitivity is out of scope for this checker.
                return Ok(());
            }
            let Some(p1) = clause_by_index.get(&premises[0]) else {
                return Ok(());
            };
            let Some(p2) = clause_by_index.get(&premises[1]) else {
                return Ok(());
            };
            if p1.len() != 1 || p2.len() != 1 {
                return Ok(());
            }
            if clause.len() != 1 {
                return Err(invalid("trans step must conclude exactly one literal"));
            }
            let pe1 = parse_sexpr(&p1[0]).map_err(malformed)?;
            let pe2 = parse_sexpr(&p2[0]).map_err(malformed)?;
            let ce = parse_sexpr(&clause[0]).map_err(malformed)?;
            let (a1, b1) = as_binary("=", &pe1)
                .ok_or_else(|| invalid(format!("trans premise '{}' is not an equality", p1[0])))?;
            let (a2, b2) = as_binary("=", &pe2)
                .ok_or_else(|| invalid(format!("trans premise '{}' is not an equality", p2[0])))?;
            let (u, v) = as_binary("=", &ce).ok_or_else(|| {
                invalid(format!(
                    "trans conclusion '{}' is not an equality",
                    clause[0]
                ))
            })?;
            if trans_chains_to(a1, b1, a2, b2, u, v) {
                Ok(())
            } else {
                Err(invalid(format!(
                    "trans conclusion '{}' does not follow from premises '{}' and '{}'",
                    clause[0], p1[0], p2[0]
                )))
            }
        }
        AletheRule::Cong | AletheRule::EqCong => {
            if clause.len() != 1 {
                return Ok(()); // multi-literal congruence steps are out of scope
            }
            let e = parse_sexpr(&clause[0]).map_err(malformed)?;
            let Some((l, r)) = as_binary("=", &e) else {
                return Ok(());
            };
            let (Some((lf, largs)), Some((rf, rargs))) = (as_call(l), as_call(r)) else {
                return Ok(());
            };
            if lf != rf || largs.len() != rargs.len() {
                return Err(invalid(format!(
                    "cong conclusion '{}' does not equate two applications of the same function",
                    clause[0]
                )));
            }
            let mut premise_iter = premises.iter();
            for i in 0..largs.len() {
                if largs[i] == rargs[i] {
                    continue;
                }
                let Some(premise_clause) =
                    premise_iter.next().and_then(|idx| clause_by_index.get(idx))
                else {
                    return Err(invalid(format!(
                        "cong conclusion '{}' has no premise establishing argument {i} equal",
                        clause[0]
                    )));
                };
                if premise_clause.len() != 1 {
                    continue; // cannot verify this premise's shape; skip rather than reject
                }
                let Ok(p) = parse_sexpr(&premise_clause[0]) else {
                    continue;
                };
                let Some((pa, pb)) = as_binary("=", &p) else {
                    continue;
                };
                if !((pa == &largs[i] && pb == &rargs[i]) || (pa == &rargs[i] && pb == &largs[i])) {
                    return Err(invalid(format!(
                        "cong premise '{}' does not establish argument {i} equal",
                        premise_clause[0]
                    )));
                }
            }
            Ok(())
        }
        AletheRule::Resolution => {
            // Necessary condition: every literal in the concluded clause must
            // appear in at least one premise clause (basic resolution only
            // ever drops the resolved-on pivot literals and unions the rest).
            // This does not verify a valid pivot chain exists -- doing so
            // would require pivot literals the format does not record here --
            // but it does reject conclusions containing literals fabricated
            // out of nowhere.
            let mut allowed: HashSet<SExpr> = HashSet::new();
            let mut any_premise_known = false;
            for idx in premises {
                if let Some(pc) = clause_by_index.get(idx) {
                    any_premise_known = true;
                    for lit in pc {
                        if let Ok(e) = parse_sexpr(lit) {
                            allowed.insert(e);
                        }
                    }
                }
            }
            if !any_premise_known {
                return Ok(());
            }
            for lit in clause {
                let e = parse_sexpr(lit).map_err(malformed)?;
                if !allowed.contains(&e) {
                    return Err(invalid(format!(
                        "resolution conclusion literal '{lit}' does not appear in any premise clause"
                    )));
                }
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::theory::ProofTerm;

    #[test]
    fn test_check_result_is_valid() {
        assert!(CheckResult::Valid.is_valid());
        assert!(
            !CheckResult::Invalid {
                step: 0,
                error: CheckError::EmptyProof
            }
            .is_valid()
        );
    }

    #[test]
    fn test_check_error_display() {
        let err = CheckError::MissingPremise(5);
        let msg = format!("{}", err);
        assert!(msg.contains("5"));
        assert!(msg.contains("does not exist"));

        let err = CheckError::WrongPremiseCount {
            expected: 2,
            got: 1,
        };
        let msg = format!("{}", err);
        assert!(msg.contains("requires 2"));
        assert!(msg.contains("1 was provided"));
    }

    #[test]
    fn test_theory_proof_empty() {
        let proof = TheoryProof::new();
        let result = proof.check();
        assert!(!result.is_valid());
        assert!(matches!(result.error(), Some(CheckError::EmptyProof)));
    }

    #[test]
    fn test_theory_proof_valid_refl() {
        let mut proof = TheoryProof::new();
        proof.refl("x");

        let result = proof.check();
        assert!(result.is_valid());
    }

    #[test]
    fn test_theory_proof_valid_transitivity() {
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        proof.trans(s1, s2, "a", "c");

        let result = proof.check();
        assert!(result.is_valid());
    }

    #[test]
    fn test_theory_proof_invalid_trans_premises() {
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        // Trans with only 1 premise should fail
        proof.add_step(TheoryRule::Trans, vec![s1], "(= a c)");

        let result = proof.check();
        assert!(!result.is_valid());
    }

    #[test]
    fn test_theory_proof_missing_premise() {
        let mut proof = TheoryProof::new();
        // Reference a non-existent premise
        proof.add_step(
            TheoryRule::Trans,
            vec![TheoryStepId(99), TheoryStepId(100)],
            "(= a c)",
        );

        let result = proof.check();
        assert!(!result.is_valid());
        assert!(matches!(
            result.error(),
            Some(CheckError::MissingPremise(_))
        ));
    }

    #[test]
    fn test_alethe_proof_empty() {
        let proof = AletheProof::new();
        let result = proof.check();
        assert!(!result.is_valid());
    }

    #[test]
    fn test_alethe_proof_valid() {
        let mut proof = AletheProof::new();
        proof.assume("p");
        proof.step_simple(vec![], AletheRule::Refl);

        let result = proof.check();
        assert!(result.is_valid());
    }

    #[test]
    fn test_checker_continue_on_error() {
        let mut proof = TheoryProof::new();
        // Multiple invalid steps
        proof.add_step(TheoryRule::Trans, vec![TheoryStepId(99)], "(= a b)");
        proof.add_step(TheoryRule::Trans, vec![TheoryStepId(100)], "(= c d)");

        let config = CheckerConfig {
            continue_on_error: true,
            ..Default::default()
        };

        let result = proof.check_with_config(config);
        assert!(matches!(result, CheckResult::MultipleErrors(_)));
    }

    #[test]
    fn test_checker_refl_with_premises_fails() {
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        // Refl should have no premises
        proof.add_step(TheoryRule::Refl, vec![s1], "(= x x)");

        let result = proof.check();
        assert!(!result.is_valid());
    }

    #[test]
    fn test_checker_farkas_needs_premises() {
        let mut proof = TheoryProof::new();
        // Farkas with only 1 premise should fail
        let s1 = proof.add_axiom(TheoryRule::Custom("bound".into()), "(>= x 0)");
        proof.add_step(TheoryRule::LaGeneric, vec![s1], "false");

        let result = proof.check();
        assert!(!result.is_valid());
    }

    #[test]
    fn test_checker_arr_read_write_1_axiom() {
        let mut proof = TheoryProof::new();
        // ArrReadWrite1 is an axiom (no premises)
        proof.add_axiom(TheoryRule::ArrReadWrite1, "(= (select (store a i v) i) v)");

        let result = proof.check();
        assert!(result.is_valid());
    }

    #[test]
    fn test_checker_arr_read_write_2_needs_premise() {
        let mut proof = TheoryProof::new();
        // ArrReadWrite2 needs proof of i ≠ j
        proof.add_axiom(
            TheoryRule::ArrReadWrite2,
            "(= (select (store a i v) j) (select a j))",
        );

        let result = proof.check();
        assert!(!result.is_valid());
    }

    // ------------------------------------------------------------------
    // verify_conclusions gating (audit finding proof-p3 / checker.rs:279)
    // ------------------------------------------------------------------

    #[test]
    fn test_verify_conclusions_off_accepts_bogus_trans_conclusion() {
        // Default config: verify_conclusions is false, so only structural
        // checks run. A Trans step whose conclusion has nothing to do with
        // its premises must still be accepted (unchanged legacy behavior).
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        proof.add_step(TheoryRule::Trans, vec![s1, s2], "(= x y)");

        let result = proof.check();
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_rejects_bogus_trans_conclusion() {
        // Same proof as above, but with verify_conclusions: true the
        // fabricated conclusion "(= x y)" must now be rejected: it does not
        // follow from "(= a b)" and "(= b c)".
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        proof.add_step(TheoryRule::Trans, vec![s1, s2], "(= x y)");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(!result.is_valid());
        assert!(matches!(
            result.error(),
            Some(CheckError::InvalidConclusion(_))
        ));
    }

    #[test]
    fn test_verify_conclusions_on_accepts_genuine_trans_conclusion() {
        // A correctly derived transitivity conclusion must still pass with
        // semantic checking enabled.
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        proof.trans(s1, s2, "a", "c");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_accepts_reversed_premise_trans() {
        // Transitivity must also chain correctly when a premise equality is
        // stated in the reverse orientation.
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b a)");
        let s2 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= b c)");
        proof.add_step(TheoryRule::Trans, vec![s1, s2], "(= a c)");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_rejects_bogus_refl() {
        let mut proof = TheoryProof::new();
        proof.add_axiom(TheoryRule::Refl, "(= x y)");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(!result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_accepts_genuine_refl() {
        let mut proof = TheoryProof::new();
        proof.refl("x");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_rejects_bogus_symm() {
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        proof.add_step(TheoryRule::Symm, vec![s1], "(= a b)");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(!result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_accepts_genuine_symm() {
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        proof.symm(s1, "a", "b");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_accepts_genuine_cong() {
        let mut proof = TheoryProof::new();
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        proof.cong(
            vec![s1],
            "f",
            &[ProofTerm::from("a")],
            &[ProofTerm::from("b")],
        );

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_rejects_bogus_cong() {
        let mut proof = TheoryProof::new();
        // Premise establishes a = b, but the congruence conclusion claims
        // f(a) = f(c) -- c was never shown equal to a.
        let s1 = proof.add_axiom(TheoryRule::Custom("assert".into()), "(= a b)");
        proof.add_step(TheoryRule::Cong, vec![s1], "(= (f a) (f c))");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(!result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_rejects_bogus_array_axiom() {
        let mut proof = TheoryProof::new();
        // Claims the wrong value is returned by the store-then-select.
        proof.add_axiom(TheoryRule::ArrReadWrite1, "(= (select (store a i v) i) w)");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(!result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_on_accepts_genuine_array_axiom() {
        let mut proof = TheoryProof::new();
        proof.add_axiom(TheoryRule::ArrReadWrite1, "(= (select (store a i v) i) v)");

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_alethe_off_accepts_bogus_trans() {
        let mut proof = AletheProof::new();
        let a1 = proof.assume("(= a b)");
        let a2 = proof.assume("(= b c)");
        proof.step(
            vec!["(= x y)".to_string()],
            AletheRule::Trans,
            vec![a1, a2],
            vec![],
        );

        let result = proof.check();
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_alethe_on_rejects_bogus_trans() {
        let mut proof = AletheProof::new();
        let a1 = proof.assume("(= a b)");
        let a2 = proof.assume("(= b c)");
        proof.step(
            vec!["(= x y)".to_string()],
            AletheRule::Trans,
            vec![a1, a2],
            vec![],
        );

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(!result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_alethe_on_accepts_genuine_trans() {
        let mut proof = AletheProof::new();
        let a1 = proof.assume("(= a b)");
        let a2 = proof.assume("(= b c)");
        proof.step(
            vec!["(= a c)".to_string()],
            AletheRule::Trans,
            vec![a1, a2],
            vec![],
        );

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_alethe_on_rejects_bogus_resolution() {
        let mut proof = AletheProof::new();
        let a1 = proof.assume("p");
        let a2 = proof.assume("(not p)");
        // A conclusion literal ("q") that appears in neither premise clause
        // cannot be derived by resolution from them.
        proof.step(
            vec!["q".to_string()],
            AletheRule::Resolution,
            vec![a1, a2],
            vec![],
        );

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(!result.is_valid());
    }

    #[test]
    fn test_verify_conclusions_alethe_on_accepts_valid_resolution() {
        let mut proof = AletheProof::new();
        // Two "input" clauses [p, q] and [(not p)]; resolving on p yields [q].
        let c1 = proof.step(
            vec!["p".to_string(), "q".to_string()],
            AletheRule::Input,
            vec![],
            vec![],
        );
        let c2 = proof.step(
            vec!["(not p)".to_string()],
            AletheRule::Input,
            vec![],
            vec![],
        );
        proof.step(
            vec!["q".to_string()],
            AletheRule::Resolution,
            vec![c1, c2],
            vec![],
        );

        let config = CheckerConfig {
            verify_conclusions: true,
            ..Default::default()
        };
        let result = proof.check_with_config(config);
        assert!(result.is_valid());
    }
}
