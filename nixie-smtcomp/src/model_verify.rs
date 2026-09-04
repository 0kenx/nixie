//! Model verification for SAT results
//!
//! This module provides functionality to verify models returned by SMT solvers
//! for satisfiable formulas.

use crate::benchmark::{BenchmarkStatus, SingleResult};
use crate::loader::Benchmark;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::smtlib::{Command, parse_script};
use nixie_solver::Solver;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;
use thiserror::Error;

/// Error type for model verification
#[derive(Error, Debug)]
pub enum ModelVerifyError {
    /// Parse error
    #[error("Parse error: {0}")]
    ParseError(String),
    /// Solver error
    #[error("Solver error: {0}")]
    SolverError(String),
    /// Model extraction failed
    #[error("Failed to extract model: {0}")]
    ModelExtractionFailed(String),
    /// Model verification failed
    #[error("Model verification failed: {0}")]
    VerificationFailed(String),
}

/// Result type for model verification
pub type ModelVerifyResult<T> = Result<T, ModelVerifyError>;

/// A model assignment (variable name -> value)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Model {
    /// Boolean assignments
    pub bools: HashMap<String, bool>,
    /// Integer assignments
    pub ints: HashMap<String, i64>,
    /// Real assignments (as string for precision)
    pub reals: HashMap<String, String>,
    /// Bitvector assignments
    pub bitvectors: HashMap<String, u64>,
}

impl Default for Model {
    fn default() -> Self {
        Self::new()
    }
}

impl Model {
    /// Create an empty model
    #[must_use]
    pub fn new() -> Self {
        Self {
            bools: HashMap::new(),
            ints: HashMap::new(),
            reals: HashMap::new(),
            bitvectors: HashMap::new(),
        }
    }

    /// Check if model is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bools.is_empty()
            && self.ints.is_empty()
            && self.reals.is_empty()
            && self.bitvectors.is_empty()
    }

    /// Get total number of assignments
    #[must_use]
    pub fn len(&self) -> usize {
        self.bools.len() + self.ints.len() + self.reals.len() + self.bitvectors.len()
    }

    /// Add a boolean assignment
    pub fn add_bool(&mut self, name: impl Into<String>, value: bool) {
        self.bools.insert(name.into(), value);
    }

    /// Add an integer assignment
    pub fn add_int(&mut self, name: impl Into<String>, value: i64) {
        self.ints.insert(name.into(), value);
    }

    /// Add a real assignment
    pub fn add_real(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.reals.insert(name.into(), value.into());
    }

    /// Add a bitvector assignment
    pub fn add_bitvector(&mut self, name: impl Into<String>, value: u64) {
        self.bitvectors.insert(name.into(), value);
    }

    /// Format model for SMT-LIB output
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        let mut lines = Vec::new();
        lines.push("(model".to_string());

        for (name, value) in &self.bools {
            lines.push(format!("  (define-fun {} () Bool {})", name, value));
        }
        for (name, value) in &self.ints {
            if *value >= 0 {
                lines.push(format!("  (define-fun {} () Int {})", name, value));
            } else {
                lines.push(format!("  (define-fun {} () Int (- {}))", name, -value));
            }
        }
        for (name, value) in &self.reals {
            lines.push(format!("  (define-fun {} () Real {})", name, value));
        }
        for (name, value) in &self.bitvectors {
            lines.push(format!(
                "  (define-fun {} () (_ BitVec 64) #x{:016x})",
                name, value
            ));
        }

        lines.push(")".to_string());
        lines.join("\n")
    }
}

/// Verification result for a single benchmark
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResult {
    /// Path to the benchmark
    pub benchmark: String,
    /// Original solver result
    pub solver_status: BenchmarkStatus,
    /// Whether verification was attempted
    pub verified: bool,
    /// Whether the model was valid
    pub model_valid: Option<bool>,
    /// The extracted model (if any)
    pub model: Option<Model>,
    /// Error message if verification failed
    pub error: Option<String>,
    /// Time taken for verification
    pub verification_time: Duration,
}

impl VerificationResult {
    /// Create a result for a non-SAT case (no verification needed)
    #[must_use]
    pub fn not_applicable(benchmark: &str, status: BenchmarkStatus) -> Self {
        Self {
            benchmark: benchmark.to_string(),
            solver_status: status,
            verified: false,
            model_valid: None,
            model: None,
            error: None,
            verification_time: Duration::ZERO,
        }
    }

    /// Create a successful verification result
    #[must_use]
    pub fn success(benchmark: &str, model: Model, time: Duration) -> Self {
        Self {
            benchmark: benchmark.to_string(),
            solver_status: BenchmarkStatus::Sat,
            verified: true,
            model_valid: Some(true),
            model: Some(model),
            error: None,
            verification_time: time,
        }
    }

    /// Create a failed verification result
    #[must_use]
    pub fn failure(benchmark: &str, model: Option<Model>, error: String, time: Duration) -> Self {
        Self {
            benchmark: benchmark.to_string(),
            solver_status: BenchmarkStatus::Sat,
            verified: true,
            model_valid: Some(false),
            model,
            error: Some(error),
            verification_time: time,
        }
    }

    /// Create an error result (verification could not be performed)
    #[must_use]
    pub fn error(benchmark: &str, error: String) -> Self {
        Self {
            benchmark: benchmark.to_string(),
            solver_status: BenchmarkStatus::Error,
            verified: false,
            model_valid: None,
            model: None,
            error: Some(error),
            verification_time: Duration::ZERO,
        }
    }
}

/// Model verifier
pub struct ModelVerifier {
    /// Timeout for verification
    timeout: Duration,
}

impl Default for ModelVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl ModelVerifier {
    /// Create a new model verifier
    #[must_use]
    pub fn new() -> Self {
        Self {
            timeout: Duration::from_secs(30),
        }
    }

    /// Set verification timeout
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Verify a benchmark result that was SAT
    pub fn verify(&self, benchmark: &Benchmark, result: &SingleResult) -> VerificationResult {
        let benchmark_name = benchmark
            .meta
            .path
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_default();

        // Only verify SAT results
        if result.status != BenchmarkStatus::Sat {
            return VerificationResult::not_applicable(&benchmark_name, result.status);
        }

        let start = std::time::Instant::now();

        // Parse benchmark and solve to get model
        let mut tm = TermManager::new();
        let commands = match parse_script(&benchmark.content, &mut tm) {
            Ok(cmds) => cmds,
            Err(e) => {
                return VerificationResult::error(&benchmark_name, format!("Parse error: {}", e));
            }
        };

        let mut solver = Solver::new();
        // (name, declared term, sort) -- the term is kept (not discarded) so
        // `extract_model` can evaluate the actual variable under the model
        // instead of fabricating a placeholder value.
        let mut variables: Vec<(String, TermId, String)> = Vec::new();
        let mut assertions: Vec<TermId> = Vec::new();

        // Execute commands to collect constraints and variables
        for cmd in &commands {
            match cmd {
                Command::SetLogic(logic) => {
                    solver.set_logic(logic);
                }
                Command::DeclareConst(name, sort) => {
                    let sort_id = parse_sort(sort, &tm);
                    let var = tm.mk_var(name, sort_id);
                    variables.push((name.clone(), var, sort.clone()));
                }
                Command::DeclareFun(name, arg_sorts, ret_sort) if arg_sorts.is_empty() => {
                    let sort_id = parse_sort(ret_sort, &tm);
                    let var = tm.mk_var(name, sort_id);
                    variables.push((name.clone(), var, ret_sort.clone()));
                }
                Command::DeclareFun(..) => {}
                // A recursive definition is the only thing constraining the
                // symbol it defines; silently dropping it would answer a
                // strictly weaker problem. Bail out of verification rather
                // than certify a weaker formula. (Upstream v0.3.3.)
                Command::DefineFunsRec(_) => {
                    // Honest bail-out: refuse to certify rather than verify a
                    // weaker formula.
                    return VerificationResult::failure(
                        &benchmark_name,
                        None,
                        "recursive function definitions are not supported by                          the model verifier"
                            .to_string(),
                        start.elapsed(),
                    );
                }
                // `:named` assertions must be asserted too -- skipping them
                // (as the previous version of this loop did) would silently
                // re-solve a *weaker* formula than the benchmark actually
                // states, which is exactly the kind of "verification that
                // doesn't verify" this module exists to avoid.
                Command::Assert(term) | Command::AssertNamed(term, _) => {
                    solver.assert(*term, &mut tm);
                    assertions.push(*term);
                }
                _ => {}
            }
        }

        // Check satisfiability and get model
        let check_result = solver.check(&mut tm);
        if check_result != nixie_solver::SolverResult::Sat {
            return VerificationResult::error(
                &benchmark_name,
                "Could not reproduce SAT result for model extraction".to_string(),
            );
        }

        let Some(solver_model) = solver.model() else {
            return VerificationResult::error(
                &benchmark_name,
                "solver reported sat but produced no model".to_string(),
            );
        };

        // Real verification: evaluate every top-level assertion under the
        // model the solver actually produced (via `Model::eval`, the same
        // evaluator `Context::eval_in_model`/`--validate-model` use) and
        // record which ones fail to reduce to `true`, instead of trusting
        // "solver said sat" as a proxy for "model is valid".
        let true_id = tm.mk_true();
        let total = assertions.len();
        let mut failing: Vec<usize> = Vec::new();
        for (idx, &assertion) in assertions.iter().enumerate() {
            let evaluated = solver_model.eval(assertion, &mut tm);
            if evaluated != true_id {
                failing.push(idx);
            }
        }

        // Extract the reported model *after* evaluation so both operations
        // read the same solver-produced assignments.
        let model = self.extract_model(&solver, &variables, &mut tm);
        let elapsed = start.elapsed();

        if failing.is_empty() {
            VerificationResult::success(&benchmark_name, model, elapsed)
        } else {
            let preview: Vec<String> = failing
                .iter()
                .take(5)
                .map(|idx| format!("#{}", idx + 1))
                .collect();
            let message = format!(
                "{} of {} assertion(s) do not evaluate to true under the extracted model \
                 (failing assertion index(es): {}{})",
                failing.len(),
                total,
                preview.join(", "),
                if failing.len() > preview.len() {
                    ", ..."
                } else {
                    ""
                }
            );
            VerificationResult::failure(&benchmark_name, Some(model), message, elapsed)
        }
    }

    /// Verify multiple results
    pub fn verify_all(
        &self,
        benchmarks: &[Benchmark],
        results: &[SingleResult],
    ) -> Vec<VerificationResult> {
        benchmarks
            .iter()
            .zip(results.iter())
            .map(|(bench, result)| self.verify(bench, result))
            .collect()
    }

    /// Extract the model the solver actually produced.
    ///
    /// For each declared variable, evaluates its term under
    /// [`nixie_solver::solver::Model::eval`] (the solver's real assignment,
    /// not a fabricated default) and records the resulting constant. A
    /// variable that has no assignment in the model (e.g. it is genuinely
    /// unconstrained, or its sort has no built-in constant representation
    /// here, such as an uninterpreted sort) is honestly omitted rather than
    /// filled in with a placeholder value.
    fn extract_model(
        &self,
        solver: &Solver,
        variables: &[(String, TermId, String)],
        tm: &mut TermManager,
    ) -> Model {
        let mut model = Model::new();

        let Some(solver_model) = solver.model() else {
            return model;
        };

        for (name, term, _sort) in variables {
            let value_id = solver_model.eval(*term, tm);
            let Some(value_term) = tm.get(value_id) else {
                continue;
            };
            match &value_term.kind {
                TermKind::True => model.add_bool(name, true),
                TermKind::False => model.add_bool(name, false),
                TermKind::IntConst(n) => {
                    // `Model.ints` is `i64`-keyed; a value outside that
                    // range is reported as a `Real` string instead of
                    // silently truncating or dropping it.
                    match n.to_string().parse::<i64>() {
                        Ok(v) => model.add_int(name, v),
                        Err(_) => model.add_real(name, n.to_string()),
                    }
                }
                TermKind::RealConst(r) => model.add_real(name, r.to_string()),
                TermKind::BitVecConst { value, .. } => {
                    // `Model.bitvectors` is `u64`-keyed; a wider value is
                    // reported as `Real` (decimal string) instead, for the
                    // same reason as the `IntConst` fallback above.
                    match value.to_string().parse::<u64>() {
                        Ok(v) => model.add_bitvector(name, v),
                        Err(_) => model.add_real(name, value.to_string()),
                    }
                }
                // Unassigned variable, or a value this reporting `Model`
                // has no field for (e.g. an uninterpreted-sort witness):
                // omit rather than fabricate.
                _ => {}
            }
        }

        model
    }
}

/// Parse sort string to sort ID
fn parse_sort(sort_str: &str, tm: &TermManager) -> nixie_core::sort::SortId {
    match sort_str {
        "Bool" => tm.sorts.bool_sort,
        "Int" => tm.sorts.int_sort,
        "Real" => tm.sorts.real_sort,
        _ => tm.sorts.bool_sort,
    }
}

/// Summary of verification results
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct VerificationSummary {
    /// Total SAT results
    pub total_sat: usize,
    /// Successfully verified
    pub verified_valid: usize,
    /// Failed verification
    pub verified_invalid: usize,
    /// Verification errors
    pub errors: usize,
    /// Benchmarks not requiring verification (non-SAT)
    pub not_applicable: usize,
}

impl VerificationSummary {
    /// Create summary from verification results
    #[must_use]
    pub fn from_results(results: &[VerificationResult]) -> Self {
        let mut summary = Self::default();

        for result in results {
            if !result.verified {
                if result.error.is_some() {
                    summary.errors += 1;
                } else {
                    summary.not_applicable += 1;
                }
            } else {
                summary.total_sat += 1;
                match result.model_valid {
                    Some(true) => summary.verified_valid += 1,
                    Some(false) => summary.verified_invalid += 1,
                    None => summary.errors += 1,
                }
            }
        }

        summary
    }

    /// Get verification success rate
    #[must_use]
    pub fn success_rate(&self) -> f64 {
        if self.total_sat == 0 {
            100.0
        } else {
            (self.verified_valid as f64 / self.total_sat as f64) * 100.0
        }
    }

    /// Check if all verifications passed
    #[must_use]
    pub fn all_valid(&self) -> bool {
        self.verified_invalid == 0 && self.errors == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::loader::{BenchmarkMeta, ExpectedStatus};
    use std::path::PathBuf;

    fn make_test_benchmark(content: &str) -> Benchmark {
        Benchmark {
            meta: BenchmarkMeta {
                path: PathBuf::from("/tmp/test.smt2"),
                logic: Some("QF_LIA".to_string()),
                expected_status: Some(ExpectedStatus::Sat),
                file_size: content.len() as u64,
                category: None,
                structural_features: None,
            },
            content: content.to_string(),
        }
    }

    #[test]
    fn test_model_creation() {
        let mut model = Model::new();
        model.add_bool("x", true);
        model.add_int("y", 42);
        model.add_real("z", "3.14");

        assert_eq!(model.len(), 3);
        assert!(!model.is_empty());
        assert_eq!(model.bools.get("x"), Some(&true));
        assert_eq!(model.ints.get("y"), Some(&42));
    }

    #[test]
    fn test_model_smtlib_output() {
        let mut model = Model::new();
        model.add_bool("b", true);
        model.add_int("i", -5);

        let output = model.to_smtlib();
        assert!(output.contains("(model"));
        assert!(output.contains("define-fun b"));
        assert!(output.contains("define-fun i"));
    }

    #[test]
    fn test_verification_result_not_applicable() {
        let result = VerificationResult::not_applicable("test.smt2", BenchmarkStatus::Unsat);
        assert!(!result.verified);
        assert!(result.model.is_none());
    }

    #[test]
    fn test_verification_summary() {
        let results = vec![
            VerificationResult::success("a.smt2", Model::new(), Duration::from_millis(10)),
            VerificationResult::success("b.smt2", Model::new(), Duration::from_millis(20)),
            VerificationResult::not_applicable("c.smt2", BenchmarkStatus::Unsat),
        ];

        let summary = VerificationSummary::from_results(&results);
        assert_eq!(summary.total_sat, 2);
        assert_eq!(summary.verified_valid, 2);
        assert_eq!(summary.not_applicable, 1);
        assert!(summary.all_valid());
    }

    #[test]
    fn test_model_verifier() {
        let benchmark = make_test_benchmark(
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)",
        );

        let result = SingleResult::new(
            &benchmark.meta,
            BenchmarkStatus::Sat,
            Duration::from_millis(100),
        );

        let verifier = ModelVerifier::new();
        let verification = verifier.verify(&benchmark, &result);

        // Should attempt verification since result was SAT
        assert!(verification.verified || verification.error.is_some());
    }

    /// `extract_model` used to always report `x -> 0` (a hardcoded
    /// placeholder) regardless of the actual constraint. `(assert (= x 5))`
    /// has exactly one satisfying value for `x`; the extracted model must
    /// report that real value, not the old placeholder.
    #[test]
    fn test_extracted_model_reports_real_solver_values_not_placeholders() {
        let benchmark = make_test_benchmark(
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 5))\n(check-sat)",
        );
        let result = SingleResult::new(
            &benchmark.meta,
            BenchmarkStatus::Sat,
            Duration::from_millis(100),
        );

        let verification = ModelVerifier::new().verify(&benchmark, &result);

        assert!(
            verification.verified,
            "expected verification to run: {verification:?}"
        );
        assert_eq!(
            verification.model_valid,
            Some(true),
            "x = 5 genuinely satisfies (= x 5): {verification:?}"
        );
        let model = verification
            .model
            .as_ref()
            .expect("a model must be reported for a verified sat result");
        assert_eq!(
            model.ints.get("x"),
            Some(&5),
            "extracted model must report the real solved value (5), not a fabricated \
             placeholder: {model:?}"
        );
    }

    /// Every top-level assertion must be checked, not just the first one.
    /// Two assertions pin `x` and `y` to distinct, non-default values;
    /// the old placeholder extractor (`Bool -> true`, `Int -> 0`,
    /// `Real -> 0.0`) would have reported wrong values for both.
    #[test]
    fn test_extracted_model_checks_every_assertion() {
        let benchmark = make_test_benchmark(
            "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n\
             (assert (= x 7))\n(assert (= y (+ x 3)))\n(check-sat)",
        );
        let result = SingleResult::new(
            &benchmark.meta,
            BenchmarkStatus::Sat,
            Duration::from_millis(100),
        );

        let verification = ModelVerifier::new().verify(&benchmark, &result);

        assert_eq!(verification.model_valid, Some(true), "{verification:?}");
        let model = verification.model.as_ref().expect("model must be present");
        assert_eq!(model.ints.get("x"), Some(&7), "{model:?}");
        assert_eq!(model.ints.get("y"), Some(&10), "{model:?}");
    }

    /// `:named` assertions used to be silently skipped by the re-solve loop
    /// (only plain `Assert` was handled), so a benchmark relying on one
    /// would be verified against a strictly weaker formula than it actually
    /// states. `(! (= x 9) :named x-is-nine)` must be asserted and checked
    /// like any other top-level assertion.
    #[test]
    fn test_named_assertions_are_asserted_and_checked() {
        let benchmark = make_test_benchmark(
            "(set-logic QF_LIA)\n(declare-const x Int)\n\
             (assert (! (= x 9) :named x-is-nine))\n(check-sat)",
        );
        let result = SingleResult::new(
            &benchmark.meta,
            BenchmarkStatus::Sat,
            Duration::from_millis(100),
        );

        let verification = ModelVerifier::new().verify(&benchmark, &result);

        assert_eq!(verification.model_valid, Some(true), "{verification:?}");
        let model = verification.model.as_ref().expect("model must be present");
        assert_eq!(
            model.ints.get("x"),
            Some(&9),
            "the :named assertion must actually constrain x: {model:?}"
        );
    }

    /// A Boolean constant forced to `false` must be reported as `false`,
    /// not the old placeholder that always reported `true` regardless of
    /// the actual constraint.
    #[test]
    fn test_extracted_bool_value_is_not_always_true() {
        let benchmark =
            make_test_benchmark("(declare-const b Bool)\n(assert (not b))\n(check-sat)");
        let result = SingleResult::new(
            &benchmark.meta,
            BenchmarkStatus::Sat,
            Duration::from_millis(100),
        );

        let verification = ModelVerifier::new().verify(&benchmark, &result);

        assert_eq!(verification.model_valid, Some(true), "{verification:?}");
        let model = verification.model.as_ref().expect("model must be present");
        assert_eq!(
            model.bools.get("b"),
            Some(&false),
            "(assert (not b)) forces b = false: {model:?}"
        );
    }
}
