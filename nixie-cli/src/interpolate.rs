//! Interpolant generation support for Nixie CLI
//!
//! This module provides Craig interpolation functionality through the CLI.
//! It parses `(assert-partition A|B <formula>)` commands (plus any ordinary
//! declarations/`set-logic` commands) out of a script, actually solves
//! `A ∧ B` with the real Nixie solver to determine satisfiability, and -- when
//! unsat -- attempts genuine proof-based Craig interpolation via
//! `nixie_proof::craig::CraigInterpolator`.
//!
//! # Building a real A/B partition
//!
//! `nixie-proof`'s `premise` module (`PremiseTracker`/`PremiseId`) is now
//! public, so this module registers every parsed A/B assertion with a real
//! [`PremiseTracker`] and builds a genuine [`InterpolantPartition`] from the
//! resulting premise IDs -- no more guessing or vacuous partitions.
//!
//! # A remaining upstream limitation
//!
//! `CraigInterpolator` attributes a proof axiom to the A or B side by
//! looking up its *conclusion text* in the `PremiseTracker` (see
//! `nixie-proof/src/craig/mod.rs`). To exercise that path for a real solve,
//! this module asks `nixie-solver` to write a binary proof log
//! (`Context::set_proof_log_path`) and reads it back with
//! `nixie_proof::replay::ProofReplayer` to reconstruct an `nixie_proof::Proof`.
//! However, `nixie-solver`'s proof-log writer (see
//! `Context::write_proof_log` in `nixie-solver/src/context.rs`) currently
//! labels every axiom with a synthetic, per-clause tag -- `input-clause-<n>`,
//! `resolution-<n>`, `theory-lemma-<theory>-<n>` -- rather than the original
//! SMT-LIB assertion text. Those tags never match anything registered in our
//! `PremiseTracker` (which holds the real `(assert-partition A|B ...)`
//! formula text), so every axiom would fall back to `CraigInterpolator`'s
//! unattributed McMillan symbol-membership heuristic and produce an
//! interpolant that is not actually validated against the real A/B split.
//!
//! Rather than present that as a genuine result, [`solve_and_interpolate`]
//! checks -- after replaying the real proof log -- whether *any* axiom's
//! conclusion was directly attributable via the partition. If none was, it
//! honestly reports the limitation instead of returning an unattributed
//! formula. Because the check is performed against the actual replayed
//! proof (not hard-coded), this starts working automatically the moment
//! `nixie-solver` logs proofs with real assertion-level conclusions --
//! without any further changes here.

use nixie_proof::proof::{Proof, ProofStep};
use nixie_proof::replay::ProofReplayer;
use nixie_proof::{
    CraigInterpolator, InterpolantPartition, InterpolationAlgorithm, InterpolationConfig,
    PremiseId, PremiseTracker,
};
use nixie_solver::{Context, SolverResult};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

/// Output format for interpolants
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InterpolateFormat {
    /// SMT-LIB2 format (default)
    #[default]
    Smtlib,
    /// Plain text format
    Text,
    /// JSON format
    Json,
}

impl InterpolateFormat {
    /// Parse format from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "smtlib" | "smt2" | "smtlib2" => Some(Self::Smtlib),
            "text" | "plain" => Some(Self::Text),
            "json" => Some(Self::Json),
            _ => None,
        }
    }
}

impl fmt::Display for InterpolateFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Smtlib => write!(f, "smtlib"),
            Self::Text => write!(f, "text"),
            Self::Json => write!(f, "json"),
        }
    }
}

/// Result of interpolation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterpolationResult {
    /// The computed interpolant formula (empty when unavailable)
    pub interpolant: String,
    /// Satisfiability status of A ∧ B: "sat", "unsat", "unknown", or "error"
    pub status: String,
    /// A partition assertions
    pub a_assertions: Vec<String>,
    /// B partition assertions
    pub b_assertions: Vec<String>,
    /// Statistics about the interpolation
    pub stats: Option<InterpolationStatistics>,
    /// Error message if any
    pub error: Option<String>,
}

/// Statistics about interpolation computation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterpolationStatistics {
    /// Number of A assertions
    pub a_count: usize,
    /// Number of B assertions
    pub b_count: usize,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Algorithm requested (mcmillan/pudlak/huang)
    pub algorithm: String,
}

/// Strip `;`-comments from an SMT-LIB2 script (to end of line).
fn strip_comments(script: &str) -> String {
    let mut out = String::with_capacity(script.len());
    let mut chars = script.chars().peekable();
    while let Some(c) = chars.next() {
        if c == ';' {
            for c2 in chars.by_ref() {
                if c2 == '\n' {
                    out.push('\n');
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Split a script into its top-level parenthesized forms, using paren-depth
/// tracking so that forms spanning multiple lines are captured whole. This
/// is more robust than line-based scanning, which would split a multi-line
/// `(assert-partition A ...)` formula into several bogus fragments.
fn top_level_forms(script: &str) -> Vec<String> {
    let cleaned = strip_comments(script);
    let chars: Vec<char> = cleaned.chars().collect();
    let mut forms = Vec::new();
    let mut depth = 0i32;
    let mut start: Option<usize> = None;

    for (i, &c) in chars.iter().enumerate() {
        match c {
            '(' => {
                if depth == 0 {
                    start = Some(i);
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0
                    && let Some(s) = start.take()
                {
                    forms.push(chars[s..=i].iter().collect());
                }
            }
            _ => {}
        }
    }

    forms
}

/// The pieces extracted from an interpolation script: declarations/other
/// commands to replay verbatim (the "preamble"), and the raw A/B formula
/// texts pulled out of `(assert-partition ...)` commands.
struct ParsedInterpolationScript {
    preamble: String,
    a_assertions: Vec<String>,
    b_assertions: Vec<String>,
}

/// Parse a script for `(assert-partition A|B <formula>)` commands, in a
/// paren-balanced (multi-line-safe) way. Every other top-level form is kept
/// verbatim in the preamble so declarations, `set-logic`, etc. still reach
/// the real solver.
fn parse_interpolation_script(script: &str) -> ParsedInterpolationScript {
    let mut preamble = String::new();
    let mut a_assertions = Vec::new();
    let mut b_assertions = Vec::new();

    for form in top_level_forms(script) {
        let trimmed = form.trim();
        let Some(inner) = trimmed.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
            continue;
        };
        let inner = inner.trim();

        if let Some(rest) = inner.strip_prefix("assert-partition") {
            let rest = rest.trim();
            let mut chars = rest.char_indices();
            if let Some((_, tag)) = chars.next() {
                let formula_start = chars.next().map(|(idx, _)| idx).unwrap_or(rest.len());
                let formula = rest[formula_start..].trim().to_string();
                if !formula.is_empty() {
                    match tag {
                        'A' | 'a' => a_assertions.push(formula),
                        'B' | 'b' => b_assertions.push(formula),
                        _ => {}
                    }
                }
            }
            continue;
        }

        preamble.push_str(&form);
        preamble.push('\n');
    }

    ParsedInterpolationScript {
        preamble,
        a_assertions,
        b_assertions,
    }
}

/// Execute interpolation on a script
pub fn execute_interpolation(
    script: &str,
    format: InterpolateFormat,
    algorithm: Option<InterpolationAlgorithm>,
) -> String {
    let start = Instant::now();

    let algo_name = match algorithm {
        Some(InterpolationAlgorithm::McMillan) => "McMillan",
        Some(InterpolationAlgorithm::Pudlak) => "Pudlak",
        Some(InterpolationAlgorithm::Huang) => "Huang",
        None => "Default",
    };

    let parsed = parse_interpolation_script(script);
    let ParsedInterpolationScript {
        preamble,
        a_assertions,
        b_assertions,
    } = parsed;

    let result = if a_assertions.is_empty() || b_assertions.is_empty() {
        InterpolationResult {
            interpolant: String::new(),
            status: "error".to_string(),
            a_assertions,
            b_assertions,
            stats: None,
            error: Some(
                "Both A and B partitions must have at least one assertion. \
                 Use (assert-partition A <formula>) and (assert-partition B <formula>)."
                    .to_string(),
            ),
        }
    } else {
        solve_and_interpolate(
            &preamble,
            &a_assertions,
            &b_assertions,
            algorithm,
            algo_name,
            start,
        )
    };

    // Format output
    match format {
        InterpolateFormat::Smtlib => {
            let mut output = String::new();
            output.push_str(&result.status);
            output.push('\n');
            if let Some(ref err) = result.error {
                output.push_str(&format!("(error \"{}\")\n", err));
            } else {
                output.push_str(&format!("(interpolant {})\n", result.interpolant));
            }
            output
        }
        InterpolateFormat::Text => {
            let mut output = String::new();
            output.push_str(&format!("Status: {}\n", result.status));
            if let Some(ref err) = result.error {
                output.push_str(&format!("Error: {}\n", err));
            } else {
                output.push_str(&format!("Interpolant: {}\n", result.interpolant));
            }
            output
        }
        InterpolateFormat::Json => {
            serde_json::to_string_pretty(&result).unwrap_or_else(|_| "{}".to_string())
        }
    }
}

/// A uniquely-named path under the OS temp directory for a one-shot binary
/// proof log, plus an RAII guard that best-effort deletes it on drop (so a
/// failed or successful interpolation attempt never litters the temp
/// directory). Uses a process ID + wall-clock time + a per-process atomic
/// counter to avoid collisions between concurrent `nixie` invocations and
/// between interpolation calls within the same process (e.g. concurrent
/// test threads).
struct TempProofLog(PathBuf);

impl TempProofLog {
    fn new() -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let seq = COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let path = std::env::temp_dir().join(format!(
            "nixie-interpolate-{}-{}-{}.nixieproof",
            std::process::id(),
            nanos,
            seq
        ));
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempProofLog {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// Register every A/B assertion's raw formula text with a fresh
/// [`PremiseTracker`], returning the tracker plus the [`PremiseId`]s for each
/// side (in the same order as the input slices).
fn build_premise_tracker(
    a_assertions: &[String],
    b_assertions: &[String],
) -> (PremiseTracker, Vec<PremiseId>, Vec<PremiseId>) {
    let mut tracker = PremiseTracker::new();
    let a_ids = a_assertions
        .iter()
        .map(|f| tracker.add_assertion(f.clone()))
        .collect();
    let b_ids = b_assertions
        .iter()
        .map(|f| tracker.add_assertion(f.clone()))
        .collect();
    (tracker, a_ids, b_ids)
}

/// Whether at least one axiom in `proof` was directly attributable to the
/// A or B side via `tracker` (i.e. its conclusion text matches a registered
/// premise). This mirrors the check `CraigInterpolator` performs internally
/// (see `precompute_axiom_partition`), so we can tell -- *before* trusting
/// its output -- whether the interpolation would rest on real attribution or
/// degenerate entirely into the unattributed heuristic fallback.
fn any_axiom_directly_attributed(proof: &Proof, tracker: &PremiseTracker) -> bool {
    proof.nodes().iter().any(|node| match &node.step {
        ProofStep::Axiom { conclusion } => tracker.get_id(conclusion).is_some(),
        ProofStep::Inference { .. } => false,
    })
}

/// Actually solve `A ∧ B` with the real solver and, when unsat, attempt
/// genuine proof-based Craig interpolation. See the module docs for the
/// upstream limitation that currently keeps this from succeeding in
/// practice, and for why it reports an honest error rather than a
/// fabricated formula in that case.
fn solve_and_interpolate(
    preamble: &str,
    a_assertions: &[String],
    b_assertions: &[String],
    algorithm: Option<InterpolationAlgorithm>,
    algo_name: &str,
    start: Instant,
) -> InterpolationResult {
    let stats = |status: &str| {
        let _ = status;
        InterpolationStatistics {
            a_count: a_assertions.len(),
            b_count: b_assertions.len(),
            time_us: start.elapsed().as_micros() as u64,
            algorithm: algo_name.to_string(),
        }
    };

    let mut ctx = Context::new();
    ctx.set_option("produce-proofs", "true");
    let proof_log = TempProofLog::new();
    ctx.set_proof_log_path(Some(proof_log.path().to_path_buf()));

    // `Context::execute_script` re-parses its argument from scratch each
    // call, and symbol resolution ("is `p` a known Bool constant?") is
    // local to that one parse -- declarations made in an *earlier*,
    // separate `execute_script` call are invisible to a later one. So the
    // preamble (declarations) and every assertion must be sent as ONE
    // combined script, not as several sequential calls.
    let mut script = String::new();
    script.push_str(preamble);
    for formula in a_assertions.iter().chain(b_assertions.iter()) {
        script.push_str(&format!("(assert {})\n", formula));
    }

    if let Err(e) = ctx.execute_script(&script) {
        return InterpolationResult {
            interpolant: String::new(),
            status: "error".to_string(),
            a_assertions: a_assertions.to_vec(),
            b_assertions: b_assertions.to_vec(),
            stats: Some(stats("error")),
            error: Some(format!("Failed to parse declarations/assertions: {}", e)),
        };
    }

    let sat_result = ctx.check_sat();

    match sat_result {
        SolverResult::Sat => InterpolationResult {
            interpolant: String::new(),
            status: "sat".to_string(),
            a_assertions: a_assertions.to_vec(),
            b_assertions: b_assertions.to_vec(),
            stats: Some(stats("sat")),
            error: Some(
                "A \u{2227} B is satisfiable; no Craig interpolant exists (interpolation is \
                 only defined when the conjunction is unsatisfiable)."
                    .to_string(),
            ),
        },
        SolverResult::Unknown => InterpolationResult {
            interpolant: String::new(),
            status: "unknown".to_string(),
            a_assertions: a_assertions.to_vec(),
            b_assertions: b_assertions.to_vec(),
            stats: Some(stats("unknown")),
            error: Some(
                "The solver could not determine satisfiability of A \u{2227} B; a Craig \
                 interpolant cannot be computed."
                    .to_string(),
            ),
        },
        SolverResult::Unsat => {
            // Build the real A/B partition via the now-public premise API.
            let (tracker, a_ids, b_ids) = build_premise_tracker(a_assertions, b_assertions);
            let partition = InterpolantPartition::new(a_ids, b_ids);

            // Read back the proof nixie-solver just logged for this solve.
            let mut replayer = ProofReplayer::new();
            match replayer.replay(proof_log.path()) {
                Err(e) => InterpolationResult {
                    interpolant: String::new(),
                    status: "unsat".to_string(),
                    a_assertions: a_assertions.to_vec(),
                    b_assertions: b_assertions.to_vec(),
                    stats: Some(stats("unsat")),
                    error: Some(format!(
                        "A \u{2227} B is unsatisfiable, but the proof log nixie-solver wrote \
                         for this solve could not be read back: {e}. No Craig interpolant is \
                         reported."
                    )),
                },
                Ok(_) => {
                    let proof = replayer.into_proof();
                    if !any_axiom_directly_attributed(&proof, &tracker) {
                        return InterpolationResult {
                            interpolant: String::new(),
                            status: "unsat".to_string(),
                            a_assertions: a_assertions.to_vec(),
                            b_assertions: b_assertions.to_vec(),
                            stats: Some(stats("unsat")),
                            error: Some(
                                "A \u{2227} B is unsatisfiable, but no Craig interpolant is \
                                 reported: this CLI built a real A/B partition via \
                                 nixie-proof's public PremiseTracker/InterpolantPartition API, \
                                 but nixie-solver's proof log labels every axiom with a \
                                 synthetic per-clause tag (e.g. `input-clause-<n>`) rather \
                                 than the original assertion text, so no axiom in the \
                                 replayed proof matches a registered premise. Every axiom \
                                 would therefore fall back to CraigInterpolator's \
                                 unattributed heuristic, producing an interpolant that is not \
                                 actually validated against the real A/B split -- so none is \
                                 returned. This will start working once nixie-solver logs \
                                 proofs with real assertion-level conclusions."
                                    .to_string(),
                            ),
                        };
                    }

                    let config = InterpolationConfig {
                        algorithm: algorithm.unwrap_or_default(),
                        ..InterpolationConfig::default()
                    };
                    let mut interpolator = CraigInterpolator::new(config, partition, tracker);
                    match interpolator.extract(&proof) {
                        Ok(term) => InterpolationResult {
                            interpolant: term.to_string(),
                            status: "unsat".to_string(),
                            a_assertions: a_assertions.to_vec(),
                            b_assertions: b_assertions.to_vec(),
                            stats: Some(stats("unsat")),
                            error: None,
                        },
                        Err(e) => InterpolationResult {
                            interpolant: String::new(),
                            status: "unsat".to_string(),
                            a_assertions: a_assertions.to_vec(),
                            b_assertions: b_assertions.to_vec(),
                            stats: Some(stats("unsat")),
                            error: Some(format!(
                                "A \u{2227} B is unsatisfiable, and nixie-proof attempted a \
                                 real, partition-attributed Craig interpolation, but reported \
                                 an error rather than a formula: {e}"
                            )),
                        },
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Guards [`test_temp_proof_log_is_cleaned_up`]'s before/after scan of
    /// the OS temp directory against sibling tests in this module
    /// concurrently creating their own (legitimately temporary)
    /// `nixie-interpolate-*` scratch proof logs. `cargo test` runs unit
    /// tests as threads within one process, so without this guard a
    /// sibling's file could be created after the "before" snapshot and not
    /// yet removed by the "after" snapshot, reading as a false leak that
    /// isn't actually this test's. Ordinary interpolation tests take a
    /// shared (read) lock via [`execute_interpolation_for_test`] -- still
    /// fully concurrent with each other -- while the directory-scanning
    /// test takes an exclusive (write) lock for its whole
    /// before/execute/after window, so no sibling's scratch file can appear
    /// or disappear mid-scan.
    static TEMP_PROOF_LOG_SCAN_GUARD: std::sync::RwLock<()> = std::sync::RwLock::new(());

    /// Test-only wrapper around [`execute_interpolation`] that holds
    /// [`TEMP_PROOF_LOG_SCAN_GUARD`]'s read lock for the duration of the
    /// call; every test below except the scan test itself must go through
    /// this instead of calling `execute_interpolation` directly.
    fn execute_interpolation_for_test(
        script: &str,
        format: InterpolateFormat,
        algorithm: Option<InterpolationAlgorithm>,
    ) -> String {
        let _guard = TEMP_PROOF_LOG_SCAN_GUARD
            .read()
            .expect("scan guard lock poisoned");
        execute_interpolation(script, format, algorithm)
    }

    #[test]
    fn test_missing_partition_is_error() {
        let script = "(assert-partition A p)\n";
        let output = execute_interpolation_for_test(script, InterpolateFormat::Smtlib, None);
        assert!(output.starts_with("error"));
        assert!(output.contains("Both A and B partitions"));
    }

    #[test]
    fn test_sat_conjunction_reports_sat_not_placeholder() {
        let script = r#"
            (declare-const p Bool)
            (declare-const q Bool)
            (assert-partition A p)
            (assert-partition B q)
        "#;
        let output = execute_interpolation_for_test(script, InterpolateFormat::Smtlib, None);
        assert!(output.starts_with("sat"));
        assert!(output.contains("no Craig interpolant exists"));
        assert!(!output.contains("(interpolant true)"));
    }

    #[test]
    fn test_unsat_conjunction_is_honest_not_fabricated() {
        let script = r#"
            (declare-const p Bool)
            (assert-partition A p)
            (assert-partition B (not p))
        "#;
        let output = execute_interpolation_for_test(script, InterpolateFormat::Smtlib, None);
        assert!(output.starts_with("unsat"));
        // Must not silently claim a fabricated interpolant of "true" as
        // though it were a verified result.
        assert!(!output.contains("(interpolant true)"));
        assert!(output.contains("(error"));
    }

    #[test]
    fn test_multiline_formula_is_parsed_whole() {
        // A formula spanning multiple lines must not be split into bogus
        // fragments by a naive line-based parser.
        let script = "(declare-const p Bool)\n(declare-const q Bool)\n\
                       (assert-partition A\n  (and p\n       q))\n\
                       (assert-partition B (not p))\n";
        let parsed = parse_interpolation_script(script);
        assert_eq!(parsed.a_assertions.len(), 1);
        assert_eq!(parsed.a_assertions[0], "(and p\n       q)");
        assert_eq!(parsed.b_assertions.len(), 1);
    }

    #[test]
    fn test_undeclared_symbol_is_reported_as_error_not_unknown() {
        let script = "(assert-partition A p)\n(assert-partition B (not p))\n";
        let output = execute_interpolation_for_test(script, InterpolateFormat::Smtlib, None);
        // `p` was never declared, so this must be a parse/type error, not a
        // silently swallowed "unknown".
        assert!(output.starts_with("error"));
    }

    #[test]
    fn test_algorithm_selection_is_recorded_in_json_stats() {
        let script = r#"
            (declare-const p Bool)
            (declare-const q Bool)
            (assert-partition A p)
            (assert-partition B q)
        "#;
        let output = execute_interpolation_for_test(
            script,
            InterpolateFormat::Json,
            Some(InterpolationAlgorithm::McMillan),
        );
        assert!(output.contains("McMillan"));
    }

    /// [`build_premise_tracker`] must register every A and B formula under a
    /// real [`PremiseId`], with A and B premises kept in distinct partitions
    /// -- this is the actual, no-longer-private premise API this module now
    /// uses end-to-end.
    #[test]
    fn test_build_premise_tracker_registers_real_partitions() {
        let a = vec!["(> x 0)".to_string(), "(> y 0)".to_string()];
        let b = vec!["(< x 100)".to_string()];

        let (tracker, a_ids, b_ids) = build_premise_tracker(&a, &b);

        assert_eq!(a_ids.len(), 2);
        assert_eq!(b_ids.len(), 1);
        // No overlap between the two sides' premise IDs.
        for id in &a_ids {
            assert!(!b_ids.contains(id));
        }

        let partition = InterpolantPartition::new(a_ids.clone(), b_ids.clone());
        for id in &a_ids {
            assert!(partition.is_a_premise(*id));
            assert!(!partition.is_b_premise(*id));
        }
        for id in &b_ids {
            assert!(partition.is_b_premise(*id));
            assert!(!partition.is_a_premise(*id));
        }

        // The tracker resolves each original formula's text back to its
        // registered ID, exactly as `CraigInterpolator` looks axioms up.
        assert_eq!(tracker.get_id("(> x 0)"), Some(a_ids[0]));
        assert_eq!(tracker.get_id("(< x 100)"), Some(b_ids[0]));
        assert_eq!(tracker.get_id("(not registered anywhere)"), None);
    }

    /// The current honest-limitation message must name the *actual* remaining
    /// gap (nixie-solver's proof log using synthetic per-clause labels instead
    /// of real assertion text) rather than the now-fixed "premise module is
    /// private" reason from before `premise` became public.
    #[test]
    fn test_unsat_error_names_current_limitation_not_stale_one() {
        let script = r#"
            (declare-const p Bool)
            (assert-partition A p)
            (assert-partition B (not p))
        "#;
        let output = execute_interpolation_for_test(script, InterpolateFormat::Smtlib, None);
        assert!(output.starts_with("unsat"));
        assert!(output.contains("input-clause"));
        assert!(!output.contains("private to nixie-proof"));
    }

    /// A completed interpolation attempt (honest-error path here, since
    /// nixie-solver's proof log does not yet carry real assertion text) must
    /// not leave its scratch binary proof log behind in the OS temp
    /// directory.
    #[test]
    fn test_temp_proof_log_is_cleaned_up() {
        // Exclusive lock: no sibling test in this module may create or
        // remove its own `nixie-interpolate-*` scratch file while this scan
        // is in flight. See `TEMP_PROOF_LOG_SCAN_GUARD`.
        let _guard = TEMP_PROOF_LOG_SCAN_GUARD
            .write()
            .expect("scan guard lock poisoned");

        let before: std::collections::HashSet<_> = std::fs::read_dir(std::env::temp_dir())
            .map(|entries| {
                entries
                    .filter_map(|e| e.ok())
                    .map(|e| e.path())
                    .filter(|p| {
                        p.file_name()
                            .and_then(|n| n.to_str())
                            .is_some_and(|n| n.starts_with("nixie-interpolate-"))
                    })
                    .collect()
            })
            .unwrap_or_default();

        let script = r#"
            (declare-const p Bool)
            (assert-partition A p)
            (assert-partition B (not p))
        "#;
        let _ = execute_interpolation(script, InterpolateFormat::Smtlib, None);

        let after: Vec<_> = std::fs::read_dir(std::env::temp_dir())
            .map(|entries| {
                entries
                    .filter_map(|e| e.ok())
                    .map(|e| e.path())
                    .filter(|p| {
                        p.file_name()
                            .and_then(|n| n.to_str())
                            .is_some_and(|n| n.starts_with("nixie-interpolate-"))
                    })
                    .filter(|p| !before.contains(p))
                    .collect()
            })
            .unwrap_or_default();

        assert!(
            after.is_empty(),
            "interpolation left scratch proof log(s) behind: {after:?}"
        );
    }
}
