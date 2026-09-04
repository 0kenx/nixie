//! Tutorial mode with guided examples
//!
//! This module provides an interactive tutorial mode to help users learn
//! how to use nixie-cli and SMT-LIB2 effectively.

use std::io::{self, Write};

/// Tutorial section
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TutorialSection {
    Introduction,
    BasicUsage,
    Theories,
    AdvancedFeatures,
    CliOptions,
    All,
}

/// Run the interactive tutorial
pub fn run_tutorial(section: Option<TutorialSection>) {
    let section = section.unwrap_or(TutorialSection::All);

    print_header("Nixie SMT Solver Tutorial");
    println!();

    match section {
        TutorialSection::Introduction => show_introduction(),
        TutorialSection::BasicUsage => show_basic_usage(),
        TutorialSection::Theories => show_theories(),
        TutorialSection::AdvancedFeatures => show_advanced_features(),
        TutorialSection::CliOptions => show_cli_options(),
        TutorialSection::All => {
            show_introduction();
            wait_for_user();
            show_basic_usage();
            wait_for_user();
            show_theories();
            wait_for_user();
            show_advanced_features();
            wait_for_user();
            show_cli_options();
        }
    }

    println!();
    println!("Tutorial complete! For more examples, run: nixie --examples");
    println!("For help, run: nixie --help");
}

/// Show introduction section
fn show_introduction() {
    print_section("1. Introduction to SMT Solving");

    println!("Welcome to Nixie, a high-performance SMT solver written in pure Rust!");
    println!();
    println!("SMT (Satisfiability Modulo Theories) solvers help you:");
    println!("  • Verify software and hardware designs");
    println!("  • Solve constraint satisfaction problems");
    println!("  • Optimize complex systems");
    println!("  • Prove mathematical theorems");
    println!();
    println!("Nixie supports the SMT-LIB2 standard format, making it compatible");
    println!("with existing SMT benchmarks and tools.");
    println!();
}

/// Show basic usage section
fn show_basic_usage() {
    print_section("2. Basic Usage");

    println!("Let's start with a simple example!");
    println!();

    print_example(
        "Checking if x = 5 is satisfiable",
        r#"
(declare-const x Int)
(assert (= x 5))
(check-sat)
    "#,
    );

    println!("This declares an integer variable 'x', asserts that x equals 5,");
    println!("and asks the solver to check if this is satisfiable.");
    println!();
    println!("To run this example:");
    println!("  echo '(declare-const x Int) (assert (= x 5)) (check-sat)' | nixie");
    println!();

    print_example(
        "Finding a model (satisfying assignment)",
        r#"
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (> x 3))
(check-sat)
(get-model)
    "#,
    );

    println!("The solver will find values for x and y that satisfy both constraints:");
    println!("  • x + y = 10");
    println!("  • x > 3");
    println!();

    print_example(
        "Checking unsatisfiability",
        r#"
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
    "#,
    );

    println!("This problem is UNSAT because x cannot be both > 10 and < 5.");
    println!();
}

/// Show theories section
fn show_theories() {
    print_section("3. Theories");

    println!("Nixie supports multiple theories. Let's explore them!");
    println!();

    print_subsection("3.1 Linear Integer Arithmetic (LIA)");
    print_example(
        "LIA example",
        r#"
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(assert (= (+ (* 2 a) (* 3 b)) 10))
(assert (>= a 0))
(assert (>= b 0))
(check-sat)
(get-model)
    "#,
    );

    println!("Try it: nixie --logic QF_LIA example.smt2");
    println!();

    print_subsection("3.2 Bit-Vectors (BV)");
    print_example(
        "Bit-vector example",
        r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvadd x y) #x0A))  ; x + y = 10 (in 8-bit)
(assert (bvult x #x05))         ; x < 5 (unsigned)
(check-sat)
(get-model)
    "#,
    );

    println!("Bit-vectors are useful for hardware verification and low-level code.");
    println!();

    print_subsection("3.3 Arrays");
    print_example(
        "Array example",
        r#"
(set-logic QF_AX)
(declare-const arr (Array Int Int))
(declare-const i Int)
(assert (= (select arr i) 42))
(assert (= (select (store arr i 10) i) 10))
(check-sat)
    "#,
    );

    println!("Arrays support select (read) and store (write) operations.");
    println!();

    print_subsection("3.4 Boolean Logic");
    print_example(
        "Boolean example",
        r#"
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (=> (and p q) r))  ; if (p AND q) then r
(assert p)
(assert q)
(assert (not r))
(check-sat)
    "#,
    );

    println!("This checks if the logical constraints are consistent.");
    println!();
}

/// Show advanced features section
fn show_advanced_features() {
    print_section("4. Advanced Features");

    print_subsection("4.1 Model Enumeration");
    println!("Find all satisfying assignments:");
    println!("  nixie --enumerate-models --max-models 10 problem.smt2");
    println!();

    print_subsection("4.2 Optimization");
    println!("Maximize or minimize objectives:");
    println!("  nixie --optimize problem.smt2");
    println!();

    print_subsection("4.3 UNSAT Core Extraction");
    println!("Find minimal unsatisfiable subset:");
    println!("  nixie --unsat-core --minimize-core problem.smt2");
    println!();

    print_subsection("4.4 Portfolio Solving");
    println!("Run multiple strategies in parallel:");
    println!("  nixie --portfolio-mode --portfolio-timeout 60 problem.smt2");
    println!();

    print_subsection("4.5 Incremental Solving");
    print_example(
        "Incremental solving",
        r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(push 1)
(assert (< x 10))
(check-sat)  ; Check: 0 < x < 10
(pop 1)
(push 1)
(assert (> x 100))
(check-sat)  ; Check: x > 100 (and x > 0 from earlier)
(pop 1)
    "#,
    );

    println!("Use push/pop to explore multiple scenarios efficiently.");
    println!("Run with: nixie --incremental example.smt2");
    println!();

    print_subsection("4.6 Problem Analysis");
    println!("Analyze problem complexity:");
    println!("  nixie --analyze problem.smt2");
    println!("  nixie --classify problem.smt2");
    println!("  nixie --auto-tune problem.smt2");
    println!();

    print_subsection("4.7 Dependency Analysis");
    println!("Understand assertion dependencies:");
    println!("  nixie --dependencies problem.smt2");
    println!("  nixie --dependencies-detailed problem.smt2");
    println!();

    print_subsection("4.8 Diagnostic Mode");
    println!("Check for potential issues:");
    println!("  nixie --diagnostic problem.smt2");
    println!();
}

/// Show CLI options section
fn show_cli_options() {
    print_section("5. CLI Options");

    print_subsection("5.1 Output Formats");
    println!("  nixie -f json problem.smt2    # JSON output");
    println!("  nixie -f yaml problem.smt2    # YAML output");
    println!("  nixie --stats problem.smt2    # Show statistics");
    println!();

    print_subsection("5.2 Performance Options");
    println!("  nixie --parallel problem.smt2           # Parallel solving");
    println!("  nixie --threads 8 problem.smt2          # Use 8 threads");
    println!("  nixie --timeout 60 problem.smt2         # 60 second timeout");
    println!("  nixie --cache problem.smt2              # Enable result caching");
    println!();

    print_subsection("5.3 Solver Configuration");
    println!("  nixie --preset fast problem.smt2        # Fast preset");
    println!("  nixie --preset balanced problem.smt2    # Balanced preset");
    println!("  nixie --preset thorough problem.smt2    # Thorough preset");
    println!("  nixie --simplify problem.smt2           # Enable simplification");
    println!();

    print_subsection("5.4 Batch Processing");
    println!("  nixie -R *.smt2                   # Recursive directory");
    println!("  nixie --parallel -R benchmarks/   # Parallel batch processing");
    println!("  nixie --profile -R tests/         # Profile all tests");
    println!();

    print_subsection("5.5 Interactive Mode");
    println!("  nixie -i                  # Start REPL (Read-Eval-Print Loop)");
    println!();
    println!("In interactive mode, you can:");
    println!("  • Type SMT-LIB2 commands interactively");
    println!("  • Use multi-line input (auto-balances parentheses)");
    println!("  • Access command history with arrow keys");
    println!("  • Get tab completion for commands");
    println!();

    print_subsection("5.6 Validation and Formatting");
    println!("  nixie --validate-only problem.smt2      # Syntax check only");
    println!("  nixie --format-smtlib problem.smt2      # Pretty-print");
    println!("  nixie --validate-model problem.smt2     # Verify model");
    println!("  nixie --validate-proof problem.smt2     # Verify proof");
    println!();

    print_subsection("5.7 Watch Mode");
    println!("  nixie --watch problem.smt2        # Re-run on file changes");
    println!();
}

/// Print formatted header
fn print_header(title: &str) {
    let width = 70;
    println!("{}", "=".repeat(width));
    println!("{:^width$}", title, width = width);
    println!("{}", "=".repeat(width));
}

/// Print formatted section
fn print_section(title: &str) {
    println!();
    println!("{}", "─".repeat(70));
    println!("{}", title);
    println!("{}", "─".repeat(70));
    println!();
}

/// Print formatted subsection
fn print_subsection(title: &str) {
    println!("{}", title);
    println!("{}", "·".repeat(title.len()));
}

/// Print formatted example
fn print_example(description: &str, code: &str) {
    println!("Example: {}", description);
    println!("```smt2");
    println!("{}", code.trim());
    println!("```");
    println!();
}

/// Wait for user to press Enter
fn wait_for_user() {
    println!();
    print!("Press Enter to continue...");
    io::stdout().flush().expect("flush should succeed");
    let mut buffer = String::new();
    io::stdin()
        .read_line(&mut buffer)
        .expect("failed to read line from stdin");
}

/// List available tutorial sections
pub fn list_tutorial_sections() {
    println!("Available tutorial sections:");
    println!("  1. introduction    - Introduction to SMT solving");
    println!("  2. basic-usage     - Basic usage and simple examples");
    println!("  3. theories        - Different theories (LIA, BV, Arrays, etc.)");
    println!("  4. advanced        - Advanced features (optimization, cores, etc.)");
    println!("  5. cli-options     - CLI options and flags");
    println!("  all                - Show all sections (default)");
    println!();
    println!("Usage: nixie --tutorial [section]");
}

/// Parse tutorial section from string
pub fn parse_tutorial_section(s: &str) -> Option<TutorialSection> {
    match s.to_lowercase().as_str() {
        "introduction" | "intro" | "1" => Some(TutorialSection::Introduction),
        "basic-usage" | "basic" | "2" => Some(TutorialSection::BasicUsage),
        "theories" | "theory" | "3" => Some(TutorialSection::Theories),
        "advanced" | "advanced-features" | "4" => Some(TutorialSection::AdvancedFeatures),
        "cli-options" | "cli" | "options" | "5" => Some(TutorialSection::CliOptions),
        "all" => Some(TutorialSection::All),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_tutorial_section() {
        assert_eq!(
            parse_tutorial_section("introduction"),
            Some(TutorialSection::Introduction)
        );
        assert_eq!(
            parse_tutorial_section("basic"),
            Some(TutorialSection::BasicUsage)
        );
        assert_eq!(parse_tutorial_section("all"), Some(TutorialSection::All));
        assert_eq!(parse_tutorial_section("invalid"), None);
    }

    #[test]
    fn test_parse_tutorial_section_numbers() {
        assert_eq!(
            parse_tutorial_section("1"),
            Some(TutorialSection::Introduction)
        );
        assert_eq!(
            parse_tutorial_section("2"),
            Some(TutorialSection::BasicUsage)
        );
        assert_eq!(parse_tutorial_section("3"), Some(TutorialSection::Theories));
    }
}
