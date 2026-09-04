//! Regressions for the regex engines and the AIG walks in `nixie-theories`.
//!
//! Two classes of defect are pinned here:
//!
//! * **stack depth** – walks whose return type has no error channel and which
//!   are now explicit-stack driven (`compile_regex`, `const_string`,
//!   `collect_atoms`, `AigCut::evaluate_node`, `compute_cuts`, the two
//!   Plaisted-Greenbaum encoders). Reaching the assertion is the proof: an
//!   overflow aborts the process.
//! * **wrong or fatal answers** – a `while match(inner) {}` loop that never
//!   terminated on an ε-matching body, `split_at` panicking off a UTF-8
//!   boundary, `{5,2}` underflowing a repetition count, and a
//!   `_ => Ok(true)` arm that reported every string as a member of the regex
//!   operators the procedure had not implemented.

use nixie_core::ast::{TermId, TermManager};
use nixie_theories::bv::{AdvancedBitBlaster, AigCircuit, AigCut, BitBlastConfig, NodeId};
use nixie_theories::string::advanced_regex::{AdvancedRegex, RegexMatcher};
use nixie_theories::string::regex_membership::compile_regex;
use nixie_theories::string::regex_solver::{Regex as SolverRegex, RegexSolver};

/// A worker stack small enough that any surviving recursion overflows it.
///
/// This constant and every nesting depth below are scaled **together**, and
/// only their ratio – about 21 bytes of stack per nesting level – decides what
/// these tests detect. A recursive walk needs tens of bytes per frame at the
/// very least, so it still overflows; an iterative one uses O(1) native stack,
/// so it still returns. Raising a depth back to 100_000 without also restoring
/// a 1 MiB stack buys no extra detection power and costs 64× as much, because
/// several of the walks reached from here are quadratic in the depth.
const WORKER_STACK: usize = 1 << 17;

/// Run `body` on a small dedicated stack and return its value.
fn on_worker_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(WORKER_STACK)
        .spawn(body)
        .expect("spawn worker thread")
        .join()
        .expect("worker thread must return, not abort")
}

// ========  ========
// regex_membership::compile_regex / const_string
// ========  ========

#[test]
fn deep_regex_term_compiles() {
    // `(re.* (re.* … (str.to_re "a") …))` – `re.*` is idempotent on the built
    // regex but the *term* is genuinely nested, so the compiler walks every
    // level.
    const LEVELS: usize = 12_500;
    let compiled = on_worker_stack(|| {
        let mut manager = TermManager::new();
        let lit = manager.mk_string_lit("a");
        let re_sort = manager.sorts.bool_sort;
        let mut re = manager.mk_apply("str.to_re", vec![lit], re_sort);
        for _ in 0..LEVELS {
            re = manager.mk_apply("re.*", vec![re], re_sort);
        }
        compile_regex(&manager, re).is_some()
    });
    assert!(compiled, "a deeply nested ground regex must still compile");
}

#[test]
fn long_concat_regex_literal_compiles() {
    // `(str.to_re (str.++ "a" (str.++ "a" …)))`: the concat spine is as deep as
    // the operand count, and `const_string` folds it.
    const LEVELS: usize = 12_500;
    let len = on_worker_stack(|| {
        let mut manager = TermManager::new();
        let unit = manager.mk_string_lit("a");
        let mut chain = manager.mk_string_lit("");
        for _ in 0..LEVELS {
            chain = manager.mk_str_concat(unit, chain);
        }
        let re_sort = manager.sorts.bool_sort;
        let re = manager.mk_apply("str.to_re", vec![chain], re_sort);
        compile_regex(&manager, re).map(|r| {
            // The compiled literal must have one `Char` per input character.
            let mut count = 0usize;
            if let nixie_theories::string::RegexOp::Concat(parts) = &r.op {
                count = parts.len();
            }
            count
        })
    });
    assert_eq!(
        len,
        Some(LEVELS),
        "every operand of the concat spine must reach the compiled literal"
    );
}

// ========  ========
// advanced_regex – ε-body repetition must terminate, `{5,2}` must not underflow
// ========  ========

#[test]
fn star_over_epsilon_body_terminates() {
    // `(a*)*`: the inner `a*` matches the empty string, so the greedy loop that
    // repeated it "while it matches" never advanced and never stopped.
    let matched = on_worker_stack(|| {
        let inner = AdvancedRegex::Star(Box::new(AdvancedRegex::Char('a')));
        let outer = AdvancedRegex::Star(Box::new(inner));
        let matcher = RegexMatcher::new(outer);
        matcher.is_match("aaa")
    });
    assert!(matched);
}

#[test]
fn star_over_empty_body_terminates() {
    let matched = on_worker_stack(|| {
        let outer = AdvancedRegex::Star(Box::new(AdvancedRegex::Empty));
        let matcher = RegexMatcher::new(outer);
        matcher.is_match("")
    });
    assert!(matched);
}

#[test]
fn inverted_repeat_range_does_not_underflow() {
    // `a{5,2}` is unsatisfiable; the point is that computing `max - min` no
    // longer wraps into a near-`usize::MAX` repetition count.
    let matched = on_worker_stack(|| {
        let regex = AdvancedRegex::RepeatRange(Box::new(AdvancedRegex::Char('a')), 5, Some(2));
        let matcher = RegexMatcher::new(regex);
        matcher.is_match("aa")
    });
    assert!(!matched, "`a{{5,2}}` must not match a two-character string");
}

// ========  ========
// regex_solver – UTF-8 splitting, and no `_ => Ok(true)` blanket membership
// ========  ========

#[test]
fn membership_over_multibyte_subject_does_not_abort() {
    // Every `split_at` index used to come from a raw byte range, so any
    // multi-byte character panicked (and release builds abort on panic).
    let result = on_worker_stack(|| {
        let mut solver =
            RegexSolver::new(nixie_theories::string::regex_solver::RegexSolverConfig::default());
        let regex = SolverRegex::Concat(vec![
            SolverRegex::Char('あ'),
            SolverRegex::Star(Box::new(SolverRegex::Char('い'))),
        ]);
        solver.test_membership("あいい", &regex)
    });
    assert_eq!(result, Ok(true));
}

#[test]
fn unimplemented_operators_are_not_reported_as_matching_everything() {
    let (opt_no, plus_no, repeat_no, range_no) = on_worker_stack(|| {
        let mut solver =
            RegexSolver::new(nixie_theories::string::regex_solver::RegexSolverConfig::default());
        let a = || Box::new(SolverRegex::Char('a'));
        (
            solver.test_membership("bb", &SolverRegex::Optional(a())),
            solver.test_membership("b", &SolverRegex::Plus(a())),
            solver.test_membership(
                "aaa",
                &SolverRegex::Repeat {
                    regex: a(),
                    count: 2,
                },
            ),
            solver.test_membership(
                "aaaa",
                &SolverRegex::RepeatRange {
                    regex: a(),
                    min: 1,
                    max: Some(2),
                },
            ),
        )
    });
    assert_eq!(opt_no, Ok(false), "`a?` must not match \"bb\"");
    assert_eq!(plus_no, Ok(false), "`a+` must not match \"b\"");
    assert_eq!(repeat_no, Ok(false), "`a{{2}}` must not match \"aaa\"");
    assert_eq!(range_no, Ok(false), "`a{{1,2}}` must not match \"aaaa\"");
}

#[test]
fn implemented_operators_still_match_what_they_should() {
    let (opt_yes, plus_yes, repeat_yes, range_yes) = on_worker_stack(|| {
        let mut solver =
            RegexSolver::new(nixie_theories::string::regex_solver::RegexSolverConfig::default());
        let a = || Box::new(SolverRegex::Char('a'));
        (
            solver.test_membership("", &SolverRegex::Optional(a())),
            solver.test_membership("aa", &SolverRegex::Plus(a())),
            solver.test_membership(
                "aa",
                &SolverRegex::Repeat {
                    regex: a(),
                    count: 2,
                },
            ),
            solver.test_membership(
                "aa",
                &SolverRegex::RepeatRange {
                    regex: a(),
                    min: 1,
                    max: Some(2),
                },
            ),
        )
    });
    assert_eq!(opt_yes, Ok(true));
    assert_eq!(plus_yes, Ok(true));
    assert_eq!(repeat_yes, Ok(true));
    assert_eq!(range_yes, Ok(true));
}

// ========  ========
// bv::bitblast_advanced – AIG cut evaluation, cut enumeration, PG encoding
// ========  ========

/// An AIG that is a chain of `levels` `And` nodes over two primary inputs.
fn deep_aig(levels: usize) -> (AigCircuit, NodeId) {
    let mut aig = AigCircuit::new();
    let a = aig.new_input("a".to_string());
    let b = aig.new_input("b".to_string());
    let mut edge = aig.and(a, b);
    for _ in 0..levels {
        edge = aig.and(edge, b);
    }
    aig.add_output(edge);
    (aig, edge.node())
}

#[test]
fn deep_aig_cut_truth_table_returns() {
    // `AigCut::compute_truth_table` walks the whole cone below the cut root
    // through `evaluate_node`, which had neither a memo of internal nodes nor
    // a bound on its depth.
    const LEVELS: usize = 12_500;
    let table = on_worker_stack(|| {
        let (aig, root) = deep_aig(LEVELS);
        let mut cut = AigCut::trivial(root);
        cut.compute_truth_table(&aig);
        cut.truth_table
    });
    // A trivial (one-input) cut of a node evaluates to the input's own value:
    // 0 when the input is false, 1 when it is true.
    assert_eq!(table, Some(0b10));
}

#[test]
fn deep_aig_blaster_walks_return() {
    // Drive the blaster's own AIG to a comparable depth through its public
    // encoders, then run the two walks that used to recurse over it.
    const LEVELS: usize = 6_250;
    let outcome = on_worker_stack(|| {
        let mut blaster = AdvancedBitBlaster::new(BitBlastConfig::default());
        let a = blaster.create_variable(TermId::new(1), 1);
        let b = blaster.create_variable(TermId::new(2), 1);
        let mut acc = blaster.encode_and(&a, &b);
        for _ in 0..LEVELS {
            acc = blaster.encode_and(&acc, &b);
        }
        let root = match acc.first() {
            Some(edge) => edge.node(),
            None => return Err("encoder produced no output edge".to_string()),
        };
        let cuts = blaster
            .compute_cuts(root)
            .map_err(|e| format!("compute_cuts: {e:?}"))?;
        let mut sat = nixie_sat::Solver::new();
        blaster
            .to_cnf_plaisted_greenbaum(&mut sat)
            .map_err(|e| format!("pg: {e:?}"))?;
        Ok(cuts.len())
    });
    assert!(matches!(outcome, Ok(n) if n >= 1), "{outcome:?}");
}
