//! Deletion-based UNSAT-core minimization driven from the CLI.
//!
//! `--minimize-core` runs a real minimal-unsat-core search: starting from the
//! full assertion set, it repeatedly drops one assertion and re-checks
//! satisfiability, keeping the assertion removed whenever the remainder is
//! still `unsat`. The result is a *1-minimal* core — removing any single
//! remaining assertion makes it satisfiable — which is a stronger guarantee
//! than the conservative core `(get-unsat-core)` reports for `:named`
//! assertions.
//!
//! Unlike the solver-internal, `:named`-based core, this operates purely on
//! the CLI-visible `Context` surface (`get_assertions` / `reset_assertions` /
//! `assert` / `check_sat`), so it works for *every* script, whether or not it
//! used `:named` annotations.

use std::time::{Duration, Instant};

use oxiz_core::ast::TermId;
use oxiz_core::smtlib::Printer;
use oxiz_solver::{Context, SolverResult};

/// Wall-clock budget for the whole minimization loop. Each round re-solves a
/// growing/shrinking assertion set, so a pathological problem could otherwise
/// spend unbounded time here; on timeout we return the best (still `unsat`)
/// core found so far with an honest note rather than hanging.
const MINIMIZE_WALL_CLOCK_BUDGET: Duration = Duration::from_secs(30);

/// Re-assert exactly `subset` on a freshly reset solver and report the result.
///
/// `reset_assertions` keeps every declaration (constants, functions, sorts)
/// intact while dropping the current assertions, and the `TermId`s in `subset`
/// are stable hash-consed handles, so re-asserting them reconstructs the exact
/// same problem restricted to `subset`.
fn check_subset(ctx: &mut Context, subset: &[TermId]) -> SolverResult {
    ctx.reset_assertions();
    for &term in subset {
        ctx.assert(term);
    }
    ctx.check_sat()
}

/// Run deletion-based minimization over the context's current assertions and
/// return the formatted report lines (to be appended to the solver output).
///
/// Precondition: the caller has already observed an `unsat` result for the
/// full assertion set. If the full set does not reproduce as `unsat` here
/// (e.g. it only reached `unknown`), the function reports that honestly
/// instead of fabricating a core.
///
/// On return, `ctx` holds exactly the minimized core (re-asserted), so a
/// following `format_assertions` would show the same set.
pub fn minimize_core(ctx: &mut Context) -> Vec<String> {
    let assertions: Vec<TermId> = ctx.get_assertions().to_vec();
    let total = assertions.len();

    if assertions.is_empty() {
        return vec!["; minimize-core: no assertions to minimize".to_string()];
    }

    // Confirm the full set really is unsat under a clean re-assertion.
    if check_subset(ctx, &assertions) != SolverResult::Unsat {
        return vec![
            "; minimize-core: the full assertion set did not reproduce as unsat \
             (nothing to minimize)"
                .to_string(),
        ];
    }

    let start = Instant::now();
    let mut core = assertions;
    let mut budget_exhausted = false;

    // Single deletion pass: try to drop each still-present assertion once. A
    // single pass already yields a 1-minimal core because every retained
    // assertion was individually proven necessary (its removal made the
    // remainder satisfiable) at the moment it was tested.
    let mut index = 0;
    while index < core.len() {
        if start.elapsed() > MINIMIZE_WALL_CLOCK_BUDGET {
            budget_exhausted = true;
            break;
        }

        // Candidate subset = core without the assertion at `index`.
        let mut candidate = Vec::with_capacity(core.len() - 1);
        candidate.extend_from_slice(&core[..index]);
        candidate.extend_from_slice(&core[index + 1..]);

        if check_subset(ctx, &candidate) == SolverResult::Unsat {
            // The dropped assertion was not needed; keep it removed and retest
            // the assertion that shifted into `index`.
            core = candidate;
        } else {
            // The dropped assertion is essential; keep it and move on.
            index += 1;
        }
    }

    // Leave the context holding exactly the minimized core.
    let _ = check_subset(ctx, &core);

    let mut lines = Vec::new();
    if budget_exhausted {
        lines.push(format!(
            "; minimize-core: wall-clock budget ({:.0}s) exceeded; reporting the smallest \
             core found so far",
            MINIMIZE_WALL_CLOCK_BUDGET.as_secs_f64()
        ));
    }
    lines.push(format!(
        "; minimized unsat core: {} of {} assertion(s)",
        core.len(),
        total
    ));

    let printer = Printer::new(&ctx.terms);
    for &term in &core {
        lines.push(format!("(assert {})", printer.print_term(term)));
    }

    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a context with a known over-constrained problem and confirm the
    /// deletion loop shrinks it to a genuine minimal core.
    #[test]
    fn minimize_core_drops_irrelevant_assertions() {
        let mut ctx = Context::new();
        let script = "(declare-const x Int)\n\
                      (declare-const y Int)\n\
                      (assert (> x 10))\n\
                      (assert (> y 0))\n\
                      (assert (< x 5))\n\
                      (assert (< y 100))\n";
        // Execute the declarations + assertions so the context holds them.
        ctx.execute_script(script).expect("script should execute");

        // Full set is unsat: x > 10 and x < 5 contradict.
        assert_eq!(ctx.check_sat(), SolverResult::Unsat);

        let lines = minimize_core(&mut ctx);
        let report = lines.join("\n");

        // The minimal core must contain exactly the two contradictory
        // constraints on x and neither y constraint.
        assert!(
            report.contains("minimized unsat core: 2 of 4"),
            "expected a 2-of-4 minimal core, got:\n{report}"
        );
        // Both x-constraints must survive.
        assert!(report.contains("(> x 10)") || report.contains("(< 10 x)"));
        assert!(report.contains("(< x 5)") || report.contains("(> 5 x)"));
        // The y-constraints are irrelevant and must be dropped.
        assert!(
            !report.contains("(> y 0)"),
            "y constraint should be dropped:\n{report}"
        );
        assert!(
            !report.contains("(< y 100)"),
            "y constraint should be dropped:\n{report}"
        );
    }

    #[test]
    fn minimize_core_handles_empty_assertions() {
        let mut ctx = Context::new();
        let lines = minimize_core(&mut ctx);
        assert!(lines[0].contains("no assertions"));
    }
}
