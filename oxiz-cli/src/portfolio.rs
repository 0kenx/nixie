//! Portfolio solving with parallel strategy execution
//!
//! This module implements parallel portfolio solving where multiple solver strategies
//! are executed concurrently, and the first one to find a solution wins.
//!
//! # How strategies actually differ today
//!
//! Two independent, genuinely-applied sources of diversity feed each
//! strategy:
//!
//! 1. **A real, per-worker [`SolverConfig`]** (see
//!    [`StrategyConfig::solver_config`]), applied via the now-public
//!    `Context::set_solver_config`. Each default strategy uses a distinct
//!    `(theory_mode, simplify, restart_strategy)` triplet (checked by
//!    `test_default_strategies_have_distinct_solver_configs`). `theory_mode`
//!    and `simplify` are consumed on every `check_sat` call (see
//!    `oxiz-solver/src/solver/mod.rs`), so they genuinely change search
//!    behaviour. `restart_strategy` (and the `enable_*` preprocessing
//!    toggles) are stored on the config but are only read once, by
//!    `Solver::with_config` at construction time inside `Context::new()`
//!    (see `oxiz-solver/src/solver/mod.rs`); `Context::set_solver_config`
//!    replaces the stored config without rebuilding that already-constructed
//!    SAT engine, so -- for the fresh `Context` each portfolio worker
//!    creates -- these fields do not yet retroactively change behaviour.
//!    They are still set (not fabricated no-ops) so strategies pick up the
//!    real effect automatically once `oxiz-solver` gains a way to construct
//!    a `Context`/`Solver` with a caller-supplied config up front.
//! 2. **A deterministic reordering of the top-level `(assert ...)`
//!    commands** (see [`diversify_script`]). Assertion/clause order is a
//!    real, well-known lever for CDCL search diversity -- it changes which
//!    conflicts are met first and how VSIDS-style activity accumulates --
//!    so this produces genuinely different solver executions regardless of
//!    the `SolverConfig` limitation above.
//!
//! `StrategyConfig::apply` also still sets a handful of advisory
//! `set_option` string keys (`strategy`, `restarts`, `branching`, ...) for
//! `(get-option ...)` introspection; those are recorded but not consumed by
//! the solve loop (only `simplify`, `timeout`, `max-conflicts`,
//! `max-decisions`, `produce-proofs`, and `produce-unsat-cores` are wired --
//! see `Context::set_option`'s doc comment), so they are not counted as a
//! source of diversity here.

use std::sync::mpsc::{Receiver, Sender, channel};
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

use oxiz_solver::{Context, RestartStrategy, SolverConfig, TheoryMode};

use crate::Args;

/// Deterministic reordering applied to a script's `(assert ...)` forms to
/// give a strategy a genuinely different search path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssertOrdering {
    /// Keep assertions in their original order.
    Original,
    /// Reverse the assertion order.
    Reversed,
    /// Shortest (syntactically simplest) assertions first.
    ShortestFirst,
    /// Longest (syntactically largest) assertions first.
    LongestFirst,
    /// A fixed pseudo-random permutation, seeded for reproducibility.
    Shuffled(u64),
}

impl AssertOrdering {
    /// Apply this ordering to a list of `(assert ...)` form strings.
    fn apply(self, mut asserts: Vec<String>) -> Vec<String> {
        match self {
            Self::Original => asserts,
            Self::Reversed => {
                asserts.reverse();
                asserts
            }
            Self::ShortestFirst => {
                asserts.sort_by_key(|a| a.len());
                asserts
            }
            Self::LongestFirst => {
                asserts.sort_by_key(|a| std::cmp::Reverse(a.len()));
                asserts
            }
            Self::Shuffled(seed) => {
                deterministic_shuffle(&mut asserts, seed);
                asserts
            }
        }
    }
}

/// A small, dependency-free xorshift64* generator, used only to produce a
/// reproducible shuffle -- not for anything security-sensitive.
fn deterministic_shuffle(items: &mut [String], seed: u64) {
    let mut state = seed ^ 0x9E37_79B9_7F4A_7C15;
    if state == 0 {
        state = 1;
    }
    let mut next_u64 = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for i in (1..items.len()).rev() {
        let r = (next_u64() % (i as u64 + 1)) as usize;
        items.swap(i, r);
    }
}

/// Split a script into its top-level parenthesized forms (paren-depth
/// tracked, so multi-line forms are captured whole rather than split by
/// line).
fn top_level_forms(script: &str) -> Vec<String> {
    let mut forms = Vec::new();
    let chars: Vec<char> = script.chars().collect();
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

/// Whether a top-level form is exactly an `(assert ...)` command (not e.g.
/// `(assert-partition ...)` or anything else that merely starts with the
/// same prefix).
fn is_assert_form(form: &str) -> bool {
    let trimmed = form.trim();
    let Some(rest) = trimmed.strip_prefix('(') else {
        return false;
    };
    let rest = rest.trim_start();
    match rest.strip_prefix("assert") {
        Some(after) => {
            after.is_empty() || after.starts_with(char::is_whitespace) || after.starts_with('(')
        }
        None => false,
    }
}

/// Reorder a script's `(assert ...)` forms according to `ordering`, leaving
/// every other command (declarations, `set-logic`, `check-sat`, ...) in its
/// original relative position. The reordered assertions are emitted where
/// the *first* assertion originally appeared, so declarations still precede
/// use and trailing commands (`check-sat`, `get-model`, ...) still trail.
///
/// This never adds, drops, or mutates an assertion -- only their relative
/// order changes, which is semantically safe since conjunction is
/// commutative.
pub fn diversify_script(script: &str, ordering: AssertOrdering) -> String {
    let forms = top_level_forms(script);

    let mut asserts = Vec::new();
    let mut skeleton: Vec<Option<String>> = Vec::new();
    let mut assert_slot: Option<usize> = None;

    for form in forms {
        if is_assert_form(&form) {
            asserts.push(form);
            if assert_slot.is_none() {
                assert_slot = Some(skeleton.len());
                skeleton.push(None);
            }
        } else {
            skeleton.push(Some(form));
        }
    }

    let ordered = ordering.apply(asserts);

    let mut out = String::new();
    for slot in skeleton {
        match slot {
            Some(form) => {
                out.push_str(&form);
                out.push('\n');
            }
            None => {
                for a in &ordered {
                    out.push_str(a);
                    out.push('\n');
                }
            }
        }
    }
    out
}

/// Strategy configuration for portfolio solving
#[derive(Debug, Clone)]
pub struct StrategyConfig {
    /// Name of the strategy
    pub name: &'static str,
    /// Description of the strategy
    #[allow(dead_code)]
    pub description: &'static str,
    /// Options to set for this strategy (advisory: see module docs -- most
    /// keys are not yet consumed by `Context::set_option`).
    pub options: Vec<(&'static str, &'static str)>,
    /// A genuinely-applied, per-worker solver configuration (theory mode,
    /// simplification, restart policy, preprocessing toggles). See the
    /// module docs for exactly which fields take effect today.
    pub solver_config: SolverConfig,
    /// The other genuinely-applied source of search diversity for this
    /// strategy: a reordering of the script's assertions.
    pub ordering: AssertOrdering,
}

impl StrategyConfig {
    /// Apply this strategy configuration to a context: the real
    /// [`SolverConfig`] first, then the advisory `set_option` string keys
    /// (which may reaffirm one of the config's fields, e.g. `simplify`, for
    /// `(get-option ...)` introspection). Also see [`diversify_script`],
    /// which supplies this strategy's other genuine diversification.
    pub fn apply(&self, ctx: &mut Context) {
        ctx.set_solver_config(self.solver_config.clone());
        for (key, value) in &self.options {
            ctx.set_option(key, value);
        }
    }
}

/// Result from a portfolio solver strategy
#[derive(Debug, Clone)]
pub struct PortfolioResult {
    /// Name of the strategy that found the result
    pub strategy_name: String,
    /// The output from the solver
    pub output: Vec<String>,
    /// Time taken in milliseconds
    pub time_ms: u128,
}

/// Get default portfolio strategies
///
/// Each strategy applies a distinct, verifiable [`AssertOrdering`] (checked
/// in `test_strategies_have_distinct_orderings`) *and* a distinct
/// `(theory_mode, simplify, restart_strategy)` [`SolverConfig`] triplet
/// (checked in `test_default_strategies_have_distinct_solver_configs`); see
/// module docs for exactly which of those fields are consumed by the solve
/// loop today versus stored for a future `oxiz-solver` change, and for why
/// the `options` below are advisory only.
pub fn get_default_strategies() -> Vec<StrategyConfig> {
    vec![
        StrategyConfig {
            name: "CDCL-Aggressive",
            description: "Fast preset (eager theory checking), Luby restarts, original assertion order",
            options: vec![
                ("strategy", "cdcl"),
                ("simplify", "true"),
                ("restarts", "frequent"),
                ("branching", "vsids"),
                ("clause-learning", "aggressive"),
            ],
            solver_config: SolverConfig {
                restart_strategy: RestartStrategy::Luby,
                ..SolverConfig::fast()
            },
            ordering: AssertOrdering::Original,
        },
        StrategyConfig {
            name: "CDCL-Stable",
            description: "Balanced preset (eager theory checking), Glucose restarts, reversed assertion order",
            options: vec![
                ("strategy", "cdcl"),
                ("simplify", "true"),
                ("restarts", "moderate"),
                ("branching", "vmtf"),
                ("clause-learning", "moderate"),
            ],
            solver_config: SolverConfig::balanced(),
            ordering: AssertOrdering::Reversed,
        },
        StrategyConfig {
            name: "DPLL-Lookahead",
            description: "Lazy theory checking, Geometric restarts, shortest assertions first",
            options: vec![
                ("strategy", "dpll"),
                ("simplify", "true"),
                ("lookahead", "true"),
                ("branching", "moms"),
            ],
            solver_config: SolverConfig {
                theory_mode: TheoryMode::Lazy,
                restart_strategy: RestartStrategy::Geometric,
                ..SolverConfig::balanced()
            },
            ordering: AssertOrdering::ShortestFirst,
        },
        StrategyConfig {
            name: "LocalSearch",
            description: "Minimal preset (lazy theory checking, no simplification), LocalLbd restarts, longest assertions first",
            options: vec![
                ("strategy", "local-search"),
                ("simplify", "false"),
                ("max-tries", "1000000"),
                ("noise", "0.1"),
            ],
            solver_config: SolverConfig {
                restart_strategy: RestartStrategy::LocalLbd,
                ..SolverConfig::minimal()
            },
            ordering: AssertOrdering::LongestFirst,
        },
        StrategyConfig {
            name: "Simplify-Heavy",
            description: "Thorough preset (aggressive preprocessing), LocalLbd restarts, deterministically shuffled assertion order",
            options: vec![
                ("strategy", "cdcl"),
                ("simplify", "true"),
                ("preprocessing", "aggressive"),
                ("elimination", "true"),
                ("subsumption", "true"),
                ("vivification", "true"),
            ],
            solver_config: SolverConfig {
                restart_strategy: RestartStrategy::LocalLbd,
                ..SolverConfig::thorough()
            },
            ordering: AssertOrdering::Shuffled(0xC0FF_EE00_1234_5678),
        },
    ]
}

/// Run portfolio solving with multiple strategies in parallel
pub fn solve_portfolio(
    script: &str,
    args: &Args,
    logic: Option<&str>,
    _base_ctx: &Context,
    timeout_secs: u64,
) -> Result<PortfolioResult, String> {
    solve_portfolio_custom(
        script,
        get_default_strategies(),
        args,
        logic,
        _base_ctx,
        timeout_secs,
    )
}

/// Run portfolio solving with custom strategies
///
/// Each strategy's script is independently reordered via
/// [`StrategyConfig::ordering`] before solving (see module docs), so threads
/// genuinely explore different search paths rather than repeating the same
/// solve five times.
///
/// # Residual limitation
///
/// A losing thread cannot be safely cancelled mid-`execute_script` -- Rust
/// has no safe API to interrupt another thread's execution, and
/// `oxiz_solver::Context` does not expose an internal cancellation hook. The
/// `solved` flag is therefore only checked *between* threads, not inside a
/// thread's solve; join handles are intentionally left unjoined (dropped) so
/// this function returns as soon as the first result arrives instead of
/// waiting for every strategy to finish.
pub fn solve_portfolio_custom(
    script: &str,
    strategies: Vec<StrategyConfig>,
    args: &Args,
    logic: Option<&str>,
    _base_ctx: &Context,
    timeout_secs: u64,
) -> Result<PortfolioResult, String> {
    if strategies.is_empty() {
        return Err("No strategies provided".to_string());
    }

    let script = Arc::new(script.to_string());
    let (tx, rx): (Sender<PortfolioResult>, Receiver<PortfolioResult>) = channel();
    let solved = Arc::new(AtomicBool::new(false));
    let start_time = Instant::now();

    let mut handles = Vec::new();

    for strategy in strategies {
        let tx = tx.clone();
        let script = Arc::clone(&script);
        let solved = Arc::clone(&solved);
        let logic = logic.map(|s| s.to_string());
        let args_clone = args.clone();

        let handle = thread::spawn(move || {
            // Bail out early if another strategy has already won.
            if solved.load(Ordering::SeqCst) {
                return;
            }

            let mut ctx = Context::new();

            if let Some(ref logic_str) = logic {
                ctx.set_logic(logic_str);
            }

            strategy.apply(&mut ctx);

            let mut modified_args = args_clone.clone();
            modified_args.strategy = None;
            crate::apply_solver_options(&mut ctx, &modified_args);

            let strategy_start = Instant::now();
            let diversified_script = diversify_script(&script, strategy.ordering);

            if let Ok(output) = ctx.execute_script(&diversified_script)
                && !solved.swap(true, Ordering::SeqCst)
            {
                let result = PortfolioResult {
                    strategy_name: strategy.name.to_string(),
                    output,
                    time_ms: strategy_start.elapsed().as_millis(),
                };
                let _ = tx.send(result);
            }
        });

        handles.push(handle);
    }

    // Deliberately not joined -- see the "Residual limitation" doc above.
    drop(handles);
    drop(tx);

    let timeout = if timeout_secs > 0 {
        Duration::from_secs(timeout_secs)
    } else {
        Duration::from_secs(300)
    };

    if let Ok(result) = rx.recv_timeout(timeout) {
        solved.store(true, Ordering::SeqCst);
        Ok(result)
    } else if start_time.elapsed() >= timeout {
        Err("Portfolio solving timed out".to_string())
    } else {
        Err("All strategies failed".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strategy_config() {
        let strategies = get_default_strategies();
        assert!(!strategies.is_empty());
        assert!(strategies.len() >= 3);

        // Check that each strategy has a name and options
        for strategy in strategies {
            assert!(!strategy.name.is_empty());
            assert!(!strategy.options.is_empty());
        }
    }

    #[test]
    fn test_strategy_apply() {
        let mut ctx = Context::new();
        let strategy = StrategyConfig {
            name: "test",
            description: "test strategy",
            options: vec![("strategy", "cdcl"), ("simplify", "true")],
            solver_config: SolverConfig::balanced(),
            ordering: AssertOrdering::Original,
        };

        strategy.apply(&mut ctx);
        // `apply` sets the real `SolverConfig` first: confirm it actually
        // landed on the context, not just the advisory `set_option` keys.
        assert_eq!(ctx.solver_config().theory_mode, TheoryMode::Eager);
        assert!(ctx.solver_config().simplify);
    }

    /// The core diversity claim of this module: every default strategy uses
    /// a distinct ordering, so no two threads run byte-identical scripts on
    /// a multi-assertion problem.
    #[test]
    fn test_strategies_have_distinct_orderings() {
        let strategies = get_default_strategies();
        let orderings: Vec<AssertOrdering> = strategies.iter().map(|s| s.ordering).collect();
        for i in 0..orderings.len() {
            for j in (i + 1)..orderings.len() {
                assert_ne!(
                    orderings[i], orderings[j],
                    "strategies {} and {} share an ordering",
                    strategies[i].name, strategies[j].name
                );
            }
        }
    }

    /// The other genuine diversity claim of this module: every default
    /// strategy uses a distinct `(theory_mode, simplify, restart_strategy)`
    /// triplet, so no two workers race with an identical `SolverConfig`.
    /// `theory_mode`/`simplify` are consumed on every `check_sat` (real,
    /// present-day diversity); `restart_strategy` is stored for the
    /// construction-time wiring `oxiz-solver` does today (see module docs).
    #[test]
    fn test_default_strategies_have_distinct_solver_configs() {
        let strategies = get_default_strategies();
        let triplets: Vec<(TheoryMode, bool, RestartStrategy)> = strategies
            .iter()
            .map(|s| {
                (
                    s.solver_config.theory_mode,
                    s.solver_config.simplify,
                    s.solver_config.restart_strategy,
                )
            })
            .collect();
        for i in 0..triplets.len() {
            for j in (i + 1)..triplets.len() {
                assert_ne!(
                    triplets[i], triplets[j],
                    "strategies {} and {} share a (theory_mode, simplify, restart_strategy) \
                     solver config",
                    strategies[i].name, strategies[j].name
                );
            }
        }
    }

    /// `StrategyConfig::apply` must actually install the strategy's
    /// `SolverConfig` on the context (not just the advisory string options),
    /// and different strategies must produce genuinely different installed
    /// configs.
    #[test]
    fn test_apply_installs_distinct_solver_configs() {
        let strategies = get_default_strategies();
        let mut installed = Vec::new();
        for strategy in &strategies {
            let mut ctx = Context::new();
            strategy.apply(&mut ctx);
            let cfg = ctx.solver_config();
            installed.push((cfg.theory_mode, cfg.simplify, cfg.restart_strategy));
        }
        for i in 0..installed.len() {
            for j in (i + 1)..installed.len() {
                assert_ne!(
                    installed[i], installed[j],
                    "strategies {} and {} installed the same effective solver config",
                    strategies[i].name, strategies[j].name
                );
            }
        }
    }

    const SAMPLE_SCRIPT: &str = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (> x 0))
        (assert (and (> y 0) (> z 0)))
        (assert (< (+ x y) 100))
        (assert (= z (+ x y)))
        (check-sat)
    "#;

    #[test]
    fn test_diversify_script_preserves_all_assertions() {
        use std::collections::HashSet;

        let original_asserts: Vec<String> = top_level_forms(SAMPLE_SCRIPT)
            .into_iter()
            .filter(|f| is_assert_form(f))
            .collect();
        assert_eq!(original_asserts.len(), 4);
        let original_set: HashSet<&str> = original_asserts.iter().map(String::as_str).collect();

        for ordering in [
            AssertOrdering::Original,
            AssertOrdering::Reversed,
            AssertOrdering::ShortestFirst,
            AssertOrdering::LongestFirst,
            AssertOrdering::Shuffled(42),
        ] {
            let diversified = diversify_script(SAMPLE_SCRIPT, ordering);
            let got_asserts: Vec<String> = top_level_forms(&diversified)
                .into_iter()
                .filter(|f| is_assert_form(f))
                .collect();

            // Same multiset of assertions -- reordering must not drop, add,
            // or mutate any assertion.
            let got_set: HashSet<&str> = got_asserts.iter().map(String::as_str).collect();
            assert_eq!(
                original_set, got_set,
                "ordering {:?} lost/added an assertion",
                ordering
            );

            // Declarations must still precede check-sat.
            assert!(diversified.contains("declare-const x"));
            assert!(
                diversified.find("check-sat").unwrap()
                    > diversified.find("declare-const x").unwrap()
            );
        }
    }

    #[test]
    fn test_diversify_script_orderings_genuinely_differ() {
        let original = diversify_script(SAMPLE_SCRIPT, AssertOrdering::Original);
        let reversed = diversify_script(SAMPLE_SCRIPT, AssertOrdering::Reversed);
        let shortest = diversify_script(SAMPLE_SCRIPT, AssertOrdering::ShortestFirst);
        let longest = diversify_script(SAMPLE_SCRIPT, AssertOrdering::LongestFirst);

        assert_ne!(original, reversed);
        assert_ne!(original, shortest);
        assert_ne!(original, longest);
        assert_ne!(shortest, longest);
    }

    #[test]
    fn test_is_assert_form_excludes_assert_partition() {
        assert!(is_assert_form("(assert (> x 0))"));
        assert!(is_assert_form("(assert p)"));
        assert!(!is_assert_form("(assert-partition A p)"));
        assert!(!is_assert_form("(declare-const x Int)"));
    }

    #[test]
    fn test_solve_portfolio_custom_runs_real_solve() {
        use clap::Parser;

        let strategies = get_default_strategies();
        let args = Args::parse_from(["oxiz"]);
        let ctx = Context::new();
        let result = solve_portfolio_custom(
            "(declare-const p Bool)\n(assert p)\n(check-sat)\n",
            strategies,
            &args,
            None,
            &ctx,
            10,
        );
        let result = result.expect("portfolio solve should succeed");
        assert_eq!(result.output, vec!["sat".to_string()]);
    }
}
