//! Tactic Registry for OxiZ.
//!
//! Provides a string-keyed factory map for all concrete tactic implementations
//! in `oxiz-core`. Any crate that can access `oxiz-core` can call
//! [`default_registry`] to obtain a fully populated registry and then call
//! [`TacticRegistry::create`] by name, without knowing the concrete types.
//!
//! # Design
//!
//! - [`TacticRegistry`] is a plain `HashMap`-backed struct – no
//!   `lazy_static`/`once_cell` global state.  Each call to
//!   [`default_registry`] produces an independent instance, which is cheap
//!   because the factories are function pointers wrapped in `Box<dyn Fn>`.
//! - Factories that require a `TermManager` (stateful tactics) are represented
//!   by their *stateless* Newtype wrappers, which implement
//!   [`crate::tactic::core::Tactic`] and honestly return
//!   [`TacticResult::NotApplicable`] (or an unchanged goal) from `apply`,
//!   since [`Tactic::apply`] has no
//!   `TermManager` parameter to allocate fresh terms with.
//! - Tactics whose *real* transformation genuinely requires `&mut
//!   TermManager` access (currently `ArithBoundsTactic::analyze` and
//!   `BitBlaster::blast_goal`) are additionally exposed through a second,
//!   parallel by-name dispatch path: [`ManagedTactic`] /
//!   [`TacticRegistry::create_managed`]. This is the *real, working*
//!   implementation – callers that hold a `&mut TermManager` (e.g. a
//!   tactic-pipeline driver that owns the goal's term manager) should
//!   prefer `create_managed` over `create` for these names to get an actual
//!   transformation instead of a honest no-op/`NotApplicable`.
//! - Tactics that have no zero-argument constructor (e.g. `DerTactic`,
//!   `MbpTactic`) are excluded and documented below.
//!
//! # Excluded tactics
//!
//! | Tactic | Reason |
//! |--------|--------|
//! | `DerTactic` / `StatelessDerTactic` | `StatelessDerTactic` does not implement `Tactic`; its `apply` requires a `&mut TermManager` argument. |
//! | `MbpTactic` | No `Tactic` impl; requires a `&mut TermManager` and `MbpEngine` at construction. |
//! | `ScriptableTactic` | Requires a Rhai script string at construction time. |
//! | `CondTactic` / `WhenTactic` / `FailIfTactic` | Require combinator sub-tactics at construction. |
//! | `TseitinCnfTactic` / `NnfTactic` (stateful) | Require `&mut TermManager`. |
//! | `SkolemizationTactic` / `QuantifierInstantiationTactic` / `UniversalEliminationTactic` | Require `&mut TermManager`. |
//! | `FactorTactic` | Registered as "factor" using `Default`. |
//! | `BvArray2UfTactic` | Registered as "bvarray2uf" using `Default`. |
//!
//! `ArithBoundsTactic` ("arith-bounds") and the bit-blasting engine
//! (`BitBlaster`, "bit-blast") are registered on *both* paths: the plain
//! [`Tactic`]-only path (honest `NotApplicable`/detection-only, for callers
//! without manager access) and the [`ManagedTactic`] path (the real
//! analysis/blasting, for callers with manager access).

use std::collections::HashMap;

use crate::ast::TermManager;
use crate::error::Result;
use crate::tactic::core::{Goal, Tactic, TacticResult};

// ======== Type aliases ========

/// Type alias for a boxed tactic factory closure.
type TacticFactory = Box<dyn Fn() -> Box<dyn Tactic> + Send + Sync>;

/// Type alias for a boxed [`ManagedTactic`] factory closure.
type ManagedTacticFactory = Box<dyn Fn() -> Box<dyn ManagedTactic> + Send + Sync>;

// ======== Concrete tactic imports ========

// Top-level stateless tactics
use super::ackermann::StatelessAckermannizeTactic;
use super::aggressive_simplify::StatelessAggressiveSimplifyTactic;
use super::bitblast::{BitBlaster, StatelessBitBlastTactic};
use super::ctx_simplify::StatelessCtxSolverSimplifyTactic;
use super::eliminate::StatelessEliminateUnconstrainedTactic;
use super::pb2bv::StatelessPb2BvTactic;
use super::propagate::StatelessPropagateValuesTactic;
use super::simplify::StatelessSimplifyTactic;
use super::solve_eqs::{
    StatelessCnfTactic, StatelessFourierMotzkinTactic, StatelessNnfTactic, StatelessSolveEqsTactic,
};
use super::split::StatelessSplitTactic;

// Arith tactics
use super::arith::arith_bounds::{ArithBoundsConfig, ArithBoundsTactic};
use super::arith::factor::{FactorTactic, FactorTacticConfig};

// BV tactics
use super::bv::bvarray2uf::{BvArray2UfConfig, BvArray2UfTactic};

// Sub-module tactics with Tactic impl
use super::lia2card::StatelessLia2CardTactic;
use super::nla2bv::StatelessNla2BvTactic;

// ======== ManagedTactic ========

/// A tactic whose real transformation requires mutable access to the
/// [`TermManager`] that owns the goal's terms (to allocate fresh Boolean
/// variables, circuit terms, etc.).
///
/// This exists alongside [`Tactic`] rather than replacing it because
/// [`Tactic::apply`] intentionally has no `TermManager` parameter (many
/// tactics are genuinely stateless and manager-free). Implementors that
/// *also* implement [`Tactic`] must keep that impl honest – e.g. by
/// returning [`TacticResult::NotApplicable`] or the goal unchanged – since
/// [`Tactic::apply`] structurally cannot perform the real transformation.
pub trait ManagedTactic: Send + Sync {
    /// The canonical registry name of this tactic.
    fn name(&self) -> &str;

    /// Apply the tactic to `goal`, allocating any new terms it needs in
    /// `manager`.
    fn apply_with_manager(
        &mut self,
        goal: &Goal,
        manager: &mut TermManager,
    ) -> Result<TacticResult>;

    /// Get a description of the tactic.
    fn description(&self) -> &str {
        ""
    }
}

impl ManagedTactic for ArithBoundsTactic {
    fn name(&self) -> &str {
        "arith-bounds"
    }

    fn apply_with_manager(
        &mut self,
        goal: &Goal,
        manager: &mut TermManager,
    ) -> Result<TacticResult> {
        // `analyze` only reads the manager (it never allocates terms), so
        // the `&mut TermManager` is implicitly reborrowed as `&TermManager`
        // here.
        self.analyze(goal, manager)
    }

    fn description(&self) -> &str {
        "Extracts literal variable bounds, detects inconsistencies as early UNSAT, \
         and drops assertions provably implied by the surviving bounds"
    }
}

impl ManagedTactic for BitBlaster {
    fn name(&self) -> &str {
        "bit-blast"
    }

    fn apply_with_manager(
        &mut self,
        goal: &Goal,
        manager: &mut TermManager,
    ) -> Result<TacticResult> {
        self.blast_goal(goal, manager)
    }

    fn description(&self) -> &str {
        "Bit-blasts quantifier-free BitVector/Boolean formulas into pure Boolean circuits \
         (ripple-carry arithmetic, shift-and-add multiplier, restoring divider, barrel \
         shifter, MSB-to-LSB comparators); bails out honestly via NotApplicable on any \
         unsupported construct"
    }
}

// ======== TacticRegistry ========

/// A registry mapping string names to zero-argument tactic constructor closures.
///
/// Call [`default_registry`] to obtain a pre-populated instance.
pub struct TacticRegistry {
    factories: HashMap<&'static str, TacticFactory>,
    managed_factories: HashMap<&'static str, ManagedTacticFactory>,
}

impl TacticRegistry {
    /// Create an empty registry.
    #[must_use]
    pub fn new() -> Self {
        Self {
            factories: HashMap::new(),
            managed_factories: HashMap::new(),
        }
    }

    /// Register a tactic factory under the given canonical name.
    ///
    /// Subsequent calls with the same name overwrite the previous registration.
    pub fn register<F>(&mut self, name: &'static str, factory: F)
    where
        F: Fn() -> Box<dyn Tactic> + Send + Sync + 'static,
    {
        self.factories
            .insert(name, Box::new(factory) as TacticFactory);
    }

    /// Register a [`ManagedTactic`] factory under the given canonical name.
    ///
    /// Subsequent calls with the same name overwrite the previous registration.
    pub fn register_managed<F>(&mut self, name: &'static str, factory: F)
    where
        F: Fn() -> Box<dyn ManagedTactic> + Send + Sync + 'static,
    {
        self.managed_factories
            .insert(name, Box::new(factory) as ManagedTacticFactory);
    }

    /// Create a fresh tactic instance by name.
    ///
    /// Returns `None` if `name` is not registered.
    #[must_use]
    pub fn create(&self, name: &str) -> Option<Box<dyn Tactic>> {
        self.factories.get(name).map(|f| f())
    }

    /// Create a fresh [`ManagedTactic`] instance by name.
    ///
    /// Returns `None` if `name` has no manager-aware registration – either
    /// because the tactic doesn't need `TermManager` access at all (use
    /// [`create`](Self::create) instead), or because it isn't registered.
    #[must_use]
    pub fn create_managed(&self, name: &str) -> Option<Box<dyn ManagedTactic>> {
        self.managed_factories.get(name).map(|f| f())
    }

    /// Returns a sorted list of all registered tactic names.
    #[must_use]
    pub fn names(&self) -> Vec<&'static str> {
        let mut v: Vec<_> = self.factories.keys().copied().collect();
        v.sort_unstable();
        v
    }

    /// Returns a sorted list of all registered [`ManagedTactic`] names.
    #[must_use]
    pub fn managed_names(&self) -> Vec<&'static str> {
        let mut v: Vec<_> = self.managed_factories.keys().copied().collect();
        v.sort_unstable();
        v
    }

    /// Returns `true` if `name` is registered in this registry.
    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.factories.contains_key(name)
    }

    /// Returns `true` if `name` has a manager-aware registration.
    #[must_use]
    pub fn contains_managed(&self, name: &str) -> bool {
        self.managed_factories.contains_key(name)
    }
}

impl Default for TacticRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ======== SkipTactic ========

/// A no-op tactic that always returns `SubGoals` with the goal unchanged.
///
/// Used as the `"skip"` entry in the default registry.
#[derive(Debug, Clone, Default)]
struct SkipTactic;

impl Tactic for SkipTactic {
    fn name(&self) -> &str {
        "skip"
    }

    fn apply(&self, goal: &Goal) -> Result<TacticResult> {
        Ok(TacticResult::SubGoals(vec![goal.clone()]))
    }

    fn description(&self) -> &str {
        "A no-op tactic that returns the goal unchanged"
    }
}

// ======== Manager-backed wrappers for the stateful tactics ========
//
// Each stateful tactic (`SimplifyTactic`, `SolveEqsTactic`, …) borrows a
// `&mut TermManager` at construction and performs its real transformation in
// `apply_mut`. Their `Tactic`-only newtypes cannot do this (the manager-free
// `Tactic::apply` returns an honest `NotApplicable`). These zero-sized
// [`ManagedTactic`] wrappers construct the stateful tactic with the caller's
// manager and delegate to `apply_mut`, so `create_managed(name)` performs the
// actual work (P4-1107).
macro_rules! managed_stateful_wrapper {
    ($wrapper:ident, $name:literal, $ctor:path, $desc:literal) => {
        struct $wrapper;

        impl ManagedTactic for $wrapper {
            fn name(&self) -> &str {
                $name
            }

            fn apply_with_manager(
                &mut self,
                goal: &Goal,
                manager: &mut TermManager,
            ) -> Result<TacticResult> {
                $ctor(manager).apply_mut(goal)
            }

            fn description(&self) -> &str {
                $desc
            }
        }
    };
}

managed_stateful_wrapper!(
    ManagedSimplify,
    "simplify",
    super::simplify::SimplifyTactic::new,
    "Simplifies boolean and arithmetic expressions"
);
managed_stateful_wrapper!(
    ManagedPropagateValues,
    "propagate-values",
    super::propagate::PropagateValuesTactic::new,
    "Propagates constant values through the formula"
);
managed_stateful_wrapper!(
    ManagedCtxSolverSimplify,
    "ctx-solver-simplify",
    super::ctx_simplify::CtxSolverSimplifyTactic::new,
    "Simplifies assertions using other assertions as context"
);
managed_stateful_wrapper!(
    ManagedAggressiveSimplify,
    "aggressive-simplify",
    super::aggressive_simplify::AggressiveSimplifyTactic::new,
    "Applies aggressive Boolean and arithmetic simplifications"
);
managed_stateful_wrapper!(
    ManagedElimUncnstr,
    "elim-uncnstr",
    super::eliminate::EliminateUnconstrainedTactic::new,
    "Eliminates unconstrained variables from the formula"
);
managed_stateful_wrapper!(
    ManagedSolveEqs,
    "solve-eqs",
    super::solve_eqs::SolveEqsTactic::new,
    "Gaussian elimination for linear equations - solves x = expr and substitutes"
);
managed_stateful_wrapper!(
    ManagedFourierMotzkin,
    "fm",
    super::solve_eqs::FourierMotzkinTactic::new,
    "Fourier-Motzkin variable elimination for linear arithmetic"
);
managed_stateful_wrapper!(
    ManagedNnf,
    "nnf",
    super::solve_eqs::NnfTactic::new,
    "Convert formulas to Negation Normal Form"
);
managed_stateful_wrapper!(
    ManagedTseitinCnf,
    "tseitin-cnf",
    super::solve_eqs::TseitinCnfTactic::new,
    "Convert formulas to Conjunctive Normal Form using the Tseitin transformation"
);
managed_stateful_wrapper!(
    ManagedAckermannize,
    "ackermannize",
    super::ackermann::AckermannizeTactic::new,
    "Eliminates uninterpreted functions by adding functional consistency constraints"
);
managed_stateful_wrapper!(
    ManagedSplit,
    "split",
    super::split::SplitTactic::new,
    "Performs case splitting on boolean subterms"
);

// ======== default_registry ========

/// Build and return the default registry with all known zero-argument tactics
/// registered under their canonical names.
///
/// This is a free function (not a global singleton) so that callers always
/// get an independent, freshly constructed registry – useful for testing and
/// for avoiding `Send`/`Sync` complexity of globals.
#[must_use]
pub fn default_registry() -> TacticRegistry {
    let mut reg = TacticRegistry::new();

    // ======== Core simplification tactics ========
    reg.register("simplify", || Box::new(StatelessSimplifyTactic));
    reg.register("propagate-values", || {
        Box::new(StatelessPropagateValuesTactic)
    });
    reg.register("ctx-solver-simplify", || {
        Box::new(StatelessCtxSolverSimplifyTactic)
    });
    reg.register("aggressive-simplify", || {
        Box::new(StatelessAggressiveSimplifyTactic)
    });

    // ======== Bit-blasting and bitvector tactics ========
    reg.register("bit-blast", || Box::new(StatelessBitBlastTactic));
    reg.register("bvarray2uf", || {
        Box::new(BvArray2UfTactic::new(BvArray2UfConfig::default()))
    });

    // ======== UF (uninterpreted functions) ========
    reg.register("ackermannize", || Box::new(StatelessAckermannizeTactic));

    // ======== Variable elimination and equation solving ========
    reg.register("elim-uncnstr", || {
        Box::new(StatelessEliminateUnconstrainedTactic)
    });
    reg.register("solve-eqs", || Box::new(StatelessSolveEqsTactic));

    // ======== Normal forms and CNF ========
    reg.register("nnf", || Box::new(StatelessNnfTactic));
    reg.register("tseitin-cnf", || Box::new(StatelessCnfTactic));

    // ======== Arithmetic tactics ========
    reg.register("fm", || Box::new(StatelessFourierMotzkinTactic));
    reg.register("arith-bounds", || {
        Box::new(ArithBoundsTactic::new(ArithBoundsConfig::default()))
    });
    reg.register("factor", || {
        Box::new(FactorTactic::new(FactorTacticConfig::default()))
    });

    // ======== Pseudo-boolean and cardinality ========
    reg.register("pb2bv", || Box::new(StatelessPb2BvTactic));
    reg.register("lia2card", || Box::new(StatelessLia2CardTactic::new()));

    // ======== Non-linear arithmetic ========
    reg.register("nla2bv", || Box::new(StatelessNla2BvTactic::new()));

    // ======== Goal splitting ========
    reg.register("split", || Box::new(StatelessSplitTactic));

    // ======== Utility ========
    reg.register("skip", || Box::new(SkipTactic));

    // ======== Manager-aware tactics (real, TermManager-backed implementations) ========
    //
    // These duplicate the "arith-bounds" / "bit-blast" names on the
    // `create_managed` path with the *working* implementation: unlike their
    // `Tactic`-only counterparts above (which are structurally limited to
    // NotApplicable / detection-only, since `Tactic::apply` has no manager
    // parameter), these call the real `ArithBoundsTactic::analyze` /
    // `BitBlaster::blast_goal` entry points.
    reg.register_managed("arith-bounds", || {
        Box::new(ArithBoundsTactic::new(ArithBoundsConfig::default()))
    });
    reg.register_managed("bit-blast", || Box::new(BitBlaster::new()));

    // Manager-backed wrappers for the remaining stateful tactics. Their
    // `Tactic`-only counterparts registered above are honest `NotApplicable`
    // no-ops (they have no manager to transform with); these `create_managed`
    // entries run the real `apply_mut` transformation (P4-1107).
    reg.register_managed("simplify", || Box::new(ManagedSimplify));
    reg.register_managed("propagate-values", || Box::new(ManagedPropagateValues));
    reg.register_managed("ctx-solver-simplify", || Box::new(ManagedCtxSolverSimplify));
    reg.register_managed("aggressive-simplify", || {
        Box::new(ManagedAggressiveSimplify)
    });
    reg.register_managed("elim-uncnstr", || Box::new(ManagedElimUncnstr));
    reg.register_managed("solve-eqs", || Box::new(ManagedSolveEqs));
    reg.register_managed("fm", || Box::new(ManagedFourierMotzkin));
    reg.register_managed("nnf", || Box::new(ManagedNnf));
    reg.register_managed("tseitin-cnf", || Box::new(ManagedTseitinCnf));
    reg.register_managed("ackermannize", || Box::new(ManagedAckermannize));
    reg.register_managed("split", || Box::new(ManagedSplit));

    reg
}

// ======== Tests ========

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_contains_simplify() {
        let reg = default_registry();
        assert!(reg.contains("simplify"));
    }

    #[test]
    fn test_registry_create_simplify_returns_some() {
        let reg = default_registry();
        assert!(reg.create("simplify").is_some());
    }

    #[test]
    fn test_registry_create_unknown_returns_none() {
        let reg = default_registry();
        assert!(reg.create("not-a-real-tactic").is_none());
    }

    #[test]
    fn test_registry_names_sorted() {
        let reg = default_registry();
        let names = reg.names();
        assert!(!names.is_empty());
        assert!(names.contains(&"simplify"));
        // names should be sorted
        let mut sorted = names.clone();
        sorted.sort_unstable();
        assert_eq!(names, sorted);
    }

    #[test]
    fn test_registry_create_produces_independent_instances() {
        let reg = default_registry();
        let _t1 = reg.create("simplify").unwrap();
        let _t2 = reg.create("simplify").unwrap();
        // Two independent instances – just verifying both are Some
    }

    #[test]
    fn test_registry_contains_all_core_tactics() {
        let reg = default_registry();
        let expected = [
            "simplify",
            "propagate-values",
            "bit-blast",
            "ackermannize",
            "ctx-solver-simplify",
            "elim-uncnstr",
            "pb2bv",
            "solve-eqs",
            "fm",
            "nnf",
            "tseitin-cnf",
            "split",
            "aggressive-simplify",
            "lia2card",
            "nla2bv",
            "arith-bounds",
            "factor",
            "bvarray2uf",
            "skip",
        ];
        for name in expected {
            assert!(
                reg.contains(name),
                "default_registry missing tactic: {}",
                name
            );
        }
    }

    #[test]
    fn test_registry_create_skip_returns_subgoals() {
        let reg = default_registry();
        let tactic = reg.create("skip").unwrap();
        let goal = crate::tactic::core::Goal::empty();
        let result = tactic.apply(&goal).expect("skip should not fail");
        assert!(matches!(result, TacticResult::SubGoals(_)));
    }

    #[test]
    fn test_registry_names_count() {
        let reg = default_registry();
        // We register 19 tactics; ensure count is at least 19
        assert!(reg.names().len() >= 19);
    }

    #[test]
    fn test_registry_tactic_names_match_canonical() {
        let reg = default_registry();
        let names = reg.names();
        for name in &names {
            let tactic = reg.create(name).unwrap();
            assert_eq!(
                tactic.name(),
                *name,
                "tactic.name() '{}' does not match registry key '{}'",
                tactic.name(),
                name
            );
        }
    }

    #[test]
    fn test_registry_default_is_empty() {
        let reg = TacticRegistry::default();
        assert!(reg.names().is_empty());
        assert!(!reg.contains("simplify"));
    }

    #[test]
    fn test_registry_register_and_create() {
        let mut reg = TacticRegistry::new();
        reg.register("skip", || Box::new(SkipTactic));
        assert!(reg.contains("skip"));
        let tactic = reg.create("skip").unwrap();
        assert_eq!(tactic.name(), "skip");
    }

    // ======== ManagedTactic wiring regression tests ========
    //
    // Wave-1 left `ArithBoundsTactic::apply` and the `Tactic` impls around
    // bit-blasting honestly `NotApplicable`/detection-only, because
    // `Tactic::apply` has no `TermManager` parameter. These tests confirm
    // that by-name lookup on the *managed* path returns the real,
    // TermManager-backed implementations instead.

    #[test]
    fn test_registry_create_managed_unknown_returns_none() {
        let reg = default_registry();
        assert!(reg.create_managed("not-a-real-tactic").is_none());
    }

    #[test]
    fn test_registry_managed_names_contains_arith_bounds_and_bit_blast() {
        let reg = default_registry();
        let names = reg.managed_names();
        assert!(names.contains(&"arith-bounds"));
        assert!(names.contains(&"bit-blast"));
    }

    #[test]
    fn test_registry_managed_tactic_names_match_canonical() {
        let reg = default_registry();
        for name in reg.managed_names() {
            let tactic = reg
                .create_managed(name)
                .expect("managed_names() entries must be creatable");
            assert_eq!(
                tactic.name(),
                name,
                "ManagedTactic::name() '{}' does not match registry key '{}'",
                tactic.name(),
                name
            );
        }
    }

    #[test]
    fn test_registry_managed_arith_bounds_detects_inconsistency() {
        use crate::tactic::core::SolveResult;

        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let ten = manager.mk_int(10);
        let five = manager.mk_int(5);
        let ge = manager.mk_ge(x, ten); // x >= 10
        let le = manager.mk_le(x, five); // x <= 5

        let goal = Goal::new(vec![ge, le]);
        let reg = default_registry();
        let mut tactic = reg
            .create_managed("arith-bounds")
            .expect("arith-bounds must be manager-aware registered");
        let result = tactic
            .apply_with_manager(&goal, &mut manager)
            .expect("analyze should not error");

        assert!(matches!(result, TacticResult::Solved(SolveResult::Unsat)));
    }

    #[test]
    fn test_registry_managed_arith_bounds_drops_redundant_assertion() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let three = manager.mk_int(3);
        let five = manager.mk_int(5);
        let ge5 = manager.mk_ge(x, five); // x >= 5
        let ge3 = manager.mk_ge(x, three); // x >= 3, implied by x >= 5

        let goal = Goal::new(vec![ge5, ge3]);
        let reg = default_registry();
        let mut tactic = reg
            .create_managed("arith-bounds")
            .expect("arith-bounds must be manager-aware registered");
        let result = tactic
            .apply_with_manager(&goal, &mut manager)
            .expect("analyze should not error");

        match result {
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1);
                assert_eq!(goals[0].assertions, vec![ge5]);
            }
            other => panic!("expected SubGoals dropping the redundant assertion, got {other:?}"),
        }
    }

    #[test]
    fn test_registry_managed_bit_blast_produces_pure_boolean_circuit() {
        let mut manager = TermManager::new();
        let a = manager.mk_bitvec(3u64, 4);
        let b = manager.mk_bitvec(5u64, 4);
        // Interned raw: `mk_bv_add` folds two literals, and a goal with no BV
        // structure left would be honestly NotApplicable instead of exercising
        // the registry's manager-aware bit-blast path.
        let bv4 = manager.sorts.bitvec(4);
        let sum = manager.intern_term(crate::ast::TermKind::BvAdd(a, b), bv4);
        let expected = manager.mk_bitvec(8u64, 4); // 3 + 5 = 8
        let eq = manager.mk_eq(sum, expected);

        let goal = Goal::new(vec![eq]);
        let reg = default_registry();
        let mut tactic = reg
            .create_managed("bit-blast")
            .expect("bit-blast must be manager-aware registered");
        let result = tactic
            .apply_with_manager(&goal, &mut manager)
            .expect("blast_goal should not error");

        match result {
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1);
                // The blasted circuit for a valid arithmetic identity must
                // simplify away to the Boolean constant `true` -- a real
                // transformation happened, not a pass-through.
                assert_eq!(goals[0].assertions, vec![manager.mk_true()]);
            }
            other => panic!("expected SubGoals with a blasted circuit, got {other:?}"),
        }
    }

    #[test]
    fn test_registry_plain_arith_bounds_stays_honestly_not_applicable() {
        // The plain `Tactic`-only path has no manager access and must stay
        // an honest NotApplicable rather than silently doing (or faking)
        // the real analysis performed on the managed path above.
        let reg = default_registry();
        let tactic = reg.create("arith-bounds").unwrap();
        let goal = Goal::empty();
        let result = tactic.apply(&goal).expect("apply should not error");
        assert!(matches!(result, TacticResult::NotApplicable));
    }

    #[test]
    fn test_registry_plain_bit_blast_is_honestly_not_applicable() {
        // The plain `Tactic`-only path cannot allocate terms, so even a goal
        // with real BitVector content must come back honestly NotApplicable
        // (never a silent goal-unchanged "success", never a partial/incorrect
        // blast).
        let mut manager = TermManager::new();
        let a = manager.mk_bitvec(3u64, 4);
        let b = manager.mk_bitvec(5u64, 4);
        let sum = manager.mk_bv_add(a, b);
        let expected = manager.mk_bitvec(8u64, 4);
        let eq = manager.mk_eq(sum, expected);

        let reg = default_registry();
        let tactic = reg.create("bit-blast").unwrap();
        let goal = Goal::new(vec![eq]);
        let result = tactic.apply(&goal).expect("apply should not error");
        assert!(matches!(result, TacticResult::NotApplicable));
    }

    #[test]
    fn test_registry_plain_transforming_tactics_are_not_applicable() {
        // Every manager-requiring stateless tactic's plain path must be an
        // honest NotApplicable rather than a silent goal-unchanged success
        // (P4-1107). `skip` is intentionally excluded – its name honestly
        // advertises a no-op.
        let reg = default_registry();
        let goal = Goal::empty();
        for name in [
            "simplify",
            "propagate-values",
            "ctx-solver-simplify",
            "aggressive-simplify",
            "elim-uncnstr",
            "solve-eqs",
            "fm",
            "nnf",
            "tseitin-cnf",
            "ackermannize",
            "split",
            "bit-blast",
            "arith-bounds",
        ] {
            let tactic = reg.create(name).unwrap();
            let result = tactic.apply(&goal).expect("apply should not error");
            assert!(
                matches!(result, TacticResult::NotApplicable),
                "plain path of '{name}' must be NotApplicable, got {result:?}"
            );
        }
    }

    #[test]
    fn test_registry_managed_solve_eqs_performs_real_substitution() {
        // The managed path must actually solve `x = 5` and substitute, not
        // return the goal unchanged.
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let five = manager.mk_int(5);
        let eq_x5 = manager.mk_eq(x, five); // x = 5
        let x_gt_y = manager.mk_gt(x, y); // x > y

        let goal = Goal::new(vec![eq_x5, x_gt_y]);
        let reg = default_registry();
        let mut tactic = reg
            .create_managed("solve-eqs")
            .expect("solve-eqs must be manager-aware registered");
        let result = tactic
            .apply_with_manager(&goal, &mut manager)
            .expect("apply_mut should not error");

        match result {
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1);
                // The x = 5 equation is consumed and x is substituted, so the
                // transformed goal is strictly smaller than the original and
                // no longer contains the solved equation.
                assert!(
                    !goals[0].assertions.contains(&eq_x5),
                    "solved equation must be removed"
                );
                assert!(goals[0].assertions.len() < 2);
            }
            other => panic!("expected SubGoals from real solve-eqs, got {other:?}"),
        }
    }

    #[test]
    fn test_registry_managed_simplify_performs_real_simplification() {
        // simplify on `(or true false)` must fold to a solved/true result,
        // not return the goal unchanged.
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();
        let or_tf = manager.mk_or([t, f]); // simplifies to true

        let goal = Goal::new(vec![or_tf]);
        let reg = default_registry();
        let mut tactic = reg
            .create_managed("simplify")
            .expect("simplify must be manager-aware registered");
        let result = tactic
            .apply_with_manager(&goal, &mut manager)
            .expect("apply_mut should not error");

        // `(or true false)` == true, so the single assertion folds away and
        // the goal is solved SAT.
        assert!(matches!(
            result,
            TacticResult::Solved(crate::tactic::core::SolveResult::Sat)
        ));
    }

    #[test]
    fn test_registry_managed_names_cover_transforming_tactics() {
        let reg = default_registry();
        let names = reg.managed_names();
        for expected in [
            "arith-bounds",
            "bit-blast",
            "simplify",
            "propagate-values",
            "ctx-solver-simplify",
            "aggressive-simplify",
            "elim-uncnstr",
            "solve-eqs",
            "fm",
            "nnf",
            "tseitin-cnf",
            "ackermannize",
            "split",
        ] {
            assert!(
                names.contains(&expected),
                "managed registry missing '{expected}'"
            );
        }
    }
}
