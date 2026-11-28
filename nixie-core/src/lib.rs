//! Nixie Core - AST, Sorts, and Traits for the SMT Solver
//!
//! This crate provides the foundational types and traits for the Nixie SMT solver:
//! - Arena-allocated terms with efficient [`TermId`] references
//! - Sort system for type checking
//! - SMT-LIB2 parser and printer (requires `std` feature)
//! - Tactic framework for preprocessing and simplification (requires `std` feature)
//! - Rewrite system for term transformations
//!
//! # Examples
//!
//! ## Creating Terms
//!
//! ```
//! use nixie_core::ast::TermManager;
//! use num_bigint::BigInt;
//!
//! let mut tm = TermManager::new();
//!
//! // Boolean terms
//! let p = tm.mk_var("p", tm.sorts.bool_sort);
//! let q = tm.mk_var("q", tm.sorts.bool_sort);
//! let and_pq = tm.mk_and(vec![p, q]);
//!
//! // Integer terms
//! let x = tm.mk_var("x", tm.sorts.int_sort);
//! let five = tm.mk_int(BigInt::from(5));
//! let ge = tm.mk_ge(x, five);
//! ```
//!
//! ## Parsing SMT-LIB2
//!
//! ```
//! use nixie_core::smtlib::parse_script;
//! use nixie_core::ast::TermManager;
//!
//! let input = r#"
//!     (declare-const x Int)
//!     (assert (> x 0))
//!     (check-sat)
//! "#;
//!
//! let mut tm = TermManager::new();
//! let commands = parse_script(input, &mut tm).unwrap();
//! ```
//!
//! ## Using Tactics
//!
//! ```
//! use nixie_core::tactic::{Goal, StatelessSimplifyTactic, Tactic};
//! use nixie_core::ast::TermManager;
//!
//! let mut tm = TermManager::new();
//!
//! // Create a goal with some formula
//! let t = tm.mk_true();
//! let f = tm.mk_false();
//! let or_tf = tm.mk_or(vec![t, f]);
//!
//! let goal = Goal::new(vec![or_tf]);
//! let tactic = StatelessSimplifyTactic;
//!
//! // Apply simplification
//! let result = tactic.apply(&goal);
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unsafe_code)]
#![warn(missing_docs)]
// Without `std`, every item whose only users are `std`-gated (file tracers,
// thread-backed combinators, environment probes behind them) is unused by
// construction; the configuration is still compiled warning-clean otherwise.
#![cfg_attr(
    not(feature = "std"),
    allow(dead_code, unused_variables, unused_assignments, unused_mut)
)]

// Native builds must never silently end up on nixie-time's frozen stub clock
// (the `nixie-time/std` feature in this crate's manifest is what selects the
// real one; see nixie-time/src/lib.rs). The frozen clock is *by design* in the
// two configurations the cfg excludes: `no_std` (`--no-default-features`) and
// `wasm32-unknown-unknown`, which has no clock.
#[cfg(all(
    feature = "std",
    not(all(target_arch = "wasm32", target_os = "unknown"))
))]
const _: () = assert!(!nixie_time::IS_FROZEN, "nixie-time/std must be forwarded");

#[cfg(not(feature = "std"))]
extern crate alloc;

/// The process environment, for the `NIXIE_*` knobs the library crates still
/// read where they are used (each crate's `env` module re-exports it).
///
/// Every read goes through [`env::var`] or [`env::var_os`] so that a `no_std`
/// build – which has no environment – compiles the same call sites: each lookup
/// answers [`env::VarError::NotPresent`] / `None` and every gated path takes its
/// "off" branch, exactly as on `wasm32-unknown-unknown`, where there is no
/// environment either. The crate's own diagnostics and feature switches are
/// the only consumers; the typed `Config` structs are the public interface.
pub mod env {
    /// Why a [`var`] lookup failed.
    #[cfg(feature = "std")]
    pub use std::env::VarError;

    /// Why a [`var`] lookup failed. Without an operating system every lookup
    /// is [`VarError::NotPresent`].
    #[cfg(not(feature = "std"))]
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum VarError {
        /// The variable is not set (always, without an operating system).
        NotPresent,
        /// Kept for signature parity with `std::env::VarError`; never produced.
        NotUnicode,
    }

    #[cfg(feature = "std")]
    use std::ffi::OsStr;
    /// The platform string [`var_os`] returns.
    #[cfg(feature = "std")]
    pub use std::ffi::OsString;

    /// The platform string [`var_os`] returns: a type with no values, since
    /// there is no environment to read one from.
    #[cfg(not(feature = "std"))]
    pub type OsString = core::convert::Infallible;

    /// Fetches the environment variable `key` from the current process.
    #[cfg(feature = "std")]
    #[inline]
    pub fn var<K: AsRef<OsStr>>(key: K) -> Result<String, VarError> {
        std::env::var(key)
    }

    /// Fetches the environment variable `key` from the current process: there
    /// is none without an operating system.
    #[cfg(not(feature = "std"))]
    #[inline]
    pub fn var<K: AsRef<str>>(_key: K) -> Result<alloc::string::String, VarError> {
        Err(VarError::NotPresent)
    }

    /// Fetches the environment variable `key` from the current process as a
    /// platform string.
    #[cfg(feature = "std")]
    #[inline]
    pub fn var_os<K: AsRef<OsStr>>(key: K) -> Option<OsString> {
        std::env::var_os(key)
    }

    /// Fetches the environment variable `key` from the current process as a
    /// platform string: there is none without an operating system.
    #[cfg(not(feature = "std"))]
    #[inline]
    pub fn var_os<K: AsRef<str>>(_key: K) -> Option<OsString> {
        None
    }
}

/// The pieces the workspace's `no_std` builds use in place of `std` ones.
///
/// Present only without the `std` feature: under `std` the originals are used
/// and a call site is written once either way (the crate preludes pick).
#[cfg(not(feature = "std"))]
pub mod no_std {
    /// The `std`-only `f64` methods for `no_std` builds (defined in
    /// `nixie-math`, re-exported so the crates above this one need no direct
    /// edge on it).
    pub use nixie_math::F64Ext;

    /// [`std::sync::OnceLock`]'s shape: a cell a `static` can hold, which the
    /// first `get_or_init` initializes and every later one reads.
    ///
    /// `core` has no `Sync` once-cell, and this crate and the ones above it
    /// forbid `unsafe`, so the storage is `spin::once::Once` – `Sync` for
    /// `T: Send + Sync` through its own atomics, which this newtype inherits.
    /// As with `std`'s, the initializing closure may run more than once if two
    /// threads race; only one result is kept.
    pub struct OnceLock<T> {
        inner: spin::once::Once<T>,
    }

    impl<T> OnceLock<T> {
        /// A cell with no value yet.
        pub const fn new() -> Self {
            Self {
                inner: spin::once::Once::new(),
            }
        }

        /// The value, if initialized.
        pub fn get(&self) -> Option<&T> {
            self.inner.get()
        }

        /// The value, initializing it with `f` on the first call.
        pub fn get_or_init<F: FnOnce() -> T>(&self, f: F) -> &T {
            self.inner.call_once(f)
        }
    }

    impl<T: Default> Default for OnceLock<T> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T: core::fmt::Debug> core::fmt::Debug for OnceLock<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_struct("OnceLock")
                .field("value", &self.get())
                .finish()
        }
    }

    /// [`std::sync::Mutex`]'s shape over `spin::mutex::Mutex`: a lock an
    /// `Arc` can share across threads, `Sync` for `T: Send` through the
    /// spin lock's own atomics. `lock` keeps the original's `Result`, so a
    /// poison-aware call site (`if let Ok(g) = m.lock()`) is written once;
    /// the `Err` is a [`PoisonError`] that is never produced.
    pub struct Mutex<T: ?Sized> {
        inner: spin::mutex::Mutex<T>,
    }

    impl<T> Mutex<T> {
        /// A lock holding `value`.
        pub const fn new(value: T) -> Self {
            Self {
                inner: spin::mutex::Mutex::new(value),
            }
        }

        /// The value, consuming the lock.
        pub fn into_inner(self) -> T {
            self.inner.into_inner()
        }
    }

    impl<T: ?Sized> Mutex<T> {
        /// The lock's guard, which dereferences to the value.
        ///
        /// The `Err` arm exists for the poison-aware call sites; a spin lock
        /// cannot be poisoned, so it is never produced.
        pub fn lock(&self) -> Result<MutexGuard<'_, T>, PoisonError> {
            Ok(self.inner.lock())
        }
    }

    /// `std::sync::PoisonError`'s shape: the `Err` of [`Mutex::lock`], never
    /// produced (kept as a distinct, inhabited type so the call sites' `Err`
    /// arms stay refutable rather than dead).
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct PoisonError;

    impl<T: Default> Default for Mutex<T> {
        fn default() -> Self {
            Self::new(T::default())
        }
    }

    impl<T: ?Sized + core::fmt::Debug> core::fmt::Debug for Mutex<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_struct("Mutex")
                .field("value", &self.inner.lock())
                .finish()
        }
    }

    /// The guard [`Mutex::lock`] returns.
    pub type MutexGuard<'a, T> = spin::mutex::MutexGuard<'a, T>;

    /// The stand-in for a `thread_local!` `Cell<T>` in a build without threads:
    /// the one thread there is shares one cell, with the same `get`/`set`/
    /// `replace` and a `with` that hands out `&self`. One type per primitive,
    /// so that `new` is `const` and a `static` can hold one.
    macro_rules! local_cell {
        ($name:ident, $t:ty, $atomic:ty) => {
            /// A shared cell holding a primitive.
            pub struct $name($atomic);

            impl $name {
                /// A cell holding `value`.
                pub const fn new(value: $t) -> Self {
                    Self(<$atomic>::new(value))
                }

                /// The value.
                pub fn get(&self) -> $t {
                    self.0.load(core::sync::atomic::Ordering::Relaxed)
                }

                /// Sets the value.
                pub fn set(&self, value: $t) {
                    self.0.store(value, core::sync::atomic::Ordering::Relaxed);
                }

                /// Sets the value and returns the old one.
                #[allow(dead_code)]
                pub fn replace(&self, value: $t) -> $t {
                    self.0.swap(value, core::sync::atomic::Ordering::Relaxed)
                }

                /// `thread_local!`'s `with`, for the call sites written against it.
                pub fn with<R>(&self, f: impl FnOnce(&Self) -> R) -> R {
                    f(self)
                }
            }
        };
    }
    local_cell!(LocalBool, bool, core::sync::atomic::AtomicBool);
    local_cell!(LocalU32, u32, core::sync::atomic::AtomicU32);
    local_cell!(LocalU64, u64, core::sync::atomic::AtomicU64);
    local_cell!(LocalUsize, usize, core::sync::atomic::AtomicUsize);
}

pub mod interner;
pub(crate) mod lru_cache;
mod prelude;

// ======== Always-available modules (no_std compatible) ========
pub mod ast;
pub mod config;
pub mod error;
pub mod error_context;
pub mod error_recovery;
pub mod error_utils;
pub mod literal;
pub mod lockfree;
#[cfg(feature = "profiling")]
pub mod profiling;
pub mod reserved;
pub mod rewrite;
pub mod simplification;
pub mod sort;
pub mod theories;
pub mod traits;
pub mod unsat_core;

// ======== std-only modules ========
#[cfg(feature = "std")]
pub mod alloc;
#[cfg(feature = "std")]
pub mod datalog;
#[cfg(feature = "std")]
pub mod diagnostics;
pub mod ematching;
#[cfg(feature = "std")]
pub mod model;
#[cfg(feature = "std")]
pub mod qe;
#[cfg(feature = "std")]
pub mod resource;
pub mod smtlib;
#[cfg(feature = "std")]
pub mod statistics;
pub mod tactic;

// ======== Always-available exports ========
pub use ast::{Term, TermId, TermKind, TermManager};
pub use config::{
    ClauseDeletionStrategy, Config, GeneralParams, PhaseSaving, ResourceLimits, SatParams,
    SimplifyParams,
};
pub use error::{
    EnhancedError, NixieError, Result, extract_context_snippet, find_closest_match,
    levenshtein_distance,
};
pub use error_context::{ErrorContext, ResultExt};
pub use error_recovery::{
    ErrorBatch, ErrorRecovery, RecoveryConfig, RecoveryResult, RecoveryStats, RecoveryStrategy,
};
pub use error_utils::{
    ContextResult, OptionErrorExt, SortErrorExt, arity_mismatch, error_chain, parse_error,
    sort_mismatch, suggest_fixes, type_error, undefined_symbol, validate_arity,
    validate_arity_range, validate_max_arity, validate_min_arity,
};
pub use literal::{Lit, Var};
pub use simplification::{AggressiveSimplifier, SimplificationConfig};
pub use sort::{DataTypeConstructor, Sort, SortId, SortKind};
pub use unsat_core::{UnsatCore, UnsatCoreBuilder, UnsatCoreStrategy};

// Rewrite exports
pub use rewrite::{
    ArithRewriter, ArrayRewriter, BoolRewriter, BottomUpRewriter, BvRewriter, CompositeRewriter,
    IteratingRewriter, Monomial, Polynomial, RewriteConfig, RewriteContext, RewriteResult,
    RewriteStats, RewriteStrategy, Rewriter, StringRewriter,
};

// Trait exports
pub use traits::{
    CachedRewriter as CachedRewriterTrait, ConditionalRewriter, FixpointRewriter, Goal,
    GoalMetadata, IterativeTactic, LazyPropagator, ModelBasedPropagator, OptimizingTheory,
    PropagationPriority, PropagationResult as TraitPropagationResult, Propagator,
    PropagatorManager, PropagatorStatus, QuantifiedTheory, RewriteConfig as TraitRewriteConfig,
    RewriteResult as TraitRewriteResult, RewriteStats as TraitRewriteStats,
    Rewriter as RewriterTrait, SequentialRewriter as SequentialRewriterTrait, Tactic,
    TacticCombinator, TacticConfig, TacticResult, TacticStats, Theory, TheoryCheckResult,
    TheoryConflict, TheoryModel, TheoryPropagationResult, WatchedPropagator,
};

// ======== std-only exports ========
#[cfg(feature = "std")]
pub use diagnostics::{Diagnostic, DiagnosticEmitter, Fix, RelatedDiagnostic, Severity};
#[cfg(feature = "profiling")]
pub use profiling::{
    ProfilingCategory, ProfilingCategorySnapshot, ProfilingSnapshot, ProfilingStats, ScopedTimer,
};
#[cfg(feature = "std")]
pub use resource::{LimitStatus, ResourceManager};
#[cfg(feature = "std")]
pub use statistics::{Statistics, Timer};

// Allocator exports
#[cfg(feature = "std")]
pub use alloc::{
    Arena, ArenaConfig, ArenaError, ArenaHandle, ObjectPool, PoolConfig, PoolGuard, PoolStats,
    Region, RegionAllocator, RegionRef, RegionSlice, SharedObjectPool, SharedPoolGuard,
};

// Model exports
#[cfg(feature = "std")]
pub use model::{
    EvalCache, EvalResult, FuncEntry, FuncInterp, ImplicantConfig, ImplicantExtractor, Model,
    ModelCompletion, ModelCompletionConfig, ModelEvaluator, PrimeImplicant, Value, ValueFactory,
    ValueFactoryConfig,
};

// QE exports
#[cfg(feature = "std")]
pub use qe::{
    MbiConfig, MbiInterpolant, MbiSolver, MbiStats, QeLiteConfig, QeLiteResult, QeLiteSolver,
    QeLiteStats, TermGraph, TermGraphConfig, TermGraphStats, TermNode, TermNodeKind,
};
