//! Property-based testing entry point for nixie-solver
//!
//! `property-tests` is now a default feature (see `Cargo.toml`), so this
//! suite (48 properties across backtracking, conflict analysis, models, and
//! propagation) compiles and runs under plain `cargo test`/`cargo nextest`:
//!
//! ```text
//! cargo nextest run -p nixie-solver --test property_based
//! ```
//!
//! Measured runtime: well under a second of test execution (48 tests,
//! default 256 cases each); the one-time crate compile adds well under the
//! 120s budget considered for gating this suite behind an opt-in feature.
//! The `#![cfg(feature = "property-tests")]` gate is kept (rather than
//! removed outright) so the suite can still be explicitly disabled with
//! `--no-default-features --features std` for a faster iterative build.
#![cfg(feature = "property-tests")]

mod property_tests;
