//! Property-based tests for nixie-solver
//!
//! Comprehensive testing of CDCL(T) solver invariants
//!
//! `property-tests` is a default feature (see `Cargo.toml`), so this suite
//! (48 properties across backtracking, conflict analysis, models, and
//! propagation) runs under plain `cargo test`/`cargo nextest run -p
//! nixie-solver`. Disable it explicitly (`--no-default-features --features
//! std`) to skip it, e.g. for a fast iterative build.

#![cfg(feature = "property-tests")]

mod backtrack_properties;
mod conflict_properties;
mod model_properties;
mod propagation_properties;
