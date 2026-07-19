//! Entry point for the `sweep-solver` minor-item triage sweep.
//!
//! Audit finding: `tests/mbqi_tests/integration_tests.rs` existed on disk
//! but was never referenced by any `mod` declaration -- `tests/mbqi_tests.rs`
//! (the sibling entry point Cargo actually discovers) only pulls in
//! `conflict_priority_tests`, `coverage_tests`, and `heuristics_tests`. The
//! whole file was therefore dead code: `cargo test`/`cargo nextest run`
//! never compiled or ran a single one of its assertions.
//!
//! This file wires it in without touching `tests/mbqi_tests.rs` (outside
//! this sweep's file ownership), using the same `#[path = ...]` pattern that
//! file already uses for its own submodules.
#[path = "mbqi_tests/integration_tests.rs"]
mod mbqi_integration_tests;
