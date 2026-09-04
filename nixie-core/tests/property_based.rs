//! Property-based testing entry point for nixie-core
//!
//! Run with: cargo test --test property_based --features property-tests

#![cfg(feature = "property-tests")]

mod property_tests;
