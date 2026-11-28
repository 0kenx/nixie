//! Property-based testing entry point for nixie-core
//!
//! Run with: cargo test -p nixie-core --features property-tests --test integration property_based::

#![cfg(feature = "property-tests")]

mod property_tests;
