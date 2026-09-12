//! Encoding TLA+ kernel terms into Nixie's SMT solver.
//!
//! Milestone 3 of `docs/TLA_FRONTEND_DESIGN.md`. See [`encode`].

#![deny(unsafe_code)]
#![warn(missing_docs)]

pub mod encode;

pub use encode::{EncodeError, Encoder};
