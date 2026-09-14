//! Encoding TLA+ kernel terms into Nixie's SMT solver.
//!
//! Milestone 3 of `docs/TLA_FRONTEND_DESIGN.md`. See [`encode`].

#![deny(unsafe_code)]
#![warn(missing_docs)]

pub mod arena;
pub mod bmc;
pub mod encode;
pub mod sorts;
pub mod trace;

pub use arena::{Member, SetCell, Value};
pub use bmc::{Bmc, Outcome, SetupError};
pub use encode::{EncodeError, Encoder, SetEncoding};
pub use sorts::{NoSort, sort_of};
