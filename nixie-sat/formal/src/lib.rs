//! Literal representation obligations over the real Nixie SAT crate.
//!
//! Plain release tests exercise concrete boundary inputs. Formal and runtime
//! harnesses require a real oxiformal checkout; use prepare.py to configure it.
//! No upstream proof verdict is a verification result for Nixie.
#![forbid(unsafe_code)]
pub mod harness;
pub mod spec;
