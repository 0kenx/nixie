//! TLA+ intermediate representation.
//!
//! Milestone 2 of `docs/TLA_FRONTEND_DESIGN.md`: the two-level IR. The
//! *surface* tree lives in [`nixie_tla_syntax::ast`] and mirrors what the user
//! wrote; this crate holds the **KerA kernel** ([`kera`]) and the [`lower`]
//! pass that reduces the surface to it.
//!
//! Only the kernel is ever encoded, so everything downstream matches
//! exhaustively on a small closed enum and a new construct breaks compilation
//! rather than slipping through a `_ =>` arm.
//!
//! # Example
//!
//! ```
//! use nixie_tla::Lowerer;
//! use nixie_tla_syntax::parse_file;
//!
//! let src = r"
//! ---- MODULE Counter ----
//! VARIABLE x
//! Limit == 10
//! Next == x < Limit /\ x' = x + 1
//! ====
//! ";
//! let parsed = parse_file(src).expect("parses");
//! let mut low = Lowerer::new();
//! low.add_module(&parsed.module);
//! // `Limit` is inlined, so the kernel term mentions 10 rather than a name.
//! let next = low.lower_named(&parsed.module, "Next").expect("lowers");
//! assert!(format!("{next:?}").contains("10"));
//! ```

#![deny(unsafe_code)]
#![warn(missing_docs)]

pub mod error;
pub mod kera;
pub mod lower;

pub use error::{LowerError, LowerErrorKind};
pub use kera::{Kera, KeraRef, Name};
pub use lower::Lowerer;
