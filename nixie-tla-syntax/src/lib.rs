//! Pure-Rust TLA+ lexer and parser.
//!
//! This crate is the SANY replacement described in
//! `docs/TLA_FRONTEND_DESIGN.md` §1. Apalache does not parse TLA+ — it shells
//! out to SANY, from the Java `tla2tools` distribution — so a pure-Rust
//! pipeline has to write the one component Apalache never needed. There is no
//! JVM here and no FFI, matching the constraint the solver core already works
//! under.
//!
//! # Shape
//!
//! * [`lexer`] — tokens, retained comments, canonicalised operator spellings.
//! * [`op`] — the operator table: fixity, precedence **ranges**, associativity.
//! * [`parser`] — recursive descent for units, Pratt for expressions, with
//!   junction-list layout decided in the parser rather than the lexer.
//! * [`ast`] — the surface tree, with a span on every node.
//! * [`level`] — TLA+ level checking (constant / state / action / temporal).
//! * [`module`] — following `EXTENDS` to load a spec's transitive imports.
//!
//! # Why not LR(1)
//!
//! Three reasons, in increasing severity: junction lists are layout-sensitive
//! and so not context-free; `[` is overloaded six ways with an arbitrarily
//! distant disambiguating token; and TLA+ precedence is an *interval* per
//! operator, where overlap is a static error that deserves a real diagnostic
//! and `%left`/`%nonassoc` can only express a single level. See
//! [`parser`] and [`op`] for the details, and `docs/TLA_FRONTEND_DESIGN.md`
//! §1.0 for the full argument.
//!
//! # Example
//!
//! ```
//! use nixie_tla_syntax::parse_file;
//!
//! let src = r"
//! ---- MODULE Counter ----
//! EXTENDS Naturals
//! VARIABLE x
//!
//! Init == x = 0
//! Next == /\ x < 10
//!         /\ x' = x + 1
//! Spec == Init /\ [][Next]_x
//! ====
//! ";
//! let parsed = parse_file(src).expect("Counter parses");
//! assert_eq!(parsed.module.name.name, "Counter");
//! assert_eq!(parsed.module.variables().len(), 1);
//! ```
//!
//! # Status
//!
//! Milestone 1 targets the fragment Apalache accepts. Constructs that are real
//! TLA+ but outside that fragment — `RECURSIVE`, structured `<n>` proofs —
//! are **rejected with a named diagnostic**, never silently accepted or
//! given a default. That is the `AGENTS.md` no-silent-fallthrough rule applied
//! to the front end.

#![deny(unsafe_code)]
#![warn(missing_docs)]

pub mod ast;
pub mod error;
pub mod level;
pub mod lexer;
pub mod module;
pub mod op;
pub mod parser;
pub mod span;
pub mod token;

pub use ast::{Expr, ExprKind, Module, Unit, UnitKind};
pub use error::{ErrorKind, SyntaxError};
pub use level::{Imports, Level, LevelError, LevelReport, check_module, check_spec};
pub use lexer::lex;
pub use module::{LoadedSpec, Loader};
pub use parser::{ParsedFile, Parser, parse_expr_str, parse_file};
pub use span::{Pos, Span};
pub use token::{Keyword, NumBase, Token, TokenKind};
