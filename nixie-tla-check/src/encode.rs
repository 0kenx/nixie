//! Encoding KerA into Nixie's term language.
//!
//! Milestone 3 of `docs/TLA_FRONTEND_DESIGN.md`: the naive encoding, the first
//! point where the front end actually reaches the solver.
//!
//! # What is encoded, and what is declined
//!
//! The arithmetic and propositional fragment maps onto SMT integers and
//! booleans directly. Sets, functions, tuples and records do **not**: the
//! design doc's O3 keeps them in the kernel precisely so the encoder can hand
//! them to `nixie-theories`' set theory rather than expanding them into
//! quantifiers, and that theory integration is a later milestone.
//!
//! Until then every unencodable construct is **declined by name**. An encoder
//! that silently approximated would be the worst possible place for it: a
//! wrong answer from a model checker is exactly the catastrophe `AGENTS.md`
//! opens with.
//!
//! # Why the division operators line up
//!
//! TLA+ requires `a % b \in 0..b-1`, so `\div` rounds towards minus infinity.
//! SMT-LIB's `div`/`mod` on `Int` are Euclidean and give the same answers for
//! the positive divisors TLA+ defines. That is a genuine agreement, not an
//! assumption: `nixie-tla`'s evaluator pins the same semantics, and the
//! cross-check in `examples/encodecheck.rs` compares the two on every ground
//! definition of the corpora.

use nixie_core::{SortId, TermId, TermManager};
use nixie_tla::kera::{ArithOp, CmpOp, Kera, KeraRef};
use std::collections::HashMap;
use thiserror::Error;

/// Why a kernel term could not be encoded.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum EncodeError {
    /// A construct with no encoding yet.
    #[error("{0} has no encoding yet")]
    Unsupported(String),
    /// A free name whose sort could not be determined.
    #[error("`{0}` is free and its sort is unknown")]
    UnknownSort(String),
    /// Nesting past the configured limit.
    #[error("the term nests deeper than the limit of {limit}")]
    DepthLimit {
        /// The configured limit.
        limit: usize,
    },
}

/// Result alias for encoding.
pub type Result<T> = core::result::Result<T, EncodeError>;

/// Default maximum encoding depth.
pub const DEFAULT_MAX_DEPTH: usize = 512;

/// Encodes kernel terms into a [`TermManager`].
pub struct Encoder {
    /// Free names given a sort by the caller.
    sorts: HashMap<String, SortId>,
    vars: HashMap<String, TermId>,
    max_depth: usize,
    depth: usize,
}

impl Encoder {
    /// An encoder with no free names declared.
    #[must_use]
    pub fn new() -> Self {
        Self {
            sorts: HashMap::new(),
            vars: HashMap::new(),
            max_depth: DEFAULT_MAX_DEPTH,
            depth: 0,
        }
    }

    /// Declare the sort of a free name, so it can be encoded as a variable.
    pub fn declare(&mut self, name: impl Into<String>, sort: SortId) {
        self.sorts.insert(name.into(), sort);
    }

    /// Encode a kernel term.
    ///
    /// # Errors
    ///
    /// Returns the construct it could not encode, by name. Never approximates.
    pub fn encode(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<TermId> {
        self.depth = 0;
        self.go(term, tm)
    }

    fn go(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<TermId> {
        self.depth += 1;
        if self.depth > self.max_depth {
            self.depth -= 1;
            return Err(EncodeError::DepthLimit {
                limit: self.max_depth,
            });
        }
        let out = self.go_inner(term, tm);
        self.depth -= 1;
        out
    }

    fn go_inner(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<TermId> {
        match term.as_ref() {
            Kera::Bool(b) => Ok(tm.mk_bool(*b)),
            Kera::Int(digits) => {
                // Parsed into a big integer, never through `i64`: a wide
                // literal must survive exactly.
                let value: num_bigint::BigInt = digits
                    .parse()
                    .map_err(|_| EncodeError::Unsupported(format!("the numeral `{digits}`")))?;
                Ok(tm.mk_int(value))
            }
            Kera::Var(n) => {
                if let Some(t) = self.vars.get(n.as_str()) {
                    return Ok(*t);
                }
                let Some(sort) = self.sorts.get(n.as_str()).copied() else {
                    return Err(EncodeError::UnknownSort(n.to_string()));
                };
                let t = tm.mk_var(n.as_str(), sort);
                self.vars.insert(n.0.clone(), t);
                Ok(t)
            }
            Kera::Not(a) => {
                let x = self.go(a, tm)?;
                Ok(tm.mk_not(x))
            }
            Kera::And(xs) => {
                let mut args = Vec::with_capacity(xs.len());
                for x in xs {
                    args.push(self.go(x, tm)?);
                }
                Ok(tm.mk_and(args))
            }
            Kera::Or(xs) => {
                let mut args = Vec::with_capacity(xs.len());
                for x in xs {
                    args.push(self.go(x, tm)?);
                }
                Ok(tm.mk_or(args))
            }
            Kera::Ite(c, t, e) => {
                let c = self.go(c, tm)?;
                let t = self.go(t, tm)?;
                let e = self.go(e, tm)?;
                Ok(tm.mk_ite(c, t, e))
            }
            Kera::Eq(a, b) => {
                let x = self.go(a, tm)?;
                let y = self.go(b, tm)?;
                Ok(tm.mk_eq(x, y))
            }
            Kera::Neg(a) => {
                let x = self.go(a, tm)?;
                let zero = tm.mk_int(0);
                Ok(tm.mk_sub(zero, x))
            }
            Kera::Arith(op, a, b) => {
                let x = self.go(a, tm)?;
                let y = self.go(b, tm)?;
                Ok(match op {
                    ArithOp::Add => tm.mk_add([x, y]),
                    ArithOp::Sub => tm.mk_sub(x, y),
                    ArithOp::Mul => tm.mk_mul([x, y]),
                    // SMT-LIB `div`/`mod` on Int are Euclidean, which is what
                    // TLA+ requires for the positive divisors it defines.
                    ArithOp::Div => tm.mk_div(x, y),
                    ArithOp::Mod => tm.mk_mod(x, y),
                    ArithOp::Exp => {
                        return Err(EncodeError::Unsupported(
                            "`^` (exponentiation is non-linear)".into(),
                        ));
                    }
                })
            }
            Kera::Cmp(op, a, b) => {
                let x = self.go(a, tm)?;
                let y = self.go(b, tm)?;
                Ok(match op {
                    CmpOp::Lt => tm.mk_lt(x, y),
                    CmpOp::Le => tm.mk_le(x, y),
                    CmpOp::Gt => tm.mk_gt(x, y),
                    CmpOp::Ge => tm.mk_ge(x, y),
                })
            }
            other => Err(EncodeError::Unsupported(describe(other))),
        }
    }
}

impl Default for Encoder {
    fn default() -> Self {
        Self::new()
    }
}

/// Name a kernel construct for a diagnostic.
fn describe(k: &Kera) -> String {
    let s = match k {
        Kera::Str(_) => "a string literal",
        Kera::Prime(_) => "`'`",
        Kera::Forall { .. } | Kera::Exists { .. } => "a quantifier",
        Kera::Choose { .. } | Kera::ChooseUnbounded { .. } => "`CHOOSE`",
        Kera::In(_, _) => "`\\in`",
        Kera::SetEnum(_)
        | Kera::Filter { .. }
        | Kera::Map { .. }
        | Kera::SetBin(_, _, _)
        | Kera::Powerset(_)
        | Kera::BigUnion(_)
        | Kera::Range(_, _)
        | Kera::Times(_) => "a set expression (the set theory is not wired up yet)",
        Kera::FunDef { .. }
        | Kera::FunApp(_, _)
        | Kera::Domain(_)
        | Kera::Except { .. }
        | Kera::FunSet { .. } => "a function expression",
        Kera::Tuple(_) => "a tuple",
        Kera::Record(_) | Kera::RecordSet(_) => "a record",
        Kera::Opaque(n, _) => return format!("`{n}`"),
        _ => "this construct",
    };
    s.to_string()
}
