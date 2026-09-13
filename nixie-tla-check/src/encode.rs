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
use std::collections::{HashMap, HashSet};
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
    /// Names declared `VARIABLE`, whose value differs from step to step.
    state: HashSet<String>,
    /// One SMT variable per (name, step). A constant has a single entry at
    /// step 0, because its value does not change.
    vars: HashMap<(String, u32), TermId>,
    /// The step the term currently being encoded is read at. `'` raises it.
    step: u32,
    max_depth: usize,
    depth: usize,
}

impl Encoder {
    /// An encoder with no free names declared.
    #[must_use]
    pub fn new() -> Self {
        Self {
            sorts: HashMap::new(),
            state: HashSet::new(),
            vars: HashMap::new(),
            step: 0,
            max_depth: DEFAULT_MAX_DEPTH,
            depth: 0,
        }
    }

    /// Declare the sort of a rigid name — a `CONSTANT`, or a parameter.
    ///
    /// Its value is the same in every state, so it encodes to one SMT variable
    /// however many steps are unrolled.
    pub fn declare(&mut self, name: impl Into<String>, sort: SortId) {
        self.sorts.insert(name.into(), sort);
    }

    /// Declare the sort of a `VARIABLE`, whose value differs per step.
    ///
    /// A state variable encodes to a *family* of SMT variables, one per step,
    /// which is what makes an unrolling possible. Getting this distinction
    /// wrong in either direction is a soundness bug, not an inefficiency: a
    /// constant treated as a state variable can change value mid-trace, and a
    /// state variable treated as rigid can never change at all.
    pub fn declare_state(&mut self, name: impl Into<String>, sort: SortId) {
        let name = name.into();
        self.state.insert(name.clone());
        self.sorts.insert(name, sort);
    }

    /// Encode a term as read in state `step`.
    ///
    /// # Errors
    ///
    /// As [`Encoder::encode`].
    pub fn encode_at(&mut self, term: &KeraRef, step: u32, tm: &mut TermManager) -> Result<TermId> {
        self.depth = 0;
        self.step = step;
        let out = self.go(term, tm);
        self.step = 0;
        out
    }

    /// The SMT variable standing for `name` in state `step`, if it is declared.
    #[must_use]
    pub fn var_at(&self, name: &str, step: u32) -> Option<TermId> {
        let key = if self.state.contains(name) { step } else { 0 };
        self.vars.get(&(name.to_string(), key)).copied()
    }

    /// The names declared as state variables.
    pub fn state_names(&self) -> impl Iterator<Item = &str> {
        self.state.iter().map(String::as_str)
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
                // A rigid name is the same variable at every step; only a
                // `VARIABLE` gets one per step.
                let step = if self.state.contains(n.as_str()) {
                    self.step
                } else {
                    0
                };
                let key = (n.0.clone(), step);
                if let Some(t) = self.vars.get(&key) {
                    return Ok(*t);
                }
                let Some(sort) = self.sorts.get(n.as_str()).copied() else {
                    return Err(EncodeError::UnknownSort(n.to_string()));
                };
                let smt_name = if self.state.contains(n.as_str()) {
                    format!("{n}@{step}")
                } else {
                    n.0.clone()
                };
                let t = tm.mk_var(&smt_name, sort);
                self.vars.insert(key, t);
                Ok(t)
            }
            // `x'` is `x` read one step later. Priming distributes over
            // everything in TLA+ — `(x + 1)'` is `x' + 1` — so raising the step
            // for the whole subterm is the definition, not an approximation.
            Kera::Prime(a) => {
                let Some(next) = self.step.checked_add(1) else {
                    return Err(EncodeError::Unsupported(
                        "a term primed past the step limit".into(),
                    ));
                };
                let saved = std::mem::replace(&mut self.step, next);
                let out = self.go(a, tm);
                self.step = saved;
                out
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
