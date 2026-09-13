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

use crate::arena::{Member, SetCell, Value, cardinality, eq_values, member_of};
use nixie_core::{SortId, TermId, TermManager};
use nixie_tla::kera::{ArithOp, CmpOp, Kera, KeraRef, Name, SetOp};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
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
    /// Two values that had to be compared have different shapes.
    ///
    /// A type error the inferencer should have caught. Reported rather than
    /// answered `FALSE`, which would make a genuine equality unsatisfiable and
    /// could hide a counterexample.
    #[error("a set and a non-set were compared")]
    ShapeClash,
    /// A set whose candidate members cannot be enumerated.
    #[error("{0} has no enumerable members")]
    NotEnumerable(String),
    /// A set expression produced more candidates than the budget allows.
    #[error("a set expression exceeded the candidate budget of {limit}")]
    TooManyCandidates {
        /// The configured budget.
        limit: usize,
    },
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

/// Default ceiling on the candidate members of a single set.
///
/// The encoding's size is driven by candidate counts, and they multiply:
/// `A \X B` is `|A| * |B|`, `SUBSET A` is `2^|A|`. A ceiling turns a blow-up
/// into a reported refusal rather than an out-of-memory kill.
pub const DEFAULT_MAX_CANDIDATES: usize = 4_096;

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
    /// Whether any encoded term relied on a function's domain not being
    /// modelled. See [`Encoder::domain_unmodelled`].
    domain_unmodelled: bool,
    /// Bound variables in scope, mapped to the value they stand for.
    ///
    /// A binder over a set is encoded once per candidate member, with the
    /// variable bound to that member — so the body is *instantiated*, not
    /// quantified. Lowering renames every binder uniquely, so a flat map
    /// needs no scope stack; what it does need is to be popped, because the
    /// same binder is entered once per member.
    bound: HashMap<Name, Rc<Value>>,
    /// Ceiling on candidates in any one set.
    max_candidates: usize,
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
            domain_unmodelled: false,
            bound: HashMap::new(),
            max_candidates: DEFAULT_MAX_CANDIDATES,
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

    /// Whether anything encoded so far depended on a function domain that the
    /// array encoding does not carry.
    ///
    /// A TLA+ function has a domain and `f[x]` outside it is *undefined*; an
    /// SMT array is total and returns some value. The encoding therefore
    /// admits behaviours the specification does not have, which can produce a
    /// spurious counterexample but can never hide a real one. Surfaced rather
    /// than logged, for the same reason `Bmc::dropped_assumptions` is: a
    /// caller deciding whether to trust a trace needs to know.
    #[must_use]
    pub fn domain_unmodelled(&self) -> bool {
        self.domain_unmodelled
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

    /// Encode a kernel term to its full representation.
    ///
    /// Unlike [`Encoder::encode`] this accepts a set-valued term and hands
    /// back the candidate list, which is what a caller needs to compare two
    /// sets or to read one out of a model.
    ///
    /// # Errors
    ///
    /// As [`Encoder::encode`].
    pub fn encode_value(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<Rc<Value>> {
        self.depth = 0;
        self.value(term, tm)
    }

    /// Encode a term as read in state `step`, keeping its full representation.
    ///
    /// # Errors
    ///
    /// As [`Encoder::encode`].
    pub fn encode_value_at(
        &mut self,
        term: &KeraRef,
        step: u32,
        tm: &mut TermManager,
    ) -> Result<Rc<Value>> {
        self.depth = 0;
        self.step = step;
        let out = self.value(term, tm);
        self.step = 0;
        out
    }

    /// Encode a term and require it to have an SMT sort of its own.
    ///
    /// A set has no sort — it is a candidate list — so anything that needs a
    /// `TermId` must go through here and gets a named refusal otherwise.
    fn go(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<TermId> {
        match &*self.value(term, tm)? {
            Value::Scalar(t) => Ok(*t),
            Value::Set(_) => Err(EncodeError::Unsupported(
                "a set where a single value is needed".into(),
            )),
        }
    }

    /// Encode a term and require it to be a set.
    fn set(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<SetCell> {
        match &*self.value(term, tm)? {
            Value::Set(s) => Ok(s.clone()),
            Value::Scalar(_) => Err(EncodeError::NotEnumerable(
                "a value used as a set".to_string(),
            )),
        }
    }

    fn value(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<Rc<Value>> {
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

    /// Build a set, refusing one that outgrew the candidate budget.
    fn mk_set(&self, members: Vec<Member>) -> Result<Rc<Value>> {
        if members.len() > self.max_candidates {
            return Err(EncodeError::TooManyCandidates {
                limit: self.max_candidates,
            });
        }
        Ok(Rc::new(Value::Set(SetCell { members })))
    }

    /// Encode `body` once with `var` bound to `value`.
    ///
    /// This is instantiation, not quantification: the body is encoded afresh
    /// for each candidate member, which is what keeps the result quantifier-free
    /// and lets the propositional structure do the work.
    fn with_bound(
        &mut self,
        var: &Name,
        value: Rc<Value>,
        body: &KeraRef,
        tm: &mut TermManager,
    ) -> Result<Rc<Value>> {
        let saved = self.bound.insert(var.clone(), value);
        let out = self.value(body, tm);
        match saved {
            Some(v) => self.bound.insert(var.clone(), v),
            None => self.bound.remove(var),
        };
        out
    }

    fn shape(&self, r: Option<TermId>) -> Result<TermId> {
        r.ok_or(EncodeError::ShapeClash)
    }

    #[allow(clippy::too_many_lines)]
    fn go_inner(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<Rc<Value>> {
        match term.as_ref() {
            Kera::Bool(b) => scalar(tm.mk_bool(*b)),
            Kera::Int(digits) => {
                // Parsed into a big integer, never through `i64`: a wide
                // literal must survive exactly.
                let value: num_bigint::BigInt = digits
                    .parse()
                    .map_err(|_| EncodeError::Unsupported(format!("the numeral `{digits}`")))?;
                scalar(tm.mk_int(value))
            }
            Kera::Var(n) => {
                // A binder's variable shadows everything: it stands for the
                // candidate member currently being instantiated.
                if let Some(v) = self.bound.get(n) {
                    return Ok(Rc::clone(v));
                }
                // A rigid name is the same variable at every step; only a
                // `VARIABLE` gets one per step.
                let step = if self.state.contains(n.as_str()) {
                    self.step
                } else {
                    0
                };
                let key = (n.0.clone(), step);
                if let Some(t) = self.vars.get(&key) {
                    return scalar(*t);
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
                scalar(t)
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
                let out = self.value(a, tm);
                self.step = saved;
                out
            }
            Kera::Not(a) => {
                let x = self.go(a, tm)?;
                scalar(tm.mk_not(x))
            }
            Kera::And(xs) => {
                let mut args = Vec::with_capacity(xs.len());
                for x in xs {
                    args.push(self.go(x, tm)?);
                }
                scalar(tm.mk_and(args))
            }
            Kera::Or(xs) => {
                let mut args = Vec::with_capacity(xs.len());
                for x in xs {
                    args.push(self.go(x, tm)?);
                }
                scalar(tm.mk_or(args))
            }
            Kera::Ite(c, t, e) => {
                let c = self.go(c, tm)?;
                let t = self.go(t, tm)?;
                let e = self.go(e, tm)?;
                scalar(tm.mk_ite(c, t, e))
            }
            // Equality is structural: extensional for sets, `=` otherwise.
            Kera::Eq(a, b) => {
                let x = self.value(a, tm)?;
                let y = self.value(b, tm)?;
                let t = self.shape(eq_values(&x, &y, tm))?;
                scalar(t)
            }
            Kera::In(a, s) => {
                let v = self.value(a, tm)?;
                let set = self.set(s, tm)?;
                let t = self.shape(member_of(&v, &set, tm))?;
                scalar(t)
            }

            // ---- sets ----
            Kera::SetEnum(xs) => {
                let yes = tm.mk_bool(true);
                let mut members = Vec::with_capacity(xs.len());
                for x in xs {
                    members.push(Member {
                        value: self.value(x, tm)?,
                        present: yes,
                    });
                }
                self.mk_set(members)
            }
            // `a..b` is enumerable only when both ends are literal. A symbolic
            // bound has no finite candidate list, and inventing one would
            // silently check a different specification.
            Kera::Range(a, b) => {
                let lo = literal_int(a).ok_or_else(|| {
                    EncodeError::NotEnumerable("`..` with a non-literal lower bound".into())
                })?;
                let hi = literal_int(b).ok_or_else(|| {
                    EncodeError::NotEnumerable("`..` with a non-literal upper bound".into())
                })?;
                let yes = tm.mk_bool(true);
                let mut members = Vec::new();
                let mut i = lo.clone();
                while i <= hi {
                    if members.len() > self.max_candidates {
                        return Err(EncodeError::TooManyCandidates {
                            limit: self.max_candidates,
                        });
                    }
                    members.push(Member {
                        value: Rc::new(Value::Scalar(tm.mk_int(i.clone()))),
                        present: yes,
                    });
                    i += 1;
                }
                self.mk_set(members)
            }
            Kera::Filter { var, set, pred } => {
                let base = self.set(set, tm)?;
                let mut members = Vec::with_capacity(base.members.len());
                for m in &base.members {
                    let keep = self.with_bound(var, Rc::clone(&m.value), pred, tm)?;
                    let Value::Scalar(keep) = &*keep else {
                        return Err(EncodeError::Unsupported(
                            "a set-valued filter predicate".into(),
                        ));
                    };
                    members.push(Member {
                        value: Rc::clone(&m.value),
                        present: tm.mk_and([m.present, *keep]),
                    });
                }
                self.mk_set(members)
            }
            Kera::Map { var, set, expr } => {
                let base = self.set(set, tm)?;
                let mut members = Vec::with_capacity(base.members.len());
                for m in &base.members {
                    let mapped = self.with_bound(var, Rc::clone(&m.value), expr, tm)?;
                    members.push(Member {
                        value: mapped,
                        present: m.present,
                    });
                }
                self.mk_set(members)
            }
            Kera::SetBin(op, a, b) => {
                let x = self.set(a, tm)?;
                let y = self.set(b, tm)?;
                let mut members = Vec::new();
                match op {
                    // Candidates of both sides, each keeping its own
                    // membership. Duplicates across the two lists are fine:
                    // membership is a disjunction, so counting a value twice
                    // changes nothing. Cardinality de-duplicates separately.
                    SetOp::Union => {
                        members.extend(x.members.iter().cloned());
                        members.extend(y.members.iter().cloned());
                    }
                    SetOp::Intersect => {
                        for m in &x.members {
                            let inside = self.shape(member_of(&m.value, &y, tm))?;
                            members.push(Member {
                                value: Rc::clone(&m.value),
                                present: tm.mk_and([m.present, inside]),
                            });
                        }
                    }
                    SetOp::Difference => {
                        for m in &x.members {
                            let inside = self.shape(member_of(&m.value, &y, tm))?;
                            let outside = tm.mk_not(inside);
                            members.push(Member {
                                value: Rc::clone(&m.value),
                                present: tm.mk_and([m.present, outside]),
                            });
                        }
                    }
                }
                self.mk_set(members)
            }
            // `UNION S` flattens one level: every candidate of every candidate,
            // present when both the inner set and the member are.
            Kera::BigUnion(a) => {
                let outer = self.set(a, tm)?;
                let mut members = Vec::new();
                for m in &outer.members {
                    let Value::Set(inner) = &*m.value else {
                        return Err(EncodeError::NotEnumerable(
                            "`UNION` of something that is not a set of sets".into(),
                        ));
                    };
                    for k in &inner.members {
                        members.push(Member {
                            value: Rc::clone(&k.value),
                            present: tm.mk_and([m.present, k.present]),
                        });
                    }
                }
                self.mk_set(members)
            }

            // ---- binders over a set ----
            // Instantiated, not quantified: one copy of the body per candidate.
            Kera::Forall { var, set, body } => {
                let base = self.set(set, tm)?;
                let mut conj = Vec::with_capacity(base.members.len());
                for m in &base.members {
                    let b = self.with_bound(var, Rc::clone(&m.value), body, tm)?;
                    let Value::Scalar(b) = &*b else {
                        return Err(EncodeError::Unsupported("a set-valued predicate".into()));
                    };
                    let not_present = tm.mk_not(m.present);
                    conj.push(tm.mk_or([not_present, *b]));
                }
                scalar(tm.mk_and(conj))
            }
            Kera::Exists { var, set, body } => {
                let base = self.set(set, tm)?;
                let mut disj = Vec::with_capacity(base.members.len());
                for m in &base.members {
                    let b = self.with_bound(var, Rc::clone(&m.value), body, tm)?;
                    let Value::Scalar(b) = &*b else {
                        return Err(EncodeError::Unsupported("a set-valued predicate".into()));
                    };
                    disj.push(tm.mk_and([m.present, *b]));
                }
                scalar(tm.mk_or(disj))
            }

            Kera::Neg(a) => {
                let x = self.go(a, tm)?;
                let zero = tm.mk_int(0);
                scalar(tm.mk_sub(zero, x))
            }
            Kera::Arith(op, a, b) => {
                let x = self.go(a, tm)?;
                let y = self.go(b, tm)?;
                scalar(match op {
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
            // A TLA+ function application is an array select, and `EXCEPT` is
            // a store. Both are exact *inside* the function's domain. Outside
            // it TLA+ leaves `f[x]` undefined while the array returns some
            // value, which admits behaviours the specification does not have:
            // that can manufacture a counterexample, never hide one.
            Kera::FunApp(f, i) => {
                let arr = self.go(f, tm)?;
                let idx = self.go(i, tm)?;
                self.domain_unmodelled = true;
                scalar(tm.mk_select(arr, idx))
            }
            Kera::Except { fun, index, value } => {
                let arr = self.go(fun, tm)?;
                let idx = self.go(index, tm)?;
                let val = self.go(value, tm)?;
                self.domain_unmodelled = true;
                scalar(tm.mk_store(arr, idx, val))
            }
            Kera::Cmp(op, a, b) => {
                let x = self.go(a, tm)?;
                let y = self.go(b, tm)?;
                scalar(match op {
                    CmpOp::Lt => tm.mk_lt(x, y),
                    CmpOp::Le => tm.mk_le(x, y),
                    CmpOp::Gt => tm.mk_gt(x, y),
                    CmpOp::Ge => tm.mk_ge(x, y),
                })
            }
            // Standard-module operators whose meaning is arena-level.
            Kera::Opaque(name, args) => match (name.as_str(), args.len()) {
                ("Cardinality", 1) => {
                    let s = self.set(&args[0], tm)?;
                    let t = self.shape(cardinality(&s, tm))?;
                    scalar(t)
                }
                // Every set the arena can build is finite by construction.
                ("IsFiniteSet", 1) => {
                    let _ = self.set(&args[0], tm)?;
                    scalar(tm.mk_bool(true))
                }
                _ => Err(EncodeError::Unsupported(describe(term.as_ref()))),
            },
            other => Err(EncodeError::Unsupported(describe(other))),
        }
    }
}

impl Default for Encoder {
    fn default() -> Self {
        Self::new()
    }
}

/// Wrap an SMT term as a value.
fn scalar(t: TermId) -> Result<Rc<Value>> {
    Ok(Rc::new(Value::Scalar(t)))
}

/// The integer a term denotes, if it is a literal (possibly negated).
///
/// Used only where a *candidate list* has to be built, which is the one place
/// a symbolic value cannot be carried: `a..b` needs to know how many elements
/// there are, not merely how to compare them.
fn literal_int(term: &KeraRef) -> Option<num_bigint::BigInt> {
    match term.as_ref() {
        Kera::Int(d) => d.parse().ok(),
        Kera::Neg(a) => literal_int(a).map(|v| -v),
        _ => None,
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
        Kera::FunDef { .. } => "a function constructor `[x \\in S |-> e]`",
        Kera::Domain(_) => "`DOMAIN`",
        Kera::FunSet { .. } => "a function set `[S -> T]`",
        Kera::Tuple(_) => "a tuple",
        Kera::Record(_) | Kera::RecordSet(_) => "a record",
        Kera::Opaque(n, _) => return format!("`{n}`"),
        _ => "this construct",
    };
    s.to_string()
}
