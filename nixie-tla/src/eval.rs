//! Evaluating a ground kernel term to a [`Value`].
//!
//! # What this is for
//!
//! It is the semantic half of validation. Structural checks — SANY parity,
//! level parity, lowering coverage — cannot tell a correct lowering from a
//! well-formed wrong one. Evaluating a lowered term and comparing the answer
//! against TLC's can.
//!
//! # What it evaluates
//!
//! Ground, finite terms: no free variables, no `'`, and every set it has to
//! enumerate must be finite and small. Anything else returns an error naming
//! the reason rather than a value — an evaluator that guesses is worse than no
//! evaluator, because the differential would then be comparing two guesses.
//!
//! `CHOOSE` is deliberately **not** evaluated. TLA+ says only that it picks
//! *some* element satisfying the predicate; which one is unspecified. Any
//! answer here could differ from TLC's without either being wrong, so a
//! differential over `CHOOSE` would produce noise indistinguishable from real
//! failures.
//!
//! # Recursion
//!
//! The walk is recursive with an explicit depth guard, the same shape the
//! parser uses: an evaluator over a set-valued language re-enters its body
//! once per element, and threading that through a manual stack buys nothing
//! over a counter that turns deep input into a diagnostic. Deep input yields
//! [`EvalErrorKind::DepthLimit`], never a crash.

use crate::kera::{ArithOp, CmpOp, FoldOver, Kera, KeraRef, Name, SetOp};
use crate::value::Value;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use thiserror::Error;

/// Default maximum evaluation depth.
pub const DEFAULT_MAX_DEPTH: usize = 256;
/// Default cap on how many elements a single set may hold.
pub const DEFAULT_MAX_SET: usize = 4096;

/// Why a term could not be evaluated.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum EvalErrorKind {
    /// A free name: the term is not ground.
    #[error("`{0}` is free, so the term is not ground")]
    FreeName(String),
    /// A construct this evaluator does not handle.
    #[error("{0} is not evaluated")]
    Unsupported(String),
    /// An operation applied to the wrong kind of value.
    #[error("expected {expected}, got {found}")]
    Type {
        /// What the operation needed.
        expected: String,
        /// What it was given.
        found: String,
    },
    /// A set grew past the configured cap.
    #[error("a set exceeded the limit of {limit} elements")]
    SetTooLarge {
        /// The configured cap.
        limit: usize,
    },
    /// Integer arithmetic that would overflow.
    ///
    /// TLA+ integers are unbounded; wrapping here would be exactly the silent
    /// truncation this codebase has shipped soundness bugs from before.
    #[error("integer overflow in {0}")]
    Overflow(String),
    /// A function or record applied outside its domain.
    #[error("{0} is outside the domain")]
    OutOfDomain(String),
    /// Nesting past the configured depth.
    #[error("evaluation nests deeper than the limit of {limit}")]
    DepthLimit {
        /// The configured limit.
        limit: usize,
    },
}

/// Result alias for evaluation.
pub type Result<T> = core::result::Result<T, EvalErrorKind>;

/// Evaluates ground kernel terms.
pub struct Evaluator {
    max_depth: usize,
    max_set: usize,
    depth: usize,
    /// The values the state variables take *after* the step, for `'`.
    ///
    /// `None` for an ordinary evaluation, which is what keeps a ground
    /// definition that mentions `'` an honest error rather than a value read
    /// out of an empty map: a state predicate has no next state.
    next: Option<HashMap<String, Value>>,
    /// Whether the term being evaluated sits under a `'`.
    primed: bool,
}

impl Default for Evaluator {
    fn default() -> Self {
        Self::new()
    }
}

impl Evaluator {
    /// An evaluator with the default limits.
    #[must_use]
    pub fn new() -> Self {
        Self {
            max_depth: DEFAULT_MAX_DEPTH,
            max_set: DEFAULT_MAX_SET,
            depth: 0,
            next: None,
            primed: false,
        }
    }

    /// Override the maximum set size.
    #[must_use]
    pub fn with_max_set(mut self, n: usize) -> Self {
        self.max_set = n;
        self
    }

    /// Evaluate a ground term.
    ///
    /// # Errors
    ///
    /// Returns the reason the term could not be evaluated. Never guesses.
    pub fn eval(&mut self, term: &KeraRef) -> Result<Value> {
        let mut env: HashMap<String, Value> = HashMap::new();
        self.depth = 0;
        self.next = None;
        self.primed = false;
        self.go(term, &mut env)
    }

    /// Evaluate a **state predicate** with the state variables bound.
    ///
    /// `Init` and an invariant are of this shape. `'` is still refused: there
    /// is no next state to read it from, and answering from the current one
    /// would silently check a different formula.
    ///
    /// # Errors
    ///
    /// Returns the reason the term could not be evaluated. Never guesses.
    pub fn eval_state(&mut self, term: &KeraRef, state: &HashMap<String, Value>) -> Result<Value> {
        let mut env = state.clone();
        self.depth = 0;
        self.next = None;
        self.primed = false;
        self.go(term, &mut env)
    }

    /// Evaluate an **action** between two states.
    ///
    /// `Next` is of this shape. An unprimed name reads `state`, and a name
    /// under a `'` reads `next` — which is what `'` means in TLA+: not a
    /// different variable, but the *same* expression evaluated in the
    /// successor state.
    ///
    /// # Errors
    ///
    /// Returns the reason the term could not be evaluated. Never guesses.
    pub fn eval_action(
        &mut self,
        term: &KeraRef,
        state: &HashMap<String, Value>,
        next: &HashMap<String, Value>,
    ) -> Result<Value> {
        let mut env = state.clone();
        self.depth = 0;
        self.next = Some(next.clone());
        self.primed = false;
        let out = self.go(term, &mut env);
        self.next = None;
        out
    }

    fn go(&mut self, term: &KeraRef, env: &mut HashMap<String, Value>) -> Result<Value> {
        self.depth += 1;
        if self.depth > self.max_depth {
            self.depth -= 1;
            return Err(EvalErrorKind::DepthLimit {
                limit: self.max_depth,
            });
        }
        let out = self.go_inner(term, env);
        self.depth -= 1;
        out
    }

    fn go_inner(&mut self, term: &KeraRef, env: &mut HashMap<String, Value>) -> Result<Value> {
        match term.as_ref() {
            Kera::Bool(b) => Ok(Value::Bool(*b)),
            Kera::Str(s) => Ok(Value::Str(s.clone())),
            Kera::Int(d) => d
                .parse::<i128>()
                .map(Value::Int)
                .map_err(|_| EvalErrorKind::Overflow(format!("the literal {d}"))),
            // Under a `'`, a *state variable* takes its successor value. The
            // successor map is consulted first and the ordinary environment
            // second, which is the only order that can be right: a state
            // variable is in both, and reading `env` first would hand back the
            // value before the step.
            //
            // A binder's variable is not in the successor map, so it falls
            // through — and cannot collide with a state variable's name
            // either, because lowering renames every binder uniquely. A
            // `CONSTANT` falls through for the same reason and is unchanged by
            // the step, which is what a constant is.
            Kera::Var(n) => {
                if self.primed
                    && let Some(next) = self.next.as_ref()
                    && let Some(v) = next.get(n.as_str())
                {
                    return Ok(v.clone());
                }
                env.get(n.as_str())
                    .cloned()
                    .ok_or_else(|| EvalErrorKind::FreeName(n.to_string()))
            }
            Kera::Prime(a) => {
                if self.next.is_none() {
                    return Err(EvalErrorKind::Unsupported(
                        "`'` outside an action (there is no next state to read)".into(),
                    ));
                }
                // TLA+ has no `x''`: priming is not an operator that composes,
                // it selects the successor state, and there is only one.
                if self.primed {
                    return Err(EvalErrorKind::Unsupported(
                        "`''` (TLA+ has no double prime)".into(),
                    ));
                }
                self.primed = true;
                let out = self.go(a, env);
                self.primed = false;
                out
            }
            Kera::Opaque(n, args) => {
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.go(a, env)?);
                }
                standard_operator(n.as_str(), &vals)
            }
            Kera::Choose { .. } | Kera::ChooseUnbounded { .. } => Err(EvalErrorKind::Unsupported(
                "`CHOOSE` (TLA+ leaves which element it picks unspecified)".into(),
            )),

            Kera::Not(a) => Ok(Value::Bool(!self.boolean(a, env)?)),
            Kera::And(xs) => {
                for x in xs {
                    if !self.boolean(x, env)? {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            Kera::Or(xs) => {
                for x in xs {
                    if self.boolean(x, env)? {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(false))
            }
            Kera::Ite(c, t, e) => {
                if self.boolean(c, env)? {
                    self.go(t, env)
                } else {
                    self.go(e, env)
                }
            }

            Kera::Eq(a, b) => Ok(Value::Bool(self.go(a, env)? == self.go(b, env)?)),
            // `x \in Nat` is decidable even though `Nat` is not a value this
            // evaluator can build. The standard infinite sets have no finite
            // extension, so they are answered by the *kind* of the value
            // rather than by membership in a set — which is the only thing
            // they are ever used for in a state predicate, and the whole
            // reason a specification may say `x \in Nat` at all.
            //
            // They stay unavailable everywhere else: `Nat` as a value, or as
            // the range of a quantifier, is still refused rather than
            // approximated by some finite prefix.
            Kera::In(a, b) if standard_infinite_set(b).is_some() => {
                let x = self.go(a, env)?;
                let Some(which) = standard_infinite_set(b) else {
                    return Err(EvalErrorKind::Unsupported("a standard set".into()));
                };
                Ok(Value::Bool(match (which, &x) {
                    ("Nat", Value::Int(i)) => *i >= 0,
                    ("Int", Value::Int(_)) => true,
                    // TLA+'s `Real` contains every integer. A genuine real is
                    // not a value this evaluator has, so the answer is exact
                    // for everything it can be asked about.
                    ("Real", Value::Int(_)) => true,
                    ("STRING", Value::Str(_)) => true,
                    _ => false,
                }))
            }
            Kera::In(a, b) => {
                let x = self.go(a, env)?;
                let s = self.set_of(b, env)?;
                Ok(Value::Bool(s.contains(&x)))
            }

            Kera::Forall { var, set, body } => {
                for v in self.set_of(set, env)? {
                    if !self.with_bound(var, v, env, |e, en| e.boolean(body, en))? {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            Kera::Exists { var, set, body } => {
                for v in self.set_of(set, env)? {
                    if self.with_bound(var, v, env, |e, en| e.boolean(body, en))? {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(false))
            }

            Kera::SetEnum(xs) => {
                let mut out = BTreeSet::new();
                for x in xs {
                    out.insert(self.go(x, env)?);
                    self.check_set(&out)?;
                }
                Ok(Value::Set(out))
            }
            Kera::Filter { var, set, pred } => {
                let mut out = BTreeSet::new();
                for v in self.set_of(set, env)? {
                    if self.with_bound(var, v.clone(), env, |e, en| e.boolean(pred, en))? {
                        out.insert(v);
                    }
                }
                Ok(Value::Set(out))
            }
            Kera::Map { var, set, expr } => {
                let mut out = BTreeSet::new();
                for v in self.set_of(set, env)? {
                    let mapped = self.with_bound(var, v, env, |e, en| e.go(expr, en))?;
                    out.insert(mapped);
                    self.check_set(&out)?;
                }
                Ok(Value::Set(out))
            }
            // A fold, the one standard operator that takes an operator.
            //
            // TLA+ leaves the *order* of a fold over a set unspecified, so the
            // result is only well defined when the operator is associative and
            // commutative. Apalache does not check that and neither does this;
            // what this does guarantee is that the order is **deterministic**,
            // because `Value` is ordered and the members come out of a
            // `BTreeSet`. An evaluator whose answer depended on hash order
            // would be useless as a differential oracle against TLC.
            Kera::Fold {
                over,
                acc,
                elem,
                base,
                collection,
                body,
            } => {
                let items: Vec<Value> = match over {
                    FoldOver::Set => self.set_of(collection, env)?.into_iter().collect(),
                    FoldOver::SeqLeft => match self.go(collection, env)? {
                        Value::Tuple(items) => items,
                        other => {
                            return Err(EvalErrorKind::Type {
                                expected: "a sequence".into(),
                                found: other.kind().into(),
                            });
                        }
                    },
                };
                let mut a = self.go(base, env)?;
                for item in items {
                    a = self.with_bound(acc, a, env, |e, en| {
                        e.with_bound(elem, item, en, |e2, en2| e2.go(body, en2))
                    })?;
                }
                Ok(a)
            }
            Kera::SetBin(op, a, b) => {
                let x = self.set_of(a, env)?;
                let y = self.set_of(b, env)?;
                let out: BTreeSet<Value> = match op {
                    SetOp::Union => x.union(&y).cloned().collect(),
                    SetOp::Intersect => x.intersection(&y).cloned().collect(),
                    SetOp::Difference => x.difference(&y).cloned().collect(),
                };
                self.check_set(&out)?;
                Ok(Value::Set(out))
            }
            Kera::Powerset(a) => {
                let base: Vec<Value> = self.set_of(a, env)?.into_iter().collect();
                if base.len() > 16 {
                    return Err(EvalErrorKind::SetTooLarge {
                        limit: self.max_set,
                    });
                }
                let mut out = BTreeSet::new();
                for mask in 0u32..(1u32 << base.len()) {
                    let subset: BTreeSet<Value> = base
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, v)| v.clone())
                        .collect();
                    out.insert(Value::Set(subset));
                }
                Ok(Value::Set(out))
            }
            Kera::BigUnion(a) => {
                let outer = self.set_of(a, env)?;
                let mut out = BTreeSet::new();
                for s in outer {
                    let Value::Set(inner) = s else {
                        return Err(EvalErrorKind::Type {
                            expected: "a set of sets".into(),
                            found: s.kind().into(),
                        });
                    };
                    out.extend(inner);
                    self.check_set(&out)?;
                }
                Ok(Value::Set(out))
            }
            Kera::Range(a, b) => {
                let lo = self.integer(a, env)?;
                let hi = self.integer(b, env)?;
                if hi < lo {
                    return Ok(Value::Set(BTreeSet::new()));
                }
                let n = hi
                    .checked_sub(lo)
                    .ok_or_else(|| EvalErrorKind::Overflow("a range".into()))?;
                if n >= self.max_set as i128 {
                    return Err(EvalErrorKind::SetTooLarge {
                        limit: self.max_set,
                    });
                }
                Ok(Value::Set((lo..=hi).map(Value::Int).collect()))
            }
            Kera::Times(parts) => {
                let sets: Vec<Vec<Value>> = parts
                    .iter()
                    .map(|p| self.set_of(p, env).map(|s| s.into_iter().collect()))
                    .collect::<Result<_>>()?;
                let mut acc: Vec<Vec<Value>> = vec![Vec::new()];
                for s in &sets {
                    let mut next = Vec::new();
                    for prefix in &acc {
                        for v in s {
                            let mut p = prefix.clone();
                            p.push(v.clone());
                            next.push(p);
                        }
                    }
                    if next.len() > self.max_set {
                        return Err(EvalErrorKind::SetTooLarge {
                            limit: self.max_set,
                        });
                    }
                    acc = next;
                }
                Ok(Value::Set(acc.into_iter().map(Value::Tuple).collect()))
            }

            Kera::Tuple(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.go(x, env)?);
                }
                Ok(Value::Tuple(out))
            }
            Kera::Record(fs) => {
                let mut out = BTreeMap::new();
                for (k, v) in fs {
                    out.insert(k.clone(), self.go(v, env)?);
                }
                Ok(Value::Record(out))
            }
            Kera::RecordSet(fs) => {
                let mut acc: Vec<BTreeMap<String, Value>> = vec![BTreeMap::new()];
                for (k, v) in fs {
                    let choices = self.set_of(v, env)?;
                    let mut next = Vec::new();
                    for prefix in &acc {
                        for c in &choices {
                            let mut p = prefix.clone();
                            p.insert(k.clone(), c.clone());
                            next.push(p);
                        }
                    }
                    if next.len() > self.max_set {
                        return Err(EvalErrorKind::SetTooLarge {
                            limit: self.max_set,
                        });
                    }
                    acc = next;
                }
                Ok(Value::Set(acc.into_iter().map(Value::Record).collect()))
            }

            Kera::FunDef { var, set, body } => {
                let mut out = BTreeMap::new();
                for v in self.set_of(set, env)? {
                    let r = self.with_bound(var, v.clone(), env, |e, en| e.go(body, en))?;
                    out.insert(v, r);
                    if out.len() > self.max_set {
                        return Err(EvalErrorKind::SetTooLarge {
                            limit: self.max_set,
                        });
                    }
                }
                Ok(Value::fun(out))
            }
            Kera::FunApp(f, a) => {
                let func = self.go(f, env)?;
                let arg = self.go(a, env)?;
                apply(&func, &arg)
            }
            Kera::Domain(f) => match self.go(f, env)? {
                Value::Fun(m) => Ok(Value::Set(m.into_keys().collect())),
                Value::Tuple(xs) => {
                    Ok(Value::Set((1..=xs.len() as i128).map(Value::Int).collect()))
                }
                Value::Record(fs) => Ok(Value::Set(fs.into_keys().map(Value::Str).collect())),
                other => Err(EvalErrorKind::Type {
                    expected: "a function".into(),
                    found: other.kind().into(),
                }),
            },
            Kera::Except { fun, index, value } => {
                let base = self.go(fun, env)?;
                let at = self.go(index, env)?;
                let to = self.go(value, env)?;
                update(base, at, to)
            }
            Kera::FunSet { set, cod } => {
                let dom: Vec<Value> = self.set_of(set, env)?.into_iter().collect();
                let range: Vec<Value> = self.set_of(cod, env)?.into_iter().collect();
                let total = range.len().checked_pow(dom.len() as u32);
                if total.is_none_or(|t| t > self.max_set) {
                    return Err(EvalErrorKind::SetTooLarge {
                        limit: self.max_set,
                    });
                }
                let mut acc: Vec<BTreeMap<Value, Value>> = vec![BTreeMap::new()];
                for d in &dom {
                    let mut next = Vec::new();
                    for prefix in &acc {
                        for r in &range {
                            let mut p = prefix.clone();
                            p.insert(d.clone(), r.clone());
                            next.push(p);
                        }
                    }
                    acc = next;
                }
                Ok(Value::Set(acc.into_iter().map(Value::Fun).collect()))
            }

            Kera::Neg(a) => {
                Ok(Value::Int(self.integer(a, env)?.checked_neg().ok_or_else(
                    || EvalErrorKind::Overflow("negation".into()),
                )?))
            }
            Kera::Arith(op, a, b) => {
                let x = self.integer(a, env)?;
                let y = self.integer(b, env)?;
                arith(*op, x, y)
            }
            Kera::Cmp(op, a, b) => {
                let x = self.integer(a, env)?;
                let y = self.integer(b, env)?;
                Ok(Value::Bool(match op {
                    CmpOp::Lt => x < y,
                    CmpOp::Le => x <= y,
                    CmpOp::Gt => x > y,
                    CmpOp::Ge => x >= y,
                }))
            }
        }
    }

    fn with_bound<T>(
        &mut self,
        var: &Name,
        v: Value,
        env: &mut HashMap<String, Value>,
        f: impl FnOnce(&mut Self, &mut HashMap<String, Value>) -> Result<T>,
    ) -> Result<T> {
        // Lowering renames every binder to a unique name, so a binding can
        // never shadow one that is still live; restoring the previous value is
        // belt and braces.
        let prev = env.insert(var.0.clone(), v);
        let out = f(self, env);
        match prev {
            Some(p) => env.insert(var.0.clone(), p),
            None => env.remove(var.as_str()),
        };
        out
    }

    fn boolean(&mut self, t: &KeraRef, env: &mut HashMap<String, Value>) -> Result<bool> {
        match self.go(t, env)? {
            Value::Bool(b) => Ok(b),
            other => Err(EvalErrorKind::Type {
                expected: "a boolean".into(),
                found: other.kind().into(),
            }),
        }
    }

    fn integer(&mut self, t: &KeraRef, env: &mut HashMap<String, Value>) -> Result<i128> {
        match self.go(t, env)? {
            Value::Int(i) => Ok(i),
            other => Err(EvalErrorKind::Type {
                expected: "an integer".into(),
                found: other.kind().into(),
            }),
        }
    }

    fn set_of(&mut self, t: &KeraRef, env: &mut HashMap<String, Value>) -> Result<BTreeSet<Value>> {
        match self.go(t, env)? {
            Value::Set(s) => Ok(s),
            other => Err(EvalErrorKind::Type {
                expected: "a set".into(),
                found: other.kind().into(),
            }),
        }
    }

    fn check_set(&self, s: &BTreeSet<Value>) -> Result<()> {
        if s.len() > self.max_set {
            return Err(EvalErrorKind::SetTooLarge {
                limit: self.max_set,
            });
        }
        Ok(())
    }
}

/// Operators the standard modules define, which lowering carries through by
/// name because the kernel has no node for them.
///
/// Implementing them here is what lets the TLC differential cover sequence and
/// finite-set code rather than declining it. Anything not listed still returns
/// an error naming the operator: an evaluator that guesses would make the
/// differential compare two guesses.
fn standard_operator(name: &str, args: &[Value]) -> Result<Value> {
    let arg = |i: usize| -> Result<&Value> {
        args.get(i).ok_or_else(|| EvalErrorKind::Type {
            expected: format!("{} argument(s) to `{name}`", i + 1),
            found: format!("{}", args.len()),
        })
    };
    /// A sequence is a function on `1..n`; TLC prints one as a tuple, and both
    /// spellings reach here.
    fn as_seq(v: &Value) -> Result<Vec<Value>> {
        match v {
            Value::Tuple(xs) => Ok(xs.clone()),
            Value::Fun(m) => {
                let mut out = Vec::with_capacity(m.len());
                for i in 1..=m.len() {
                    let k = Value::Int(i as i128);
                    match m.get(&k) {
                        Some(v) => out.push(v.clone()),
                        None => {
                            return Err(EvalErrorKind::Type {
                                expected: "a sequence (a function on 1..n)".into(),
                                found: "a function with a gap in its domain".into(),
                            });
                        }
                    }
                }
                Ok(out)
            }
            other => Err(EvalErrorKind::Type {
                expected: "a sequence".into(),
                found: other.kind().into(),
            }),
        }
    }

    match (name, args.len()) {
        // ---- Sequences ----
        ("Len", 1) => Ok(Value::Int(as_seq(arg(0)?)?.len() as i128)),
        ("Head", 1) => as_seq(arg(0)?)?
            .first()
            .cloned()
            .ok_or_else(|| EvalErrorKind::OutOfDomain("`Head` of the empty sequence".into())),
        ("Tail", 1) => {
            let s = as_seq(arg(0)?)?;
            if s.is_empty() {
                return Err(EvalErrorKind::OutOfDomain(
                    "`Tail` of the empty sequence".into(),
                ));
            }
            Ok(Value::Tuple(s[1..].to_vec()))
        }
        ("Append", 2) => {
            let mut s = as_seq(arg(0)?)?;
            s.push(arg(1)?.clone());
            Ok(Value::Tuple(s))
        }
        ("\\o", 2) => {
            let mut s = as_seq(arg(0)?)?;
            s.extend(as_seq(arg(1)?)?);
            Ok(Value::Tuple(s))
        }
        ("SubSeq", 3) => {
            let s = as_seq(arg(0)?)?;
            let (Value::Int(m), Value::Int(n)) = (arg(1)?, arg(2)?) else {
                return Err(EvalErrorKind::Type {
                    expected: "integer bounds".into(),
                    found: "something else".into(),
                });
            };
            if *n < *m {
                return Ok(Value::Tuple(Vec::new()));
            }
            let lo = usize::try_from(*m).ok().filter(|i| *i >= 1);
            let hi = usize::try_from(*n).ok();
            match (lo, hi) {
                (Some(lo), Some(hi)) if hi <= s.len() => Ok(Value::Tuple(s[lo - 1..hi].to_vec())),
                _ => Err(EvalErrorKind::OutOfDomain(format!("SubSeq {m}..{n}"))),
            }
        }

        // ---- FiniteSets ----
        ("Cardinality", 1) => match arg(0)? {
            Value::Set(s) => Ok(Value::Int(s.len() as i128)),
            other => Err(EvalErrorKind::Type {
                expected: "a set".into(),
                found: other.kind().into(),
            }),
        },
        ("IsFiniteSet", 1) => Ok(Value::Bool(matches!(arg(0)?, Value::Set(_)))),

        // ---- TLC ----
        // `d :> e` is the one-element function, `f @@ g` merges two with the
        // left winning on a shared key.
        (":>", 2) => {
            let mut m = BTreeMap::new();
            m.insert(arg(0)?.clone(), arg(1)?.clone());
            Ok(Value::fun(m))
        }
        ("@@", 2) => {
            let as_fun = |v: &Value| -> Result<BTreeMap<Value, Value>> {
                match v {
                    Value::Fun(m) => Ok(m.clone()),
                    Value::Tuple(xs) => Ok(xs
                        .iter()
                        .enumerate()
                        .map(|(i, x)| (Value::Int(i as i128 + 1), x.clone()))
                        .collect()),
                    Value::Record(fs) => Ok(fs
                        .iter()
                        .map(|(k, v)| (Value::Str(k.clone()), v.clone()))
                        .collect()),
                    other => Err(EvalErrorKind::Type {
                        expected: "a function".into(),
                        found: other.kind().into(),
                    }),
                }
            };
            let left = as_fun(arg(0)?)?;
            let mut out = as_fun(arg(1)?)?;
            // `@@` keeps the left operand's value on a shared key.
            for (k, v) in left {
                out.insert(k, v);
            }
            Ok(Value::fun(out))
        }

        // `Print` and `PrintT` are TLC's tracing operators: they return their
        // value (respectively `TRUE`) and exist for their side effect, which
        // this evaluator has no business reproducing.
        ("Print", 2) => Ok(arg(1)?.clone()),
        ("PrintT", 1) => Ok(Value::Bool(true)),
        // `Assert(cond, out)` is `TRUE` when `cond` holds and an error
        // otherwise -- the error is the point of it.
        ("Assert", 2) => match arg(0)? {
            Value::Bool(true) => Ok(Value::Bool(true)),
            Value::Bool(false) => Err(EvalErrorKind::Unsupported(format!(
                "a failing `Assert`: {}",
                arg(1)?
            ))),
            other => Err(EvalErrorKind::Type {
                expected: "a boolean condition".into(),
                found: other.kind().into(),
            }),
        },

        _ => Err(EvalErrorKind::Unsupported(format!("`{name}`"))),
    }
}

fn arith(op: ArithOp, x: i128, y: i128) -> Result<Value> {
    let v = match op {
        ArithOp::Add => x.checked_add(y),
        ArithOp::Sub => x.checked_sub(y),
        ArithOp::Mul => x.checked_mul(y),
        // TLA+ defines `\div` and `%` only for a *positive* divisor: `a % b`
        // is required to lie in `0 .. b-1`, which says nothing when `b < 0`.
        // Rust's `/` and `%` truncate towards zero, which is not the TLA+
        // answer even when `b > 0`, so `div_euclid` / `rem_euclid` are used —
        // and a non-positive divisor is declined rather than guessed at.
        ArithOp::Div => {
            if y <= 0 {
                return Err(EvalErrorKind::Unsupported(
                    "`\\div` by a non-positive divisor (TLA+ leaves it undefined)".into(),
                ));
            }
            Some(x.div_euclid(y))
        }
        ArithOp::Mod => {
            if y <= 0 {
                return Err(EvalErrorKind::Unsupported(
                    "`%` by a non-positive divisor (TLA+ leaves it undefined)".into(),
                ));
            }
            Some(x.rem_euclid(y))
        }
        ArithOp::Exp => {
            if y < 0 {
                return Err(EvalErrorKind::Unsupported("a negative exponent".into()));
            }
            u32::try_from(y).ok().and_then(|e| x.checked_pow(e))
        }
    };
    v.map(Value::Int)
        .ok_or_else(|| EvalErrorKind::Overflow(format!("`{}`", op.as_str())))
}

fn apply(func: &Value, arg: &Value) -> Result<Value> {
    match func {
        Value::Fun(m) => m
            .get(arg)
            .cloned()
            .ok_or_else(|| EvalErrorKind::OutOfDomain(format!("{arg}"))),
        Value::Tuple(xs) => {
            let Value::Int(i) = arg else {
                return Err(EvalErrorKind::Type {
                    expected: "an integer index".into(),
                    found: arg.kind().into(),
                });
            };
            usize::try_from(*i)
                .ok()
                .filter(|i| *i >= 1)
                .and_then(|i| xs.get(i - 1))
                .cloned()
                .ok_or_else(|| EvalErrorKind::OutOfDomain(format!("{arg}")))
        }
        Value::Record(fs) => {
            let Value::Str(k) = arg else {
                return Err(EvalErrorKind::Type {
                    expected: "a field name".into(),
                    found: arg.kind().into(),
                });
            };
            fs.get(k)
                .cloned()
                .ok_or_else(|| EvalErrorKind::OutOfDomain(format!("{arg}")))
        }
        other => Err(EvalErrorKind::Type {
            expected: "a function".into(),
            found: other.kind().into(),
        }),
    }
}

fn update(base: Value, at: Value, to: Value) -> Result<Value> {
    match base {
        Value::Fun(mut m) => {
            if !m.contains_key(&at) {
                return Err(EvalErrorKind::OutOfDomain(format!("{at}")));
            }
            m.insert(at, to);
            Ok(Value::fun(m))
        }
        Value::Tuple(mut xs) => {
            let Value::Int(i) = at else {
                return Err(EvalErrorKind::Type {
                    expected: "an integer index".into(),
                    found: at.kind().into(),
                });
            };
            let idx = usize::try_from(i)
                .ok()
                .filter(|i| *i >= 1 && *i <= xs.len())
                .ok_or_else(|| EvalErrorKind::OutOfDomain(format!("{i}")))?;
            xs[idx - 1] = to;
            Ok(Value::Tuple(xs))
        }
        Value::Record(mut fs) => {
            let Value::Str(k) = at else {
                return Err(EvalErrorKind::Type {
                    expected: "a field name".into(),
                    found: at.kind().into(),
                });
            };
            if !fs.contains_key(&k) {
                return Err(EvalErrorKind::OutOfDomain(k));
            }
            fs.insert(k, to);
            Ok(Value::Record(fs))
        }
        other => Err(EvalErrorKind::Type {
            expected: "a function".into(),
            found: other.kind().into(),
        }),
    }
}

/// The standard *infinite* set a term names, if it is one.
///
/// `BOOLEAN` is not here: lowering expands it to `{FALSE, TRUE}`, which is a
/// finite set and needs no special case.
fn standard_infinite_set(term: &KeraRef) -> Option<&'static str> {
    let name = match term.as_ref() {
        Kera::Var(n) => n.as_str(),
        Kera::Opaque(n, args) if args.is_empty() => n.as_str(),
        _ => return None,
    };
    match name {
        "Nat" | "Int" | "Real" | "STRING" => Some(match name {
            "Nat" => "Nat",
            "Int" => "Int",
            "Real" => "Real",
            _ => "STRING",
        }),
        _ => None,
    }
}
