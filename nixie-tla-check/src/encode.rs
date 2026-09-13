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

/// How set-valued terms reach the solver.
///
/// The two are kept side by side on purpose. The design doc's O3 is the claim
/// that a lazy theory beats the eager arena; that claim is only checkable if
/// the thing it replaces still exists and still answers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SetEncoding {
    /// Apalache's arena: a statically computed candidate list per set, with a
    /// Boolean per (candidate, set). Exact and quantifier-free, but it needs
    /// the candidates to be knowable *before* the solver runs — so it cannot
    /// represent a set-valued **state variable**, whose members are whatever
    /// the transition relation puts there.
    #[default]
    Arena,
    /// The solver's own finite-set theory (`SortKind::Set`). A set is a value
    /// with a sort, so a state variable can have one, and membership,
    /// `\cup`/`\cap`/`\`, extensional equality and cardinality are decided
    /// by the theory rather than expanded here.
    ///
    /// What it does not have is a comprehension: `{x \in S : P(x)}` and
    /// `{e(x) : x \in S}` have no native form, so they are declined in this
    /// mode rather than silently approximated.
    Native,
}

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
    /// The companion *domain* variable of a function-sorted name.
    ///
    /// A TLA+ function is a domain and a graph, and an SMT array is only the
    /// graph — so a function-typed `VARIABLE` needs two SMT variables, not
    /// one. Keyed exactly like [`Encoder::vars`], so a state variable gets a
    /// domain per step and a `CONSTANT` gets one for the whole unrolling:
    /// a constant function's domain cannot change either.
    var_domains: HashMap<(String, u32), TermId>,
    /// The step the term currently being encoded is read at. `'` raises it.
    step: u32,
    /// Whether any encoded term relied on a function's domain not being
    /// modelled. See [`Encoder::domain_unmodelled`].
    domain_unmodelled: bool,
    /// How set-valued terms are encoded.
    set_encoding: SetEncoding,
    /// Sorts for individual kernel nodes, keyed by pointer identity.
    ///
    /// A few terms do not carry enough information to sort themselves: `{}`
    /// is the whole motivation, since an empty set literal has no element to
    /// take an element sort from. Type inference knows, so the caller can say.
    node_sorts: HashMap<*const Kera, SortId>,
    /// Bound variables in scope, mapped to the value they stand for.
    ///
    /// A binder over a set is encoded once per candidate member, with the
    /// variable bound to that member — so the body is *instantiated*, not
    /// quantified. Lowering renames every binder uniquely, so a flat map
    /// needs no scope stack; what it does need is to be popped, because the
    /// same binder is entered once per member.
    bound: HashMap<Name, Rc<Value>>,
    /// Counter for the synthetic names [`Encoder::membership`] binds.
    fresh: u32,
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
            var_domains: HashMap::new(),
            step: 0,
            domain_unmodelled: false,
            set_encoding: SetEncoding::default(),
            node_sorts: HashMap::new(),
            bound: HashMap::new(),
            fresh: 0,
            max_candidates: DEFAULT_MAX_CANDIDATES,
            max_depth: DEFAULT_MAX_DEPTH,
            depth: 0,
        }
    }

    /// Choose how set-valued terms reach the solver.
    #[must_use]
    pub fn with_set_encoding(mut self, encoding: SetEncoding) -> Self {
        self.set_encoding = encoding;
        self
    }

    /// Tell the encoder the sort of one kernel node.
    ///
    /// Only consulted where a term cannot sort itself; see [`Encoder`]'s
    /// `node_sorts`.
    pub fn declare_node_sort(&mut self, node: &KeraRef, sort: SortId) {
        self.node_sorts.insert(Rc::as_ptr(node), sort);
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
            Value::Tuple(_) => Err(EncodeError::Unsupported(
                "a tuple where a single value is needed".into(),
            )),
            Value::Record(_) => Err(EncodeError::Unsupported(
                "a record where a single value is needed".into(),
            )),
            // A function is a domain *and* a graph; handing back the graph
            // alone would silently drop the domain, which is the half that
            // makes equality right.
            Value::Fun { .. } => Err(EncodeError::Unsupported(
                "a function where a single value is needed".into(),
            )),
        }
    }

    /// Encode a term as an arena candidate list, whatever the current mode.
    ///
    /// A bounded quantifier is the one construct that mixes cleanly: its
    /// *result* is a `Bool`, so the bound set can be enumerated by the arena
    /// while the body goes on using native set terms. Without this, native
    /// mode declines `\E x \in {1, 2, 3} : P` — a perfectly ordinary shape —
    /// purely because the theory has no comprehension.
    fn set_as_arena(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<SetCell> {
        let saved = std::mem::replace(&mut self.set_encoding, SetEncoding::Arena);
        let out = self.set(term, tm);
        self.set_encoding = saved;
        out
    }

    /// Encode a term and require it to be a set.
    fn set(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<SetCell> {
        match &*self.value(term, tm)? {
            Value::Set(s) => Ok(s.clone()),
            // A set-sorted term where a candidate list is wanted. That is not
            // automatically a refusal: a term *this encoder built* is a union
            // of singletons, so its candidates can be read back off it. Only a
            // genuinely opaque one — a set variable — has none.
            Value::Scalar(t) => {
                let t = *t;
                match self.candidates_of(t, 0, tm) {
                    Some(members) => Ok(SetCell { members }),
                    None => Err(EncodeError::NotEnumerable(
                        "a set-valued term with no candidate list to enumerate".to_string(),
                    )),
                }
            }
            Value::Tuple(_) | Value::Record(_) | Value::Fun { .. } => Err(
                EncodeError::NotEnumerable("a value used as a set".to_string()),
            ),
        }
    }

    /// Read an arena candidate list back off a set-sorted term.
    ///
    /// The inverse of [`Encoder::native_set_of`], and the reason the hybrid
    /// works at all: a bounded quantifier is *instantiated* per candidate, so
    /// `\A i \in DOMAIN f : P(i)` needs a candidate list for a domain that
    /// is, by now, a set-sorted term. Every set this encoder builds is a union
    /// of (conditional) singletons — the normal form CVC5 uses for a set
    /// constant — so the list is recoverable exactly.
    ///
    /// `None` for anything else, which is an honest refusal rather than an
    /// approximation: a set *variable* has no candidate list, and inventing
    /// one would check a different specification.
    fn candidates_of(
        &mut self,
        set: TermId,
        depth: usize,
        tm: &mut TermManager,
    ) -> Option<Vec<Member>> {
        use nixie_core::TermKind;
        // The term was built by this encoder, so it is as deep as the
        // specification is; bounded anyway, and a refusal beyond the bound.
        if depth > self.max_depth {
            return None;
        }
        let kind = tm.get(set).map(|t| t.kind.clone())?;
        match kind {
            TermKind::SetEmpty(_) => Some(Vec::new()),
            TermKind::SetSingleton(e) => Some(vec![Member {
                value: Rc::new(Value::Scalar(e)),
                present: tm.mk_bool(true),
            }]),
            TermKind::SetUnion(a, b) => {
                let mut xs = self.candidates_of(a, depth + 1, tm)?;
                xs.extend(self.candidates_of(b, depth + 1, tm)?);
                (xs.len() <= self.max_candidates).then_some(xs)
            }
            // The same three rules the arena uses for `\cup`, `\cap` and
            // `\`: an intersection keeps the left candidates guarded by
            // membership on the right, a difference by its negation.
            TermKind::SetInter(a, b) => {
                let xs = self.candidates_of(a, depth + 1, tm)?;
                self.guard_by_membership(xs, b, false, tm)
            }
            TermKind::SetMinus(a, b) => {
                let xs = self.candidates_of(a, depth + 1, tm)?;
                self.guard_by_membership(xs, b, true, tm)
            }
            // A conditional set contributes each branch under its condition.
            TermKind::Ite(c, a, b) => {
                let not_c = tm.mk_not(c);
                let mut out = Vec::new();
                for (guard, side) in [(c, a), (not_c, b)] {
                    for m in self.candidates_of(side, depth + 1, tm)? {
                        out.push(Member {
                            present: tm.mk_and([guard, m.present]),
                            value: m.value,
                        });
                    }
                }
                (out.len() <= self.max_candidates).then_some(out)
            }
            _ => None,
        }
    }

    /// Strengthen each candidate by membership (or non-membership) in `other`.
    ///
    /// `None` if a candidate has no SMT term to test with, which cannot happen
    /// for a list [`Encoder::candidates_of`] built — every one of those comes
    /// from a singleton. Refused rather than left unguarded all the same: an
    /// unguarded candidate is claimed *present* when it may not be, and a
    /// spurious member of the set an invariant quantifies over can satisfy an
    /// existential that should have failed, which hides a violation.
    fn guard_by_membership(
        &mut self,
        members: Vec<Member>,
        other: TermId,
        negated: bool,
        tm: &mut TermManager,
    ) -> Option<Vec<Member>> {
        let mut out = Vec::with_capacity(members.len());
        for m in members {
            let Value::Scalar(e) = &*m.value else {
                return None;
            };
            let inside = tm.mk_set_member(*e, other);
            let g = if negated { tm.mk_not(inside) } else { inside };
            let present = tm.mk_and([m.present, g]);
            out.push(Member {
                present,
                value: m.value,
            });
        }
        Some(out)
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

    /// The sort of an encoded term.
    fn sort_of(&self, t: TermId, tm: &TermManager) -> Result<SortId> {
        tm.get(t)
            .map(|d| d.sort)
            .ok_or_else(|| EncodeError::Unsupported("a term with no sort".into()))
    }

    /// An arena candidate list as a single set-sorted term.
    ///
    /// The bridge between the two set encodings, and it only goes this way:
    /// candidates carry a `present` Boolean, which becomes a conditional
    /// singleton, whereas a set-sorted term has no candidate list to recover.
    ///
    /// `element` is passed rather than read off the first candidate because an
    /// empty domain has no candidate to read it from, and guessing there would
    /// build the empty set at the wrong sort — a different value.
    fn native_set_of(
        &mut self,
        members: &[Member],
        element: SortId,
        tm: &mut TermManager,
    ) -> Result<TermId> {
        let set_sort = tm.sorts.set(element);
        let empty = tm.mk_set_empty_at(set_sort);
        let mut acc = empty;
        for m in members {
            let Value::Scalar(k) = &*m.value else {
                return Err(EncodeError::Unsupported(
                    "a set whose members have no SMT sort, used as a function domain".into(),
                ));
            };
            if self.sort_of(*k, tm)? != element {
                return Err(EncodeError::Unsupported(
                    "a function domain whose members do not share one sort".into(),
                ));
            }
            let single = tm.mk_set_singleton(*k);
            // A candidate that may not be present contributes conditionally.
            // `ite` at a set sort is decided by the set theory, so this needs
            // no case split of its own.
            let piece = tm.mk_ite(m.present, single, empty);
            acc = tm.mk_set_union(acc, piece);
        }
        Ok(acc)
    }

    /// The shared base array every function graph is built on; see
    /// [`crate::arena::fun_base`] for why it is shared.
    fn fun_base(&mut self, array_sort: SortId, tm: &mut TermManager) -> TermId {
        crate::arena::fun_base(array_sort, tm)
    }

    /// The element sort of a set-sorted term.
    fn element_sort_of(&self, set: TermId, tm: &TermManager) -> Result<SortId> {
        let sort = self.sort_of(set, tm)?;
        match tm.sorts.get(sort).map(|s| &s.kind) {
            Some(nixie_core::SortKind::Set(e)) => Ok(*e),
            _ => Err(EncodeError::Unsupported(
                "a term used as a set that does not have a set sort".into(),
            )),
        }
    }

    /// `value \in set`, where `value` is already encoded and `set` is not.
    ///
    /// Goes back through the ordinary `\in` dispatch rather than picking a
    /// membership encoding here, by binding the value to a synthetic name.
    /// That is not a trick for its own sake: `\in` has four different
    /// encodings depending on the set — a standard infinite set, a native set
    /// term, an arena candidate list — and reproducing the choice at a second
    /// site is how the two drift apart.
    fn membership(&mut self, v: Rc<Value>, set: &KeraRef, tm: &mut TermManager) -> Result<TermId> {
        let name = Name(format!("@img{}", self.fresh));
        self.fresh = self.fresh.wrapping_add(1);
        let node: KeraRef = Rc::new(Kera::In(Rc::new(Kera::Var(name.clone())), Rc::clone(set)));
        let saved = self.bound.insert(name.clone(), v);
        let out = self.value(&node, tm);
        match saved {
            Some(x) => self.bound.insert(name, x),
            None => self.bound.remove(&name),
        };
        match &*out? {
            Value::Scalar(t) => Ok(*t),
            _ => Err(EncodeError::Unsupported(
                "a membership test that did not produce a Boolean".into(),
            )),
        }
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
            // A TLA+ string is an atom: it is only ever compared for equality
            // and never taken apart. `StringLit` gives that exactly, and the
            // string theory is already in Nelson-Oppen.
            Kera::Str(text) => scalar(tm.mk_string_lit(text)),
            // A standard infinite set reaching here is being used as a
            // *value* rather than in a membership test — `s = Nat`, say. It
            // has no finite representation, and making it an opaque set
            // constant would leave it unconstrained, so it is declined.
            Kera::Var(_) | Kera::Opaque(_, _) if standard_set(term).is_some() => {
                let name = standard_set(term).map_or("a standard set", |n| n);
                Err(EncodeError::Unsupported(format!(
                    "`{name}` used as a value (it is infinite)"
                )))
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
                if let Some(t) = self.vars.get(&key).copied() {
                    return match self.var_domains.get(&key).copied() {
                        Some(domain) => Ok(Rc::new(Value::Fun { domain, array: t })),
                        None => scalar(t),
                    };
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
                self.vars.insert(key.clone(), t);
                // A function-sorted name gets its domain as a second variable.
                // Without it the name would be a bare graph, and `f = g`, and
                // `DOMAIN f`, would both be answered by the array alone — the
                // first unsoundly (see `arena::eq_values`), the second not at
                // all.
                if let Some(nixie_core::SortKind::Array { domain, .. }) =
                    tm.sorts.get(sort).map(|s| s.kind.clone())
                {
                    let set_sort = tm.sorts.set(domain);
                    let d = tm.mk_var(&format!("{smt_name}$dom"), set_sort);
                    self.var_domains.insert(key, d);
                    return Ok(Rc::new(Value::Fun {
                        domain: d,
                        array: t,
                    }));
                }
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
            // The standard *infinite* sets are not sets this encoding can
            // hold, and must never become opaque set constants: an
            // unconstrained `Nat` lets the solver decide `0 \notin Nat`, so
            // `TypeOK == x \in Nat` "fails" in the initial state. That is a
            // false counterexample, and it was found on `AddTwo.tla`.
            //
            // Membership in them *is* exactly expressible, so it is encoded
            // rather than declined:
            // `f \in [S -> T]`: exactly "the domain is `S`, and every value on
            // it is in `T`". This is how `TypeOK` states a function variable's
            // type in most specifications, so it is worth encoding rather than
            // declining — and it is only *statable* because the function value
            // carries its domain.
            //
            // The set of functions itself is still refused as a value: `[S -> T]`
            // has `|T|^|S|` members and enumerating it is not a plan.
            Kera::In(f, s) if matches!(s.as_ref(), Kera::FunSet { .. }) => {
                let Kera::FunSet { set, cod } = s.as_ref() else {
                    return Err(EncodeError::Unsupported("a function set".into()));
                };
                let value = self.value(f, tm)?;
                let Value::Fun { domain, array } = &*value else {
                    return Err(EncodeError::Unsupported(
                        "`\\in [S -> T]` applied to something that is not a function".into(),
                    ));
                };
                let (domain, array) = (*domain, *array);
                let elem = self.element_sort_of(domain, tm)?;
                let base = self.set_as_arena(set, tm)?;
                let want = self.native_set_of(&base.members, elem, tm)?;
                let mut conj = vec![tm.mk_eq(domain, want)];
                for m in &base.members {
                    let Value::Scalar(key) = &*m.value else {
                        return Err(EncodeError::Unsupported(
                            "a function domain whose members have no SMT sort".into(),
                        ));
                    };
                    let image = Rc::new(Value::Scalar(tm.mk_select(array, *key)));
                    let inside = self.membership(image, cod, tm)?;
                    // A candidate that is not in `S` constrains nothing.
                    let absent = tm.mk_not(m.present);
                    conj.push(tm.mk_or([absent, inside]));
                }
                scalar(tm.mk_and(conj))
            }
            Kera::In(a, s) if standard_set(s).is_some() => {
                let Some(name) = standard_set(s) else {
                    return Err(EncodeError::Unsupported("a standard set".into()));
                };
                let x = self.go(a, tm)?;
                match name {
                    // `x \in Nat` is `x >= 0` for an integer `x`.
                    "Nat" => {
                        let zero = tm.mk_int(0);
                        scalar(tm.mk_ge(x, zero))
                    }
                    // Every value of the matching sort is in these, and the
                    // type checker has already established the sort.
                    "Int" | "Real" | "STRING" | "BOOLEAN" => scalar(tm.mk_bool(true)),
                    other => Err(EncodeError::Unsupported(format!("`{other}` as a set"))),
                }
            }
            Kera::In(a, s) if self.set_encoding == SetEncoding::Native => {
                let e = self.go(a, tm)?;
                let set = self.go(s, tm)?;
                scalar(tm.mk_set_member(e, set))
            }
            Kera::SetBin(op, a, b) if self.set_encoding == SetEncoding::Native => {
                let x = self.go(a, tm)?;
                let y = self.go(b, tm)?;
                scalar(match op {
                    SetOp::Union => tm.mk_set_union(x, y),
                    SetOp::Intersect => tm.mk_set_inter(x, y),
                    SetOp::Difference => tm.mk_set_minus(x, y),
                })
            }
            Kera::In(a, s) => {
                let v = self.value(a, tm)?;
                let set = self.set(s, tm)?;
                let t = self.shape(member_of(&v, &set, tm))?;
                scalar(t)
            }

            // ---- sets ----
            // Native: a set literal is a union of singletons, which is also
            // the normal form CVC5 uses for a set constant.
            Kera::SetEnum(xs) if self.set_encoding == SetEncoding::Native => {
                let mut acc: Option<TermId> = None;
                for x in xs {
                    let e = self.go(x, tm)?;
                    let single = tm.mk_set_singleton(e);
                    acc = Some(match acc {
                        None => single,
                        Some(prev) => tm.mk_set_union(prev, single),
                    });
                }
                match acc {
                    Some(t) => scalar(t),
                    // `{}` carries no element to take a sort from, so the
                    // sort has to come from the caller's type inference.
                    // Declined, never guessed: an empty set at the wrong
                    // element sort is a different value.
                    None => match self.node_sorts.get(&Rc::as_ptr(term)).copied() {
                        Some(set_sort) => scalar(tm.mk_set_empty_at(set_sort)),
                        None => Err(EncodeError::Unsupported(
                            "`{}` with no element sort to give it".into(),
                        )),
                    },
                }
            }
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
            Kera::Filter { .. } | Kera::Map { .. } if self.set_encoding == SetEncoding::Native => {
                Err(EncodeError::Unsupported(
                    "a set comprehension (the set theory has no comprehension)".into(),
                ))
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

            // ---- tuples and records ----
            // Structural, not an SMT value: TLA+ tuples and records are
            // heterogeneous, so flattening them into an array would force
            // every component to one sort.
            Kera::Tuple(xs) => {
                let mut parts = Vec::with_capacity(xs.len());
                for x in xs {
                    parts.push(self.value(x, tm)?);
                }
                Ok(Rc::new(Value::Tuple(parts)))
            }
            Kera::Record(fs) => {
                let mut fields = std::collections::BTreeMap::new();
                for (k, v) in fs {
                    fields.insert(k.clone(), self.value(v, tm)?);
                }
                Ok(Rc::new(Value::Record(fields)))
            }
            // `[a : S, b : T]` is the set of records with one field drawn from
            // each set — a cartesian product over the field sets.
            Kera::RecordSet(fs) => {
                /// A partial record under construction, with the guard that
                /// says every field chosen so far is really in its set.
                type Partial = (Vec<(String, Rc<Value>)>, TermId);
                let mut combos: Vec<Partial> = vec![(Vec::new(), tm.mk_bool(true))];
                for (name, set) in fs {
                    let cell = self.set(set, tm)?;
                    let mut next = Vec::new();
                    for (prefix, guard) in &combos {
                        for m in &cell.members {
                            let mut fields = prefix.clone();
                            fields.push((name.clone(), Rc::clone(&m.value)));
                            next.push((fields, tm.mk_and([*guard, m.present])));
                        }
                    }
                    if next.len() > self.max_candidates {
                        return Err(EncodeError::TooManyCandidates {
                            limit: self.max_candidates,
                        });
                    }
                    combos = next;
                }
                let members = combos
                    .into_iter()
                    .map(|(fields, present)| Member {
                        value: Rc::new(Value::Record(fields.into_iter().collect())),
                        present,
                    })
                    .collect();
                self.mk_set(members)
            }
            // `A \X B \X ...` is the set of tuples, one component per set.
            Kera::Times(sets) => {
                let mut combos: Vec<(Vec<Rc<Value>>, TermId)> =
                    vec![(Vec::new(), tm.mk_bool(true))];
                for set in sets {
                    let cell = self.set(set, tm)?;
                    let mut next = Vec::new();
                    for (prefix, guard) in &combos {
                        for m in &cell.members {
                            let mut parts = prefix.clone();
                            parts.push(Rc::clone(&m.value));
                            next.push((parts, tm.mk_and([*guard, m.present])));
                        }
                    }
                    if next.len() > self.max_candidates {
                        return Err(EncodeError::TooManyCandidates {
                            limit: self.max_candidates,
                        });
                    }
                    combos = next;
                }
                let members = combos
                    .into_iter()
                    .map(|(parts, present)| Member {
                        value: Rc::new(Value::Tuple(parts)),
                        present,
                    })
                    .collect();
                self.mk_set(members)
            }

            // ---- binders over a set ----
            // Instantiated, not quantified: one copy of the body per candidate.
            Kera::Forall { var, set, body } => {
                let base = self.set_as_arena(set, tm)?;
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
                let base = self.set_as_arena(set, tm)?;
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
            // `[x \in S |-> e]` is the only place a TLA+ function is written
            // down, and it is where both halves of a function value come from:
            // the domain is `S`, and the graph is `e` evaluated at each of its
            // members.
            //
            // The domain is enumerated by the arena — `S` is written in the
            // specification, so its candidates are exactly what the arena
            // computes — and then turned into one set-sorted term, so the
            // resulting value carries a domain the solver can reason about
            // rather than one the encoder merely knew at build time.
            Kera::FunDef { var, set, body } => {
                let base = self.set_as_arena(set, tm)?;
                let mut entries = Vec::with_capacity(base.members.len());
                for m in &base.members {
                    let Value::Scalar(key) = &*m.value else {
                        return Err(EncodeError::Unsupported(
                            "a function over a domain whose members have no SMT sort".into(),
                        ));
                    };
                    let image = self.with_bound(var, Rc::clone(&m.value), body, tm)?;
                    let Value::Scalar(val) = &*image else {
                        return Err(EncodeError::Unsupported(
                            "a function whose values are not single values".into(),
                        ));
                    };
                    entries.push((*key, *val, m.present));
                }
                // Sorts come from the entries when there are any, and from the
                // caller's type inference when there are none: `[x \in {} |-> e]`
                // is a real function and its sort is not recoverable from the
                // term. Declined rather than guessed.
                let (dom_sort, rng_sort) = match entries.first() {
                    Some((k, v, _)) => (self.sort_of(*k, tm)?, self.sort_of(*v, tm)?),
                    None => {
                        let Some(sort) = self.node_sorts.get(&Rc::as_ptr(term)).copied() else {
                            return Err(EncodeError::Unsupported(
                                "a function over an empty domain, with no sort to give it".into(),
                            ));
                        };
                        match tm.sorts.get(sort).map(|s| s.kind.clone()) {
                            Some(nixie_core::SortKind::Array { domain, range }) => (domain, range),
                            _ => {
                                return Err(EncodeError::Unsupported(
                                    "a function whose declared sort is not an array".into(),
                                ));
                            }
                        }
                    }
                };
                for (k, v, _) in &entries {
                    if self.sort_of(*k, tm)? != dom_sort || self.sort_of(*v, tm)? != rng_sort {
                        return Err(EncodeError::Unsupported(
                            "a function whose domain or values do not share one sort".into(),
                        ));
                    }
                }
                let domain = self.native_set_of(&base.members, dom_sort, tm)?;
                let array_sort = tm.sorts.array(dom_sort, rng_sort);
                let mut array = self.fun_base(array_sort, tm);
                for (key, val, present) in &entries {
                    // A candidate that may not be present must not be written
                    // unconditionally. The conditional is put on the *value*
                    // rather than on the store, so every `ite` here is at the
                    // range sort — the generic mux pass owns that, while an
                    // `ite` between two arrays is left for the array theory to
                    // recurse through and is better not built at all.
                    let old = tm.mk_select(array, *key);
                    let chosen = tm.mk_ite(*present, *val, old);
                    array = tm.mk_store(array, *key, chosen);
                }
                Ok(Rc::new(Value::Fun { domain, array }))
            }
            // A TLA+ function application is an array select, and `EXCEPT` is
            // a store. Both are exact *inside* the function's domain. Outside
            // it TLA+ leaves `f[x]` undefined while the array returns some
            // value, which admits behaviours the specification does not have:
            // that can manufacture a counterexample, never hide one.
            Kera::FunApp(f, i) => {
                let target = self.value(f, tm)?;
                match &*target {
                    // A tuple is a function on `1..n`, so a literal index
                    // selects a component. A non-literal index into a
                    // heterogeneous tuple has no well-sorted answer, and is
                    // refused rather than approximated.
                    Value::Tuple(parts) => {
                        let Some(n) = literal_int(i) else {
                            return Err(EncodeError::Unsupported(
                                "a tuple indexed by a non-literal".into(),
                            ));
                        };
                        let idx = usize::try_from(&n).ok().filter(|k| *k >= 1);
                        let Some(v) = idx.and_then(|k| parts.get(k - 1)) else {
                            return Err(EncodeError::Unsupported(format!(
                                "index {n} into a {}-tuple",
                                parts.len()
                            )));
                        };
                        Ok(Rc::clone(v))
                    }
                    // A record is a function on its field names; `r.f` lowers
                    // to exactly this shape.
                    Value::Record(fields) => {
                        let Kera::Str(name) = i.as_ref() else {
                            return Err(EncodeError::Unsupported(
                                "a record indexed by a non-literal field name".into(),
                            ));
                        };
                        let Some(v) = fields.get(name) else {
                            return Err(EncodeError::Unsupported(format!(
                                "field `{name}`, which the record does not have"
                            )));
                        };
                        Ok(Rc::clone(v))
                    }
                    // The domain is carried, so nothing is being approximated
                    // away here. `f[x]` for an `x` outside the domain is
                    // *undefined* in TLA+ and the array answers with whatever
                    // the base holds — the standard underspecified reading,
                    // and the same one Apalache takes.
                    Value::Fun { array, .. } => {
                        let idx = self.go(i, tm)?;
                        scalar(tm.mk_select(*array, idx))
                    }
                    // A bare array with no domain: a function reached through
                    // a select (`f[x][y]`), where the inner sort carries no
                    // domain of its own.
                    Value::Scalar(arr) => {
                        let idx = self.go(i, tm)?;
                        self.domain_unmodelled = true;
                        scalar(tm.mk_select(*arr, idx))
                    }
                    Value::Set(_) => Err(EncodeError::Unsupported(
                        "a set applied as a function".into(),
                    )),
                }
            }
            Kera::Except { fun, index, value } => {
                let target = self.value(fun, tm)?;
                match &*target {
                    Value::Tuple(parts) => {
                        let Some(n) = literal_int(index) else {
                            return Err(EncodeError::Unsupported(
                                "`EXCEPT` on a tuple at a non-literal index".into(),
                            ));
                        };
                        let at = usize::try_from(&n).ok().filter(|k| *k >= 1);
                        let Some(at) = at.filter(|k| *k <= parts.len()) else {
                            return Err(EncodeError::Unsupported(format!(
                                "`EXCEPT` at index {n} of a {}-tuple",
                                parts.len()
                            )));
                        };
                        let mut parts = parts.clone();
                        parts[at - 1] = self.value(value, tm)?;
                        Ok(Rc::new(Value::Tuple(parts)))
                    }
                    Value::Record(fields) => {
                        let Kera::Str(name) = index.as_ref() else {
                            return Err(EncodeError::Unsupported(
                                "`EXCEPT` on a record at a non-literal field".into(),
                            ));
                        };
                        if !fields.contains_key(name) {
                            return Err(EncodeError::Unsupported(format!(
                                "`EXCEPT` on field `{name}`, which the record does not have"
                            )));
                        }
                        let mut fields = fields.clone();
                        fields.insert(name.clone(), self.value(value, tm)?);
                        Ok(Rc::new(Value::Record(fields)))
                    }
                    // `[f EXCEPT ![i] = v]` has the *same domain* as `f` —
                    // `EXCEPT` never extends a function. An `i` outside that
                    // domain leaves the result unspecified in TLA+; storing it
                    // anyway writes at a point domain-relative equality does
                    // not look at, so it changes no answer.
                    Value::Fun { domain, array } => {
                        let idx = self.go(index, tm)?;
                        let val = self.go(value, tm)?;
                        let array = tm.mk_store(*array, idx, val);
                        Ok(Rc::new(Value::Fun {
                            domain: *domain,
                            array,
                        }))
                    }
                    Value::Scalar(arr) => {
                        let idx = self.go(index, tm)?;
                        let val = self.go(value, tm)?;
                        self.domain_unmodelled = true;
                        scalar(tm.mk_store(*arr, idx, val))
                    }
                    Value::Set(_) => Err(EncodeError::Unsupported("`EXCEPT` on a set".into())),
                }
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
            // `DOMAIN` is exact for the structural values: a tuple's domain is
            // `1..n` and a record's is its field names. For an array-backed
            // function it is not represented at all, and is refused rather
            // than answered with something plausible.
            Kera::Domain(f) => {
                let target = self.value(f, tm)?;
                let yes = tm.mk_bool(true);
                match &*target {
                    Value::Tuple(parts) => {
                        let members = (1..=parts.len())
                            .map(|i| Member {
                                value: Rc::new(Value::Scalar(tm.mk_int(i as i64))),
                                present: yes,
                            })
                            .collect();
                        self.mk_set(members)
                    }
                    Value::Record(fields) => {
                        let members = fields
                            .keys()
                            .map(|k| Member {
                                value: Rc::new(Value::Scalar(tm.mk_string_lit(k))),
                                present: yes,
                            })
                            .collect();
                        self.mk_set(members)
                    }
                    // Exact, which is the whole point of carrying a domain.
                    Value::Fun { domain, .. } => scalar(*domain),
                    Value::Scalar(_) | Value::Set(_) => Err(EncodeError::Unsupported(
                        "`DOMAIN` of a function the array encoding does not carry a domain for"
                            .into(),
                    )),
                }
            }

            // Standard-module operators whose meaning is arena-level.
            Kera::Opaque(name, args)
                if self.set_encoding == SetEncoding::Native
                    && matches!(
                        (name.as_str(), args.len()),
                        ("Cardinality", 1) | ("IsFiniteSet", 1)
                    ) =>
            {
                let set = self.go(&args[0], tm)?;
                match name.as_str() {
                    "Cardinality" => scalar(tm.mk_set_card(set)),
                    // Every set in this theory is finite.
                    _ => scalar(tm.mk_bool(true)),
                }
            }
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

/// The name of a standard *infinite* set, if the term is one.
///
/// These cannot be represented by a finite-set theory, and must not be turned
/// into opaque set constants either — an unconstrained `Nat` admits models in
/// which `0` is not a natural number.
fn standard_set(term: &KeraRef) -> Option<&'static str> {
    let name = match term.as_ref() {
        Kera::Var(n) => n.as_str(),
        Kera::Opaque(n, args) if args.is_empty() => n.as_str(),
        _ => return None,
    };
    match name {
        "Nat" => Some("Nat"),
        "Int" => Some("Int"),
        "Real" => Some("Real"),
        "STRING" => Some("STRING"),
        "BOOLEAN" => Some("BOOLEAN"),
        _ => None,
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
