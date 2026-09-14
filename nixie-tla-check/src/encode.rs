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

use crate::arena::{Member, SetCell, Value, cardinality, eq_values, ite_values, member_of};
use nixie_core::{SortId, TermId, TermManager};
use nixie_tla::kera::{ArithOp, CmpOp, FoldOver, Kera, KeraRef, Name, SetOp};
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

/// The SMT name standing for `CHOOSE v : TRUE` read as a Boolean.
///
/// TLA+ says `CHOOSE` over a predicate nothing pins down picks *some* fixed
/// value, the same one wherever the expression is written -- so this is one
/// shared free constant, not a fresh one per occurrence. It is the `ELSE`
/// branch of `TLC!Assert`.
const CHOOSE_ANY_BOOL: &str = "@tla_choose_any_bool";

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

/// How one set-valued term came out.
///
/// Not the same thing as [`SetEncoding`], which says what a *new* set is built
/// as. A single problem routinely holds both: `1..3` has only an arena form
/// and a set-valued state variable only a native one.
#[derive(Debug, Clone)]
enum SetRepr {
    /// A candidate list.
    Arena(SetCell),
    /// A set-sorted SMT term.
    Native(TermId),
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

    /// Every free name the caller gave a sort: the `VARIABLE`s and the
    /// `CONSTANT`s together.
    ///
    /// Both are needed to rebuild a state for replay. A constant does not
    /// change from step to step, but the evaluator still has to be told what
    /// it is, or the specification's own definitions cannot be evaluated at
    /// all.
    pub fn declared_names(&self) -> impl Iterator<Item = &str> {
        self.sorts.keys().map(String::as_str)
    }

    /// The companion **domain** term of a function-sorted name at `step`.
    ///
    /// An SMT array is only a graph. Reading a function back out of a model
    /// without this would give a total function over the whole index sort,
    /// which is a different value from the one the specification has.
    #[must_use]
    pub fn domain_at(&self, name: &str, step: u32) -> Option<TermId> {
        let key = if self.state.contains(name) { step } else { 0 };
        self.var_domains.get(&(name.to_string(), key)).copied()
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
        let v = self.value(term, tm)?;
        self.reify(&v, tm)
    }

    /// A value as a single SMT term.
    ///
    /// A tuple and a record reify into a **single-constructor datatype**, one
    /// field per component. The structural form stays primary — it is what
    /// makes a literal index and an exact `DOMAIN` possible — and this is what
    /// it becomes when something needs a term: a member of a set of tuples, a
    /// record-valued state variable's new value, an operand of `=`.
    ///
    /// A set and a function are refused rather than reified: a set *has* a
    /// sort but its arena form is a candidate list rather than one term, and a
    /// function is a domain and a graph, so handing back the graph alone would
    /// drop the half that makes equality right.
    fn reify(&mut self, v: &Rc<Value>, tm: &mut TermManager) -> Result<TermId> {
        match &**v {
            Value::Scalar(t) => Ok(*t),
            Value::Set(_) => Err(EncodeError::Unsupported(
                "a set where a single value is needed".into(),
            )),
            Value::Fun { .. } => Err(EncodeError::Unsupported(
                "a function where a single value is needed".into(),
            )),
            Value::Tuple(parts) => {
                let mut fields = Vec::with_capacity(parts.len());
                for (i, p) in parts.iter().enumerate() {
                    fields.push((crate::sorts::tuple_field(i), Rc::clone(p)));
                }
                self.reify_struct(&fields, tm)
            }
            Value::Record(entries) => {
                let mut fields = Vec::with_capacity(entries.len());
                for (name, p) in entries {
                    fields.push((crate::sorts::record_field(name), Rc::clone(p)));
                }
                self.reify_struct(&fields, tm)
            }
        }
    }

    /// Build the datatype term for a structural value.
    ///
    /// The constructor's name is a function of the field names and their
    /// sorts, computed the same way [`crate::sorts::sort_of`] computes it —
    /// which is what makes the value the encoder builds and the sort the type
    /// checker assigned the *same* datatype rather than two that merely look
    /// alike.
    fn reify_struct(
        &mut self,
        fields: &[(String, Rc<Value>)],
        tm: &mut TermManager,
    ) -> Result<TermId> {
        let mut args = Vec::with_capacity(fields.len());
        let mut sorts = Vec::with_capacity(fields.len());
        for (name, v) in fields {
            let t = self.reify(v, tm)?;
            sorts.push((name.clone(), self.sort_of(t, tm)?));
            args.push(t);
        }
        let sort = crate::sorts::declare_struct(&sorts, tm);
        let name = crate::sorts::struct_name(&sorts, tm);
        Ok(tm.mk_dt_constructor(&name, args, sort))
    }

    /// The datatype selector a TLA+ index names, if it is a literal.
    ///
    /// `t[2]` selects a tuple's second component and `r.f` its `f` field; both
    /// arrive here as an index expression. A non-literal index is `None`,
    /// which is a refusal rather than an approximation — a datatype has no
    /// dynamic field access, and picking one would be a guess.
    fn field_name(&self, index: &KeraRef) -> Option<String> {
        match index.as_ref() {
            Kera::Str(name) => Some(crate::sorts::record_field(name)),
            // Anything else is tried as a tuple index, which is an integer —
            // and one that need not be written as a literal, since a `.cfg`
            // substitution leaves arithmetic behind. A term that is not a
            // ground integer falls through to `None`, which is the refusal.
            _ => {
                let n = ground_int(index)?;
                let i = usize::try_from(&n).ok().filter(|k| *k >= 1)?;
                Some(crate::sorts::tuple_field(i - 1))
            }
        }
    }

    /// `t[index]` where `t` is a reified tuple or record.
    fn select_field(
        &mut self,
        t: TermId,
        sort: SortId,
        index: &KeraRef,
        tm: &mut TermManager,
    ) -> Result<Rc<Value>> {
        let Some(fields) = self.struct_fields(sort, tm) else {
            return Err(EncodeError::Unsupported(
                "an index into a datatype with no fields".into(),
            ));
        };
        let Some(want) = self.field_name(index) else {
            return Err(EncodeError::Unsupported(
                "a tuple or record indexed by a non-literal".into(),
            ));
        };
        let Some((name, fs)) = fields.iter().find(|(f, _)| *f == want) else {
            return Err(EncodeError::Unsupported(format!(
                "`{want}`, which this value does not have"
            )));
        };
        scalar(tm.mk_dt_selector(name, t, *fs))
    }

    /// The field names of a tuple-or-record datatype sort, in order.
    fn struct_fields(&self, sort: SortId, tm: &TermManager) -> Option<Vec<(String, SortId)>> {
        crate::sorts::struct_fields(sort, tm)
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

    /// A set-valued term, in whichever representation it came out in.
    ///
    /// The two encodings are not a mode the whole problem is in — they are a
    /// property of each *term*. `1..3` only has an arena form (the theory has
    /// no range constructor) while a set-valued state variable only has a
    /// native one (its members are not knowable before the solver runs), and
    /// `x \in 1..3` has to work in either mode. Dispatching on the value
    /// rather than on the mode is what makes that true; dispatching on the
    /// mode made native mode decline a perfectly ordinary membership test.
    fn set_repr(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<SetRepr> {
        match &*self.value(term, tm)? {
            Value::Set(cell) => Ok(SetRepr::Arena(cell.clone())),
            Value::Scalar(t) if self.element_sort_of(*t, tm).is_ok() => Ok(SetRepr::Native(*t)),
            Value::Scalar(_) | Value::Tuple(_) | Value::Record(_) | Value::Fun { .. } => Err(
                EncodeError::NotEnumerable("a value used as a set".to_string()),
            ),
        }
    }

    /// Both operands of a binary set operation, in one representation.
    ///
    /// Native wins when either side is native, because a native set may be an
    /// opaque variable with no candidate list to fall back to, while an arena
    /// set can always be written out as a union of singletons.
    fn set_pair(
        &mut self,
        a: &KeraRef,
        b: &KeraRef,
        tm: &mut TermManager,
    ) -> Result<(SetRepr, SetRepr)> {
        let (x, y) = (self.set_repr(a, tm)?, self.set_repr(b, tm)?);
        Ok(match (x, y) {
            (SetRepr::Arena(p), SetRepr::Native(q)) => {
                let elem = self.element_sort_of(q, tm)?;
                let p = self.native_set_of(&p.members, elem, tm)?;
                (SetRepr::Native(p), SetRepr::Native(q))
            }
            (SetRepr::Native(p), SetRepr::Arena(q)) => {
                let elem = self.element_sort_of(p, tm)?;
                let q = self.native_set_of(&q.members, elem, tm)?;
                (SetRepr::Native(p), SetRepr::Native(q))
            }
            same => same,
        })
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

    /// Encode `body` once with two names bound at the same time.
    ///
    /// A fold's operator takes an accumulator and an element, and the two have
    /// to be in scope together. Nesting [`Encoder::with_bound`] would do it,
    /// but it also has to *unbind* in the right order, and doing that by hand
    /// at the call site is how a binding leaks.
    fn with_two_bound(
        &mut self,
        first: &Name,
        fv: Rc<Value>,
        second: &Name,
        sv: Rc<Value>,
        body: &KeraRef,
        tm: &mut TermManager,
    ) -> Result<Rc<Value>> {
        let saved_first = self.bound.insert(first.clone(), fv);
        let saved_second = self.bound.insert(second.clone(), sv);
        let out = self.value(body, tm);
        match saved_second {
            Some(v) => self.bound.insert(second.clone(), v),
            None => self.bound.remove(second),
        };
        match saved_first {
            Some(v) => self.bound.insert(first.clone(), v),
            None => self.bound.remove(first),
        };
        out
    }

    /// The empty sequence at a sequence sort.
    ///
    /// Built over the **shared** base array, which is what makes two sequences
    /// with the same elements equal: the datatype's equality compares the
    /// array at every index, so two empty sequences over different bases would
    /// compare unequal. See [`crate::arena::fun_base`] for the same argument
    /// about functions.
    fn empty_seq(&mut self, sort: SortId, elem: SortId, tm: &mut TermManager) -> Result<TermId> {
        let int = tm.sorts.int_sort;
        let arr = tm.sorts.array(int, elem);
        let base = self.fun_base(arr, tm);
        let zero = tm.mk_int(num_bigint::BigInt::from(0));
        let name = tm
            .sorts
            .datatype_name(sort)
            .ok_or(EncodeError::ShapeClash)?
            .to_string();
        Ok(tm.mk_dt_constructor(&name, [zero, base], sort))
    }

    /// `Len(s)`.
    fn seq_len(&self, seq: TermId, tm: &mut TermManager) -> TermId {
        let int = tm.sorts.int_sort;
        tm.mk_dt_selector(crate::sorts::SEQ_LEN, seq, int)
    }

    /// The graph of `s`, as an array from `1..`.
    fn seq_fun(&self, seq: TermId, elem: SortId, tm: &mut TermManager) -> TermId {
        let int = tm.sorts.int_sort;
        let arr = tm.sorts.array(int, elem);
        tm.mk_dt_selector(crate::sorts::SEQ_FUN, seq, arr)
    }

    /// `Append(s, e)` — `e` written one past the end, and the length raised.
    fn seq_append(
        &mut self,
        seq: TermId,
        e: TermId,
        sort: SortId,
        tm: &mut TermManager,
    ) -> Result<TermId> {
        let Some(elem) = crate::sorts::seq_element(sort, tm) else {
            return Err(EncodeError::ShapeClash);
        };
        let len = self.seq_len(seq, tm);
        let fun = self.seq_fun(seq, elem, tm);
        let one = tm.mk_int(num_bigint::BigInt::from(1));
        let next = tm.mk_add([len, one]);
        let stored = tm.mk_store(fun, next, e);
        let name = tm
            .sorts
            .datatype_name(sort)
            .ok_or(EncodeError::ShapeClash)?
            .to_string();
        Ok(tm.mk_dt_constructor(&name, [next, stored], sort))
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
            //
            // Two sets may arrive in different representations — `DOMAIN r` is
            // an arena candidate list while `{"a", "b"}` in native mode is a
            // set term — so they are promoted to one first, the same way a
            // binary set operation does. Without that the comparison is a
            // shape clash, which is an honest refusal of a perfectly ordinary
            // equality.
            Kera::Eq(a, b) => {
                let x = self.value(a, tm)?;
                let y = self.value(b, tm)?;
                let mixed = matches!(
                    (&*x, &*y),
                    (Value::Set(_), Value::Scalar(_)) | (Value::Scalar(_), Value::Set(_))
                );
                if mixed
                    && let Ok((p, q)) = self.set_pair(a, b, tm)
                    && let (SetRepr::Native(p), SetRepr::Native(q)) = (p, q)
                {
                    return scalar(tm.mk_eq(p, q));
                }
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
            // Membership follows the *set's* representation, not the mode.
            // `x \in 1..3` in native mode reaches an arena candidate list,
            // because `..` has no native form; dispatching on the mode
            // declined it.
            Kera::In(a, s) => match self.set_repr(s, tm)? {
                SetRepr::Native(set) => {
                    let e = self.go(a, tm)?;
                    scalar(tm.mk_set_member(e, set))
                }
                SetRepr::Arena(cell) => {
                    let v = self.value(a, tm)?;
                    let t = self.shape(member_of(&v, &cell, tm))?;
                    scalar(t)
                }
            },
            Kera::SetBin(op, a, b) => match self.set_pair(a, b, tm)? {
                (SetRepr::Native(x), SetRepr::Native(y)) => scalar(match op {
                    SetOp::Union => tm.mk_set_union(x, y),
                    SetOp::Intersect => tm.mk_set_inter(x, y),
                    SetOp::Difference => tm.mk_set_minus(x, y),
                }),
                (SetRepr::Arena(x), SetRepr::Arena(y)) => {
                    let mut members = Vec::new();
                    match op {
                        // Candidates of both sides, each keeping its own
                        // membership. Duplicates across the two lists are
                        // fine: membership is a disjunction, so counting a
                        // value twice changes nothing. Cardinality
                        // de-duplicates separately.
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
                // `set_pair` promotes to a single representation, so a mixed
                // pair cannot reach here. Written as a refusal rather than an
                // `unreachable!`: the rule against `expect` is exactly about
                // "cannot happen" arms surviving a refactor.
                _ => Err(EncodeError::ShapeClash),
            },

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
            // `a..b` is enumerable only when both ends are *ground*. A
            // symbolic bound has no finite candidate list, and inventing one
            // would silently check a different specification — but ground is
            // not the same as literal, and reading it as literal is what kept
            // `0 .. N-1` out after a `.cfg` had already pinned `N`.
            Kera::Range(a, b) => {
                let lo = ground_int(a).ok_or_else(|| {
                    EncodeError::NotEnumerable("`..` with a non-literal lower bound".into())
                })?;
                let hi = ground_int(b).ok_or_else(|| {
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
            // `<<…>>` is a tuple *and* a sequence — TLA+ does not distinguish
            // them — so which one it encodes to is decided by the sort the
            // caller's type inference gave this node, not by the term. `<<>>`
            // is the case that forces it: an empty tuple has no component to
            // take a sort from, and `history = <<>>` where `history` is a
            // `Seq(Str)` is comparing against the empty *sequence*.
            Kera::Tuple(xs)
                if self
                    .node_sorts
                    .get(&Rc::as_ptr(term))
                    .copied()
                    .and_then(|s| crate::sorts::seq_element(s, tm))
                    .is_some() =>
            {
                let Some(sort) = self.node_sorts.get(&Rc::as_ptr(term)).copied() else {
                    return Err(EncodeError::ShapeClash);
                };
                let Some(elem) = crate::sorts::seq_element(sort, tm) else {
                    return Err(EncodeError::ShapeClash);
                };
                let mut seq = self.empty_seq(sort, elem, tm)?;
                for x in xs {
                    let v = self.go(x, tm)?;
                    seq = self.seq_append(seq, v, sort, tm)?;
                }
                scalar(seq)
            }
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
                    // Reified, not required to be scalar already: a domain of
                    // tuples and a range of records are both ordinary, and
                    // both are datatypes now.
                    let key = self.reify(&m.value, tm)?;
                    let image = self.with_bound(var, Rc::clone(&m.value), body, tm)?;
                    let val = self.reify(&image, tm)?;
                    entries.push((key, val, m.present));
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
                        let Some(n) = ground_int(i) else {
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
                    // A tuple or record that reached here as a *term* rather
                    // than structurally — a member of a set of tuples, or a
                    // record-valued state variable. It is a datatype, so the
                    // index selects a field.
                    Value::Scalar(t)
                        if self.sort_of(*t, tm).is_ok_and(|s| tm.sorts.is_datatype(s)) =>
                    {
                        let t = *t;
                        let sort = self.sort_of(t, tm)?;
                        self.select_field(t, sort, i, tm)
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
                        let Some(n) = ground_int(index) else {
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
                    // `EXCEPT` on a reified tuple or record rebuilds the
                    // constructor with one field replaced. Taking it apart and
                    // putting it back is exact: a single-constructor datatype
                    // has no other shape to be.
                    Value::Scalar(t)
                        if self.sort_of(*t, tm).is_ok_and(|s| tm.sorts.is_datatype(s)) =>
                    {
                        let t = *t;
                        let sort = self.sort_of(t, tm)?;
                        let Some(fields) = self.struct_fields(sort, tm) else {
                            return Err(EncodeError::Unsupported(
                                "`EXCEPT` on a datatype with no fields".into(),
                            ));
                        };
                        let Some(want) = self.field_name(index) else {
                            return Err(EncodeError::Unsupported(
                                "`EXCEPT` on a tuple or record at a non-literal index".into(),
                            ));
                        };
                        if !fields.iter().any(|(f, _)| *f == want) {
                            return Err(EncodeError::Unsupported(format!(
                                "`EXCEPT` at `{want}`, which this value does not have"
                            )));
                        }
                        let replacement = self.go(value, tm)?;
                        let mut args = Vec::with_capacity(fields.len());
                        for (f, fs) in &fields {
                            if *f == want {
                                args.push(replacement);
                            } else {
                                args.push(tm.mk_dt_selector(f, t, *fs));
                            }
                        }
                        let name = crate::sorts::struct_name(&fields, tm);
                        scalar(tm.mk_dt_constructor(&name, args, sort))
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
                    // A reified tuple or record still knows its own domain:
                    // the field names are in the datatype declaration.
                    Value::Scalar(t)
                        if self.sort_of(*t, tm).is_ok_and(|s| tm.sorts.is_datatype(s)) =>
                    {
                        let sort = self.sort_of(*t, tm)?;
                        let Some(fields) = self.struct_fields(sort, tm) else {
                            return Err(EncodeError::Unsupported(
                                "`DOMAIN` of a datatype with no fields".into(),
                            ));
                        };
                        let members = fields
                            .iter()
                            .enumerate()
                            .map(|(i, (f, _))| Member {
                                value: Rc::new(Value::Scalar(match f.strip_prefix("@f") {
                                    Some(name) => tm.mk_string_lit(name),
                                    None => tm.mk_int((i + 1) as i64),
                                })),
                                present: yes,
                            })
                            .collect();
                        self.mk_set(members)
                    }
                    Value::Scalar(_) | Value::Set(_) => Err(EncodeError::Unsupported(
                        "`DOMAIN` of a function the array encoding does not carry a domain for"
                            .into(),
                    )),
                }
            }

            // A fold, which is `FoldSetRule` / `FoldSeqRule` in Apalache.
            //
            // The accumulator starts at the base and is stepped once per
            // element, with the operator's body encoded afresh each time —
            // instantiation, exactly as a binder over a set already works
            // here. That is what keeps the result quantifier-free.
            //
            // What makes a *set* fold harder than a sequence fold is that an
            // arena candidate list is an over-approximation in two ways at
            // once: a candidate may not be in the set, and two candidates may
            // denote the same value. A step therefore only takes effect when
            // the candidate is present **and** is not a duplicate of an
            // earlier present one, which is the same guard `cardinality` uses
            // and the same one Apalache builds in `SetOps.dedup`. Without the
            // second half, `ApaFoldSet(+, 0, {x, y})` would answer `x + y`
            // when `x = y`.
            Kera::Fold {
                over,
                acc,
                elem,
                base,
                collection,
                body,
            } => {
                let mut a = self.value(base, tm)?;
                match over {
                    FoldOver::Set => {
                        // A fold needs a candidate list, exactly as a bounded
                        // quantifier does, so it goes through the same
                        // coercion: a set-sorted term this encoder built is a
                        // union of singletons and its candidates read back off
                        // it, while a genuinely opaque set variable has none
                        // and is declined. Answering from the base alone would
                        // be the shape of the bug Apalache fixed for infinite
                        // sets (their issue 1691), and the same wrong answer.
                        let cell = self.set(collection, tm)?;
                        for (i, m) in cell.members.iter().enumerate() {
                            let mut counts = vec![m.present];
                            for earlier in &cell.members[..i] {
                                let same = self.shape(eq_values(&m.value, &earlier.value, tm))?;
                                let dup = tm.mk_and([earlier.present, same]);
                                counts.push(tm.mk_not(dup));
                            }
                            let counts = tm.mk_and(counts);
                            let stepped = self.with_two_bound(
                                acc,
                                Rc::clone(&a),
                                elem,
                                Rc::clone(&m.value),
                                body,
                                tm,
                            )?;
                            let picked = ite_values(counts, &stepped, &a, tm)
                                .ok_or(EncodeError::ShapeClash)?;
                            a = Rc::new(picked);
                        }
                    }
                    // A sequence has neither problem: every element is there,
                    // once, in order. It does have to *be* a sequence — a
                    // literal tuple, which is what a TLA+ sequence is — and a
                    // sequence-sorted state variable has no encoding yet, so
                    // it is declined rather than approximated.
                    FoldOver::SeqLeft => {
                        // Read off the *kernel* term rather than the encoded
                        // value. `<<…>>` is a tuple and a sequence at once, so
                        // whether it encodes to a structural tuple or to a
                        // sequence datatype depends on the sort inference gave
                        // it — and a fold over a literal does not care which.
                        // Taking the components here is exact either way.
                        let items: Vec<Rc<Value>> = match collection.as_ref() {
                            Kera::Tuple(xs) => {
                                let mut out = Vec::with_capacity(xs.len());
                                for x in xs {
                                    out.push(self.value(x, tm)?);
                                }
                                out
                            }
                            _ => match &*self.value(collection, tm)? {
                                Value::Tuple(items) => items.clone(),
                                _ => {
                                    return Err(EncodeError::Unsupported(
                                        "a fold over a sequence that is not a literal".into(),
                                    ));
                                }
                            },
                        };
                        for item in items {
                            a = self.with_two_bound(acc, a, elem, item, body, tm)?;
                        }
                    }
                }
                Ok(a)
            }

            // The `Sequences` operators, on the datatype `sorts::seq_sort`
            // builds: a length and an array from `1..`. Every one of them is
            // exact — nothing here approximates — and the ones that are not
            // here are declined by name.
            Kera::Opaque(name, args)
                if matches!(
                    (name.as_str(), args.len()),
                    ("Len", 1) | ("Append", 2) | ("Head", 1)
                ) =>
            {
                let target = self.go(&args[0], tm)?;
                let sort = self.sort_of(target, tm)?;
                let Some(elem) = crate::sorts::seq_element(sort, tm) else {
                    return Err(EncodeError::Unsupported(format!(
                        "`{name}` applied to something that is not a sequence"
                    )));
                };
                match name.as_str() {
                    "Len" => scalar(self.seq_len(target, tm)),
                    "Append" => {
                        let e = self.go(&args[1], tm)?;
                        if self.sort_of(e, tm)? != elem {
                            return Err(EncodeError::Unsupported(
                                "`Append` of a value at the wrong element sort".into(),
                            ));
                        }
                        let out = self.seq_append(target, e, sort, tm)?;
                        scalar(out)
                    }
                    // `Head(s)` is `s[1]`. TLA+ leaves it *undefined* on the
                    // empty sequence, and so does this: the array's value at
                    // index 1 is then whatever the base holds, which is an
                    // unconstrained term — some value, never a chosen one.
                    _ => {
                        let fun = self.seq_fun(target, elem, tm);
                        let one = tm.mk_int(num_bigint::BigInt::from(1));
                        scalar(tm.mk_select(fun, one))
                    }
                }
            }

            // TLC's tracing and assertion operators, encoded as `TLC.tla`
            // *defines* them rather than approximated:
            //
            //     Print(out, val)  == val
            //     PrintT(out)      == TRUE
            //     Assert(val, out) == IF val = TRUE THEN TRUE
            //                                       ELSE CHOOSE v : TRUE
            //
            // `out` is the string TLC would print. It cannot reach the value,
            // so it is deliberately not encoded: declining a specification
            // because its *message* has no encoding would be a refusal about
            // the wrong term.
            //
            // The `ELSE` branch is the whole difficulty. `CHOOSE v : TRUE` is
            // a value TLA+ leaves unspecified -- some fixed member of the
            // universe, the same one at every occurrence -- so a failing
            // `Assert` does **not** have the value `FALSE`. Encoding it as
            // `FALSE` would turn TLC's abort into a violation the
            // specification does not have; encoding it as `TRUE` would hide
            // one. It is encoded as a single shared free Boolean, which is
            // exactly what "unspecified" means and is the only reading that
            // neither manufactures nor hides a counterexample.
            //
            // The free Boolean is chosen by the solver *within the query*, so
            // a failing `Assert` under an invariant still reports a
            // `Violation` -- it means "there is a behaviour, and a reading of
            // the unspecified value, under which the invariant fails", which
            // is a genuine failure to establish it and is what TLC reports by
            // halting. In `Init` or `Next` the same freedom means the state is
            // *not* pruned, so no counterexample is deleted. That is the
            // asymmetry the rest of the encoder keeps: a `Violation` may be
            // spurious, `NoViolationWithin` stays sound.
            Kera::Opaque(name, args)
                if matches!(
                    (name.as_str(), args.len()),
                    ("Print", 2) | ("PrintT", 1) | ("Assert", 2)
                ) =>
            {
                match name.as_str() {
                    "PrintT" => scalar(tm.mk_bool(true)),
                    "Print" => self.value(&args[1], tm),
                    // `Assert`. Inference already unifies the condition with
                    // `BOOLEAN`, so `val = TRUE` is `val`; the check below is
                    // what makes that a fact rather than a belief.
                    _ => {
                        let encoded = self.value(&args[0], tm)?;
                        let Value::Scalar(cond) = &*encoded else {
                            return Err(EncodeError::Unsupported(
                                "`Assert` of a condition that is not a scalar".into(),
                            ));
                        };
                        let cond = *cond;
                        let bool_sort = tm.sorts.bool_sort;
                        if self.sort_of(cond, tm)? != bool_sort {
                            return Err(EncodeError::Unsupported(
                                "`Assert` of a condition that is not Boolean".into(),
                            ));
                        }
                        // One name for every occurrence: `CHOOSE` picks the
                        // same value each time it is written, and two
                        // independent free Booleans would let one failing
                        // `Assert` be read two ways at once.
                        let arbitrary = tm.mk_var(CHOOSE_ANY_BOOL, bool_sort);
                        scalar(tm.mk_or([cond, arbitrary]))
                    }
                }
            }

            // Standard-module operators whose meaning is arena-level.
            // Cardinality follows the set's representation too: the theory
            // decides it for a native set, the de-duplicating sum for an
            // arena one.
            Kera::Opaque(name, args)
                if matches!(
                    (name.as_str(), args.len()),
                    ("Cardinality", 1) | ("IsFiniteSet", 1)
                ) =>
            {
                let repr = self.set_repr(&args[0], tm)?;
                match (name.as_str(), repr) {
                    ("Cardinality", SetRepr::Native(set)) => scalar(tm.mk_set_card(set)),
                    ("Cardinality", SetRepr::Arena(cell)) => {
                        let t = self.shape(cardinality(&cell, tm))?;
                        scalar(t)
                    }
                    // Every set either encoding can hold is finite: the arena
                    // by construction, and the theory is the theory of
                    // *finite* sets.
                    _ => scalar(tm.mk_bool(true)),
                }
            }
            Kera::Opaque(_, _) => Err(EncodeError::Unsupported(describe(term.as_ref()))),
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
fn literal_int(term: &KeraRef) -> Option<num_bigint::BigInt> {
    match term.as_ref() {
        Kera::Int(d) => d.parse().ok(),
        Kera::Neg(a) => literal_int(a).map(|v| -v),
        _ => None,
    }
}

/// The integer a **ground** term denotes.
///
/// Used where a *candidate list* or a component index has to be built, which
/// is the one place a symbolic value cannot be carried: `a..b` needs to know
/// how many elements there are, not merely how to compare them, and a
/// heterogeneous tuple has no well-sorted answer for a dynamic index.
///
/// A literal is not enough, and assuming it was is what kept a large part of
/// the corpus out. `CONSTANT N = 4` is a *substitution*, so `0 .. N-1` becomes
/// `0 .. (4-1)` — as ground as `0 .. 3` and rejected all the same. The value
/// has to be computed, not pattern-matched.
///
/// It is computed by `nixie-tla`'s evaluator, which is the right authority
/// rather than a convenience: it is the implementation of TLA+ arithmetic that
/// `bench/tla_eval` checks against TLC, and a second constant folder here
/// would be a second semantics to keep in agreement. It fails closed — a free
/// name, an overflow or the depth limit all give `None`, which is the refusal
/// that was already there.
fn ground_int(term: &KeraRef) -> Option<num_bigint::BigInt> {
    if let Some(n) = literal_int(term) {
        return Some(n);
    }
    match nixie_tla::Evaluator::new().eval(term) {
        Ok(nixie_tla::Value::Int(i)) => Some(i.into()),
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
