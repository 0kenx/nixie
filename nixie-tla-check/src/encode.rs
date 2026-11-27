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
    /// the candidates to be knowable *before* the solver runs – so it cannot
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

/// The identity a `CHOOSE x : x \\notin S` idiom is keyed by.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum UnboundedChooseKey {
    /// A ground set: its canonical member rendering, and the element sort.
    Ground(String, SortId),
    /// A symbolic set: its term, and the element sort.
    Term(TermId, SortId),
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
pub(crate) const DEFAULT_MAX_CANDIDATES: usize = 4_096;

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
    /// graph – so a function-typed `VARIABLE` needs two SMT variables, not
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
    /// variable bound to that member – so the body is *instantiated*, not
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
    /// Constraints the caller must assert alongside whatever it encoded.
    ///
    /// A recursive function is *defined* by equations rather than built as a
    /// value – `f[k] = body(k)` at every point of its domain – so encoding one
    /// produces a term (the array) and a set of facts about it. The facts have
    /// to reach the solver, and the encoder has no way to assert them itself.
    side: Vec<TermId>,
    /// Recursive functions already defined, so a second use reuses the array
    /// rather than defining a second one.
    recfuns: HashMap<(*const Kera, u32), (TermId, TermId)>,
    /// The shared constants behind `CHOOSE x : x \\notin S` occurrences,
    /// keyed by the set's identity so the same idiom over the same set is
    /// one value everywhere – which is what `CHOOSE`'s determinism
    /// requires. A ground set keys by its canonical value (two spellings,
    /// one constant); a symbolic one by its term.
    unbounded_chooses: HashMap<UnboundedChooseKey, TermId>,
    /// Domains whose member lists this encoder learned while encoding another
    /// constraint, keyed by the domain term.
    ///
    /// `f \in [S -> T]` pins `DOMAIN f = S` as an equation, which the solver
    /// reasons about but `candidates_of` cannot read back – a domain *variable*
    /// has no member list. Remembering the members the equation was built from
    /// is exact – the equation says precisely that the domain is the set of
    /// those members – and it is what lets a later `\A a \in DOMAIN f : …`
    /// over the same function enumerate instead of decline. This is the
    /// `TestHash2.tla` shape (`ConstInit` pins `hash` with `[S -> T]`, and
    /// `IsInjective` quantifies over `DOMAIN hash`).
    known_domains: HashMap<TermId, Vec<Member>>,
    /// Candidate universes for set-valued state variables (issue #20), by
    /// variable name: the frame analysis's derivation, consulted when an
    /// opaque set-sorted variable needs a candidate list.
    frames: crate::frames::Frames,
    /// The variables whose frames failed to materialise at encode time: an
    /// element that will not encode poisons the frame, which is removed, and
    /// the variable declines exactly as it did before frames existed.
    framing: std::collections::HashSet<String>,
    /// Reverse of [`Encoder::vars`]: the variable a set-sorted term is, and
    /// the step it was read at – what the frame lookup needs.
    var_of: HashMap<TermId, (String, u32)>,
    /// The **domain** side of a function-sorted state variable: its
    /// `name$dom` set term back to `(name, step)` (issue #20, step 5). A
    /// bounded quantifier over `DOMAIN b` meets exactly this term, and the
    /// function-frame key universe instantiates it.
    dom_of: HashMap<TermId, (String, u32)>,
}

/// Whether a kernel term mentions a skolem witness, walked with an explicit
/// stack and pointer deduplication (a lowered term is a shared DAG).
fn mentions_skolem_witness(root: &KeraRef) -> bool {
    let mut seen: std::collections::HashSet<*const Kera> = std::collections::HashSet::new();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !seen.insert(Rc::as_ptr(t)) {
            continue;
        }
        if let Kera::Var(n) = t.as_ref()
            && nixie_tla::lower::is_skolem_witness(n.as_str())
        {
            return true;
        }
        stack.extend(t.as_ref().children());
    }
    false
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
            side: Vec::new(),
            recfuns: HashMap::new(),
            unbounded_chooses: HashMap::new(),
            known_domains: HashMap::new(),
            frames: crate::frames::Frames::default(),
            framing: std::collections::HashSet::new(),
            var_of: HashMap::new(),
            dom_of: HashMap::new(),
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

    /// The constraints that the terms encoded so far depend on.
    ///
    /// Must be asserted alongside them, and **every time**: these are facts
    /// about terms, not a queue. Draining them was the first attempt, and it
    /// is wrong for a reason worth recording – the bounded check builds one
    /// solver per depth, so the equations produced while encoding `Init`
    /// reached the depth-0 query and then no other, leaving the recursive
    /// function an unconstrained array from depth 1 onwards. `Rec3.tla` then
    /// reported `Fib[1] = 2`, and the trace replay caught it.
    #[must_use]
    pub fn side_constraints(&self) -> &[TermId] {
        &self.side
    }

    /// The installed frames' subjects: the set-frame names, then the
    /// function-frame names (the paranoid containment probe enumerates
    /// them).
    pub fn framed_names(&self) -> (Vec<String>, Vec<String>) {
        (
            self.frames.universe.keys().cloned().collect(),
            self.frames.fun_universe.keys().cloned().collect(),
        )
    }

    /// Test-only: remove one element from a set frame's universe,
    /// simulating a bad analysis, so the paranoid containment probe's
    /// fail-closed path can be exercised on a frame that really does miss
    /// a member.
    #[cfg(test)]
    pub(crate) fn drop_frame_element_for_test(&mut self, name: &str, n: usize) {
        if let Some(u) = self.frames.universe.get_mut(name) {
            u.remove(n);
        }
    }

    /// Install the frame analysis's candidate universes (issue #20).
    ///
    /// Called once per [`crate::bmc::Bmc`] before the depth loop; the frames
    /// are kernel terms, so they encode per step on demand.
    pub fn set_frames(&mut self, frames: crate::frames::Frames) {
        self.frames = frames;
    }

    /// Tell the encoder the sort of one kernel node.
    ///
    /// Only consulted where a term cannot sort itself; see [`Encoder`]'s
    /// `node_sorts`.
    pub fn declare_node_sort(&mut self, node: &KeraRef, sort: SortId) {
        self.node_sorts.insert(Rc::as_ptr(node), sort);
    }

    /// Declare the sort of a rigid name – a `CONSTANT`, or a parameter.
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
        let key = (name.to_string(), if self.flexible(name) { step } else { 0 });
        self.vars.get(&key).copied()
    }

    /// Whether a name gets one SMT variable **per step**: a `VARIABLE`, or a
    /// skolem witness (see [`nixie_tla::lower::is_skolem_witness`]), which
    /// stands for "some member at the step the quantifier is evaluated". A
    /// `CONSTANT` is one variable for the whole unrolling.
    fn flexible(&self, name: &str) -> bool {
        self.state.contains(name) || nixie_tla::lower::is_skolem_witness(name)
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
        let key = (name.to_string(), if self.flexible(name) { step } else { 0 });
        self.var_domains.get(&key).copied()
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
    /// A set has no sort – it is a candidate list – so anything that needs a
    /// `TermId` must go through here and gets a named refusal otherwise.
    fn go(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<TermId> {
        let v = self.value(term, tm)?;
        self.reify(&v, tm)
    }

    /// A value as a single SMT term.
    ///
    /// A tuple and a record reify into a **single-constructor datatype**, one
    /// field per component. The structural form stays primary – it is what
    /// makes a literal index and an exact `DOMAIN` possible – and this is what
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
    /// sorts, computed the same way [`crate::sorts::sort_of`] computes it –
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
    /// which is a refusal rather than an approximation – a datatype has no
    /// dynamic field access, and picking one would be a guess.
    fn field_name(&self, index: &KeraRef) -> Option<String> {
        match index.as_ref() {
            Kera::Str(name) => Some(crate::sorts::record_field(name)),
            // Anything else is tried as a tuple index, which is an integer –
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
    /// mode declines `\E x \in {1, 2, 3} : P` – a perfectly ordinary shape –
    /// purely because the theory has no comprehension.
    fn set_as_arena(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<SetCell> {
        let saved = std::mem::replace(&mut self.set_encoding, SetEncoding::Arena);
        let out = self.set(term, tm);
        self.set_encoding = saved;
        out
    }

    /// A set-valued term, in whichever representation it came out in.
    ///
    /// The two encodings are not a mode the whole problem is in – they are a
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
            // genuinely opaque one – a set variable – has none.
            Value::Scalar(t) => {
                let t = *t;
                if let Some(members) = self.known_domains.get(&t) {
                    return Ok(SetCell {
                        members: members.clone(),
                    });
                }
                // A framed set-valued variable (issue #20): its candidate
                // universe, encoded at this step, guarded by membership in
                // the **real** variable – the frame never decides presence,
                // the set theory does.
                if let Some((name, step)) = self.var_of.get(&t).cloned()
                    && self.frames.universe.contains_key(&name)
                    && let Some(members) = self.frame_members(&name, step, t, tm)
                {
                    return Ok(SetCell { members });
                }
                // A function-sorted state variable's domain term: its
                // **key** universe (issue #20, step 5), guarded by
                // membership in the real domain variable – the same
                // solver-mediated presence the set frames use.
                if let Some((name, step)) = self.dom_of.get(&t).cloned()
                    && self.frames.fun_universe.contains_key(&name)
                    && let Some(members) = self.fun_frame_members(&name, step, t, tm)
                {
                    return Ok(SetCell { members });
                }
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

    /// The universe's elements with the steps to read them at, for a
    /// quantifier (or an obligation) at `step`.
    ///
    /// An element that mentions no skolem witness is read at `step`. One
    /// that does was added by the transition of some earlier step – a
    /// witness is "some member at the step the quantifier is evaluated", one
    /// SMT variable per step, and the member it denotes stays in the set
    /// from then on – so it is read at every step `0..=step`: one too many,
    /// which only adds a candidate guarded by membership. Read at `step`
    /// alone it names the *next* transition's witness, not the member in
    /// the set: `Paxos/Consensus.tla` – `chosen' = {c}` under `\E v \in
    /// Value` – is falsified by the paranoid probe at step 1 that way.
    fn readings(&self, elems: &[KeraRef], step: u32) -> Vec<(KeraRef, u32)> {
        let mut out = Vec::with_capacity(elems.len());
        for e in elems {
            if mentions_skolem_witness(e) {
                out.extend((0..=step).map(|at| (Rc::clone(e), at)));
            } else {
                out.push((Rc::clone(e), step));
            }
        }
        out
    }

    /// The arena cell of a framed set-valued variable at one step: the
    /// universe's elements, encoded at that step, each guarded by
    /// membership in the real variable term.
    ///
    /// `None` poisons the frame (see [`Encoder::framing`]) – an element that
    /// will not encode, or a re-entrant request for the same variable, means
    /// the universe cannot be materialised here, and the variable declines
    /// exactly as it did before frames existed. Never a partial list: a
    /// missing candidate could hide a member, which is the unsound
    /// direction.
    fn frame_members(
        &mut self,
        name: &str,
        step: u32,
        var_term: TermId,
        tm: &mut TermManager,
    ) -> Option<Vec<Member>> {
        if !self.framing.insert(name.to_string()) {
            return None;
        }
        let elems = self.frames.universe.get(name)?.clone();
        let saved = std::mem::replace(&mut self.step, step);
        let readings = self.readings(&elems, step);
        let mut members = Vec::with_capacity(readings.len());
        let mut ok = true;
        // The variable's element sort – the merged row's datatype, which has
        // every tag the universe's elements carry. A one-tag `Variant`
        // element is built **at this sort**: left at its own, the universe
        // would hold members of several one-tag datatypes that the set's
        // element sort cannot hold.
        let elem_sort = self.sort_of(var_term, tm).ok().and_then(|sort| {
            match tm.sorts.get(sort).map(|s| s.kind.clone()) {
                Some(nixie_core::SortKind::Set(e)) => Some(e),
                _ => None,
            }
        });
        for (e, at) in &readings {
            self.step = *at;
            let v = match (e.as_ref(), elem_sort) {
                (Kera::Variant { tag, value }, Some(target)) => {
                    let Ok(payload) = self.value(value, tm) else {
                        ok = false;
                        break;
                    };
                    let Some(payload_sort) = variant_payload_sort(target, tag, tm) else {
                        ok = false;
                        break;
                    };
                    let Ok(reified) = self.reify(&payload, tm) else {
                        ok = false;
                        break;
                    };
                    if self.sort_of(reified, tm).ok() != Some(payload_sort) {
                        ok = false;
                        break;
                    }
                    Rc::new(Value::Scalar(tm.mk_dt_constructor(
                        &format!("@v_{tag}"),
                        [reified],
                        target,
                    )))
                }
                _ => match self.value(e, tm) {
                    Ok(v) => v,
                    Err(_) => {
                        ok = false;
                        break;
                    }
                },
            };
            let present = match &*v {
                Value::Scalar(e_term) => tm.mk_set_member(*e_term, var_term),
                structural => {
                    let v = Rc::new(structural.clone());
                    match self.reify(&v, tm) {
                        Ok(r) => tm.mk_set_member(r, var_term),
                        Err(_) => {
                            ok = false;
                            break;
                        }
                    }
                }
            };
            members.push(Member { value: v, present });
        }
        self.step = saved;
        self.framing.remove(name);
        ok.then_some(members)
    }

    /// The candidate universe of a framed variable at one step, as **one
    /// native set term** – every element unconditionally present (issue #20,
    /// step 6). This is the `U_k` of the containment obligation, not the
    /// guarded-members form a quantifier instantiates over: `v@k \subseteq
    /// U_k` is the promise the frame analysis makes, and the paranoid probe
    /// asks the solver to falsify exactly it.
    ///
    /// `None` when an element will not encode at this step – the obligation
    /// cannot be stated, and the caller fails closed.
    pub fn universe_set_at(
        &mut self,
        name: &str,
        step: u32,
        fun: bool,
        tm: &mut TermManager,
    ) -> Option<TermId> {
        let universe = if fun {
            self.frames.fun_universe.get(name)?.clone()
        } else {
            self.frames.universe.get(name)?.clone()
        };
        let saved = std::mem::replace(&mut self.step, step);
        let readings = self.readings(&universe, step);
        let mut members = Vec::with_capacity(readings.len());
        let mut ok = true;
        for (e, at) in &readings {
            self.step = *at;
            let v = match self.value(e, tm) {
                Ok(v) => v,
                Err(_) => {
                    ok = false;
                    break;
                }
            };
            let scalar = match &*v {
                Value::Scalar(t) => *t,
                structural => {
                    let v = Rc::new(structural.clone());
                    match self.reify(&v, tm) {
                        Ok(r) => r,
                        Err(_) => {
                            ok = false;
                            break;
                        }
                    }
                }
            };
            members.push(Member {
                value: Rc::new(Value::Scalar(scalar)),
                present: tm.mk_bool(true),
            });
        }
        self.step = saved;
        if !ok || members.is_empty() {
            return None;
        }
        // The containing term is the set variable for a set frame and the
        // **domain** variable for a function frame – the array is not a
        // set and has no element sort.
        let holder = if fun {
            self.domain_at(name, step)?
        } else {
            self.var_at(name, step)?
        };
        let elem = self.element_sort_of(holder, tm).ok()?;
        self.native_set_of(&members, elem, tm).ok()
    }

    /// The arena cell of a function-sorted state variable's domain at one
    /// step: the key universe's elements, encoded at that step, each guarded
    /// by membership in the **real** domain term (issue #20, step 5).
    ///
    /// `None` poisons the frame, exactly as [`Encoder::frame_members`] does:
    /// never a partial list – a missing key could hide a member, which is
    /// the unsound direction.
    fn fun_frame_members(
        &mut self,
        name: &str,
        step: u32,
        dom_term: TermId,
        tm: &mut TermManager,
    ) -> Option<Vec<Member>> {
        if !self.framing.insert(format!("{name}$dom")) {
            return None;
        }
        let elems = self.frames.fun_universe.get(name)?.clone();
        let saved = std::mem::replace(&mut self.step, step);
        let readings = self.readings(&elems, step);
        let mut members = Vec::with_capacity(readings.len());
        let mut ok = true;
        for (e, at) in &readings {
            self.step = *at;
            let v = match self.value(e, tm) {
                Ok(v) => v,
                Err(_) => {
                    ok = false;
                    break;
                }
            };
            let present = match &*v {
                Value::Scalar(e_term) => tm.mk_set_member(*e_term, dom_term),
                structural => {
                    let v = Rc::new(structural.clone());
                    match self.reify(&v, tm) {
                        Ok(r) => tm.mk_set_member(r, dom_term),
                        Err(_) => {
                            ok = false;
                            break;
                        }
                    }
                }
            };
            members.push(Member { value: v, present });
        }
        self.step = saved;
        self.framing.remove(&format!("{name}$dom"));
        ok.then_some(members)
    }

    /// Read an arena candidate list back off a set-sorted term.
    ///
    /// The inverse of [`Encoder::native_set_of`], and the reason the hybrid
    /// works at all: a bounded quantifier is *instantiated* per candidate, so
    /// `\A i \in DOMAIN f : P(i)` needs a candidate list for a domain that
    /// is, by now, a set-sorted term. Every set this encoder builds is a union
    /// of (conditional) singletons – the normal form CVC5 uses for a set
    /// constant – so the list is recoverable exactly.
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
    /// for a list [`Encoder::candidates_of`] built – every one of those comes
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

    /// The components of a **literal** sequence, for the right-hand side of
    /// `\o`.
    ///
    /// Read off the kernel term where it is a tuple literal, so it works
    /// whichever shape the literal encoded to – and refused otherwise, since a
    /// symbolic sequence has no statically known number of elements to append.
    fn seq_items(&mut self, term: &KeraRef, tm: &mut TermManager) -> Result<Vec<Rc<Value>>> {
        if let Kera::Tuple(xs) = term.as_ref() {
            let mut out = Vec::with_capacity(xs.len());
            for x in xs {
                out.push(self.value(x, tm)?);
            }
            return Ok(out);
        }
        match &*self.value(term, tm)? {
            Value::Tuple(items) => Ok(items.clone()),
            _ => Err(EncodeError::Unsupported(
                "`\\o` with a right side that is not a literal sequence".into(),
            )),
        }
    }

    /// Two values as sequence terms, when exactly one of them is a structural
    /// tuple and the other is a sequence.
    ///
    /// `None` when the pair is not that mixture, which leaves every other
    /// comparison exactly as it was.
    fn seq_pair(
        &mut self,
        x: &Rc<Value>,
        y: &Rc<Value>,
        tm: &mut TermManager,
    ) -> Result<Option<(TermId, TermId)>> {
        let seq_of = |this: &Self, v: &Rc<Value>, tm: &TermManager| match &**v {
            Value::Scalar(t) => this
                .sort_of(*t, tm)
                .ok()
                .filter(|s| crate::sorts::seq_element(*s, tm).is_some())
                .map(|s| (*t, s)),
            _ => None,
        };
        let (tuple, seq, sort, flipped) = match (seq_of(self, x, tm), seq_of(self, y, tm)) {
            (None, Some((t, sort))) if matches!(&**x, Value::Tuple(_)) => (x, t, sort, false),
            (Some((t, sort)), None) if matches!(&**y, Value::Tuple(_)) => (y, t, sort, true),
            _ => return Ok(None),
        };
        let Value::Tuple(items) = &**tuple else {
            return Ok(None);
        };
        let Some(elem) = crate::sorts::seq_element(sort, tm) else {
            return Ok(None);
        };
        let mut built = self.empty_seq(sort, elem, tm)?;
        for item in items.clone() {
            let e = self.reify(&item, tm)?;
            built = self.seq_append(built, e, sort, tm)?;
        }
        Ok(Some(if flipped { (seq, built) } else { (built, seq) }))
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
        Ok(tm.mk_dt_constructor(&name, [zero, zero, base], sort))
    }

    /// `Len(s)`.
    fn seq_len(&self, seq: TermId, tm: &mut TermManager) -> TermId {
        let int = tm.sorts.int_sort;
        tm.mk_dt_selector(crate::sorts::SEQ_LEN, seq, int)
    }

    /// Where `s`'s window starts in its graph: `s[i]` is `fun[off + i]`.
    fn seq_off(&self, seq: TermId, tm: &mut TermManager) -> TermId {
        let int = tm.sorts.int_sort;
        tm.mk_dt_selector(crate::sorts::SEQ_OFF, seq, int)
    }

    /// `s[i]`, for a sequence in the datatype shape.
    fn seq_at(
        &mut self,
        seq: TermId,
        index: TermId,
        sort: SortId,
        tm: &mut TermManager,
    ) -> Result<TermId> {
        let Some(elem) = crate::sorts::seq_element(sort, tm) else {
            return Err(EncodeError::ShapeClash);
        };
        let off = self.seq_off(seq, tm);
        let fun = self.seq_fun(seq, elem, tm);
        let at = tm.mk_add([off, index]);
        Ok(tm.mk_select(fun, at))
    }

    /// The graph of `s`, as an array from `1..`.
    fn seq_fun(&self, seq: TermId, elem: SortId, tm: &mut TermManager) -> TermId {
        let int = tm.sorts.int_sort;
        let arr = tm.sorts.array(int, elem);
        tm.mk_dt_selector(crate::sorts::SEQ_FUN, seq, arr)
    }

    /// `Append(s, e)` – `e` written one past the end, and the length raised.
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
        let off = self.seq_off(seq, tm);
        let len = self.seq_len(seq, tm);
        let fun = self.seq_fun(seq, elem, tm);
        let one = tm.mk_int(num_bigint::BigInt::from(1));
        let next = tm.mk_add([len, one]);
        // One past the end *of the window*, not of the array.
        let at = tm.mk_add([off, next]);
        let stored = tm.mk_store(fun, at, e);
        let name = tm
            .sorts
            .datatype_name(sort)
            .ok_or(EncodeError::ShapeClash)?
            .to_string();
        Ok(tm.mk_dt_constructor(&name, [off, next, stored], sort))
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
    /// build the empty set at the wrong sort – a different value.
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
            let k = match &*m.value {
                Value::Scalar(k) => *k,
                // A structural member (a tuple, a record) is not stuck: it
                // reifies to the datatype the sorts module already gives
                // it – the same reification the function-constructor arm
                // applies to its keys, and what lets `SetAsFun`'s `CHOOSE`
                // run over a set of pairs. Only genuinely unscalarisable
                // members (a set or function *inside* the domain) still
                // refuse, through `reify`'s own error.
                _ => self.reify(&m.value, tm)?,
            };
            if self.sort_of(k, tm)? != element {
                return Err(EncodeError::Unsupported(
                    "a function domain whose members do not share one sort".into(),
                ));
            }
            let single = tm.mk_set_singleton(k);
            // A candidate that may not be present contributes conditionally.
            // `ite` at a set sort is decided by the set theory, so this needs
            // no case split of its own – but a *literally true* guard is
            // folded away: the theories reason about `a ∪ b` far better than
            // about `ite(true, a, {}) ∪ b`, and `CHOOSE x \in S : TRUE`'s
            // filter is the motivating all-true case.
            let piece = if matches!(m.present, t if matches!(tm.get(t).map(|d| d.kind.clone()), Some(nixie_core::TermKind::True)))
            {
                single
            } else {
                tm.mk_ite(m.present, single, empty)
            };
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
    /// encodings depending on the set – a standard infinite set, a native set
    /// term, an arena candidate list – and reproducing the choice at a second
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
            // *value* rather than in a membership test – `s = Nat`, say. It
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
                // A rigid name is the same variable at every step; a
                // `VARIABLE` – and a skolem witness, which is "some member"
                // anew at every step the quantifier is evaluated – get one
                // per step.
                let flexible = self.flexible(n.as_str());
                let step = if flexible { self.step } else { 0 };
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
                let smt_name = if flexible {
                    format!("{n}@{step}")
                } else {
                    n.0.clone()
                };
                let t = tm.mk_var(&smt_name, sort);
                self.vars.insert(key.clone(), t);
                self.var_of.insert(t, (n.0.clone(), step));
                // A function-sorted name gets its domain as a second variable.
                // Without it the name would be a bare graph, and `f = g`, and
                // `DOMAIN f`, would both be answered by the array alone – the
                // first unsoundly (see `arena::eq_values`), the second not at
                // all.
                if let Some(nixie_core::SortKind::Array { domain, .. }) =
                    tm.sorts.get(sort).map(|s| s.kind.clone())
                {
                    let set_sort = tm.sorts.set(domain);
                    let d = tm.mk_var(&format!("{smt_name}$dom"), set_sort);
                    self.var_domains.insert(key, d);
                    self.dom_of.insert(d, (n.0.clone(), step));
                    return Ok(Rc::new(Value::Fun {
                        domain: d,
                        array: t,
                    }));
                }
                scalar(t)
            }
            // `x'` is `x` read one step later. Priming distributes over
            // everything in TLA+ – `(x + 1)'` is `x' + 1` – so raising the step
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
            // Two sets may arrive in different representations – `DOMAIN r` is
            // an arena candidate list while `{"a", "b"}` in native mode is a
            // set term – so they are promoted to one first, the same way a
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
                // A **sequence** compared with a tuple. `<<>>` is both, and
                // which one it encoded to depends on the sort inference gave
                // that literal – so `h = <<>>` can have a sequence on one side
                // and a structural tuple on the other. Comparing those as
                // different shapes would report two TLA+-equal values unequal,
                // which is a counterexample the specification does not have.
                //
                // Promoted rather than declined, the same way a mixed pair of
                // set representations is.
                if let Some((p, q)) = self.seq_pair(&x, &y, tm)? {
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
            // declining – and it is only *statable* because the function value
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
                // Remember that this domain's members are exactly `set`'s, so
                // a later `DOMAIN f` (a quantifier, a fold) enumerates instead
                // of declining. See `known_domains`.
                self.known_domains
                    .entry(domain)
                    .or_insert_with(|| base.members.clone());
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
                in_standard(x, name, tm)
                    .map(|t| Rc::new(Value::Scalar(t)))
                    .ok_or_else(|| EncodeError::Unsupported(format!("`{name}` as a set")))
            }
            // `x \in a..b` is `a <= x /\ x <= b` – Apalache's own rewrite
            // (`ExprOptimizer`), and the difference between a range with a
            // symbolic bound being checkable and not: the arena needs ground
            // ends to enumerate, the comparison needs nothing. This is the
            // single largest blocker class in the corpus ("`..` with a
            // non-literal upper bound", 21+ specifications).
            Kera::In(x, s) if matches!(s.as_ref(), Kera::Range(_, _)) => {
                let Kera::Range(lo, hi) = s.as_ref() else {
                    return Err(EncodeError::Unsupported("..".into()));
                };
                let e = self.go(x, tm)?;
                let l = self.go(lo, tm)?;
                let h = self.go(hi, tm)?;
                let ge = tm.mk_ge(e, l);
                let le = tm.mk_le(e, h);
                scalar(tm.mk_and([ge, le]))
            }
            // `r \in [f_1 : S_1, …, f_n : S_n]` is the conjunction of the
            // field memberships – never an enumeration of the cartesian
            // product, which is what the arena path would need. Each field's
            // membership goes back through the ordinary dispatch, so a range
            // or a standard set as `S_i` composes (`SetMembershipSimplifier`'s
            // structural rule, the same one `Nat` already takes).
            Kera::In(r, s) if matches!(s.as_ref(), Kera::RecordSet(_)) => {
                let Kera::RecordSet(fs) = s.as_ref() else {
                    return Err(EncodeError::Unsupported("a record set".into()));
                };
                let mut conj = Vec::with_capacity(fs.len());
                for (name, set) in fs {
                    let field: KeraRef =
                        Rc::new(Kera::FunApp(Rc::clone(r), Rc::new(Kera::Str(name.clone()))));
                    let v = self.value(&field, tm)?;
                    conj.push(self.membership(v, set, tm)?);
                }
                scalar(tm.mk_and(conj))
            }
            // `t \in S_1 \\X … \\X S_n` is likewise componentwise.
            Kera::In(t, s) if matches!(s.as_ref(), Kera::Times(_)) => {
                let Kera::Times(sets) = s.as_ref() else {
                    return Err(EncodeError::Unsupported("\\X".into()));
                };
                let mut conj = Vec::with_capacity(sets.len());
                for (i, set) in sets.iter().enumerate() {
                    let index = Rc::new(Kera::Int((i + 1).to_string()));
                    let field: KeraRef = Rc::new(Kera::FunApp(Rc::clone(t), index));
                    let v = self.value(&field, tm)?;
                    conj.push(self.membership(v, set, tm)?);
                }
                scalar(tm.mk_and(conj))
            }
            // `s \in Seq(S)`: pointwise, `\A i \in 1..Len(s) : s[i] \in S`,
            // enumerated when the elements are statically known – a literal
            // tuple – and declined otherwise (a symbolic sequence's length
            // has no enumeration until the frames work lands). Never a
            // blanket TRUE for a "type-defining" `S`: `<<1, -2>> \notin
            // Seq(Nat)` is a fact about values, and the type checker only
            // ever knew the elements were `Int`.
            Kera::In(a, s) if matches!(s.as_ref(), Kera::Opaque(n, xs) if n.as_str() == "Seq" && xs.len() == 1) =>
            {
                let Kera::Opaque(_, xs) = s.as_ref() else {
                    return Err(EncodeError::Unsupported("Seq".into()));
                };
                let inner = Rc::clone(&xs[0]);
                // A literal tuple's components are the whole membership
                // question; each goes through the ordinary `\in` dispatch,
                // so `Nat`, ranges and set terms all compose.
                let parts: Option<Vec<Rc<Value>>> = match a.as_ref() {
                    Kera::Tuple(ks) => {
                        let mut out = Vec::with_capacity(ks.len());
                        for k in ks {
                            out.push(self.value(k, tm)?);
                        }
                        Some(out)
                    }
                    _ => match &*self.value(a, tm)? {
                        Value::Tuple(vs) => Some(vs.clone()),
                        _ => None,
                    },
                };
                match parts {
                    Some(ps) => {
                        let mut conj = Vec::with_capacity(ps.len());
                        for p in ps {
                            conj.push(self.membership(p, &inner, tm)?);
                        }
                        // Empty is `TRUE`: the empty sequence is in every
                        // `Seq(S)`, elements or no elements.
                        scalar(tm.mk_and(conj))
                    }
                    None => Err(EncodeError::Unsupported(
                        "`\\in Seq(S)` over a sequence whose elements are not \
                         statically known (a symbolic length has no enumeration)"
                            .into(),
                    )),
                }
            }
            // `x \in SUBSET T` is subset-or-equal, decided by the set theory
            // – no 2^n expansion, no candidate list. This is Apalache's
            // `PowSetCtorRule` in substance: keep the powerset symbolic and
            // decide membership structurally.
            Kera::In(a, s) if matches!(s.as_ref(), Kera::Powerset(_)) => {
                let Kera::Powerset(base) = s.as_ref() else {
                    return Err(EncodeError::Unsupported("SUBSET".into()));
                };
                let elem = self.go(a, tm)?;
                let inner = match self.set_repr(base, tm)? {
                    SetRepr::Native(t) => t,
                    SetRepr::Arena(cell) => {
                        // The base's element sort is the sort of its members;
                        // when there are none, the element being tested is a
                        // set whose element sort is the one to use (a subset
                        // of the empty set is `{}` at that sort). Anything
                        // else has no sort to build the empty base at, and is
                        // declined rather than guessed.
                        let e = match cell.members.first().map(|m| &*m.value) {
                            Some(Value::Scalar(k)) => self.sort_of(*k, tm)?,
                            _ => {
                                let s = self.sort_of(elem, tm)?;
                                match tm.sorts.get(s).map(|x| x.kind.clone()) {
                                    Some(nixie_core::SortKind::Set(el)) => el,
                                    _ => {
                                        return Err(EncodeError::Unsupported(
                                            "SUBSET of a base with no element sort".into(),
                                        ));
                                    }
                                }
                            }
                        };
                        self.native_set_of(&cell.members, e, tm)?
                    }
                };
                scalar(tm.mk_set_subset(elem, inner))
            }
            // Membership in a binary set operation whose one side is a
            // standard **infinite** set is encoded structurally on that side,
            // because the standard side has no finite representation to
            // enumerate: `N \in Nat \ {0}` is `N >= 0 /\ N /= 0`, not a
            // candidate list. Without this, an `ASSUME` pinning a constant
            // with exactly this shape cannot be encoded, is dropped, and the
            // search runs with an arbitrary `N` – the `EWD840.tla` shape.
            //
            // The finite side goes back through the ordinary `\in` dispatch
            // (by re-encoding a synthesized `In` node), so every other
            // membership encoding – native, arena, structural – applies to it
            // unchanged. A recursion here is always on the *non-standard*
            // side, so it cannot loop.
            Kera::In(a, s) if bin_standard(s).is_some() => {
                let (op, std_first, x, y) = bin_standard(s).expect("checked above");
                // `elem` as an SMT term, needed for the structural side; a
                // structural membership only exists for scalar elements.
                let mut side = |t: &KeraRef, structural: bool| -> Result<TermId> {
                    if structural {
                        let name = standard_set(t).expect("caller checked");
                        let e = self.go(a, tm)?;
                        in_standard(e, name, tm)
                            .ok_or_else(|| EncodeError::Unsupported(format!("`{name}` as a set")))
                    } else {
                        let node: KeraRef = Rc::new(Kera::In(Rc::clone(a), Rc::clone(t)));
                        match &*self.value(&node, tm)? {
                            Value::Scalar(v) => Ok(*v),
                            _ => Err(EncodeError::Unsupported(
                                "a membership test that did not produce a Boolean".into(),
                            )),
                        }
                    }
                };
                let lhs = side(x, std_first);
                let rhs = side(y, !std_first);
                let (l, r) = (lhs?, rhs?);
                let combined = match op {
                    SetOp::Union => tm.mk_or([l, r]),
                    SetOp::Intersect => tm.mk_and([l, r]),
                    // `a \ b`: in `a` and not in `b`.
                    SetOp::Difference => {
                        if std_first {
                            let not_r = tm.mk_not(r);
                            tm.mk_and([l, not_r])
                        } else {
                            let not_l = tm.mk_not(l);
                            tm.mk_and([not_l, r])
                        }
                    }
                };
                scalar(combined)
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

            // ======== sets ========
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
            // would silently check a different specification – but ground is
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
            // A comprehension in native mode is declined **only when its base
            // set has no candidate list**. When the base is enumerable – a
            // literal, a range, a set this encoder built, or a framed state
            // set – the filter/map is built as an arena cell and converted
            // back with `native_set_of`, exactly as a bounded quantifier
            // already crosses that line through `set_as_arena`. Declining
            // the enumerable case was what blocked `MustardWatch.tla`'s
            // `{t \in Threads : …}` in `Init`, where the base is a literal.
            Kera::Filter { var, set, pred } if self.set_encoding == SetEncoding::Native => {
                // A filter over an infinite **integer** set whose predicate
                // bounds the binder from both sides by ground literals —
                // `{v \in Int : v >= 0 /\ v <= 50}`, Apalache's `Range`
                // idiom in its liveness cells — has exactly the ground range
                // for members. The predicate is still evaluated per candidate
                // below (`present`), so a bound read wrong could only ever
                // *offer* a non-member, never drop one; and no two-sided
                // ground bound means no candidates, the honest refusal.
                // (only `Int`/`Nat` bases: an infinite set is the case the arena cannot enumerate)
                let base = match nixie_tla::kera::bounded_int_range(
                    var,
                    pred,
                    matches!(set.as_ref(), Kera::Var(n) if n.as_str() == "Nat"),
                ) {
                    Some((lo, hi)) => {
                        if hi - lo > self.max_candidates as i128 {
                            return Err(EncodeError::NotEnumerable(
                                "an integer filter whose bounds exceed the candidate budget"
                                    .to_string(),
                            ));
                        }
                        let mut members = Vec::with_capacity((hi - lo + 1) as usize);
                        for v in lo..=hi {
                            members.push(Member {
                                value: Rc::new(Value::Scalar(tm.mk_int(v))),
                                present: tm.mk_bool(true),
                            });
                        }
                        SetCell { members }
                    }
                    None => self.set_as_arena(set, tm)?,
                };
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
            Kera::Map { var, set, expr } if self.set_encoding == SetEncoding::Native => {
                let base = self.set_as_arena(set, tm)?;
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
            // `SUBSET S` as a **value**: the full 2^n expansion over the
            // base's candidate list, bounded by `max_candidates` – the same
            // budget that guards every other blow-up, and for the same
            // reason: 2^n turns a large set into an out-of-memory kill
            // where the budget turns it into a named refusal. Members are
            // conditional exactly when the base's candidates are.
            //
            // Only the *value* needs the expansion. Membership took the
            // structural shortcut above, so a `SUBSET` that is only ever
            // tested never enumerates at all.
            Kera::Powerset(base) => {
                let cell = self.set(base, tm)?;
                // Bit-parallel over the candidate list: `out` starts as the
                // one empty-subset candidate and each base member doubles it.
                let mut out = vec![Member {
                    value: Rc::new(Value::Set(SetCell {
                        members: Vec::new(),
                    })),
                    present: tm.mk_bool(true),
                }];
                for m in &cell.members {
                    if out.len() > self.max_candidates {
                        return Err(EncodeError::TooManyCandidates {
                            limit: self.max_candidates,
                        });
                    }
                    let mut next = Vec::with_capacity(out.len() * 2);
                    for sub in &out {
                        // Without this member.
                        next.push(Member {
                            value: Rc::clone(&sub.value),
                            present: sub.present,
                        });
                        // With it – its own presence guards the choice.
                        let Value::Set(inner) = &*sub.value else {
                            return Err(EncodeError::ShapeClash);
                        };
                        let mut members = inner.members.clone();
                        members.push(Member {
                            value: Rc::clone(&m.value),
                            present: m.present,
                        });
                        next.push(Member {
                            value: Rc::new(Value::Set(SetCell { members })),
                            present: tm.mk_and([sub.present, m.present]),
                        });
                    }
                    out = next;
                }
                self.mk_set(out)
            }
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

            // ======== tuples and records ========
            // Structural, not an SMT value: TLA+ tuples and records are
            // heterogeneous, so flattening them into an array would force
            // every component to one sort.
            // `<<…>>` is a tuple *and* a sequence – TLA+ does not distinguish
            // them – so which one it encodes to is decided by the sort the
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
            // ======== variants (issue #17) ========
            // `Variant("Tag", v)`: the datatype constructor application.
            // The sort is the row's datatype, supplied by inference (the
            // node cannot sort itself: a one-tag node does not know the
            // union it flows into), and the payload is reified to the
            // constructor's payload sort – a structural payload (a record)
            // becomes the datatype term it is.
            Kera::Variant { tag, value } => {
                let v = self.value(value, tm)?;
                let sort = self
                    .node_sorts
                    .get(&Rc::as_ptr(term))
                    .copied()
                    .ok_or_else(|| {
                        EncodeError::Unsupported(
                            "`Variant` whose variant row has no sort yet".into(),
                        )
                    })?;
                let payload_sort = variant_payload_sort(sort, tag, tm).ok_or_else(|| {
                    EncodeError::Unsupported(format!(
                        "`Variant(\"{tag}\")` on a row that has no such tag"
                    ))
                })?;
                let payload = self.reify(&v, tm)?;
                if self.sort_of(payload, tm)? != payload_sort {
                    return Err(EncodeError::Unsupported(format!(
                        "`Variant(\"{tag}\")` whose payload is not at the tag's sort"
                    )));
                }
                scalar(tm.mk_dt_constructor(&format!("@v_{tag}"), [payload], sort))
            }
            // `VariantTag(v)`: a chain of testers, one per constructor of the
            // row's datatype. The final arm is the last tag – the chain
            // covers every constructor, so the solver never reaches it.
            Kera::VariantTag(v) => {
                let target = self.value(v, tm)?;
                let Value::Scalar(t) = &*target else {
                    return Err(EncodeError::Unsupported(
                        "`VariantTag` of a value that is not a variant".into(),
                    ));
                };
                let t = *t;
                let sort = self.sort_of(t, tm)?;
                let tags = variant_tags(sort, tm).ok_or_else(|| {
                    EncodeError::Unsupported(
                        "`VariantTag` of a value whose sort is not a variant row".into(),
                    )
                })?;
                let [first, rest @ ..] = tags.as_slice() else {
                    return Err(EncodeError::Unsupported(
                        "`VariantTag` of an empty variant row".into(),
                    ));
                };
                let mut out = tm.mk_string_lit(first);
                for tag in rest {
                    let tester = tm.mk_dt_tester(&format!("@v_{tag}"), t);
                    let lit = tm.mk_string_lit(tag);
                    out = tm.mk_ite(tester, lit, out);
                }
                scalar(out)
            }
            // `VariantGet{tag, v, or_else}`: the payload selector. On the
            // wrong tag, the selector is an SMT datatype accessor off its
            // own constructor – underspecified by the theory, which is
            // exactly the "fresh unconstrained value, never a fixed
            // default" the issue asks for. `or_else` turns it into the
            // given value under a tester.
            Kera::VariantGet {
                tag,
                value,
                or_else,
            } => {
                let target = self.value(value, tm)?;
                let Value::Scalar(t) = &*target else {
                    return Err(EncodeError::Unsupported(
                        "`VariantGet` of a value that is not a variant".into(),
                    ));
                };
                let t = *t;
                let sort = self.sort_of(t, tm)?;
                let payload_sort = variant_payload_sort(sort, tag, tm).ok_or_else(|| {
                    EncodeError::Unsupported(format!(
                        "`VariantGet` on a variant row without the tag `{tag}`"
                    ))
                })?;
                let selected = tm.mk_dt_selector("@vp", t, payload_sort);
                let Some(e) = or_else else {
                    return scalar(selected);
                };
                let ev = self.value(e, tm)?;
                let eterm = self.reify(&ev, tm)?;
                if self.sort_of(eterm, tm)? != payload_sort {
                    return Err(EncodeError::Unsupported(
                        "`VariantGetOrElse` whose default is not at the tag's sort".into(),
                    ));
                }
                let tester = tm.mk_dt_tester(&format!("@v_{tag}"), t);
                scalar(tm.mk_ite(tester, selected, eterm))
            }
            // `VariantFilter("Tag", S)`: the candidates of `S`, kept under
            // the tag's tester and mapped to their payloads. A filter and a
            // map in one pass – exact, because the tester decides and the
            // payload selector reads the same constructor.
            Kera::VariantFilter { tag, set } => {
                let cell = self.set(set, tm)?;
                let mut members = Vec::with_capacity(cell.members.len());
                for m in &cell.members {
                    let Value::Scalar(t) = &*m.value else {
                        return Err(EncodeError::Unsupported(
                            "`VariantFilter` over a non-variant member".into(),
                        ));
                    };
                    let t = *t;
                    let sort = self.sort_of(t, tm)?;
                    let payload_sort = variant_payload_sort(sort, tag, tm).ok_or_else(|| {
                        EncodeError::Unsupported(format!(
                            "`VariantFilter` on a variant row without the tag `{tag}`"
                        ))
                    })?;
                    let tester = tm.mk_dt_tester(&format!("@v_{tag}"), t);
                    let present = tm.mk_and([m.present, tester]);
                    members.push(Member {
                        value: scalar_clone(tm.mk_dt_selector("@vp", t, payload_sort)),
                        present,
                    });
                }
                self.mk_set(members)
            }
            // `[a : S, b : T]` is the set of records with one field drawn from
            // each set – a cartesian product over the field sets.
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

            // ======== binders over a set ========
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
                    // `^` with a **ground** exponent is a product – exact,
                    // linear once unfolded, and the only form with a value
                    // the replay can confirm. A negative exponent is
                    // undefined in TLA+ and refused; a symbolic one is
                    // non-linear and declined by name rather than
                    // approximated by an uninterpreted function whose models
                    // nothing could replay.
                    ArithOp::Exp => {
                        let Some(n) = ground_int(b) else {
                            return Err(EncodeError::Unsupported(
                                "`^` with a symbolic exponent (non-linear)".into(),
                            ));
                        };
                        if n < num_bigint::BigInt::ZERO {
                            return Err(EncodeError::Unsupported(
                                "`^` with a negative exponent (undefined in TLA+)".into(),
                            ));
                        }
                        let Ok(exp) = u32::try_from(&n) else {
                            return Err(EncodeError::Unsupported(
                                "`^` with an exponent too large to unfold".into(),
                            ));
                        };
                        if exp > 64 {
                            return Err(EncodeError::Unsupported(
                                "`^` with an exponent above the unfolding budget of 64".into(),
                            ));
                        }
                        if exp == 0 {
                            tm.mk_int(1)
                        } else {
                            let mut acc = x;
                            for _ in 1..exp {
                                acc = tm.mk_mul([acc, x]);
                            }
                            acc
                        }
                    }
                })
            }
            // `[x \in S |-> e]` is the only place a TLA+ function is written
            // down, and it is where both halves of a function value come from:
            // the domain is `S`, and the graph is `e` evaluated at each of its
            // members.
            //
            // The domain is enumerated by the arena – `S` is written in the
            // specification, so its candidates are exactly what the arena
            // computes – and then turned into one set-sorted term, so the
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
                            if std::env::var_os("NIXIE_TLA_DEBUG_SORT").is_some() {
                                eprintln!("[fundef-sort-miss2] ptr={:?}", Rc::as_ptr(term));
                            }
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
                    // range sort – the generic mux pass owns that, while an
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
            // `f[x \in S] == … f[…] …`.
            //
            // Over a **finite** domain a recursive function needs no fixpoint
            // and no quantifier: it is an array, plus one equation per point
            // of the domain saying what the function is there. The body is
            // encoded once per point with the function itself in scope, so
            // `f[k-1]` inside it is a `select` on the very array being
            // defined – the knot ties itself.
            //
            // The equations cannot be part of the value, because a value is a
            // term and these are facts; they go out through
            // [`Encoder::take_side_constraints`], and a caller that does not
            // assert them is checking a specification whose recursive
            // functions are arbitrary.
            //
            // Defined **once** per (node, step). A second use of the same
            // function must be the same array, or `f[1] = f[1]` could be
            // false.
            Kera::RecFun {
                name,
                var,
                set,
                body,
            } => {
                let key = (Rc::as_ptr(term), self.step);
                if let Some((domain, array)) = self.recfuns.get(&key).copied() {
                    return Ok(Rc::new(Value::Fun { domain, array }));
                }
                // The sort has to be known before the body is encoded, and the
                // body is the only thing that would reveal it – so it comes
                // from the caller's type inference, exactly as an empty set's
                // does.
                let Some(sort) = self.node_sorts.get(&Rc::as_ptr(term)).copied() else {
                    return Err(EncodeError::Unsupported(
                        "a recursive function whose sort was not supplied".into(),
                    ));
                };
                let Some(nixie_core::SortKind::Array { domain: dom, .. }) =
                    tm.sorts.get(sort).map(|s| s.kind.clone())
                else {
                    return Err(EncodeError::Unsupported(
                        "a recursive function whose declared sort is not an array".into(),
                    ));
                };
                let cell = self.set(set, tm)?;
                let members = cell.members.clone();
                let domain = self.native_set_of(&members, dom, tm)?;
                let array = tm.mk_var(&format!("@recfun_{}_{}", name, self.step), sort);
                self.recfuns.insert(key, (domain, array));
                let me = Rc::new(Value::Fun { domain, array });
                for m in &members {
                    let Value::Scalar(k) = &*m.value else {
                        return Err(EncodeError::Unsupported(
                            "a recursive function over a domain whose members have no sort".into(),
                        ));
                    };
                    let k = *k;
                    let at = self.with_two_bound(
                        name,
                        Rc::clone(&me),
                        var,
                        Rc::clone(&m.value),
                        body,
                        tm,
                    )?;
                    let value = self.reify(&at, tm)?;
                    let here = tm.mk_select(array, k);
                    let eq = tm.mk_eq(here, value);
                    // A candidate that is not in the domain says nothing about
                    // the function, so the equation is guarded by its
                    // presence: an arena candidate list over-approximates.
                    let guarded = tm.mk_implies(m.present, eq);
                    self.side.push(guarded);
                }
                Ok(me)
            }
            Kera::FunApp(f, i) => {
                let target = self.value(f, tm)?;
                // A **sequence** is indexed through its window: `s[i]` is
                // `fun[off + i]`, and the index need not be a literal – which
                // is the point, since `events[Len(events)]` is how a
                // specification reads the last thing that happened.
                if let Value::Scalar(seq) = &*target
                    && let Ok(sort) = self.sort_of(*seq, tm)
                    && crate::sorts::seq_element(sort, tm).is_some()
                {
                    let seq = *seq;
                    let index = self.go(i, tm)?;
                    let at = self.seq_at(seq, index, sort, tm)?;
                    return scalar(at);
                }
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
                    // the base holds – the standard underspecified reading,
                    // and the same one Apalache takes.
                    Value::Fun { array, .. } => {
                        let idx = self.go(i, tm)?;
                        scalar(tm.mk_select(*array, idx))
                    }
                    // A tuple or record that reached here as a *term* rather
                    // than structurally – a member of a set of tuples, or a
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
                    // `[f EXCEPT ![i] = v]` keeps the domain: Apalache's
                    // both `FunExcept` rules copy `dom(f)` over unchanged
                    // ("the domain, as it does not change"), and TLC errors
                    // on an out-of-domain key, so no checkable specification
                    // relies on the result at one. The stored point at such
                    // a key is invisible to `DOMAIN g` and to domain-relative
                    // equality – checked here exactly as the ecosystem does.
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
            // element, with the operator's body encoded afresh each time –
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
                        // A set has no fold order: TLA+ leaves it unspecified,
                        // so the value of the fold is only well defined when
                        // the operator's n-fold composition is order-
                        // independent – associativity and commutativity in the
                        // usual case. Folding in candidate order regardless
                        // (which is what this used to do) makes the answer a
                        // function of the order the candidates were written
                        // in, which is not a property of the specification:
                        // the *evaluator* folds in sorted order, so the two
                        // disagree on `ApaFoldSet(F, 0, {3, 2})` for
                        // `F(a, b) == a * b + a` – the encoder answered `8`
                        // and the replay expected `9`.
                        //
                        // The operator is therefore classified before the
                        // set is folded, and one whose composition is not
                        // provably order-independent **declines** unless the
                        // set has at most one member (where every order is the
                        // same order). Declining is exit 75, not a guess.
                        if !set_fold_order_independent(body, acc, elem)
                            && !at_most_one_element(collection)
                        {
                            return Err(EncodeError::Unsupported(
                                "an `ApaFoldSet` whose operator is not \
                                 associative and commutative; TLA+ specifies no \
                                 fold order for a set, so folding it in \
                                 candidate order would not be a property of \
                                 the specification"
                                    .into(),
                            ));
                        }
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
                    // once, in order. It does have to *be* a sequence – a
                    // literal tuple, which is what a TLA+ sequence is – and a
                    // sequence-sorted state variable has no encoding yet, so
                    // it is declined rather than approximated.
                    FoldOver::SeqLeft => {
                        // Read off the *kernel* term rather than the encoded
                        // value. `<<…>>` is a tuple and a sequence at once, so
                        // whether it encodes to a structural tuple or to a
                        // sequence datatype depends on the sort inference gave
                        // it – and a fold over a literal does not care which.
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
                        // The base `<<>>` is a tuple *and* a sequence, and
                        // inference keeps whichever shape is more precise –
                        // which for a fold over a literal comparison target
                        // can be the *tuple* shape, while the steps produce
                        // sequences (`Append`). Starting the accumulator in
                        // the sequence shape (same value: the empty sequence)
                        // keeps every step at one sort – the issue's
                        // "the base takes the accumulator's sort".
                        if let Value::Tuple(parts) = &*a
                            && parts.is_empty()
                            && let Some(first) = items.first()
                            && let Value::Scalar(f) = &**first
                            && let Ok(elem_sort) = self.sort_of(*f, tm)
                        {
                            let seq_sort = crate::sorts::seq_sort(elem_sort, tm);
                            a = Rc::new(Value::Scalar(self.empty_seq(seq_sort, elem_sort, tm)?));
                        }
                        for item in items {
                            a = self.with_two_bound(acc, a, elem, item, body, tm)?;
                        }
                    }
                }
                Ok(a)
            }

            // `CHOOSE x \\in S : P` – an arbitrary-but-fixed element of the
            // filter `{x \\in S : P}`, as `set.choose` over its native set.
            // The set theory owns the semantics: extensionally equal filters
            // give the same value (congruence – which is TLA+'s determinism
            // requirement exactly, and *more* precise than Apalache's
            // per-occurrence CherryPick), and an empty filter leaves the
            // value unconstrained but consistent, which matches the one
            // thing TLA+ promises about it.
            Kera::Choose { var, set, body } => {
                let filter: KeraRef = Rc::new(Kera::Filter {
                    var: var.clone(),
                    set: Rc::clone(set),
                    pred: Rc::clone(body),
                });
                let Value::Set(cell) = &*self.value(&filter, tm)? else {
                    return Err(EncodeError::Unsupported(
                        "`CHOOSE` over a set with no candidate list".into(),
                    ));
                };
                // The element sort: from the members when there are any, and
                // from the caller's inference when the filter came out empty
                // (`CHOOSE x \\in {} : TRUE` is a term with a type).
                let elem_sort = match cell.members.first().map(|m| &*m.value) {
                    Some(Value::Scalar(k)) => self.sort_of(*k, tm)?,
                    _ => {
                        let Some(sort) = self.node_sorts.get(&Rc::as_ptr(term)).copied() else {
                            return Err(EncodeError::Unsupported(
                                "`CHOOSE` over an empty filter, with no element sort to give it"
                                    .into(),
                            ));
                        };
                        sort
                    }
                };
                let filtered = self.native_set_of(&cell.members, elem_sort, tm)?;
                scalar(tm.mk_set_choose(filtered))
            }
            // `CHOOSE x : x \\notin S` – the fresh-value idiom. One shared
            // constant per filter set: TLA+ says `CHOOSE` picks the same
            // value wherever it is written, so two occurrences over the same
            // `S` are one constant, and the non-membership it asked for is a
            // fact about that constant rather than a guess.
            Kera::ChooseUnbounded { var, body } => {
                if let Kera::Not(inner) = body.as_ref()
                    && let Kera::In(x, s) = inner.as_ref()
                    && matches!(x.as_ref(), Kera::Var(n) if n == var)
                {
                    let inside = self.value(s, tm)?;
                    let Value::Scalar(set_term) = &*inside else {
                        return Err(EncodeError::Unsupported(
                            "`CHOOSE x : x \\notin S` over a set with no term form".into(),
                        ));
                    };
                    let set_term = *set_term;
                    let Some(elem_sort) = self.element_sort_of(set_term, tm).ok() else {
                        return Err(EncodeError::Unsupported(
                            "`CHOOSE x : x \\notin S` over a set with no element sort".into(),
                        ));
                    };
                    // The key is the set's **canonical value** when it is
                    // ground – two spellings of the same set (`{1, 2}` and
                    // `{2, 1}`) are one idiom and must share one constant,
                    // which is what CHOOSE's determinism says. A set that is
                    // not ground keeps its term identity.
                    let ground_key = match nixie_tla::Evaluator::new().eval(s) {
                        Ok(nixie_tla::Value::Set(members)) => {
                            let mut parts: Vec<String> =
                                members.iter().map(|v| format!("{v:?}")).collect();
                            parts.sort();
                            Some(parts.join(","))
                        }
                        _ => None,
                    };
                    let key: UnboundedChooseKey = match &ground_key {
                        Some(k) => UnboundedChooseKey::Ground(k.clone(), elem_sort),
                        None => UnboundedChooseKey::Term(set_term, elem_sort),
                    };
                    let chosen = self.unbounded_chooses.entry(key).or_insert_with(|| {
                        let n = self.fresh;
                        self.fresh = self.fresh.wrapping_add(1);
                        tm.mk_var(&format!("@choose_fresh_{n}"), elem_sort)
                    });
                    let member = tm.mk_set_member(*chosen, set_term);
                    let outside = tm.mk_not(member);
                    self.side.push(outside);
                    scalar(*chosen)
                } else {
                    Err(EncodeError::Unsupported(
                        "an unbounded `CHOOSE` whose predicate is not the fresh-value idiom \\
                         (`CHOOSE x : x \\notin S`)"
                            .into(),
                    ))
                }
            }
            // The `Sequences` operators, on the datatype `sorts::seq_sort`
            // builds: a length and an array from `1..`. Every one of them is
            // exact – nothing here approximates – and the ones that are not
            // here are declined by name.
            Kera::Opaque(name, args)
                if matches!(
                    (name.as_str(), args.len()),
                    ("Len", 1)
                        | ("Append", 2)
                        | ("Head", 1)
                        | ("Tail", 1)
                        | ("\\o", 2)
                        | ("SubSeq", 3)
                        | ("FunAsSeq", 2)
                ) =>
            {
                // A sequence has two shapes here, and the operators take
                // either – the same discipline `set_repr` follows for sets.
                // `<<"a", "b">>` is a tuple *and* a sequence, and which one it
                // encoded to depends on the sort inference gave the literal;
                // an operator that only understood the datatype would decline
                // `Len(<<"a", "b">>)`, which is how this came up.
                let value = self.value(&args[0], tm)?;
                if let Value::Tuple(items) = &*value {
                    let items = items.clone();
                    return match name.as_str() {
                        "Len" => {
                            let n = i64::try_from(items.len()).map_err(|_| {
                                EncodeError::Unsupported("a sequence longer than i64".into())
                            })?;
                            scalar(tm.mk_int(num_bigint::BigInt::from(n)))
                        }
                        "Append" => {
                            let e = self.value(&args[1], tm)?;
                            let mut out = items;
                            out.push(e);
                            Ok(Rc::new(Value::Tuple(out)))
                        }
                        "Tail" => {
                            if items.is_empty() {
                                return Err(EncodeError::Unsupported(
                                    "`Tail` of the empty sequence".into(),
                                ));
                            }
                            Ok(Rc::new(Value::Tuple(items[1..].to_vec())))
                        }
                        "SubSeq" => {
                            let (from, to) = (ground_int(&args[1]), ground_int(&args[2]));
                            let (Some(from), Some(to)) = (from, to) else {
                                return Err(EncodeError::Unsupported(
                                    "`SubSeq` of a literal with a symbolic bound".into(),
                                ));
                            };
                            // TLA+ counts from 1, and an empty range is the
                            // empty sequence rather than an error.
                            let lo = usize::try_from(&from).unwrap_or(1).max(1);
                            let hi = usize::try_from(&to).unwrap_or(0).min(items.len());
                            let picked = if lo > hi {
                                Vec::new()
                            } else {
                                items[lo - 1..hi].to_vec()
                            };
                            Ok(Rc::new(Value::Tuple(picked)))
                        }
                        "\\o" => {
                            let rest = self.seq_items(&args[1], tm)?;
                            let mut out = items;
                            out.extend(rest);
                            Ok(Rc::new(Value::Tuple(out)))
                        }
                        // `Head(<<>>)` is undefined in TLA+. A structural
                        // tuple has no value to offer for it and none is
                        // invented.
                        _ => items.first().map(Rc::clone).ok_or_else(|| {
                            EncodeError::Unsupported("`Head` of the empty sequence".into())
                        }),
                    };
                }
                // `FunAsSeq(f, len)` – the cast itself: a window of length
                // `len` at offset 0 over the function's own array, so
                // `s[i]` reads `f[i]` exactly and every read past `len` is
                // dead by the window's length. The element sort is the one
                // inference gave this term (`Seq(a)`); the array's own sort
                // must agree – the cast is exact or it is refused.
                if name.as_str() == "FunAsSeq" {
                    let Value::Fun { array, .. } = &*value else {
                        return Err(EncodeError::Unsupported(
                            "`FunAsSeq` applied to something that is not a function".into(),
                        ));
                    };
                    let array = *array;
                    let Some(sort) = self.node_sorts.get(&Rc::as_ptr(term)).copied() else {
                        return Err(EncodeError::Unsupported(
                            "`FunAsSeq` whose element sort was not inferred".into(),
                        ));
                    };
                    let Some(elem) = crate::sorts::seq_element(sort, tm) else {
                        return Err(EncodeError::Unsupported(
                            "`FunAsSeq` whose inferred sort is not a sequence".into(),
                        ));
                    };
                    let array_sort = self.sort_of(array, tm)?;
                    match tm.sorts.get(array_sort).map(|s| s.kind.clone()) {
                        Some(nixie_core::SortKind::Array { domain, range })
                            if domain == tm.sorts.int_sort && range == elem => {}
                        _ => {
                            return Err(EncodeError::Unsupported(
                                "`FunAsSeq` over a function whose array is not Int-keyed at the \
                                 sequence's element sort"
                                    .into(),
                            ));
                        }
                    }
                    let len = self.go(&args[1], tm)?;
                    let zero = tm.mk_int(num_bigint::BigInt::from(0));
                    let seq_sort = crate::sorts::seq_sort(elem, tm);
                    let ctor = tm
                        .sorts
                        .datatype_name(seq_sort)
                        .ok_or(EncodeError::ShapeClash)?
                        .to_string();
                    return scalar(tm.mk_dt_constructor(&ctor, [zero, len, array], seq_sort));
                }
                let Value::Scalar(target) = &*value else {
                    return Err(EncodeError::Unsupported(format!(
                        "`{name}` applied to something that is not a sequence"
                    )));
                };
                let target = *target;
                let sort = self.sort_of(target, tm)?;
                let Some(elem) = crate::sorts::seq_element(sort, tm) else {
                    return Err(EncodeError::Unsupported(format!(
                        "`{name}` applied to something that is not a sequence"
                    )));
                };
                match name.as_str() {
                    "Len" => scalar(self.seq_len(target, tm)),
                    "Append" => {
                        let v = self.value(&args[1], tm)?;
                        let e = self.reify(&v, tm)?;
                        if self.sort_of(e, tm)? != elem {
                            return Err(EncodeError::Unsupported(
                                "`Append` of a value at the wrong element sort".into(),
                            ));
                        }
                        let out = self.seq_append(target, e, sort, tm)?;
                        scalar(out)
                    }
                    // `Tail(s)` moves the window forward by one and shortens
                    // it. Nothing is copied and no element moves, which is the
                    // whole reason the offset is in the representation.
                    //
                    // TLA+ leaves `Tail(<<>>)` undefined, and so does this: the
                    // length becomes `-1`, a sequence nothing can read from,
                    // rather than an error about a state the specification may
                    // never reach.
                    "Tail" => {
                        let off = self.seq_off(target, tm);
                        let len = self.seq_len(target, tm);
                        let fun = self.seq_fun(target, elem, tm);
                        let one = tm.mk_int(num_bigint::BigInt::from(1));
                        let minus = tm.mk_int(num_bigint::BigInt::from(-1));
                        let off2 = tm.mk_add([off, one]);
                        let len2 = tm.mk_add([len, minus]);
                        let name = tm
                            .sorts
                            .datatype_name(sort)
                            .ok_or(EncodeError::ShapeClash)?
                            .to_string();
                        scalar(tm.mk_dt_constructor(&name, [off2, len2, fun], sort))
                    }
                    // `SubSeq(s, m, n)` moves the window and resizes it:
                    // element `i` of the result is element `m + i - 1` of `s`,
                    // so the offset gains `m - 1` and the length becomes
                    // `n - m + 1`. Nothing is copied, for the same reason
                    // `Tail` copies nothing – and `Tail` is exactly
                    // `SubSeq(s, 2, Len(s))`.
                    //
                    // The bounds may be symbolic: they are arithmetic on the
                    // offset and the length, not a count of anything that has
                    // to be enumerated.
                    "SubSeq" => {
                        let from = self.go(&args[1], tm)?;
                        let to = self.go(&args[2], tm)?;
                        let off = self.seq_off(target, tm);
                        let fun = self.seq_fun(target, elem, tm);
                        let one = tm.mk_int(num_bigint::BigInt::from(1));
                        let minus = tm.mk_int(num_bigint::BigInt::from(-1));
                        let shift = tm.mk_add([from, minus]);
                        let off2 = tm.mk_add([off, shift]);
                        let span = tm.mk_sub(to, from);
                        let len2 = tm.mk_add([span, one]);
                        let name = tm
                            .sorts
                            .datatype_name(sort)
                            .ok_or(EncodeError::ShapeClash)?
                            .to_string();
                        scalar(tm.mk_dt_constructor(&name, [off2, len2, fun], sort))
                    }
                    // `s \o t` where `t` is a *literal*, which is the only
                    // shape a bounded encoding can take exactly: appending its
                    // elements one at a time. Concatenating two symbolic
                    // sequences needs their lengths known, and is declined
                    // rather than approximated.
                    "\\o" => {
                        let rest = self.seq_items(&args[1], tm)?;
                        let mut out = target;
                        for item in rest {
                            // A record or a tuple element arrives *structural*
                            // – field by field – and a sequence holds one term
                            // per element, so it is reified into its datatype
                            // here. This is the ordinary crossing between the
                            // two forms, not a special case: a queue of
                            // records is the shape every generated
                            // specification uses.
                            let e = self.reify(&item, tm)?;
                            out = self.seq_append(out, e, sort, tm)?;
                        }
                        scalar(out)
                    }
                    // `Head(s)` is `s[1]`. TLA+ leaves it *undefined* on the
                    // empty sequence, and so does this: the array's value
                    // there is whatever the base holds, which is an
                    // unconstrained term – some value, never a chosen one.
                    _ => {
                        let one = tm.mk_int(num_bigint::BigInt::from(1));
                        let at = self.seq_at(target, one, sort, tm)?;
                        scalar(at)
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
            // `IsABag(B) == \\A x \\in DOMAIN B : B[x] > 0` over the
            // function value, whose domain is carried. Kept as an operator
            // rather than desugared in the lowerer because the evaluator
            // answers it totally (`IsABag(42)` is FALSE, not an error).
            Kera::Opaque(name, args) if matches!((name.as_str(), args.len()), ("IsABag", 1)) => {
                let f = self.value(&args[0], tm)?;
                let Value::Fun { domain, array } = &*f else {
                    return Err(EncodeError::Unsupported(
                        "`IsABag` of something that is not a function".into(),
                    ));
                };
                let (domain, array) = (*domain, *array);
                let cell = self.candidates_of(domain, 0, tm).ok_or_else(|| {
                    EncodeError::NotEnumerable(
                        "`IsABag` over a domain with no candidate list".into(),
                    )
                })?;
                let zero = tm.mk_int(0);
                let mut conj = Vec::with_capacity(cell.len());
                for m in cell.iter() {
                    let Value::Scalar(k) = &*m.value else {
                        return Err(EncodeError::Unsupported(
                            "a function domain whose members have no SMT sort".into(),
                        ));
                    };
                    let read = tm.mk_select(array, *k);
                    let positive = tm.mk_gt(read, zero);
                    conj.push(tm.mk_implies(m.present, positive));
                }
                scalar(tm.mk_and(conj))
            }
            Kera::Opaque(name, args)
                if matches!(
                    (name.as_str(), args.len()),
                    ("Cardinality", 1) | ("IsFiniteSet", 1)
                ) =>
            {
                // `Cardinality(a..b)` is arithmetic – `IF a <= b THEN
                // b - a + 1 ELSE 0` – rather than an enumeration, so a
                // symbolic bound costs nothing (Apalache's `ExprOptimizer`
                // does the same). Note `a..b` may be *empty*: TLA+ ranges
                // are empty when `a > b`, not ill-formed.
                if name.as_str() == "Cardinality"
                    && matches!(args[0].as_ref(), Kera::Range(_, _))
                    && let Kera::Range(lo, hi) = args[0].as_ref()
                {
                    let l = self.go(lo, tm)?;
                    let h = self.go(hi, tm)?;
                    let nonempty = tm.mk_le(l, h);
                    let one = tm.mk_int(1);
                    let span = tm.mk_sub(h, l);
                    let count = tm.mk_add([span, one]);
                    let zero = tm.mk_int(0);
                    return scalar(tm.mk_ite(nonempty, count, zero));
                }
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
/// into opaque set constants either – an unconstrained `Nat` admits models in
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

/// A binary set operation with a standard *infinite* set on one side, as
/// `(op, the-standard-side-is-first, x, y)`.
///
/// `Nat \ {0}` and `Nat \cap S` are the shapes an `ASSUME` uses to pin a
/// constant, and neither has a finite member list on the standard side.
fn bin_standard(s: &KeraRef) -> Option<(SetOp, bool, &KeraRef, &KeraRef)> {
    let Kera::SetBin(op, x, y) = s.as_ref() else {
        return None;
    };
    match (standard_set(x).is_some(), standard_set(y).is_some()) {
        (true, _) => Some((*op, true, x, y)),
        (false, true) => Some((*op, false, x, y)),
        (false, false) => None,
    }
}

/// `e \in <a standard infinite set>`, structurally: `Nat` is `e >= 0`, and
/// the others contain every value of the sort the type checker already
/// assigned, so membership in them is `TRUE`.
///
/// `None` for a name with no structural reading, which is a refusal rather
/// than a guess.
fn in_standard(e: TermId, name: &str, tm: &mut TermManager) -> Option<TermId> {
    match name {
        // `x \in Nat` is `x >= 0` for an integer `x`.
        "Nat" => {
            let zero = tm.mk_int(0);
            Some(tm.mk_ge(e, zero))
        }
        // Every value of the matching sort is in these, and the type checker
        // has already established the sort.
        "Int" | "Real" | "STRING" | "BOOLEAN" => Some(tm.mk_bool(true)),
        _ => None,
    }
}

/// Wrap an SMT term as a value.
fn scalar(t: TermId) -> Result<Rc<Value>> {
    Ok(Rc::new(Value::Scalar(t)))
}

// ======== the `ApaFoldSet` order-independence audit ========
//
// TLA+ specifies no order for folding a set, so a fold whose result depends
// on the order is a fold with no value. `ApaFoldSet` is Apalache's operator
// and Apalache documents the same assumption ("the operator should be AC")
// without enforcing it; Nixie enforces it, because a silent order-dependent
// answer is exactly the class of wrong answer `AGENTS.md` opens with.
//
// The classes below are **syntactic and conservative**: every one carries a
// one-line argument for why the n-fold composition of that shape commutes,
// and everything not in a class declines. The classes were chosen against
// the corpus – `+` (`Sum`), `\cup` (`FoldSetSet`, `RemakeSet`), counting
// (`p + IF P(q) THEN 1 ELSE 0`, which is an `Add` chain whose non-`acc`
// leaf is an `IF` on `q` only), `Max`/`Min`, and the function-update idiom
// `[f EXCEPT ![x] = f[x] + 1]` (`Antipatterns`, `FoldSetFun`).

/// Whether the n-fold composition of `body(acc, elem)` commutes, so that
/// folding a set in any order – candidate order here, sorted order in the
/// evaluator – gives the same value.
///
/// Called on a lowered operator body, which is user input, so every helper
/// walks with an explicit stack and a budget.
fn set_fold_order_independent(body: &KeraRef, acc: &Name, elem: &Name) -> bool {
    // The element parameter unused: the operator is `g(acc)`, and iterating
    // one function is order-independent by inspection.
    if !mentions(body, elem) {
        return true;
    }
    // The accumulator unused and the element used: the value is whichever
    // element is folded last. Order-dependent, always.
    if !mentions(body, acc) {
        return false;
    }
    // An `EXCEPT` update of the accumulator: `[f EXCEPT ![x] = e]`.
    if let Kera::Except { fun, index, value } = body.as_ref()
        && matches!(fun.as_ref(), Kera::Var(n) if n == acc)
    {
        // The index is the element itself, and the accumulator is read only
        // as `f[x]`. Every element is folded once (the duplicate guard), and
        // a step writes only its own index, so each `f[x]` read sees the
        // *original* value whatever order the steps run in. This is
        // `Antipatterns`' `addOneInCdm` and the `FoldSetFun` shape.
        if matches!(index.as_ref(), Kera::Var(n) if n == elem) && acc_read_only_at(value, acc, elem)
        {
            return true;
        }
        // A fixed index and a fixed value rewrite the same entry to the same
        // value however many times it runs: idempotent, so order-free. The
        // value must not mention the element either, or "last write wins"
        // would decide it.
        if !mentions(index, acc)
            && !mentions(index, elem)
            && !mentions(value, acc)
            && !mentions(value, elem)
        {
            return true;
        }
        return false;
    }
    // A `Max`/`Min`-shaped conditional: `IF a-side > b-side THEN a-side ELSE
    // b-side` (either comparison direction, either branch order). `Max` and
    // `Min` are associative, commutative and idempotent, which is more than
    // order-independence needs.
    if is_min_max(body, acc, elem) {
        return true;
    }
    // Bag addition, as the `Bags` desugaring writes it:
    // `[x \\in DOMAIN a \\cup DOMAIN b |-> CopiesIn(a,x) + CopiesIn(b,x)]`.
    // Pointwise addition of naturals is commutative and associative, so a
    // fold whose every step adds one contribution is order-independent –
    // this is `BagUnion`, and `BagOfAll`'s step reduces to it.
    if is_bag_addition(body, acc, elem) {
        return true;
    }
    // An AC chain: `a + b + …`, `a * b * …`, `a \cup b`, `a \cap b`,
    // `a /\ b`, `a \/ b`. Flattened to its leaves, the composition commutes
    // when each step contributes its non-accumulator leaves once and the
    // accumulator at most once – for `+` and `*` an accumulator leaf twice
    // squares it (`a * a * b` over `{2, 3}` really does depend on the order),
    // while the idempotent set/Boolean operators tolerate any count.
    ac_chain_shape(body, acc).is_some()
}

/// The AC operators a fold body may be built from, with whether repeats of
/// the accumulator leaf are harmless.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AcKind {
    /// `+`: `c₀ + k·acc + Σ mᵢ·xᵢ` commutes iff `k ≤ 1`.
    Add,
    /// `*`: same shape multiplicatively, `k ≤ 1`.
    Mul,
    /// `\cup`, `\cap`, `/\`, `\/{}`: idempotent, any count.
    Idem,
}

/// Whether `body` is a chain of one AC operator whose leaves are the
/// accumulator (bare) or accumulator-free, returning the class it is.
///
/// `None` when the top operator is not one of the four, a leaf mentions the
/// accumulator without *being* it, or (for `+`/`*`) the accumulator leaf
/// occurs more than once. Mixed chains (`a + b * c`) are leaves of the outer
/// operator, and a leaf mentioning `acc` declines the whole chain.
fn ac_chain_shape(body: &KeraRef, acc: &Name) -> Option<AcKind> {
    let kind = match body.as_ref() {
        Kera::Arith(ArithOp::Add, _, _) => AcKind::Add,
        Kera::Arith(ArithOp::Mul, _, _) => AcKind::Mul,
        Kera::SetBin(SetOp::Union, _, _) | Kera::SetBin(SetOp::Intersect, _, _) => AcKind::Idem,
        Kera::And(_) | Kera::Or(_) => AcKind::Idem,
        _ => return None,
    };
    // Flatten the homogeneous chain with an explicit stack and a budget: the
    // body is user input.
    let mut stack = vec![body.clone()];
    let mut budget = 100_000usize;
    let mut acc_leaves = 0usize;
    while let Some(t) = stack.pop() {
        budget = budget.checked_sub(1)?;
        // Only the *same* operator continues the chain: an `And` under an
        // `Or` is a leaf, and mixing `+` with `*` makes every mixed subterm a
        // leaf that mentions the accumulator and declines the whole chain.
        let body_op = match body.as_ref() {
            Kera::SetBin(o, _, _) => Some(*o),
            _ => None,
        };
        let same_chain = match t.as_ref() {
            Kera::Arith(ArithOp::Add, a, b) if kind == AcKind::Add => {
                stack.push(a.clone());
                stack.push(b.clone());
                true
            }
            Kera::Arith(ArithOp::Mul, a, b) if kind == AcKind::Mul => {
                stack.push(a.clone());
                stack.push(b.clone());
                true
            }
            Kera::SetBin(op, a, b) if kind == AcKind::Idem && Some(*op) == body_op => {
                stack.push(a.clone());
                stack.push(b.clone());
                true
            }
            Kera::And(xs) if kind == AcKind::Idem && matches!(body.as_ref(), Kera::And(_)) => {
                stack.extend(xs.iter().cloned());
                true
            }
            Kera::Or(xs) if kind == AcKind::Idem && matches!(body.as_ref(), Kera::Or(_)) => {
                stack.extend(xs.iter().cloned());
                true
            }
            _ => false,
        };
        if same_chain {
            continue;
        }
        // A leaf. The bare accumulator counts once; anything else must not
        // mention it. A leaf that mentions the accumulator without being it
        // – `(a + 1) + x`, `a * a + x` – makes the composition order-
        // dependent, and is not guessed at.
        if matches!(t.as_ref(), Kera::Var(n) if n == acc) {
            acc_leaves += 1;
            if kind != AcKind::Idem && acc_leaves > 1 {
                return None;
            }
        } else if mentions(&t, acc) {
            return None;
        }
    }
    Some(kind)
}

/// Whether `e` is `IF x > y THEN x ELSE y` in some arrangement – the `Max`
/// shape – or the `Min` one, over one `acc`-only and one `elem`-only side.
fn is_min_max(e: &KeraRef, acc: &Name, elem: &Name) -> bool {
    let Kera::Ite(cond, then, other) = e.as_ref() else {
        return false;
    };
    let Kera::Cmp(_, x, y) = cond.as_ref() else {
        return false;
    };
    // Each side of the comparison and each branch is either `acc`-only or
    // `elem`-only, and the two branches are the two sides in either order
    // (`Max`: the greater is returned; `Min`: the lesser – both are AC).
    let side = |t: &KeraRef| {
        if !mentions(t, elem) {
            Some(0u8)
        } else if !mentions(t, acc) {
            Some(1u8)
        } else {
            None
        }
    };
    let (Some(a), Some(b)) = (side(x), side(y)) else {
        return false;
    };
    if a == b {
        return false; // both sides of one polarity: not a max/min of the two
    }
    let (Some(t), Some(u)) = (side(then), side(other)) else {
        return false;
    };
    t != u && matches!((t, u), (0, 1) | (1, 0))
}

/// Whether `body` is a **bag-addition** step over `acc`: the `\\oplus`
/// desugaring
/// `[x \\in DOMAIN P \\cup DOMAIN Q |-> CopiesIn(P,x) + CopiesIn(Q,x)]`
/// where `acc` occurs in exactly one of the two bag operands (`P`), and the
/// other (`Q`) is accumulator-free.
///
/// The commutation argument is the shape's, not the operands': each step adds
/// one accumulator-free contribution pointwise, so composing the steps in any
/// order sums the same contributions at every point. `BagUnion` is the
/// special case `Q = elem`; `BagOfAll`'s step is `Q = [y \\in {F(elem)} |->
/// B[elem]]`. An `acc` on *both* sides (`Add(acc[x], g(acc)[x])`) is refused:
/// there the step depends on the accumulator twice and order can matter.
fn is_bag_addition(e: &KeraRef, acc: &Name, elem: &Name) -> bool {
    let Kera::FunDef { var, set, body } = e.as_ref() else {
        return false;
    };
    let _ = elem;
    let Kera::SetBin(SetOp::Union, a, b) = set.as_ref() else {
        return false;
    };
    // `CopiesIn(P, x) == IF x \\in DOMAIN P THEN P[x] ELSE 0`, with the same
    // `P` in the guard and the read (pointer-identical: the desugaring
    // builds it once and shares it).
    let copies_in = |t: &KeraRef| -> Option<KeraRef> {
        let Kera::Ite(c, tb, eb) = t.as_ref() else {
            return None;
        };
        let Kera::In(i, s) = c.as_ref() else {
            return None;
        };
        if !matches!(i.as_ref(), Kera::Var(v) if v == var) {
            return None;
        }
        let Kera::Domain(p1) = s.as_ref() else {
            return None;
        };
        let Kera::FunApp(p2, i2) = tb.as_ref() else {
            return None;
        };
        if !matches!(i2.as_ref(), Kera::Var(v) if v == var) || p1 != p2 {
            return None;
        }
        if !matches!(eb.as_ref(), Kera::Int(_)) {
            return None;
        }
        Some(Rc::clone(p1))
    };
    // The domain union must be exactly the two operands' domains.
    let Kera::Arith(ArithOp::Add, x, y) = body.as_ref() else {
        return false;
    };
    let (Some(p), Some(q)) = (copies_in(x), copies_in(y)) else {
        return false;
    };
    let dom_ok =
        |d: &KeraRef, op: &KeraRef| -> bool { matches!(d.as_ref(), Kera::Domain(o) if o == op) };
    if !((dom_ok(a, &p) && dom_ok(b, &q)) || (dom_ok(a, &q) && dom_ok(b, &p))) {
        return false;
    }
    // Exactly one side mentions the accumulator: the other is the
    // order-independent contribution.
    let mp = mentions(&p, acc);
    let mq = mentions(&q, acc);
    mp != mq
}

/// Whether `acc` is read in `e` only as `acc[elem]`.
///
/// Under an `EXCEPT` at index `elem`, such a read always sees the original
/// value (no other step writes that index), which is what makes the function
/// update idiom order-independent. Any other mention – a read at a different
/// index, the function as a whole – is a real dependency on the accumulated
/// state and refuses the classification.
fn acc_read_only_at(e: &KeraRef, acc: &Name, elem: &Name) -> bool {
    let mut seen: HashSet<*const Kera> = HashSet::new();
    let mut stack = vec![e.clone()];
    let mut budget = 100_000usize;
    while let Some(t) = stack.pop() {
        // Fails closed: a term too large to inspect is a term not proven
        // order-independent.
        if budget == 0 {
            return false;
        }
        budget -= 1;
        if !seen.insert(Rc::as_ptr(&t)) {
            continue;
        }
        match t.as_ref() {
            // The one allowed read: the point this same step writes.
            Kera::FunApp(f, i)
                if matches!(f.as_ref(), Kera::Var(n) if n == acc)
                    && matches!(i.as_ref(), Kera::Var(n) if n == elem) => {}
            // The accumulator as a whole – a dependency on the entire
            // accumulated state, not one original point.
            Kera::Var(n) if n == acc => return false,
            _ => stack.extend(t.as_ref().children().into_iter().cloned()),
        }
    }
    true
}

/// Whether a name occurs in a term, walked with an explicit stack.
fn mentions(term: &KeraRef, name: &Name) -> bool {
    let mut seen: HashSet<*const Kera> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(Rc::as_ptr(t)) {
            continue;
        }
        if matches!(t.as_ref(), Kera::Var(n) if n == name) {
            return true;
        }
        stack.extend(t.as_ref().children());
    }
    false
}

/// Whether a set expression has at most one member *as written*: a literal
/// `{}` or `{e}`. Every other shape – a longer literal, a range, anything
/// symbolic – has either more members or members not known at encode time,
/// both of which need the operator audit above.
fn at_most_one_element(t: &KeraRef) -> bool {
    matches!(t.as_ref(), Kera::SetEnum(xs) if xs.len() <= 1)
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
/// `0 .. (4-1)` – as ground as `0 .. 3` and rejected all the same. The value
/// has to be computed, not pattern-matched.
///
/// It is computed by `nixie-tla`'s evaluator, which is the right authority
/// rather than a convenience: it is the implementation of TLA+ arithmetic that
/// `bench/tla_eval` checks against TLC, and a second constant folder here
/// would be a second semantics to keep in agreement. It fails closed – a free
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
/// The payload sort of one tag of a variant datatype.
fn variant_payload_sort(sort: SortId, tag: &str, tm: &TermManager) -> Option<SortId> {
    let name = tm.sorts.datatype_name(sort)?;
    let def = tm.sorts.get_datatype(name)?;
    let ctor = def
        .constructors
        .iter()
        .find(|c| tm.sorts.resolve_spur(c.name) == format!("@v_{tag}"))?;
    let [(_, ps)] = ctor.selectors.as_slice() else {
        return None;
    };
    Some(*ps)
}

/// The tags of a variant datatype, in declaration order.
fn variant_tags(sort: SortId, tm: &TermManager) -> Option<Vec<String>> {
    let name = tm.sorts.datatype_name(sort)?;
    let def = tm.sorts.get_datatype(name)?;
    def.constructors
        .iter()
        .map(|c| {
            tm.sorts
                .resolve_spur(c.name)
                .strip_prefix("@v_")
                .map(str::to_string)
        })
        .collect()
}

/// A scalar `Value` for one term.
fn scalar_clone(t: TermId) -> Rc<Value> {
    Rc::new(Value::Scalar(t))
}

fn describe(k: &Kera) -> String {
    let s = match k {
        Kera::Str(_) => "a string literal",
        Kera::Forall { .. } | Kera::Exists { .. } => "a quantifier",
        Kera::Choose { .. } | Kera::ChooseUnbounded { .. } => "`CHOOSE`",
        Kera::In(_, _) => "`\\in`",
        // The set theory *is* wired into the solver; what this names is the
        // construct the encoding could not serve – usually a base set with
        // no candidate list to enumerate from. Saying "not wired up" here
        // sent readers looking for a wiring bug that was not there.
        Kera::SetEnum(_)
        | Kera::Filter { .. }
        | Kera::Map { .. }
        | Kera::SetBin(_, _, _)
        | Kera::Powerset(_)
        | Kera::BigUnion(_)
        | Kera::Range(_, _)
        | Kera::Times(_) => "a set expression with no enumerable members to build it from",
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
