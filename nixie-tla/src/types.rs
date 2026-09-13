//! Type inference for the kernel — Nixie's answer to Apalache's Snowcat.
//!
//! # Why a type system at all
//!
//! TLA+ is untyped. Every value is a set, `1 = "a"` is a legal (if
//! unspecified) expression, and nothing in the language stops a variable from
//! holding an integer in one state and a record in the next. An SMT encoder
//! has no such freedom: `nixie-core` terms are sorted, so *something* has to
//! decide that `x` is an `Int` before `x + 1` can be built at all.
//!
//! Apalache solves this with **Snowcat**, a unification-based inferencer over
//! a small type grammar, seeded by `@type:` annotations. This is the same
//! idea, and it is the gate on everything downstream: the encoder in
//! `nixie-tla-check` can reach only *ground* terms until it is told what sort
//! each free name has.
//!
//! # Where this differs from Snowcat, and why
//!
//! Two deliberate departures, both borrowed from well-established type-system
//! work rather than invented here:
//!
//! * **Records are row types** (Rémy/Wand-style), not fixed field sets.
//!   `r.foo` tells us only that `r` *has* a `foo` field, and lowering turns it
//!   into `FunApp(r, Str("foo"))` where nothing else is known. A closed record
//!   type would have to reject the expression or guess the remaining fields;
//!   an open row `[foo: a | rho]` says exactly what was learned and nothing
//!   more. Record literals are closed, so the two meet at the definition site.
//!
//! * **Tuples, sequences and functions are related by unification, not kept
//!   apart.** In TLA+ `<<a, b>>` genuinely *is* a function with domain
//!   `{1, 2}`; `Len(<<1, 2>>)` is not a coercion, it is the same value viewed
//!   through a different operator. So `Tuple` unifies with `Seq` and with
//!   `Fun(Int, _)` by equating the components, and the more specific shape
//!   survives. Apalache keeps them distinct and requires an annotation to
//!   cross over; that is a reasonable choice for a tool that already demands
//!   annotations, but it rejects specifications that are perfectly well typed
//!   under the language's own semantics.
//!
//! # What it refuses to do
//!
//! An index into a value whose shape is still unknown (`f[1]` where nothing
//! constrains `f`) is genuinely ambiguous: tuple, sequence and function are
//! all consistent, and they encode differently. Rather than pick one, the
//! inferencer **reports it**. `AGENTS.md` is explicit that an unhandled input
//! must raise an error rather than take a plausible default, and a type that
//! was guessed is exactly the kind of plausible default that turns into a
//! wrong `sat` three layers down.
//!
//! # Example
//!
//! ```
//! use nixie_tla::Lowerer;
//! use nixie_tla::types::{Inference, Type};
//! use nixie_tla_syntax::parse_file;
//!
//! let src = r"
//! ---- MODULE Counter ----
//! VARIABLE x
//! Next == x' = x + 1
//! ====
//! ";
//! let parsed = parse_file(src).expect("parses");
//! let mut low = Lowerer::new();
//! low.add_module(&parsed.module);
//! let next = low.lower_named(&parsed.module, "Next").expect("lowers");
//!
//! let mut inf = Inference::new();
//! let t = inf.infer(&next).expect("types");
//! assert_eq!(inf.to_type(t).expect("materialises"), Type::Bool);
//! // `x` was never annotated; arithmetic forced it.
//! let x = inf.free_name("x").expect("x is free");
//! assert_eq!(inf.to_type(x).expect("materialises"), Type::Int);
//! ```

use crate::kera::{Kera, KeraRef, Name};
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::rc::Rc;
use thiserror::Error;

/// A node in the type arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TyId(pub u32);

/// The structure of a type, with children given as arena ids.
///
/// Deliberately closed: a new shape must be handled everywhere, not silently
/// skipped by a `_ =>` arm.
#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    /// `BOOLEAN`.
    Bool,
    /// An integer.
    Int,
    /// A string.
    Str,
    /// A set of elements.
    Set(TyId),
    /// A sequence, i.e. a function on `1..n`.
    Seq(TyId),
    /// A function from a domain to a codomain.
    Fun(TyId, TyId),
    /// A tuple, which is also a function on `1..n` but may be heterogeneous.
    Tuple(Vec<TyId>),
    /// A record. `tail` is `None` for a closed record and `Some(row)` for one
    /// known only to *contain* these fields.
    Rec {
        /// The fields known to be present.
        fields: BTreeMap<String, TyId>,
        /// The row variable standing for the fields not yet known.
        tail: Option<TyId>,
    },
}

/// One slot of the union-find arena.
#[derive(Debug, Clone)]
enum Slot {
    /// An unbound type variable.
    Free,
    /// A link to another slot; follow it.
    Link(TyId),
    /// A resolved structure.
    Ty(Ty),
}

/// A materialised type, as a tree.
///
/// Produced by [`Inference::to_type`] for diagnostics, tests and the encoder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// `BOOLEAN`.
    Bool,
    /// An integer.
    Int,
    /// A string.
    Str,
    /// A set.
    Set(Box<Type>),
    /// A sequence.
    Seq(Box<Type>),
    /// A function.
    Fun(Box<Type>, Box<Type>),
    /// A tuple.
    Tuple(Vec<Type>),
    /// A record; `open` is true when further fields may exist.
    Rec {
        /// The known fields.
        fields: BTreeMap<String, Type>,
        /// Whether the record may have more fields than these.
        open: bool,
    },
    /// A type variable that inference never constrained. Named by its
    /// representative slot so that two occurrences of the same variable print
    /// the same way.
    Var(u32),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => f.write_str("Bool"),
            Self::Int => f.write_str("Int"),
            Self::Str => f.write_str("Str"),
            Self::Set(t) => write!(f, "Set({t})"),
            Self::Seq(t) => write!(f, "Seq({t})"),
            Self::Fun(a, b) => write!(f, "({a} -> {b})"),
            Self::Tuple(ts) => {
                f.write_str("<<")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{t}")?;
                }
                f.write_str(">>")
            }
            Self::Rec { fields, open } => {
                f.write_str("[")?;
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{k}: {v}")?;
                }
                if *open {
                    f.write_str(if fields.is_empty() { " | .." } else { ", .." })?;
                }
                f.write_str("]")
            }
            Self::Var(n) => write!(f, "'{n}"),
        }
    }
}

/// Why inference failed.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum TypeError {
    /// Two types that had to be equal are not.
    #[error("type mismatch: {left} and {right} cannot be the same type")]
    Mismatch {
        /// One side.
        left: String,
        /// The other.
        right: String,
    },
    /// A type would have to contain itself.
    #[error("`{var}` would have to be a type containing itself ({ty})")]
    Occurs {
        /// The variable.
        var: String,
        /// What it was being bound to.
        ty: String,
    },
    /// A record was required to have a field it does not have.
    #[error("a record with fields {have} has no field `{field}`")]
    NoField {
        /// The field asked for.
        field: String,
        /// The fields the closed record actually has.
        have: String,
    },
    /// An index into a value whose shape is unknown.
    ///
    /// Reported rather than guessed: tuple, sequence and function all fit, and
    /// they do not encode the same way.
    #[error("the shape of `{what}` is ambiguous (tuple, sequence and function all fit)")]
    Ambiguous {
        /// The expression, rendered.
        what: String,
    },
    /// A literal index outside a tuple's arity.
    #[error("index {index} is outside a {arity}-tuple")]
    TupleIndex {
        /// The index used.
        index: i64,
        /// The tuple's arity.
        arity: usize,
    },
    /// The type arena ran out of identifiers.
    ///
    /// Reported rather than wrapped around: a `TyId` that aliases an existing
    /// slot would silently equate two unrelated types, which is the quietest
    /// possible way to produce a wrong answer.
    #[error("the type arena is full ({limit} slots)")]
    ArenaFull {
        /// The number of slots the arena can address.
        limit: usize,
    },
    /// Inference did more work than the budget allows.
    #[error("inference exceeded its budget of {limit} steps")]
    BudgetExhausted {
        /// The configured budget.
        limit: usize,
    },
}

/// Result alias for inference.
pub type Result<T> = core::result::Result<T, TypeError>;

/// Default work budget, counted in unification and walk steps.
pub const DEFAULT_BUDGET: usize = 2_000_000;

/// Default limit on the size of a materialised type tree.
pub const DEFAULT_MATERIALISE_LIMIT: usize = 100_000;

/// A literal index waiting for its subject's shape.
///
/// This is the *only* constraint that has to wait. `DOMAIN` does not: see
/// [`Inference::domain_of`] for why the two differ.
#[derive(Debug, Clone)]
struct Deferred {
    /// The value being indexed.
    subject: TyId,
    /// The literal index.
    index: i64,
    /// The type of the element at that index.
    out: TyId,
    /// How to describe it if it stays unresolved.
    what: String,
}

/// Unification-based type inference over [`Kera`].
pub struct Inference {
    slots: Vec<Slot>,
    /// Types of names: bound variables (uniquely renamed by lowering) and the
    /// free constants and state variables of the specification.
    env: HashMap<Name, TyId>,
    /// Which names were never bound by a binder — the specification's own
    /// `CONSTANT`s and `VARIABLE`s.
    free: HashMap<String, TyId>,
    /// Types already computed, keyed by pointer identity so that a shared
    /// subterm is typed once.
    memo: HashMap<*const Kera, TyId>,
    /// Signatures of operators that lowering could not inline, monomorphic per
    /// name and arity exactly as Apalache treats a declared `CONSTANT` operator.
    opaque: HashMap<(String, usize), (Vec<TyId>, TyId)>,
    deferred: Vec<Deferred>,
    /// Every root term inferred, kept alive.
    ///
    /// `memo` is keyed by raw pointer, which is only a stable identity while
    /// the allocation lives: drop a term and a later `Rc` can land on the same
    /// address, turning a memo hit into a silently wrong type. Holding the
    /// roots makes every child of every inferred term outlive the memo.
    roots: Vec<KeraRef>,
    budget: usize,
    spent: usize,
}

impl Default for Inference {
    fn default() -> Self {
        Self::new()
    }
}

impl Inference {
    /// A fresh inferencer with nothing known.
    #[must_use]
    pub fn new() -> Self {
        Self {
            slots: Vec::new(),
            env: HashMap::new(),
            free: HashMap::new(),
            memo: HashMap::new(),
            opaque: HashMap::new(),
            deferred: Vec::new(),
            roots: Vec::new(),
            budget: DEFAULT_BUDGET,
            spent: 0,
        }
    }

    /// Set the work budget.
    #[must_use]
    pub fn with_budget(mut self, budget: usize) -> Self {
        self.budget = budget;
        self
    }

    /// The type inferred for a specific node of a term already passed to
    /// [`Inference::infer`].
    ///
    /// Keyed by pointer identity, like the inference memo itself, so a shared
    /// subterm answers once. Needed by consumers that must know a node's type
    /// where the node itself does not carry one — the empty set literal `{}`
    /// being the motivating case: its element type comes from context.
    #[must_use]
    pub fn node_ty(&self, node: &KeraRef) -> Option<TyId> {
        self.memo.get(&Rc::as_ptr(node)).copied()
    }

    /// The type assigned to a free name, if it appeared.
    #[must_use]
    pub fn free_name(&self, name: &str) -> Option<TyId> {
        self.free.get(name).copied()
    }

    /// Every free name that appeared, with its type.
    pub fn free_names(&self) -> impl Iterator<Item = (&str, TyId)> {
        self.free.iter().map(|(k, v)| (k.as_str(), *v))
    }

    /// Force a name to a type, as a `@type:` annotation would.
    ///
    /// # Errors
    ///
    /// Fails if the name already has an incompatible type.
    pub fn assume(&mut self, name: &str, ty: TyId) -> Result<()> {
        let n = Name(name.to_string());
        match self.env.get(&n).copied() {
            Some(existing) => self.unify(existing, ty),
            None => {
                self.env.insert(n, ty);
                self.free.insert(name.to_string(), ty);
                Ok(())
            }
        }
    }

    // ---- arena ----

    /// The next free slot id, or an error if the arena is exhausted.
    fn next_id(&self) -> Result<TyId> {
        u32::try_from(self.slots.len())
            .map(TyId)
            .map_err(|_| TypeError::ArenaFull {
                limit: u32::MAX as usize,
            })
    }

    /// A fresh unbound type variable.
    ///
    /// # Errors
    ///
    /// Fails only if the arena has exhausted its 2^32 identifiers.
    pub fn fresh(&mut self) -> Result<TyId> {
        let id = self.next_id()?;
        self.slots.push(Slot::Free);
        Ok(id)
    }

    /// Intern a structure.
    ///
    /// # Errors
    ///
    /// Fails only if the arena has exhausted its 2^32 identifiers.
    pub fn mk(&mut self, ty: Ty) -> Result<TyId> {
        let id = self.next_id()?;
        self.slots.push(Slot::Ty(ty));
        Ok(id)
    }

    /// `Set(t)`.
    ///
    /// # Errors
    ///
    /// As [`Inference::mk`].
    pub fn set_of(&mut self, t: TyId) -> Result<TyId> {
        self.mk(Ty::Set(t))
    }

    /// `Bool`.
    ///
    /// # Errors
    ///
    /// As [`Inference::mk`].
    pub fn bool_ty(&mut self) -> Result<TyId> {
        self.mk(Ty::Bool)
    }

    /// `Int`.
    ///
    /// # Errors
    ///
    /// As [`Inference::mk`].
    pub fn int_ty(&mut self) -> Result<TyId> {
        self.mk(Ty::Int)
    }

    /// `Str`.
    ///
    /// # Errors
    ///
    /// As [`Inference::mk`].
    pub fn str_ty(&mut self) -> Result<TyId> {
        self.mk(Ty::Str)
    }

    /// The representative slot of `id`, with path compression.
    ///
    /// Iterative: a long chain of links is user-reachable.
    #[must_use]
    pub fn find(&mut self, id: TyId) -> TyId {
        let mut root = id;
        while let Some(Slot::Link(next)) = self.slots.get(root.0 as usize) {
            root = *next;
        }
        let mut cur = id;
        while let Some(Slot::Link(next)) = self.slots.get(cur.0 as usize).cloned() {
            if let Some(s) = self.slots.get_mut(cur.0 as usize) {
                *s = Slot::Link(root);
            }
            cur = next;
        }
        root
    }

    /// The structure of `id`, if it has one.
    #[must_use]
    pub fn shape(&mut self, id: TyId) -> Option<Ty> {
        let r = self.find(id);
        match self.slots.get(r.0 as usize) {
            Some(Slot::Ty(t)) => Some(t.clone()),
            _ => None,
        }
    }

    fn set_slot(&mut self, id: TyId, slot: Slot) {
        if let Some(s) = self.slots.get_mut(id.0 as usize) {
            *s = slot;
        }
    }

    fn tick(&mut self) -> Result<()> {
        self.spent += 1;
        if self.spent > self.budget {
            return Err(TypeError::BudgetExhausted { limit: self.budget });
        }
        Ok(())
    }

    // ---- unification ----

    /// Require two types to be equal.
    ///
    /// # Errors
    ///
    /// Returns the mismatch, never a silent approximation.
    pub fn unify(&mut self, a: TyId, b: TyId) -> Result<()> {
        let mut work = vec![(a, b)];
        while let Some((x, y)) = work.pop() {
            self.tick()?;
            let rx = self.find(x);
            let ry = self.find(y);
            if rx == ry {
                continue;
            }
            let sx = self.slots.get(rx.0 as usize).cloned();
            let sy = self.slots.get(ry.0 as usize).cloned();
            match (sx, sy) {
                (Some(Slot::Free), _) => {
                    self.occurs(rx, ry)?;
                    self.set_slot(rx, Slot::Link(ry));
                }
                (_, Some(Slot::Free)) => {
                    self.occurs(ry, rx)?;
                    self.set_slot(ry, Slot::Link(rx));
                }
                (Some(Slot::Ty(tx)), Some(Slot::Ty(ty))) => {
                    self.decompose(rx, &tx, ry, &ty, &mut work)?;
                }
                // A `Link` cannot survive `find`, and an out-of-range id cannot
                // be produced by this module; neither is reachable.
                _ => {
                    return Err(TypeError::Mismatch {
                        left: self.render(rx),
                        right: self.render(ry),
                    });
                }
            }
        }
        Ok(())
    }

    /// Break two structures into the equalities they imply, and decide which
    /// representative survives.
    fn decompose(
        &mut self,
        rx: TyId,
        tx: &Ty,
        ry: TyId,
        ty: &Ty,
        work: &mut Vec<(TyId, TyId)>,
    ) -> Result<()> {
        match (tx, ty) {
            (Ty::Bool, Ty::Bool) | (Ty::Int, Ty::Int) | (Ty::Str, Ty::Str) => Ok(()),
            (Ty::Set(a), Ty::Set(b)) | (Ty::Seq(a), Ty::Seq(b)) => {
                work.push((*a, *b));
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }
            (Ty::Fun(a1, r1), Ty::Fun(a2, r2)) => {
                work.push((*a1, *a2));
                work.push((*r1, *r2));
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }
            (Ty::Tuple(xs), Ty::Tuple(ys)) => {
                if xs.len() == ys.len() {
                    for (p, q) in xs.iter().zip(ys.iter()) {
                        work.push((*p, *q));
                    }
                    self.set_slot(rx, Slot::Link(ry));
                    return Ok(());
                }
                // Different arities are not automatically an error. TLA+ has
                // no separate sequence syntax — `<<3, 5, 7, 8>>` is written
                // exactly like a 4-tuple — so a set of traces such as
                // `{<<3, 5, 7, 8>>, <<2, 4, 6, 7, 8>>}` is a perfectly ordinary
                // set of *sequences*. Two tuples of different length can only
                // share a type by being sequences, so that is what they become,
                // and every component is equated with the element type. If the
                // components genuinely disagree, the sub-unification reports
                // that conflict, which is the informative one.
                let elem = self.fresh()?;
                for p in xs.iter().chain(ys.iter()) {
                    work.push((*p, elem));
                }
                self.set_slot(ry, Slot::Ty(Ty::Seq(elem)));
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }

            // A TLA+ tuple *is* a function on `1..n`, so these meet by
            // equating components. The tuple survives: it carries the arity,
            // which the encoder needs and the other two do not have.
            (Ty::Tuple(xs), Ty::Seq(e)) => {
                for p in xs {
                    work.push((*p, *e));
                }
                // The tuple survives *except* when it is empty: a 0-tuple
                // constrains nothing, so keeping it would discard the only
                // informative shape of the two.
                if xs.is_empty() {
                    self.set_slot(rx, Slot::Link(ry));
                } else {
                    self.set_slot(ry, Slot::Link(rx));
                }
                Ok(())
            }
            (Ty::Seq(e), Ty::Tuple(xs)) => {
                for p in xs {
                    work.push((*p, *e));
                }
                if xs.is_empty() {
                    self.set_slot(ry, Slot::Link(rx));
                } else {
                    self.set_slot(rx, Slot::Link(ry));
                }
                Ok(())
            }
            (Ty::Tuple(xs), Ty::Fun(d, r)) => {
                let int = self.int_ty()?;
                work.push((*d, int));
                for p in xs {
                    work.push((*p, *r));
                }
                self.set_slot(ry, Slot::Link(rx));
                Ok(())
            }
            (Ty::Fun(d, r), Ty::Tuple(xs)) => {
                let int = self.int_ty()?;
                work.push((*d, int));
                for p in xs {
                    work.push((*p, *r));
                }
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }
            (Ty::Seq(e), Ty::Fun(d, r)) => {
                let int = self.int_ty()?;
                work.push((*d, int));
                work.push((*e, *r));
                self.set_slot(ry, Slot::Link(rx));
                Ok(())
            }
            (Ty::Fun(d, r), Ty::Seq(e)) => {
                let int = self.int_ty()?;
                work.push((*d, int));
                work.push((*e, *r));
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }

            // A record is a function on its field names. This only works when
            // the record is closed: an open row has fields we cannot name, so
            // there is nothing to equate them with.
            (Ty::Rec { fields, tail }, Ty::Fun(d, r)) => {
                self.rec_as_fun(rx, fields, tail.is_some(), ry, *d, *r, work)
            }
            (Ty::Fun(d, r), Ty::Rec { fields, tail }) => {
                self.rec_as_fun(ry, fields, tail.is_some(), rx, *d, *r, work)
            }

            (
                Ty::Rec {
                    fields: f1,
                    tail: t1,
                },
                Ty::Rec {
                    fields: f2,
                    tail: t2,
                },
            ) => self.unify_rows(rx, f1, *t1, ry, f2, *t2, work),

            _ => Err(TypeError::Mismatch {
                left: self.render(rx),
                right: self.render(ry),
            }),
        }
    }

    /// A record is a function on its field names.
    ///
    /// Real TLA+ relies on this: `IOUtils!IOEnv` is
    /// `CHOOSE r \in [STRING -> STRING] : TRUE`, and specifications then write
    /// `IOEnv.GRAPH` for `IOEnv["GRAPH"]`. Both spellings are the same
    /// operation, so the row and the function must meet.
    ///
    /// **The record survives, not the function**, and that choice is not
    /// arbitrary. Keeping the function would impose homogeneity on every field
    /// the record has or may later gain, so a heterogeneous record — which is
    /// the ordinary kind — would then fail on its *second* field access with a
    /// mismatch that the specification does not contain. Keeping the record
    /// imposes nothing, and the one fact the function contributed, that the
    /// domain is `Str`, is recorded on `d` before the function is dropped.
    ///
    /// What is given up is totality: `[STRING -> STRING]` says every string is
    /// in the domain, and an open row does not. That costs precision in the
    /// encoding, never a rejection, which is the right way round for a front
    /// end whose rejections are user-facing.
    #[allow(clippy::too_many_arguments)]
    fn rec_as_fun(
        &mut self,
        rec: TyId,
        fields: &BTreeMap<String, TyId>,
        open: bool,
        fun: TyId,
        d: TyId,
        r: TyId,
        work: &mut Vec<(TyId, TyId)>,
    ) -> Result<()> {
        let s = self.str_ty()?;
        work.push((d, s));
        // A closed record names every field it has, so equating each with the
        // range is exact. An open row does not, so only the known fields are
        // constrained and the rest stay free.
        if !open {
            for v in fields.values() {
                work.push((*v, r));
            }
        }
        self.set_slot(fun, Slot::Link(rec));
        Ok(())
    }

    /// Rémy-style row unification.
    #[allow(clippy::too_many_arguments)]
    fn unify_rows(
        &mut self,
        rx: TyId,
        f1: &BTreeMap<String, TyId>,
        t1: Option<TyId>,
        ry: TyId,
        f2: &BTreeMap<String, TyId>,
        t2: Option<TyId>,
        work: &mut Vec<(TyId, TyId)>,
    ) -> Result<()> {
        for (k, v1) in f1 {
            if let Some(v2) = f2.get(k) {
                work.push((*v1, *v2));
            }
        }
        let only1: BTreeMap<String, TyId> = f1
            .iter()
            .filter(|(k, _)| !f2.contains_key(*k))
            .map(|(k, v)| (k.clone(), *v))
            .collect();
        let only2: BTreeMap<String, TyId> = f2
            .iter()
            .filter(|(k, _)| !f1.contains_key(*k))
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        match (t1, t2) {
            (None, None) => {
                if !only1.is_empty() || !only2.is_empty() {
                    let missing = only1.keys().chain(only2.keys()).next().cloned();
                    return Err(match missing {
                        Some(field) => TypeError::NoField {
                            field,
                            have: f1.keys().cloned().collect::<Vec<_>>().join(", "),
                        },
                        None => TypeError::Mismatch {
                            left: self.render(rx),
                            right: self.render(ry),
                        },
                    });
                }
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }
            (Some(v1), None) => {
                if !only1.is_empty() {
                    return Err(TypeError::NoField {
                        field: only1.keys().cloned().collect::<Vec<_>>().join(", "),
                        have: f2.keys().cloned().collect::<Vec<_>>().join(", "),
                    });
                }
                let rest = self.mk(Ty::Rec {
                    fields: only2,
                    tail: None,
                })?;
                work.push((v1, rest));
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }
            (None, Some(v2)) => {
                if !only2.is_empty() {
                    return Err(TypeError::NoField {
                        field: only2.keys().cloned().collect::<Vec<_>>().join(", "),
                        have: f1.keys().cloned().collect::<Vec<_>>().join(", "),
                    });
                }
                let rest = self.mk(Ty::Rec {
                    fields: only1,
                    tail: None,
                })?;
                work.push((v2, rest));
                self.set_slot(ry, Slot::Link(rx));
                Ok(())
            }
            (Some(v1), Some(v2)) => {
                if only1.is_empty() && only2.is_empty() {
                    work.push((v1, v2));
                    self.set_slot(rx, Slot::Link(ry));
                    return Ok(());
                }
                let shared = self.fresh()?;
                let r2 = self.mk(Ty::Rec {
                    fields: only2,
                    tail: Some(shared),
                })?;
                let r1 = self.mk(Ty::Rec {
                    fields: only1,
                    tail: Some(shared),
                })?;
                work.push((v1, r2));
                work.push((v2, r1));
                // Both sides grow to the union of the fields; keep one.
                let merged: BTreeMap<String, TyId> = f1
                    .iter()
                    .chain(f2.iter())
                    .map(|(k, v)| (k.clone(), *v))
                    .collect();
                self.set_slot(
                    ry,
                    Slot::Ty(Ty::Rec {
                        fields: merged,
                        tail: Some(shared),
                    }),
                );
                self.set_slot(rx, Slot::Link(ry));
                Ok(())
            }
        }
    }

    /// Reject binding `var` to a type that contains it.
    fn occurs(&mut self, var: TyId, ty: TyId) -> Result<()> {
        let v = self.find(var);
        let mut stack = vec![ty];
        let mut seen: std::collections::HashSet<TyId> = std::collections::HashSet::new();
        while let Some(t) = stack.pop() {
            self.tick()?;
            let r = self.find(t);
            if r == v {
                return Err(TypeError::Occurs {
                    var: format!("'{}", v.0),
                    ty: self.render(ty),
                });
            }
            if !seen.insert(r) {
                continue;
            }
            if let Some(Slot::Ty(s)) = self.slots.get(r.0 as usize).cloned() {
                push_children(&s, &mut stack);
            }
        }
        Ok(())
    }

    // ---- materialisation ----

    /// Materialise a type as a tree.
    ///
    /// # Errors
    ///
    /// Fails if the tree would exceed [`DEFAULT_MATERIALISE_LIMIT`] nodes. The
    /// arena is a DAG, so a shared type can expand quadratically or worse.
    pub fn to_type(&mut self, id: TyId) -> Result<Type> {
        self.to_type_bounded(id, DEFAULT_MATERIALISE_LIMIT)
    }

    /// Materialise with an explicit node budget.
    ///
    /// # Errors
    ///
    /// Fails if the tree exceeds `limit` nodes.
    pub fn to_type_bounded(&mut self, id: TyId, limit: usize) -> Result<Type> {
        enum F {
            Expand(TyId),
            Build(TyId),
        }
        let mut stack = vec![F::Expand(id)];
        let mut out: Vec<Type> = Vec::new();
        let mut nodes = 0usize;
        while let Some(f) = stack.pop() {
            match f {
                F::Expand(t) => {
                    nodes += 1;
                    if nodes > limit {
                        return Err(TypeError::BudgetExhausted { limit });
                    }
                    let r = self.find(t);
                    match self.slots.get(r.0 as usize).cloned() {
                        Some(Slot::Ty(s)) => {
                            stack.push(F::Build(r));
                            let mut kids = Vec::new();
                            push_children(&s, &mut kids);
                            // Children are popped in reverse, so push reversed
                            // to have them arrive in order.
                            for k in kids.into_iter().rev() {
                                stack.push(F::Expand(k));
                            }
                        }
                        _ => out.push(Type::Var(r.0)),
                    }
                }
                F::Build(r) => {
                    let Some(Slot::Ty(s)) = self.slots.get(r.0 as usize).cloned() else {
                        // `Build` is only pushed alongside a `Ty` slot, and
                        // nothing between the two can rewrite it.
                        return Err(TypeError::Mismatch {
                            left: format!("'{}", r.0),
                            right: "a resolved type".to_string(),
                        });
                    };
                    let n = child_count(&s);
                    let at = out.len().saturating_sub(n);
                    let kids: Vec<Type> = out.split_off(at);
                    if kids.len() != n {
                        return Err(TypeError::BudgetExhausted { limit });
                    }
                    out.push(rebuild(&s, kids));
                }
            }
        }
        out.pop().ok_or(TypeError::BudgetExhausted { limit })
    }

    /// Render a type for a diagnostic, never failing.
    fn render(&mut self, id: TyId) -> String {
        match self.to_type_bounded(id, 4_096) {
            Ok(t) => t.to_string(),
            Err(_) => format!("'{}", self.find(id).0),
        }
    }
}

fn child_count(t: &Ty) -> usize {
    match t {
        Ty::Bool | Ty::Int | Ty::Str => 0,
        Ty::Set(_) | Ty::Seq(_) => 1,
        Ty::Fun(_, _) => 2,
        Ty::Tuple(xs) => xs.len(),
        Ty::Rec { fields, .. } => fields.len(),
    }
}

fn push_children(t: &Ty, out: &mut Vec<TyId>) {
    match t {
        Ty::Bool | Ty::Int | Ty::Str => {}
        Ty::Set(a) | Ty::Seq(a) => out.push(*a),
        Ty::Fun(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        Ty::Tuple(xs) => out.extend(xs.iter().copied()),
        // The row tail is deliberately not a child: it stands for fields we
        // cannot name, so materialising it would invent field names.
        Ty::Rec { fields, .. } => out.extend(fields.values().copied()),
    }
}

fn rebuild(t: &Ty, kids: Vec<Type>) -> Type {
    let mut it = kids.into_iter();
    match t {
        Ty::Bool => Type::Bool,
        Ty::Int => Type::Int,
        Ty::Str => Type::Str,
        Ty::Set(_) => match it.next() {
            Some(a) => Type::Set(Box::new(a)),
            None => Type::Var(u32::MAX),
        },
        Ty::Seq(_) => match it.next() {
            Some(a) => Type::Seq(Box::new(a)),
            None => Type::Var(u32::MAX),
        },
        Ty::Fun(_, _) => match (it.next(), it.next()) {
            (Some(a), Some(b)) => Type::Fun(Box::new(a), Box::new(b)),
            _ => Type::Var(u32::MAX),
        },
        Ty::Tuple(_) => Type::Tuple(it.collect()),
        Ty::Rec { fields, tail } => Type::Rec {
            fields: fields.keys().cloned().zip(it).collect(),
            open: tail.is_some(),
        },
    }
}

// ---------------------------------------------------------------------------
// Constraint generation
// ---------------------------------------------------------------------------

/// A frame of the inference walk.
enum Step<'a> {
    /// Introduce a binder's variable, then descend.
    Visit(&'a KeraRef),
    /// All children are typed; type this node.
    Build(&'a KeraRef),
}

impl Inference {
    /// Infer the type of a kernel term.
    ///
    /// The term is walked with an explicit stack and memoised by pointer
    /// identity, so a lowered term that shares a subterm in a thousand places
    /// is typed once rather than a thousand times.
    ///
    /// # Errors
    ///
    /// Returns the first type conflict, ambiguity or budget exhaustion. Never
    /// assigns a type it could not derive.
    pub fn infer(&mut self, term: &KeraRef) -> Result<TyId> {
        self.roots.push(Rc::clone(term));
        let mut stack = vec![Step::Visit(term)];
        while let Some(step) = stack.pop() {
            self.tick()?;
            match step {
                Step::Visit(node) => {
                    if self.memo.contains_key(&Rc::as_ptr(node)) {
                        continue;
                    }
                    // A binder's variable must have a type before its body is
                    // walked. Lowering renames every binder uniquely, so a flat
                    // environment is enough and no scope stack is needed.
                    for var in node.binders() {
                        if !self.env.contains_key(var) {
                            let v = self.fresh()?;
                            self.env.insert(var.clone(), v);
                        }
                    }
                    stack.push(Step::Build(node));
                    for child in node.as_ref().children() {
                        stack.push(Step::Visit(child));
                    }
                }
                Step::Build(node) => {
                    if self.memo.contains_key(&Rc::as_ptr(node)) {
                        continue;
                    }
                    let t = self.build(node)?;
                    self.memo.insert(Rc::as_ptr(node), t);
                }
            }
        }
        let root = self
            .memo
            .get(&Rc::as_ptr(term))
            .copied()
            .ok_or(TypeError::BudgetExhausted { limit: self.budget })?;
        self.solve_deferred()?;
        Ok(root)
    }

    /// The type already computed for a child.
    fn child(&self, node: &KeraRef) -> Result<TyId> {
        self.memo
            .get(&Rc::as_ptr(node))
            .copied()
            .ok_or(TypeError::BudgetExhausted { limit: self.budget })
    }

    /// The type of a name, creating a free one on first sight.
    fn name_ty(&mut self, n: &Name) -> Result<TyId> {
        if let Some(t) = self.env.get(n) {
            return Ok(*t);
        }
        let v = self.fresh()?;
        self.env.insert(n.clone(), v);
        self.free.insert(n.0.clone(), v);
        Ok(v)
    }

    #[allow(clippy::too_many_lines)]
    fn build(&mut self, node: &KeraRef) -> Result<TyId> {
        match node.as_ref() {
            Kera::Bool(_) => Ok(self.bool_ty()?),
            Kera::Int(_) => Ok(self.int_ty()?),
            Kera::Str(_) => Ok(self.str_ty()?),
            Kera::Var(n) => Ok(self.name_ty(n)?),
            // `x'` denotes the next-state value of `x`, which is the same kind
            // of value: priming cannot change a type.
            Kera::Prime(a) => self.child(a),

            Kera::Not(a) => {
                let t = self.child(a)?;
                let b = self.bool_ty()?;
                self.unify(t, b)?;
                Ok(b)
            }
            Kera::And(xs) | Kera::Or(xs) => {
                let b = self.bool_ty()?;
                for x in xs {
                    let t = self.child(x)?;
                    self.unify(t, b)?;
                }
                Ok(b)
            }
            Kera::Ite(c, t, e) => {
                let tc = self.child(c)?;
                let b = self.bool_ty()?;
                self.unify(tc, b)?;
                let tt = self.child(t)?;
                let te = self.child(e)?;
                self.unify(tt, te)?;
                Ok(tt)
            }

            Kera::Forall { var, set, body } | Kera::Exists { var, set, body } => {
                let elem = self.name_ty(var)?;
                let ts = self.child(set)?;
                let want = self.set_of(elem)?;
                self.unify(ts, want)?;
                let tb = self.child(body)?;
                let b = self.bool_ty()?;
                self.unify(tb, b)?;
                Ok(b)
            }
            Kera::Choose { var, set, body } => {
                let elem = self.name_ty(var)?;
                let ts = self.child(set)?;
                let want = self.set_of(elem)?;
                self.unify(ts, want)?;
                let tb = self.child(body)?;
                let b = self.bool_ty()?;
                self.unify(tb, b)?;
                Ok(elem)
            }
            Kera::ChooseUnbounded { var, body } => {
                let elem = self.name_ty(var)?;
                let tb = self.child(body)?;
                let b = self.bool_ty()?;
                self.unify(tb, b)?;
                Ok(elem)
            }

            Kera::Eq(a, b) => {
                let ta = self.child(a)?;
                let tb = self.child(b)?;
                self.unify(ta, tb)?;
                Ok(self.bool_ty()?)
            }
            Kera::In(a, s) => {
                let ta = self.child(a)?;
                let ts = self.child(s)?;
                let want = self.set_of(ta)?;
                self.unify(ts, want)?;
                Ok(self.bool_ty()?)
            }

            Kera::SetEnum(xs) => {
                let elem = self.fresh()?;
                for x in xs {
                    let t = self.child(x)?;
                    self.unify(t, elem)?;
                }
                Ok(self.set_of(elem)?)
            }
            Kera::Filter { var, set, pred } => {
                let elem = self.name_ty(var)?;
                let ts = self.child(set)?;
                let want = self.set_of(elem)?;
                self.unify(ts, want)?;
                let tp = self.child(pred)?;
                let b = self.bool_ty()?;
                self.unify(tp, b)?;
                Ok(want)
            }
            Kera::Map { var, set, expr } => {
                let elem = self.name_ty(var)?;
                let ts = self.child(set)?;
                let want = self.set_of(elem)?;
                self.unify(ts, want)?;
                let te = self.child(expr)?;
                Ok(self.set_of(te)?)
            }
            // A fold's signature, from `Apalache.tla`:
            //
            //     ApaFoldSet     : ((a, b) => a, a, Set(b)) => a
            //     ApaFoldSeqLeft : ((a, b) => a, a, Seq(b)) => a
            //
            // The accumulator is the base's type and the result's, which is
            // what makes a fold typeable at all without an operator type: the
            // two parameters are ordinary names in the environment, unified
            // against the base and the collection's element.
            Kera::Fold {
                over,
                acc,
                elem,
                base,
                collection,
                body,
            } => {
                let ta = self.name_ty(acc)?;
                let te = self.name_ty(elem)?;
                let tbase = self.child(base)?;
                self.unify(ta, tbase)?;
                let tcoll = self.child(collection)?;
                let want = match over {
                    crate::kera::FoldOver::Set => self.set_of(te)?,
                    crate::kera::FoldOver::SeqLeft => self.mk(Ty::Seq(te))?,
                };
                self.unify(tcoll, want)?;
                // The operator returns the accumulator's type. This is the
                // constraint that catches `ApaFoldSet(LAMBDA a, b: a > b, …)`,
                // where the body is a Boolean and the base is not.
                let tbody = self.child(body)?;
                self.unify(tbody, ta)?;
                Ok(ta)
            }
            Kera::SetBin(_, a, b) => {
                let ta = self.child(a)?;
                let tb = self.child(b)?;
                self.unify(ta, tb)?;
                let elem = self.fresh()?;
                let want = self.set_of(elem)?;
                self.unify(ta, want)?;
                Ok(want)
            }
            Kera::Powerset(a) => {
                let ta = self.child(a)?;
                let elem = self.fresh()?;
                let inner = self.set_of(elem)?;
                self.unify(ta, inner)?;
                Ok(self.set_of(inner)?)
            }
            Kera::BigUnion(a) => {
                let ta = self.child(a)?;
                let elem = self.fresh()?;
                let inner = self.set_of(elem)?;
                let outer = self.set_of(inner)?;
                self.unify(ta, outer)?;
                Ok(inner)
            }
            Kera::Range(a, b) => {
                let int = self.int_ty()?;
                let ta = self.child(a)?;
                let tb = self.child(b)?;
                self.unify(ta, int)?;
                self.unify(tb, int)?;
                Ok(self.set_of(int)?)
            }
            Kera::Times(xs) => {
                let mut parts = Vec::with_capacity(xs.len());
                for x in xs {
                    let tx = self.child(x)?;
                    let elem = self.fresh()?;
                    let want = self.set_of(elem)?;
                    self.unify(tx, want)?;
                    parts.push(elem);
                }
                let tup = self.mk(Ty::Tuple(parts))?;
                Ok(self.set_of(tup)?)
            }

            Kera::FunDef { var, set, body } => {
                let elem = self.name_ty(var)?;
                let ts = self.child(set)?;
                let want = self.set_of(elem)?;
                self.unify(ts, want)?;
                let tb = self.child(body)?;
                Ok(self.mk(Ty::Fun(elem, tb))?)
            }
            Kera::FunApp(f, i) => {
                let tf = self.child(f)?;
                let out = self.fresh()?;
                self.apply(tf, i, out, node)?;
                Ok(out)
            }
            Kera::Domain(f) => {
                let tf = self.child(f)?;
                self.domain_of(tf, render_kera(node.as_ref()))
            }
            Kera::Except { fun, index, value } => {
                let tf = self.child(fun)?;
                let tv = self.child(value)?;
                self.apply(tf, index, tv, node)?;
                Ok(tf)
            }
            Kera::FunSet { set, cod } => {
                let ts = self.child(set)?;
                let tc = self.child(cod)?;
                let d = self.fresh()?;
                let r = self.fresh()?;
                let ds = self.set_of(d)?;
                let rs = self.set_of(r)?;
                self.unify(ts, ds)?;
                self.unify(tc, rs)?;
                let f = self.mk(Ty::Fun(d, r))?;
                Ok(self.set_of(f)?)
            }

            Kera::Tuple(xs) => {
                // `<<>>` is the empty *sequence*, not a zero-component tuple.
                // A 0-tuple carries no component to learn anything from, and
                // typing it as one is not merely useless: unifying it with
                // `Seq(e)` equates zero components, so it succeeds vacuously
                // and the arity-0 shape survives. Every later `s[i]` on that
                // sequence is then "index outside a 0-tuple". Found on the
                // corpus, where it accounted for 78 mis-shaped state variables.
                if xs.is_empty() {
                    let e = self.fresh()?;
                    return self.mk(Ty::Seq(e));
                }
                let mut parts = Vec::with_capacity(xs.len());
                for x in xs {
                    parts.push(self.child(x)?);
                }
                Ok(self.mk(Ty::Tuple(parts))?)
            }
            Kera::Record(fs) => {
                let mut fields = BTreeMap::new();
                for (k, v) in fs {
                    fields.insert(k.clone(), self.child(v)?);
                }
                Ok(self.mk(Ty::Rec { fields, tail: None })?)
            }
            Kera::RecordSet(fs) => {
                let mut fields = BTreeMap::new();
                for (k, v) in fs {
                    let tv = self.child(v)?;
                    let elem = self.fresh()?;
                    let want = self.set_of(elem)?;
                    self.unify(tv, want)?;
                    fields.insert(k.clone(), elem);
                }
                let rec = self.mk(Ty::Rec { fields, tail: None })?;
                Ok(self.set_of(rec)?)
            }

            Kera::Arith(op, a, b) => {
                let int = self.int_ty()?;
                let ta = self.child(a)?;
                let tb = self.child(b)?;
                self.unify(ta, int)?;
                self.unify(tb, int)?;
                let _ = op; // every arithmetic operator has the same signature
                Ok(int)
            }
            Kera::Neg(a) => {
                let int = self.int_ty()?;
                let ta = self.child(a)?;
                self.unify(ta, int)?;
                Ok(int)
            }
            Kera::Cmp(_, a, b) => {
                let int = self.int_ty()?;
                let ta = self.child(a)?;
                let tb = self.child(b)?;
                self.unify(ta, int)?;
                self.unify(tb, int)?;
                Ok(self.bool_ty()?)
            }

            Kera::Opaque(name, args) => self.opaque_ty(name, args),
        }
    }

    /// Type `f[i]`, where `out` is the element type.
    ///
    /// Three cases, because TLA+ overloads application:
    ///
    /// * a **string literal** index means a record field — lowering turns
    ///   `r.foo` into exactly this — so it yields an *open* row saying only
    ///   that the field is present;
    /// * an **integer literal** index could be a tuple, a sequence or a
    ///   function, and the three differ, so it is deferred until the subject's
    ///   shape is known;
    /// * anything else must be a function, since a non-literal index into a
    ///   tuple is only well typed when the tuple is homogeneous, which the
    ///   `Tuple`/`Fun` unification rule then enforces.
    fn apply(&mut self, tf: TyId, index: &KeraRef, out: TyId, node: &KeraRef) -> Result<()> {
        match index.as_ref() {
            Kera::Str(field) => {
                let row = self.fresh()?;
                let mut fields = BTreeMap::new();
                fields.insert(field.clone(), out);
                let rec = self.mk(Ty::Rec {
                    fields,
                    tail: Some(row),
                })?;
                self.unify(tf, rec)
            }
            Kera::Int(digits) => match digits.parse::<i64>() {
                Ok(i) => {
                    self.deferred.push(Deferred {
                        subject: tf,
                        index: i,
                        out,
                        what: render_kera(node.as_ref()),
                    });
                    Ok(())
                }
                // A literal too wide for an index cannot be a tuple position,
                // so the subject can only be a function.
                Err(_) => {
                    let ti = self.child(index)?;
                    let want = self.mk(Ty::Fun(ti, out))?;
                    self.unify(tf, want)
                }
            },
            _ => {
                let ti = self.child(index)?;
                let want = self.mk(Ty::Fun(ti, out))?;
                self.unify(tf, want)
            }
        }
    }

    /// `DOMAIN f`, which requires only that `f` be applicable.
    ///
    /// Unlike an index, this needs no deferral, because `Fun(d, r)` is the
    /// *top* of the shape lattice rather than a guess among equals: a tuple,
    /// a sequence and a record are each a function, and the unification rules
    /// above let all three meet `Fun` and refine `d` to `Int` or `Str`
    /// accordingly. Committing here therefore rules nothing out.
    ///
    /// A **literal index** is the opposite case and does need deferring:
    /// `Tuple ~ Fun(Int, out)` forces every component to the same type, so
    /// committing there would reject the heterogeneous tuples TLA+ allows.
    fn domain_of(&mut self, tf: TyId, what: String) -> Result<TyId> {
        let d = self.fresh()?;
        let r = self.fresh()?;
        let want = self.mk(Ty::Fun(d, r))?;
        if self.unify(tf, want).is_err() {
            return Err(TypeError::Mismatch {
                left: self.render(tf),
                right: format!("a function, in `{what}`"),
            });
        }
        self.set_of(d)
    }

    /// The signature of an operator lowering could not inline.
    fn opaque_ty(&mut self, name: &Name, args: &[KeraRef]) -> Result<TyId> {
        let mut arg_tys = Vec::with_capacity(args.len());
        for a in args {
            arg_tys.push(self.child(a)?);
        }
        // `CASE` with no matching arm is TLA+-undefined. It is the bottom of
        // the type lattice — the Elixir gradual-typing work calls this `none` —
        // so a fresh variable per occurrence is exactly right: it fits
        // wherever it lands and constrains nothing.
        if name.as_str() == "$CaseNoMatch" {
            return self.fresh();
        }
        if let Some(result) = self.standard_sig(name.as_str(), &arg_tys)? {
            return Ok(result);
        }
        // A declared-but-undefined operator is monomorphic per name and arity,
        // as Apalache treats a `CONSTANT Op(_, _)`: nothing in the
        // specification says it is polymorphic, and assuming so would accept
        // programs TLA+ does not.
        let key = (name.0.clone(), args.len());
        if let Some((params, result)) = self.opaque.get(&key).cloned() {
            for (p, a) in params.iter().zip(arg_tys.iter()) {
                self.unify(*p, *a)?;
            }
            return Ok(result);
        }
        let result = self.fresh()?;
        self.opaque.insert(key, (arg_tys, result));
        Ok(result)
    }

    /// Signatures of the standard modules' operators, freshly instantiated at
    /// each use because they are genuinely polymorphic.
    ///
    /// Returns `None` for a name with no known signature, so the caller falls
    /// back to a monomorphic one rather than inventing something.
    fn standard_sig(&mut self, name: &str, args: &[TyId]) -> Result<Option<TyId>> {
        let arity = args.len();
        let a = |s: &mut Self| s.fresh();
        let out = match (name, arity) {
            ("Len", 1) => {
                let e = a(self)?;
                let seq = self.mk(Ty::Seq(e))?;
                self.unify(args[0], seq)?;
                self.int_ty()?
            }
            ("Head", 1) => {
                let e = a(self)?;
                let seq = self.mk(Ty::Seq(e))?;
                self.unify(args[0], seq)?;
                e
            }
            ("Tail", 1) => {
                let e = a(self)?;
                let seq = self.mk(Ty::Seq(e))?;
                self.unify(args[0], seq)?;
                seq
            }
            ("Append", 2) => {
                let e = a(self)?;
                let seq = self.mk(Ty::Seq(e))?;
                self.unify(args[0], seq)?;
                self.unify(args[1], e)?;
                seq
            }
            ("\\o", 2) => {
                let e = a(self)?;
                let seq = self.mk(Ty::Seq(e))?;
                self.unify(args[0], seq)?;
                self.unify(args[1], seq)?;
                seq
            }
            ("SubSeq", 3) => {
                let e = a(self)?;
                let seq = self.mk(Ty::Seq(e))?;
                let int = self.int_ty()?;
                self.unify(args[0], seq)?;
                self.unify(args[1], int)?;
                self.unify(args[2], int)?;
                seq
            }
            ("SelectSeq", 2) => {
                let e = a(self)?;
                let seq = self.mk(Ty::Seq(e))?;
                let b = self.bool_ty()?;
                let pred = self.mk(Ty::Fun(e, b))?;
                self.unify(args[0], seq)?;
                self.unify(args[1], pred)?;
                seq
            }
            ("Seq", 1) => {
                let e = a(self)?;
                let elems = self.set_of(e)?;
                self.unify(args[0], elems)?;
                let seq = self.mk(Ty::Seq(e))?;
                self.set_of(seq)?
            }
            ("Cardinality", 1) => {
                let e = a(self)?;
                let s = self.set_of(e)?;
                self.unify(args[0], s)?;
                self.int_ty()?
            }
            ("IsFiniteSet", 1) => {
                let e = a(self)?;
                let s = self.set_of(e)?;
                self.unify(args[0], s)?;
                self.bool_ty()?
            }
            (":>", 2) => self.mk(Ty::Fun(args[0], args[1]))?,
            ("@@", 2) => {
                let d = a(self)?;
                let r = a(self)?;
                let f = self.mk(Ty::Fun(d, r))?;
                self.unify(args[0], f)?;
                self.unify(args[1], f)?;
                f
            }
            ("Assert", 2) => {
                let b = self.bool_ty()?;
                self.unify(args[0], b)?;
                b
            }
            ("PrintT", 1) => self.bool_ty()?,
            ("Print", 2) => args[1],
            ("Nat" | "Int", 0) => {
                let int = self.int_ty()?;
                self.set_of(int)?
            }
            ("STRING", 0) => {
                let s = self.str_ty()?;
                self.set_of(s)?
            }
            _ => return Ok(None),
        };
        Ok(Some(out))
    }

    /// Discharge the index constraints that had to wait for a shape.
    ///
    /// Runs to a fixed point: resolving one can resolve another. Anything
    /// still unresolved is *reported*, not guessed — see [`TypeError::Ambiguous`].
    fn solve_deferred(&mut self) -> Result<()> {
        loop {
            let mut progress = false;
            let mut pending: Vec<Deferred> = Vec::new();
            for d in std::mem::take(&mut self.deferred) {
                self.tick()?;
                let Some(shape) = self.shape(d.subject) else {
                    pending.push(d);
                    continue;
                };
                progress = true;
                self.resolve_index(&d, &shape, d.index, d.out)?;
            }
            self.deferred = pending;
            if self.deferred.is_empty() {
                return Ok(());
            }
            if !progress {
                let d = self.deferred.remove(0);
                return Err(TypeError::Ambiguous { what: d.what });
            }
        }
    }

    /// Discharge `f[i]` once `f`'s shape is known.
    fn resolve_index(&mut self, d: &Deferred, shape: &Ty, index: i64, out: TyId) -> Result<()> {
        match shape {
            Ty::Tuple(parts) => {
                let Some(p) = usize::try_from(index)
                    .ok()
                    .filter(|i| *i >= 1)
                    .and_then(|i| parts.get(i - 1).copied())
                else {
                    return Err(TypeError::TupleIndex {
                        index,
                        arity: parts.len(),
                    });
                };
                self.unify(p, out)
            }
            Ty::Seq(e) => self.unify(*e, out),
            Ty::Fun(dom, r) => {
                let int = self.int_ty()?;
                self.unify(*dom, int)?;
                self.unify(*r, out)
            }
            Ty::Rec { .. } => Err(TypeError::Mismatch {
                left: self.render(d.subject),
                right: format!("indexable by {index}, in `{}`", d.what),
            }),
            Ty::Bool | Ty::Int | Ty::Str | Ty::Set(_) => Err(TypeError::Mismatch {
                left: self.render(d.subject),
                right: format!("a function, in `{}`", d.what),
            }),
        }
    }
}

/// Describe an expression for a diagnostic, shallowly.
///
/// Deliberately shallow: a diagnostic that printed a lowered term in full
/// would print an inlined definition, which is not what the user wrote.
fn render_kera(node: &Kera) -> String {
    match node {
        Kera::FunApp(f, i) => format!("{}[{}]", head_of(f), head_of(i)),
        Kera::Except { fun, index, .. } => {
            format!("[{} EXCEPT ![{}] = ...]", head_of(fun), head_of(index))
        }
        Kera::Domain(f) => format!("DOMAIN {}", head_of(f)),
        other => head_of_kera(other),
    }
}

fn head_of(node: &KeraRef) -> String {
    head_of_kera(node.as_ref())
}

fn head_of_kera(node: &Kera) -> String {
    match node {
        Kera::Var(n) => n.0.clone(),
        Kera::Int(d) => d.clone(),
        Kera::Str(s) => format!("\"{s}\""),
        Kera::Bool(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
        Kera::Opaque(n, _) => n.0.clone(),
        Kera::FunApp(f, _) => format!("{}[...]", head_of(f)),
        Kera::Prime(a) => format!("{}'", head_of(a)),
        _ => "...".to_string(),
    }
}
