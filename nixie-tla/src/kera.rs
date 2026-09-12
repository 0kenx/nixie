//! **KerA** — the kernel language TLA+ reduces to.
//!
//! `docs/TLA_FRONTEND_DESIGN.md` §2 describes a two-level IR: a *surface* tree
//! that mirrors what the user wrote (that is
//! [`nixie_tla_syntax::ast`]), and a small kernel that is the only thing ever
//! encoded. This is the kernel.
//!
//! # Why a kernel at all
//!
//! TLA+ has a large surface: `CASE`, `LET`, records, `\subseteq`, `EXCEPT`
//! paths, tuple patterns, six spellings of `[`. Every downstream consumer —
//! typing, transition analysis, the encoder — would otherwise have to handle
//! all of it, and each would get a slightly different subset right. Reducing
//! once to a closed enum means everything after this point matches
//! exhaustively, so a new construct **breaks compilation** rather than
//! slipping through a `_ =>` arm. That is the same discipline the solver core
//! runs on, and it is the whole reason the extra pass earns its place.
//!
//! # Where this deliberately differs from Apalache
//!
//! Apalache's Keramelizer expands set operations away: `A \cup B` becomes a
//! comprehension, `\subseteq` becomes a quantifier. That is the right move
//! when the backend is an opaque SMT solver with no set theory, because the
//! expansion is the only way to say it.
//!
//! Nixie has `nixie-theories/src/set`. Keeping `\cup`, `\cap`, `\`, `SUBSET`
//! and `UNION` *in* the kernel is what lets the encoder hand them to a set
//! theory solver instead of blowing them into quantifiers first — opportunity
//! O3 in the design doc. Expanding them here would destroy exactly the
//! structure that optimisation needs, and it cannot be recovered afterwards.

use std::fmt;
use std::rc::Rc;

/// A name in the kernel: a declared constant or variable, or a bound variable.
///
/// Bound variables are renamed during lowering so that every binder in a KerA
/// term is unique, which is what makes substitution capture-free without a
/// separate freshening pass.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(pub String);

impl Name {
    /// Borrow the name text.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Binary arithmetic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Exp,
}

impl ArithOp {
    /// The TLA+ spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "\\div",
            Self::Mod => "%",
            Self::Exp => "^",
        }
    }
}

/// Ordering comparisons.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
}

impl CmpOp {
    /// The TLA+ spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }
}

/// Binary set operations kept in the kernel rather than expanded.
///
/// See the module docs: these survive lowering so the encoder can give them to
/// a set theory instead of a quantifier blow-up.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum SetOp {
    Union,
    Intersect,
    Difference,
}

impl SetOp {
    /// The TLA+ spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Union => "\\cup",
            Self::Intersect => "\\cap",
            Self::Difference => "\\",
        }
    }
}

/// A kernel expression.
///
/// Shared by [`Rc`] because lowering inlines operator definitions, which
/// duplicates subterms; sharing keeps that from blowing up.
pub type KeraRef = Rc<Kera>;

/// The kernel language.
///
/// Deliberately closed and small. Everything the surface syntax offers is
/// either represented here or rejected by name during lowering — never
/// silently dropped.
#[derive(Debug, Clone, PartialEq)]
pub enum Kera {
    // ---- names and literals ----
    /// A constant, variable, or bound variable.
    Var(Name),
    /// `x'`.
    Prime(KeraRef),
    /// An integer literal, kept as written so that wide values stay exact.
    Int(String),
    /// A string literal.
    Str(String),
    /// `TRUE` / `FALSE`.
    Bool(bool),

    // ---- propositional ----
    /// `~p`.
    Not(KeraRef),
    /// n-ary conjunction. Empty means `TRUE`.
    And(Vec<KeraRef>),
    /// n-ary disjunction. Empty means `FALSE`.
    Or(Vec<KeraRef>),
    /// `IF c THEN t ELSE e`.
    Ite(KeraRef, KeraRef, KeraRef),

    // ---- binders (bounded only; unbounded forms are rejected in lowering) ----
    /// `\A x \in set : body`.
    Forall {
        /// The bound variable.
        var: Name,
        /// The set it ranges over.
        set: KeraRef,
        /// The body.
        body: KeraRef,
    },
    /// `\E x \in set : body`.
    Exists {
        /// The bound variable.
        var: Name,
        /// The set it ranges over.
        set: KeraRef,
        /// The body.
        body: KeraRef,
    },
    /// `CHOOSE x : body` — unbounded.
    ///
    /// TLA+ genuinely admits this, and `None == CHOOSE v : v \notin Values` is
    /// a standard idiom for a fresh value, so refusing it would reject a large
    /// share of real specs. The encoder must treat it as an uninterpreted
    /// constant constrained by `body`, not as a search.
    ChooseUnbounded {
        /// The bound variable.
        var: Name,
        /// The predicate.
        body: KeraRef,
    },
    /// `CHOOSE x \in set : body`.
    Choose {
        /// The bound variable.
        var: Name,
        /// The set it ranges over.
        set: KeraRef,
        /// The predicate.
        body: KeraRef,
    },

    // ---- equality and membership ----
    /// `a = b`.
    Eq(KeraRef, KeraRef),
    /// `a \in b`.
    In(KeraRef, KeraRef),

    // ---- sets ----
    /// `{a, b, c}`.
    SetEnum(Vec<KeraRef>),
    /// `{x \in set : pred}`.
    Filter {
        /// The bound variable.
        var: Name,
        /// The set being filtered.
        set: KeraRef,
        /// The predicate.
        pred: KeraRef,
    },
    /// `{expr : x \in set}`.
    Map {
        /// The bound variable.
        var: Name,
        /// The set being mapped over.
        set: KeraRef,
        /// The mapped expression.
        expr: KeraRef,
    },
    /// `\cup`, `\cap`, `\`.
    SetBin(SetOp, KeraRef, KeraRef),
    /// `SUBSET s`.
    Powerset(KeraRef),
    /// `UNION s`.
    BigUnion(KeraRef),
    /// `a .. b`.
    Range(KeraRef, KeraRef),
    /// `A \X B \X …`, always at least two components.
    Times(Vec<KeraRef>),

    // ---- functions ----
    /// `[x \in set |-> body]`.
    FunDef {
        /// The bound variable.
        var: Name,
        /// The domain.
        set: KeraRef,
        /// The body.
        body: KeraRef,
    },
    /// `f[arg]`.
    FunApp(KeraRef, KeraRef),
    /// `DOMAIN f`.
    Domain(KeraRef),
    /// `[f EXCEPT ![index] = value]`, always a single update: multi-update and
    /// multi-step `EXCEPT` forms are nested during lowering.
    Except {
        /// The function being updated.
        fun: KeraRef,
        /// The index to replace.
        index: KeraRef,
        /// The replacement value.
        value: KeraRef,
    },
    /// `[set -> cod]`.
    FunSet {
        /// The domain set.
        set: KeraRef,
        /// The codomain set.
        cod: KeraRef,
    },

    // ---- tuples and records ----
    /// `<<a, b>>`.
    Tuple(Vec<KeraRef>),
    /// `[a |-> x, b |-> y]`. Fields are sorted by name so that two records
    /// written in different orders are structurally equal.
    Record(Vec<(String, KeraRef)>),
    /// `[a : S, b : T]`, fields sorted like [`Kera::Record`].
    RecordSet(Vec<(String, KeraRef)>),

    // ---- arithmetic ----
    /// Binary arithmetic.
    Arith(ArithOp, KeraRef, KeraRef),
    /// Unary minus.
    Neg(KeraRef),
    /// An ordering comparison.
    Cmp(CmpOp, KeraRef, KeraRef),

    /// An application that could not be inlined: an operator declared but not
    /// defined (a `CONSTANT Op(_, _)`), or one imported from a module that was
    /// not resolved.
    ///
    /// Kept rather than rejected so that a spec with a declared operator still
    /// lowers; the encoder decides what it can do with it.
    Opaque(Name, Vec<KeraRef>),
}

impl Kera {
    /// Wrap in an [`Rc`].
    #[must_use]
    pub fn rc(self) -> KeraRef {
        Rc::new(self)
    }

    /// `TRUE`.
    #[must_use]
    pub fn t() -> KeraRef {
        Kera::Bool(true).rc()
    }

    /// `FALSE`.
    #[must_use]
    pub fn f() -> KeraRef {
        Kera::Bool(false).rc()
    }

    /// The direct children of this node, in source order.
    ///
    /// Exhaustive by construction: adding a variant without extending this
    /// stops compilation, which is the point of a closed kernel.
    #[must_use]
    pub fn children(&self) -> Vec<&KeraRef> {
        match self {
            Self::Var(_) | Self::Int(_) | Self::Str(_) | Self::Bool(_) => Vec::new(),
            Self::Prime(a)
            | Self::Not(a)
            | Self::Powerset(a)
            | Self::BigUnion(a)
            | Self::Domain(a)
            | Self::Neg(a) => vec![a],
            Self::ChooseUnbounded { body, .. } => vec![body],
            Self::And(xs)
            | Self::Or(xs)
            | Self::SetEnum(xs)
            | Self::Tuple(xs)
            | Self::Times(xs) => xs.iter().collect(),
            Self::Ite(a, b, c) => vec![a, b, c],
            Self::Forall { set, body, .. }
            | Self::Exists { set, body, .. }
            | Self::Choose { set, body, .. }
            | Self::FunDef { set, body, .. } => vec![set, body],
            Self::Filter { set, pred, .. } => vec![set, pred],
            Self::Map { set, expr, .. } => vec![set, expr],
            Self::Eq(a, b)
            | Self::In(a, b)
            | Self::SetBin(_, a, b)
            | Self::Range(a, b)
            | Self::FunApp(a, b)
            | Self::Arith(_, a, b)
            | Self::Cmp(_, a, b) => vec![a, b],
            Self::Except { fun, index, value } => vec![fun, index, value],
            Self::FunSet { set, cod } => vec![set, cod],
            Self::Record(fs) | Self::RecordSet(fs) => fs.iter().map(|(_, v)| v).collect(),
            Self::Opaque(_, args) => args.iter().collect(),
        }
    }

    /// The name a binder introduces, if this node is a binder.
    #[must_use]
    pub fn binder(&self) -> Option<&Name> {
        match self {
            Self::Forall { var, .. }
            | Self::Exists { var, .. }
            | Self::Choose { var, .. }
            | Self::ChooseUnbounded { var, .. }
            | Self::Filter { var, .. }
            | Self::Map { var, .. }
            | Self::FunDef { var, .. } => Some(var),
            _ => None,
        }
    }

    /// Number of **distinct** nodes in the term.
    ///
    /// This is the size that matters for a shared term. Lowering inlines a
    /// definition's body at every use and shares the result, so a term whose
    /// tree has 2^n nodes may have only n distinct ones — and a naive walk
    /// that does not deduplicate takes exponential time on exactly the inputs
    /// where sharing is doing the most good. Counting by pointer identity is
    /// what makes this linear.
    ///
    /// Walked with an explicit stack: a lowered term is user-controlled.
    #[must_use]
    pub fn dag_size(&self) -> usize {
        let mut seen: std::collections::HashSet<*const Kera> = std::collections::HashSet::new();
        let mut n = 1usize; // the root, which has no `Rc` to identify it by
        let mut stack: Vec<&KeraRef> = self.children();
        while let Some(e) = stack.pop() {
            if !seen.insert(Rc::as_ptr(e)) {
                continue;
            }
            n += 1;
            stack.extend(e.children());
        }
        n
    }

    /// Number of nodes counting every occurrence separately.
    ///
    /// **This is exponential** on a shared term and is provided only for
    /// comparing against a tree-shaped reference; use [`Kera::dag_size`] for
    /// anything that runs over real input. Bounded by `limit`, returning
    /// `None` when the count exceeds it, so a caller cannot accidentally hang.
    #[must_use]
    pub fn tree_size(&self, limit: usize) -> Option<usize> {
        let mut n = 0usize;
        let mut stack: Vec<&Kera> = vec![self];
        while let Some(e) = stack.pop() {
            n += 1;
            if n > limit {
                return None;
            }
            for c in e.children() {
                stack.push(c.as_ref());
            }
        }
        Some(n)
    }
}
