//! The surface syntax tree.
//!
//! This is the *surface* IR from `docs/TLA_FRONTEND_DESIGN.md` §2: a faithful
//! tree of what was written, with spans on every node. It is deliberately not
//! minimal — desugaring to the KerA kernel happens in `nixie-tla`, downstream
//! of here. Keeping the two apart is what lets diagnostics point at what the
//! user actually typed.

use crate::span::Span;
use crate::token::NumBase;

/// An identifier with its source location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    /// The identifier text.
    pub name: String,
    /// Where it was written.
    pub span: Span,
}

/// A possibly instance-qualified name, e.g. `Foo!Bar!op`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualName {
    /// The `!`-separated path. Always non-empty; the last element is the name
    /// proper and any earlier elements are instance qualifiers.
    pub path: Vec<Ident>,
    /// The span of the whole qualified name.
    pub span: Span,
}

impl QualName {
    /// The unqualified name, i.e. the final path element.
    #[must_use]
    pub fn base(&self) -> Option<&Ident> {
        self.path.last()
    }

    /// Whether this name carries instance qualifiers.
    #[must_use]
    pub fn is_qualified(&self) -> bool {
        self.path.len() > 1
    }
}

/// Which junction a bulleted list is built from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Junct {
    /// `/\` — conjunction list.
    And,
    /// `\/` — disjunction list.
    Or,
}

impl Junct {
    /// The canonical spelling of this junction.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::And => "/\\",
            Self::Or => "\\/",
        }
    }
}

/// Which quantifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuantKind {
    /// `\A` — universal.
    Forall,
    /// `\E` — existential.
    Exists,
    /// `\AA` — temporal universal.
    TemporalForall,
    /// `\EE` — temporal existential.
    TemporalExists,
}

/// Whether an action is written with square or angle brackets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ActionKind {
    /// `[A]_v` — `A` or stuttering on `v`.
    Stuttering,
    /// `<<A>>_v` — `A` and `v` changes.
    NonStuttering,
}

/// Which fairness condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FairnessKind {
    /// `WF_v(A)`.
    Weak,
    /// `SF_v(A)`.
    Strong,
}

/// A binding pattern: a plain name or a tuple destructuring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// `x`
    Name(Ident),
    /// `<<x, y>>`
    Tuple(Vec<Ident>),
}

impl Pattern {
    /// Where the pattern was written.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::Name(id) => id.span,
            Self::Tuple(ids) => match (ids.first(), ids.last()) {
                (Some(f), Some(l)) => f.span.merge(l.span),
                _ => Span::default(),
            },
        }
    }
}

/// One `pattern, … \in domain` group of a quantifier or function constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bound {
    /// The patterns sharing this domain.
    pub patterns: Vec<Pattern>,
    /// The domain they range over.
    pub domain: Expr,
}

/// One selector step in an `EXCEPT` update path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExceptSel {
    /// `[i, j]` — function application.
    Index(Vec<Expr>),
    /// `.field` — record field.
    Field(Ident),
}

/// One `!path = value` clause of an `EXCEPT`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExceptUpdate {
    /// The selector path, in application order. Always non-empty.
    pub path: Vec<ExceptSel>,
    /// The replacement value. `@` inside it refers to the old value.
    pub value: Expr,
}

/// What a declaration introduced by `NEW` ranges over.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NewKind {
    /// `NEW CONSTANT x`, or a bare `NEW x` (constant is the default).
    Constant,
    /// `NEW VARIABLE x`.
    Variable,
    /// `NEW STATE x`.
    State,
    /// `NEW ACTION x`.
    Action,
    /// `NEW TEMPORAL x`.
    Temporal,
}

/// One item in the assumption list of an `ASSUME … PROVE …`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssumeItem {
    /// `NEW CONSTANT x \in S` — a fresh declaration, scoped to the sequent.
    New {
        /// What the declaration introduces.
        kind: NewKind,
        /// The declared name, with its arity if written as `F(_, _)`.
        decl: OpDecl,
        /// The domain, when written as `NEW x \in S`.
        domain: Option<Expr>,
    },
    /// An ordinary assumed formula.
    Expr(Expr),
}

/// One `predicate -> value` arm of a `CASE`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseArm {
    /// The guard.
    pub guard: Expr,
    /// The value taken when the guard holds.
    pub value: Expr,
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    /// What kind of expression this is.
    pub kind: ExprKind,
    /// Where it was written.
    pub span: Span,
}

/// The shape of an expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    /// A name, possibly instance-qualified.
    Name(QualName),
    /// An integer literal, in the base it was written in.
    Int {
        /// The base the literal was written in.
        base: NumBase,
        /// The digits, without any base prefix.
        digits: String,
    },
    /// A decimal literal with a fractional part.
    Real(String),
    /// A string literal, already unescaped.
    Str(String),
    /// Operator application, `Op(a, b)`.
    Apply {
        /// The operator being applied.
        head: QualName,
        /// The arguments.
        args: Vec<Expr>,
    },
    /// Function application, `f[a, b]`.
    FnApply {
        /// The function.
        func: Box<Expr>,
        /// The arguments.
        args: Vec<Expr>,
    },
    /// An instance or subexpression selection whose base is not a plain name:
    /// `Inner(q)!Spec`, `A!1!2`, `R!+(a, b)`.
    ///
    /// A selection off a bare name folds into [`QualName`] instead, so this
    /// node only appears where the base is itself an expression.
    Qualified {
        /// The thing being selected from.
        base: Box<Expr>,
        /// The selector: a name, a subexpression index, `:`, `<<`, `>>`, `@`,
        /// or an operator symbol.
        ///
        /// The reserved spelling `()` marks an *argument instantiation* step,
        /// written `A!(1, 2)`: it supplies arguments to the subexpression
        /// selected so far rather than naming a new one.
        selector: Ident,
        /// Arguments, when the selection is applied.
        args: Vec<Expr>,
    },
    /// Record field access, `r.field`.
    Field {
        /// The record.
        record: Box<Expr>,
        /// The field name.
        field: Ident,
    },
    /// Prefix operator application.
    Prefix {
        /// Canonical spelling of the operator.
        op: String,
        /// Where the operator token is.
        op_span: Span,
        /// The operand.
        operand: Box<Expr>,
    },
    /// Infix operator application.
    Infix {
        /// Canonical spelling of the operator.
        op: String,
        /// Where the operator token is.
        op_span: Span,
        /// Left operand.
        lhs: Box<Expr>,
        /// Right operand.
        rhs: Box<Expr>,
    },
    /// Postfix operator application, e.g. `x'`.
    Postfix {
        /// Canonical spelling of the operator.
        op: String,
        /// Where the operator token is.
        op_span: Span,
        /// The operand.
        operand: Box<Expr>,
    },
    /// A layout-delimited bulleted list, `/\ a /\ b`.
    Junction {
        /// Which junction the list is built from.
        kind: Junct,
        /// The items, in source order.
        items: Vec<Expr>,
    },
    /// Bounded quantification, `\A x \in S : P`.
    Quant {
        /// Which quantifier.
        kind: QuantKind,
        /// The bound groups.
        bounds: Vec<Bound>,
        /// The body.
        body: Box<Expr>,
    },
    /// Unbounded quantification, `\A x : P`.
    ///
    /// Kept distinct from [`ExprKind::Quant`] because Apalache rejects it and
    /// the rejection needs to name the construct precisely.
    UnboundedQuant {
        /// Which quantifier.
        kind: QuantKind,
        /// The bound variables.
        vars: Vec<Ident>,
        /// The body.
        body: Box<Expr>,
    },
    /// `CHOOSE x \in S : P`, or unbounded `CHOOSE x : P`.
    Choose {
        /// The bound pattern.
        pattern: Pattern,
        /// The domain, if the choice is bounded.
        domain: Option<Box<Expr>>,
        /// The predicate.
        body: Box<Expr>,
    },
    /// `{a, b, c}`.
    SetEnum(Vec<Expr>),
    /// `{x \in S : P}`.
    SetFilter {
        /// The bound pattern.
        pattern: Pattern,
        /// The set being filtered.
        domain: Box<Expr>,
        /// The filter predicate.
        pred: Box<Expr>,
    },
    /// `{e : x \in S, y \in T}`.
    SetMap {
        /// The mapped expression.
        expr: Box<Expr>,
        /// The bound groups.
        bounds: Vec<Bound>,
    },
    /// `<<a, b>>`.
    Tuple(Vec<Expr>),
    /// `[x \in S |-> e]`.
    FnConstruct {
        /// The bound groups.
        bounds: Vec<Bound>,
        /// The body.
        body: Box<Expr>,
    },
    /// `[S -> T]`.
    FnSet {
        /// The domain set.
        domain: Box<Expr>,
        /// The codomain set.
        codomain: Box<Expr>,
    },
    /// `[a |-> 1, b |-> 2]`.
    RecordLit(Vec<(Ident, Expr)>),
    /// `[a : S, b : T]`.
    RecordSet(Vec<(Ident, Expr)>),
    /// `[f EXCEPT ![i] = e]`.
    Except {
        /// The function or record being updated.
        base: Box<Expr>,
        /// The updates, in source order.
        updates: Vec<ExceptUpdate>,
    },
    /// `IF p THEN a ELSE b`.
    If {
        /// The condition.
        cond: Box<Expr>,
        /// The `THEN` branch.
        then_branch: Box<Expr>,
        /// The `ELSE` branch.
        else_branch: Box<Expr>,
    },
    /// `CASE p -> a [] q -> b [] OTHER -> c`.
    Case {
        /// The guarded arms.
        arms: Vec<CaseArm>,
        /// The `OTHER` arm, if present.
        other: Option<Box<Expr>>,
    },
    /// `LET defs IN body`.
    Let {
        /// The local definitions.
        defs: Vec<Unit>,
        /// The body.
        body: Box<Expr>,
    },
    /// `[A]_v` or `<<A>>_v`.
    Action {
        /// Which bracket form was used.
        kind: ActionKind,
        /// The action.
        body: Box<Expr>,
        /// The subscript.
        subscript: Box<Expr>,
    },
    /// `WF_v(A)` or `SF_v(A)`.
    Fairness {
        /// Which fairness condition.
        kind: FairnessKind,
        /// The subscript.
        subscript: Box<Expr>,
        /// The action.
        body: Box<Expr>,
    },
    /// `LAMBDA x, y : e`.
    Lambda {
        /// The parameters.
        params: Vec<Ident>,
        /// The body.
        body: Box<Expr>,
    },
    /// `@`, the old value inside an `EXCEPT` update.
    At,
    /// A labelled subexpression, `lbl :: e` or `lbl(a, b) :: e`.
    ///
    /// Labels name a position inside a formula so that a proof or a
    /// `!`-qualified reference can point at it. They are not operators and
    /// carry no precedence: the label extends to the end of its expression.
    Label {
        /// The label name.
        name: Ident,
        /// The label's parameters, if it was written with any.
        params: Vec<Ident>,
        /// The labelled expression.
        body: Box<Expr>,
    },
    /// `ASSUME a, b PROVE g`, the sequent form of a theorem statement.
    AssumeProve {
        /// The assumptions.
        assumptions: Vec<AssumeItem>,
        /// The goal.
        goal: Box<Expr>,
    },
    /// A parenthesised expression. Retained so that the printer can round-trip
    /// and so that a precedence diagnostic can suggest exactly where to add
    /// parentheses.
    Paren(Box<Expr>),
}

/// A declared operator name together with its arity.
///
/// Arity is written with placeholders: `Op(_, _)` declares arity 2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpDecl {
    /// The declared name.
    pub name: Ident,
    /// How many arguments it takes. Zero for a plain constant.
    pub arity: usize,
    /// Where it was declared.
    pub span: Span,
}

/// An `INSTANCE M WITH a <- e, …` clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instance {
    /// The module being instantiated.
    pub module: Ident,
    /// The substitutions, in source order.
    pub substitutions: Vec<(Ident, Expr)>,
    /// Where the clause was written.
    pub span: Span,
}

/// A proof body.
///
/// Milestone 1 records the extent of a proof without interpreting it: Apalache
/// ignores proofs, so parity does not require understanding them, but the
/// tokens still have to be consumed with the right extent so that the next
/// unit is found. Structured `<n>` proofs are rejected rather than guessed at.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    /// The span the proof covers.
    pub span: Span,
}

/// A top-level or `LET`-level unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unit {
    /// What kind of unit this is.
    pub kind: UnitKind,
    /// Where it was written.
    pub span: Span,
}

/// The shape of a unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnitKind {
    /// `EXTENDS M1, M2`.
    Extends(Vec<Ident>),
    /// `CONSTANT a, Op(_, _)`.
    ConstantDecl(Vec<OpDecl>),
    /// `VARIABLE x, y`.
    VariableDecl(Vec<Ident>),
    /// `Op(a, b) == body`, or an operator-symbol definition.
    OpDef {
        /// Whether the definition is `LOCAL`.
        local: bool,
        /// The defined name (an operator symbol for infix/prefix/postfix defs).
        name: Ident,
        /// The parameters.
        params: Vec<OpDecl>,
        /// The body.
        body: Expr,
    },
    /// `f[x \in S] == body`.
    FnDef {
        /// Whether the definition is `LOCAL`.
        local: bool,
        /// The defined name.
        name: Ident,
        /// The bound groups.
        bounds: Vec<Bound>,
        /// The body.
        body: Expr,
    },
    /// A bare `INSTANCE M WITH …`.
    Instance {
        /// Whether the instantiation is `LOCAL`.
        local: bool,
        /// The instance clause.
        instance: Instance,
    },
    /// `I(x) == INSTANCE M WITH …`.
    ModuleDef {
        /// Whether the definition is `LOCAL`.
        local: bool,
        /// The name bound to the instance.
        name: Ident,
        /// The parameters.
        params: Vec<OpDecl>,
        /// The instance clause.
        instance: Instance,
    },
    /// `ASSUME e`, `AXIOM e`, optionally named.
    Assume {
        /// The name, if the assumption was named.
        name: Option<Ident>,
        /// The assumed formula.
        body: Expr,
    },
    /// `THEOREM e`, optionally named, optionally with a proof.
    Theorem {
        /// The name, if the theorem was named.
        name: Option<Ident>,
        /// The asserted formula.
        body: Expr,
        /// The proof, if one was written.
        proof: Option<Proof>,
    },
    /// `RECURSIVE F(_), G(_)`.
    ///
    /// Parsed, not rejected. Whether a construct is inside the supported
    /// *fragment* is a question for the lowering pass in `nixie-tla`, which
    /// knows what the encoder can handle; the parser's job is to recognise
    /// TLA+. Conflating the two would also block the long-term goal of
    /// accepting a superset of what Apalache takes.
    Recursive(Vec<OpDecl>),
    /// A TLAPS proof directive at unit level: `USE …`, `HIDE …`, `PROOF …`.
    ///
    /// Recorded with its extent and otherwise uninterpreted, matching
    /// Apalache, which does not check proofs.
    ProofDirective(Proof),
    /// A `----` horizontal rule between units.
    Separator,
    /// A nested module.
    Submodule(Box<Module>),
}

/// A parsed module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    /// The module name from the header.
    pub name: Ident,
    /// The units, in source order.
    pub units: Vec<Unit>,
    /// The span from `----` to `====`.
    pub span: Span,
}

impl Module {
    /// The `EXTENDS` names, flattened across every `EXTENDS` unit.
    #[must_use]
    pub fn extends(&self) -> Vec<&Ident> {
        self.units
            .iter()
            .filter_map(|u| match &u.kind {
                UnitKind::Extends(names) => Some(names),
                _ => None,
            })
            .flatten()
            .collect()
    }

    /// The declared variables, flattened across every `VARIABLE` unit.
    #[must_use]
    pub fn variables(&self) -> Vec<&Ident> {
        self.units
            .iter()
            .filter_map(|u| match &u.kind {
                UnitKind::VariableDecl(names) => Some(names),
                _ => None,
            })
            .flatten()
            .collect()
    }

    /// The modules this one instantiates, across every `INSTANCE` form.
    ///
    /// Distinct from [`Module::extends`]: `INSTANCE` substitutes for the
    /// instantiated module's declarations, so its names are *not* imported.
    /// It still has to be loaded, though — a member cannot be resolved
    /// without it.
    #[must_use]
    pub fn instantiated(&self) -> Vec<&Ident> {
        self.units
            .iter()
            .filter_map(|u| match &u.kind {
                UnitKind::Instance { instance, .. } | UnitKind::ModuleDef { instance, .. } => {
                    Some(&instance.module)
                }
                _ => None,
            })
            .collect()
    }

    /// The declared constants, flattened across every `CONSTANT` unit.
    #[must_use]
    pub fn constants(&self) -> Vec<&OpDecl> {
        self.units
            .iter()
            .filter_map(|u| match &u.kind {
                UnitKind::ConstantDecl(decls) => Some(decls),
                _ => None,
            })
            .flatten()
            .collect()
    }
}
