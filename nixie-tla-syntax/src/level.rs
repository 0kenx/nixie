//! TLA+ level checking: constant, state, action, temporal.
//!
//! # What levels are for
//!
//! TLA+ stratifies expressions into four levels, and the stratification is not
//! decoration — it is what makes `Init /\ [][Next]_vars` meaningful. A prime
//! may only be applied to something that describes a *state*; `ENABLED` may
//! only be applied to something that describes an *action*; the subscript of
//! `[A]_v` must be a state expression. Violating any of these produces a
//! formula with no meaning, and the symbolic-transition analysis in
//! `docs/TLA_FRONTEND_DESIGN.md` §2 depends on the levels being right.
//!
//! | Level | Name | Introduced by |
//! |---|---|---|
//! | 0 | Constant | `CONSTANT` declarations, literals |
//! | 1 | State | `VARIABLE` declarations |
//! | 2 | Action | `'`, `UNCHANGED`, `[A]_v`, `<<A>>_v`, `\cdot` |
//! | 3 | Temporal | `[]`, `<>`, `~>`, `-+->`, `WF_`, `SF_`, `\AA`, `\EE` |
//!
//! # Why this reports so carefully
//!
//! Two things this checker cannot yet see, both of which would otherwise make
//! it report errors on correct specifications:
//!
//! * **`EXTENDS` is not resolved.** Names imported from another module are
//!   unknown here, and a wrong guess at their level would produce a wrong
//!   verdict.
//! * **Operator levels use the max rule.** The level of `Op(a, b)` is taken as
//!   the maximum of `Op`'s body level (computed with its parameters at
//!   constant level) and the levels of the arguments. Full TLA+ additionally
//!   tracks per-parameter *argument level constraints*, which is what catches
//!   `Op(x')` for an `Op` that primes its parameter.
//!
//! So every level carries a [`Lvl::unresolved`] taint, and **a violation is
//! only reported when the verdict does not depend on a tainted value**. The
//! checker therefore under-reports and never over-reports: it will miss some
//! real level errors, and it will not reject a correct specification. That is
//! the right direction for a front end whose rejections are user-facing, and
//! it is recorded rather than hidden. Resolving `EXTENDS` and implementing
//! argument level constraints are what close the gap.

use crate::ast::*;
use crate::span::Span;
use std::collections::HashMap;

/// A TLA+ expression level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Level {
    /// Depends on no state: literals, `CONSTANT`s.
    #[default]
    Constant,
    /// Depends on the current state: `VARIABLE`s and state functions.
    State,
    /// Relates two states: contains `'`, `UNCHANGED`, `[A]_v` or `\cdot`.
    Action,
    /// Describes a behaviour: contains `[]`, `<>`, `~>`, `WF_` or `SF_`.
    Temporal,
}

impl Level {
    /// The name TLA+ uses for this level.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Constant => "constant",
            Self::State => "state",
            Self::Action => "action",
            Self::Temporal => "temporal",
        }
    }
}

impl core::fmt::Display for Level {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A level together with whether it depends on something unresolved.
///
/// See the module docs: a tainted level suppresses violation reporting, which
/// is what keeps the checker from rejecting correct specifications whose
/// `EXTENDS` this crate cannot yet follow.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Lvl {
    /// The level itself.
    pub level: Level,
    /// Whether the level depends on a name this checker could not resolve.
    pub unresolved: bool,
}

impl Lvl {
    /// A resolved level.
    #[must_use]
    pub const fn known(level: Level) -> Self {
        Self {
            level,
            unresolved: false,
        }
    }

    /// A level that depends on something unresolved.
    #[must_use]
    pub const fn tainted(level: Level) -> Self {
        Self {
            level,
            unresolved: true,
        }
    }

    fn join(self, other: Self) -> Self {
        Self {
            level: self.level.max(other.level),
            unresolved: self.unresolved || other.unresolved,
        }
    }

    fn at(self, level: Level) -> Self {
        Self {
            level,
            unresolved: self.unresolved,
        }
    }
}

/// What a level violation is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LevelErrorKind {
    /// `e'` where `e` is not a state expression.
    PrimeOfNonState(Level),
    /// `UNCHANGED e` where `e` is not a state expression.
    UnchangedOfNonState(Level),
    /// `ENABLED A` where `A` is temporal.
    EnabledOfTemporal(Level),
    /// The action part of `[A]_v` or `<<A>>_v` is temporal.
    SubscriptedTemporalAction(Level),
    /// The subscript of `[A]_v`, `<<A>>_v`, `WF_v` or `SF_v` is not a state
    /// expression.
    SubscriptNotState(Level),
    /// The action of `WF_v(A)` or `SF_v(A)` is temporal.
    FairnessOfTemporal(Level),
    /// An operand of `\cdot` is temporal.
    ComposeOfTemporal(Level),
}

impl core::fmt::Display for LevelErrorKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::PrimeOfNonState(l) => write!(
                f,
                "`'` may only be applied to a state expression, but this is {l} level"
            ),
            Self::UnchangedOfNonState(l) => write!(
                f,
                "`UNCHANGED` may only be applied to a state expression, but this is {l} level"
            ),
            Self::EnabledOfTemporal(l) => write!(
                f,
                "`ENABLED` may only be applied to an action, but this is {l} level"
            ),
            Self::SubscriptedTemporalAction(l) => write!(
                f,
                "the body of a subscripted action must be an action, but this is {l} level"
            ),
            Self::SubscriptNotState(l) => write!(
                f,
                "a subscript must be a state expression, but this is {l} level"
            ),
            Self::FairnessOfTemporal(l) => write!(
                f,
                "the argument of `WF_`/`SF_` must be an action, but this is {l} level"
            ),
            Self::ComposeOfTemporal(l) => write!(
                f,
                "an operand of `\\cdot` must be an action, but this is {l} level"
            ),
        }
    }
}

/// A located level violation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LevelError {
    /// What went wrong.
    pub kind: LevelErrorKind,
    /// Where it went wrong.
    pub span: Span,
}

impl core::fmt::Display for LevelError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}: {}", self.span, self.kind)
    }
}

/// The outcome of checking one module.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LevelReport {
    /// The level computed for each top-level definition, in source order.
    ///
    /// Carries the [`Lvl::unresolved`] taint deliberately: a level that
    /// depends on a name this crate could not resolve is a *guess*, and
    /// presenting it as a fact is how a downstream pass silently builds on
    /// sand. Use [`LevelReport::trusted_level_of`] when the answer has to be
    /// right, and [`LevelReport::level_of`] only when a best effort will do.
    pub definitions: Vec<(String, Lvl)>,
    /// Names that could not be resolved, typically imported via `EXTENDS`.
    ///
    /// Not an error: it is the reason some violations go unreported, and it
    /// disappears once module resolution lands.
    pub unresolved: Vec<String>,
    /// Violations that do **not** depend on any unresolved name.
    pub errors: Vec<LevelError>,
}

impl LevelReport {
    /// The computed level of a named top-level definition, trusted or not.
    #[must_use]
    pub fn level_of(&self, name: &str) -> Option<Level> {
        self.definitions
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, l)| l.level)
    }

    /// The level of a named top-level definition, but only when it does not
    /// depend on an unresolved name.
    ///
    /// Returns `None` both for an unknown definition and for one whose level
    /// could not be established — the caller must handle "we do not know"
    /// rather than receive a plausible default.
    #[must_use]
    pub fn trusted_level_of(&self, name: &str) -> Option<Level> {
        self.definitions
            .iter()
            .find(|(n, _)| n == name)
            .filter(|(_, l)| !l.unresolved)
            .map(|(_, l)| l.level)
    }

    /// How many definitions have a level that does not depend on an
    /// unresolved name.
    #[must_use]
    pub fn trusted_count(&self) -> usize {
        self.definitions
            .iter()
            .filter(|(_, l)| !l.unresolved)
            .count()
    }
}

/// Operators from the standard modules, all of which are constant level.
///
/// Listing them keeps ordinary arithmetic and sequence use out of the
/// unresolved set, which is what makes the taint rule selective enough to
/// still catch real violations. Anything absent here is simply unresolved,
/// which is safe — it suppresses reporting rather than inventing a level.
const STANDARD_CONSTANT_OPERATORS: &[&str] = &[
    // Naturals / Integers / Reals
    "Nat",
    "Int",
    "Real",
    "Infinity",
    "TRUE",
    "FALSE",
    "BOOLEAN",
    "STRING",
    // Sequences
    "Seq",
    "Len",
    "Head",
    "Tail",
    "Append",
    "SubSeq",
    "SelectSeq",
    // FiniteSets
    "IsFiniteSet",
    "Cardinality",
    // Bags
    "IsABag",
    "BagToSet",
    "SetToBag",
    "BagIn",
    "EmptyBag",
    "CopiesIn",
    "BagUnion",
    "SubBag",
    "BagOfAll",
    "BagCardinality",
    // TLC
    "Print",
    "PrintT",
    "Assert",
    "JavaTime",
    "Permutations",
    "SortSeq",
    "RandomElement",
    "Any",
    "ToString",
    "TLCEval",
    // Apalache
    "Gen",
    "Skolem",
    "Expand",
    "ConstInit",
    "Guess",
    "FoldSet",
    "FoldSeq",
    "SetAsFun",
];

/// Check the levels of every definition in `module`.
///
/// Never fails: the outcome is a [`LevelReport`] whose `errors` are the
/// violations that could be established without depending on an unresolved
/// name. See the module docs for why that is the right contract here.
#[must_use]
pub fn check_module(module: &Module) -> LevelReport {
    let mut checker = Checker::default();
    checker.run(module);
    let mut unresolved: Vec<String> = checker.unresolved.into_iter().collect();
    unresolved.sort();
    LevelReport {
        definitions: checker.definitions,
        unresolved,
        errors: checker.errors,
    }
}

#[derive(Default)]
struct Checker {
    scopes: Vec<HashMap<String, Lvl>>,
    definitions: Vec<(String, Lvl)>,
    unresolved: std::collections::BTreeSet<String>,
    errors: Vec<LevelError>,
}

/// A step in the explicit walk.
///
/// `AGENTS.md` forbids new unbounded native recursion over user-controlled
/// input, and an AST built from a user's `.tla` file is exactly that, so the
/// walk carries its own stack with resume state in the frame — the
/// `Expand` / `Combine` shape the rule prescribes.
enum Frame<'a> {
    Expand(&'a Expr),
    /// Pop `nchildren` values, combine them per `expr`'s rule, push one.
    Combine(&'a Expr, usize),
    PushScope(Vec<(String, Lvl)>),
    PopScope,
    /// Pop `nvals` values, join them, and bind the result under `name` in the
    /// enclosing scope. Owns the name: a frame outlives the borrow of the
    /// definition it came from.
    BindDef(String, usize),
    /// Bind a fixed level under `name`, consuming no values.
    BindLevel(String, Lvl),
}

impl Checker {
    fn run(&mut self, module: &Module) {
        // Modules nest; a worklist keeps that iterative too.
        let mut modules = vec![module];
        while let Some(m) = modules.pop() {
            self.scopes.push(HashMap::new());
            for unit in &m.units {
                self.check_unit(unit, &mut modules);
            }
            self.scopes.pop();
        }
    }

    fn check_unit<'a>(&mut self, unit: &'a Unit, modules: &mut Vec<&'a Module>) {
        match &unit.kind {
            UnitKind::ConstantDecl(decls) => {
                for d in decls {
                    self.bind(&d.name.name, Lvl::known(Level::Constant));
                }
            }
            UnitKind::VariableDecl(names) => {
                for n in names {
                    self.bind(&n.name, Lvl::known(Level::State));
                }
            }
            UnitKind::Recursive(decls) => {
                // A recursive operator's level is a fixpoint. Binding it as
                // tainted means nothing that depends on it is ever reported,
                // which is honest: we do not know the level.
                for d in decls {
                    self.bind(&d.name.name, Lvl::tainted(Level::Constant));
                }
            }
            UnitKind::OpDef {
                name, params, body, ..
            } => {
                let lvl = self.level_of_definition(params, core::slice::from_ref(body), &[]);
                self.bind(&name.name, lvl);
                self.definitions.push((name.name.clone(), lvl));
            }
            UnitKind::FnDef {
                name, bounds, body, ..
            } => {
                let lvl = self.level_of_definition(&[], core::slice::from_ref(body), bounds);
                self.bind(&name.name, lvl);
                self.definitions.push((name.name.clone(), lvl));
            }
            UnitKind::Assume { name, body } => {
                let lvl = self.eval(body);
                if let Some(n) = name {
                    self.bind(&n.name, lvl);
                }
            }
            UnitKind::Theorem { name, body, .. } => {
                let lvl = self.eval(body);
                if let Some(n) = name {
                    self.bind(&n.name, lvl);
                }
            }
            UnitKind::ModuleDef { name, .. } => {
                // Instance members are not resolved; treat the whole instance
                // as unknown rather than guessing.
                self.bind(&name.name, Lvl::tainted(Level::Constant));
            }
            UnitKind::Instance { instance, .. } => {
                for (_, expr) in &instance.substitutions {
                    let _ = self.eval(expr);
                }
            }
            UnitKind::Submodule(m) => modules.push(m),
            UnitKind::Extends(_) | UnitKind::ProofDirective(_) | UnitKind::Separator => {}
        }
    }

    /// The level of a definition body, with parameters and bound variables at
    /// constant level and bound domains folded in.
    fn level_of_definition(&mut self, params: &[OpDecl], bodies: &[Expr], bounds: &[Bound]) -> Lvl {
        let mut acc = Lvl::known(Level::Constant);
        for b in bounds {
            acc = acc.join(self.eval(&b.domain));
        }
        let mut scope = Vec::new();
        for p in params {
            scope.push((p.name.name.clone(), Lvl::known(Level::Constant)));
        }
        for b in bounds {
            for p in &b.patterns {
                push_pattern(p, &mut scope);
            }
        }
        self.scopes.push(scope.into_iter().collect());
        for body in bodies {
            acc = acc.join(self.eval(body));
        }
        self.scopes.pop();
        if !params.is_empty() && bodies.iter().any(body_lowers_level) {
            // This operator's level is not a maximum over its arguments'
            // levels, so the rule used at application sites is wrong for it.
            // `test57a.tla` is the case: `B(d) == ENABLED d` has level *state*
            // however high `d` goes, so `C == B(A)` is a state predicate even
            // though `A` is an action — but the max rule makes it an action.
            //
            // Rather than report a level we know the rule cannot compute, mark
            // it unknown. Full TLA+ tracks per-parameter argument level
            // constraints; implementing those is what makes this exact.
            acc.unresolved = true;
        }
        acc
    }

    fn bind(&mut self, name: &str, lvl: Lvl) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), lvl);
        }
    }

    fn lookup(&mut self, name: &str) -> Lvl {
        for scope in self.scopes.iter().rev() {
            if let Some(&lvl) = scope.get(name) {
                return lvl;
            }
        }
        if STANDARD_CONSTANT_OPERATORS.contains(&name) {
            return Lvl::known(Level::Constant);
        }
        self.unresolved.insert(name.to_string());
        Lvl::tainted(Level::Constant)
    }

    fn report(&mut self, lvl: Lvl, span: Span, kind: LevelErrorKind) {
        if !lvl.unresolved {
            self.errors.push(LevelError { kind, span });
        }
    }

    /// Evaluate one expression's level with an explicit stack.
    fn eval(&mut self, root: &Expr) -> Lvl {
        let mut stack: Vec<Frame<'_>> = vec![Frame::Expand(root)];
        let mut values: Vec<Lvl> = Vec::new();

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::PushScope(bindings) => {
                    self.scopes.push(bindings.into_iter().collect());
                }
                Frame::PopScope => {
                    self.scopes.pop();
                }
                Frame::BindDef(name, nvals) => {
                    let lvl = join_pop(&mut values, nvals);
                    self.bind(&name, lvl);
                }
                Frame::BindLevel(name, lvl) => self.bind(&name, lvl),
                Frame::Combine(expr, n) => {
                    let lvl = self.combine(expr, &mut values, n);
                    values.push(lvl);
                }
                Frame::Expand(expr) => self.expand(expr, &mut stack, &mut values),
            }
        }

        values.pop().unwrap_or_default()
    }

    fn expand<'a>(&mut self, expr: &'a Expr, stack: &mut Vec<Frame<'a>>, values: &mut Vec<Lvl>) {
        // Frames are popped LIFO, so children are pushed in reverse order.
        match &expr.kind {
            ExprKind::Int { .. } | ExprKind::Real(_) | ExprKind::Str(_) | ExprKind::At => {
                values.push(Lvl::known(Level::Constant));
            }
            ExprKind::Name(q) => {
                let lvl = self.lookup(name_key(q));
                values.push(lvl);
            }
            ExprKind::Apply { head, args } => {
                let head_lvl = self.lookup(name_key(head));
                values.push(head_lvl);
                // The head's level is already on the value stack, so it counts
                // as one of the children to join.
                stack.push(Frame::Combine(expr, args.len() + 1));
                for a in args.iter().rev() {
                    stack.push(Frame::Expand(a));
                }
            }
            ExprKind::Quant { bounds, body, .. } => {
                let mut scope = Vec::new();
                for b in bounds {
                    for p in &b.patterns {
                        push_pattern(p, &mut scope);
                    }
                }
                stack.push(Frame::Combine(expr, bounds.len() + 1));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
                for b in bounds.iter().rev() {
                    stack.push(Frame::Expand(&b.domain));
                }
            }
            ExprKind::UnboundedQuant { vars, body, .. } => {
                let scope = vars
                    .iter()
                    .map(|v| (v.name.clone(), Lvl::known(Level::Constant)))
                    .collect();
                stack.push(Frame::Combine(expr, 1));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
            }
            ExprKind::Choose {
                pattern,
                domain,
                body,
            } => {
                let mut scope = Vec::new();
                push_pattern(pattern, &mut scope);
                let n = 1 + usize::from(domain.is_some());
                stack.push(Frame::Combine(expr, n));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
                if let Some(d) = domain {
                    stack.push(Frame::Expand(d));
                }
            }
            ExprKind::SetFilter {
                pattern,
                domain,
                pred,
            } => {
                let mut scope = Vec::new();
                push_pattern(pattern, &mut scope);
                stack.push(Frame::Combine(expr, 2));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(pred));
                stack.push(Frame::PushScope(scope));
                stack.push(Frame::Expand(domain));
            }
            ExprKind::SetMap {
                expr: mapped,
                bounds,
            } => {
                let mut scope = Vec::new();
                for b in bounds {
                    for p in &b.patterns {
                        push_pattern(p, &mut scope);
                    }
                }
                stack.push(Frame::Combine(expr, bounds.len() + 1));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(mapped));
                stack.push(Frame::PushScope(scope));
                for b in bounds.iter().rev() {
                    stack.push(Frame::Expand(&b.domain));
                }
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut scope = Vec::new();
                for b in bounds {
                    for p in &b.patterns {
                        push_pattern(p, &mut scope);
                    }
                }
                stack.push(Frame::Combine(expr, bounds.len() + 1));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
                for b in bounds.iter().rev() {
                    stack.push(Frame::Expand(&b.domain));
                }
            }
            ExprKind::Lambda { params, body } => {
                let scope = params
                    .iter()
                    .map(|p| (p.name.clone(), Lvl::known(Level::Constant)))
                    .collect();
                stack.push(Frame::Combine(expr, 1));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
            }
            ExprKind::Label { params, body, .. } => {
                let scope = params
                    .iter()
                    .map(|p| (p.name.clone(), Lvl::known(Level::Constant)))
                    .collect();
                stack.push(Frame::Combine(expr, 1));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
            }
            ExprKind::Let { defs, body } => {
                stack.push(Frame::Combine(expr, 1));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                for def in defs.iter().rev() {
                    match &def.kind {
                        UnitKind::OpDef {
                            name, params, body, ..
                        } => {
                            stack.push(Frame::BindDef(name.name.clone(), 1));
                            stack.push(Frame::PopScope);
                            stack.push(Frame::Expand(body));
                            stack.push(Frame::PushScope(
                                params
                                    .iter()
                                    .map(|p| (p.name.name.clone(), Lvl::known(Level::Constant)))
                                    .collect(),
                            ));
                        }
                        UnitKind::FnDef {
                            name, bounds, body, ..
                        } => {
                            let mut scope = Vec::new();
                            for b in bounds {
                                for p in &b.patterns {
                                    push_pattern(p, &mut scope);
                                }
                            }
                            stack.push(Frame::BindDef(name.name.clone(), bounds.len() + 1));
                            stack.push(Frame::PopScope);
                            stack.push(Frame::Expand(body));
                            stack.push(Frame::PushScope(scope));
                            for b in bounds.iter().rev() {
                                stack.push(Frame::Expand(&b.domain));
                            }
                        }
                        UnitKind::Recursive(decls) => {
                            // A recursive operator's level is a fixpoint we do
                            // not compute; binding it tainted means nothing
                            // that depends on it is ever reported.
                            for d in decls {
                                stack.push(Frame::BindLevel(
                                    d.name.name.clone(),
                                    Lvl::tainted(Level::Constant),
                                ));
                            }
                        }
                        _ => {}
                    }
                }
                stack.push(Frame::PushScope(Vec::new()));
            }
            // Everything else is a plain join over its children.
            _ => {
                let children = child_exprs(expr);
                stack.push(Frame::Combine(expr, children.len()));
                for c in children.into_iter().rev() {
                    stack.push(Frame::Expand(c));
                }
            }
        }
    }

    /// Apply the level rule for `expr` to the `n` child levels on the stack.
    ///
    /// Children are returned in source order as well as joined, because the
    /// subscripted-action and fairness rules constrain their parts
    /// individually rather than only in aggregate.
    fn combine(&mut self, expr: &Expr, values: &mut Vec<Lvl>, n: usize) -> Lvl {
        let mut kids: Vec<Lvl> = Vec::with_capacity(n);
        for _ in 0..n {
            match values.pop() {
                Some(v) => kids.push(v),
                // The walk pushes exactly one value per `Expand`, so a short
                // stack is unreachable for a tree this module built. Treating
                // it as unknown keeps the impossible case from becoming an
                // `unwrap`, per AGENTS.md.
                None => kids.push(Lvl::tainted(Level::Constant)),
            }
        }
        kids.reverse();
        let joined = kids
            .iter()
            .copied()
            .fold(Lvl::known(Level::Constant), Lvl::join);
        match &expr.kind {
            ExprKind::Postfix { op, operand, .. } if op == "'" => {
                if joined.level > Level::State {
                    self.report(
                        joined,
                        operand.span,
                        LevelErrorKind::PrimeOfNonState(joined.level),
                    );
                }
                joined.at(Level::Action)
            }
            ExprKind::Prefix { op, operand, .. } => match op.as_str() {
                "UNCHANGED" => {
                    if joined.level > Level::State {
                        self.report(
                            joined,
                            operand.span,
                            LevelErrorKind::UnchangedOfNonState(joined.level),
                        );
                    }
                    joined.at(Level::Action)
                }
                "ENABLED" => {
                    if joined.level > Level::Action {
                        self.report(
                            joined,
                            operand.span,
                            LevelErrorKind::EnabledOfTemporal(joined.level),
                        );
                    }
                    joined.at(Level::State)
                }
                "[]" | "<>" => joined.at(Level::Temporal),
                _ => joined,
            },
            // `[A]_v` / `<<A>>_v`: the body must be an action, the subscript a
            // state expression, and the result is an action.
            ExprKind::Action {
                body, subscript, ..
            } => {
                // `child_exprs` yields [body, subscript] for this node.
                let body_lvl = kids.first().copied().unwrap_or_default();
                let sub_lvl = kids.get(1).copied().unwrap_or_default();
                if body_lvl.level > Level::Action {
                    self.report(
                        body_lvl,
                        body.span,
                        LevelErrorKind::SubscriptedTemporalAction(body_lvl.level),
                    );
                }
                if sub_lvl.level > Level::State {
                    self.report(
                        sub_lvl,
                        subscript.span,
                        LevelErrorKind::SubscriptNotState(sub_lvl.level),
                    );
                }
                joined.at(Level::Action)
            }
            // `WF_v(A)` / `SF_v(A)`: a fairness condition is temporal, whatever
            // its parts are. Missing this rule made every `Fairness == WF_v(A)`
            // come out action level, which the SANY parity run caught across
            // ten specifications.
            ExprKind::Fairness {
                subscript, body, ..
            } => {
                // `child_exprs` yields [subscript, body] for this node.
                let sub_lvl = kids.first().copied().unwrap_or_default();
                let body_lvl = kids.get(1).copied().unwrap_or_default();
                if sub_lvl.level > Level::State {
                    self.report(
                        sub_lvl,
                        subscript.span,
                        LevelErrorKind::SubscriptNotState(sub_lvl.level),
                    );
                }
                if body_lvl.level > Level::Action {
                    self.report(
                        body_lvl,
                        body.span,
                        LevelErrorKind::FairnessOfTemporal(body_lvl.level),
                    );
                }
                joined.at(Level::Temporal)
            }
            // `\AA` and `\EE` quantify over behaviours: temporal, whatever
            // the body is. (Plain `\A` / `\E` preserve the body's level.)
            ExprKind::Quant { kind, .. } | ExprKind::UnboundedQuant { kind, .. }
                if matches!(kind, QuantKind::TemporalForall | QuantKind::TemporalExists) =>
            {
                joined.at(Level::Temporal)
            }
            ExprKind::Infix { op, rhs, .. } => match op.as_str() {
                "~>" | "-+->" => joined.at(Level::Temporal),
                "\\cdot" => {
                    if joined.level > Level::Action {
                        self.report(
                            joined,
                            rhs.span,
                            LevelErrorKind::ComposeOfTemporal(joined.level),
                        );
                    }
                    joined.at(Level::Action)
                }
                _ => joined,
            },
            _ => joined,
        }
    }
}

/// A `Vec` of a node's direct children, for the plain-join cases.
fn child_exprs(expr: &Expr) -> Vec<&Expr> {
    let mut out: Vec<&Expr> = Vec::new();
    match &expr.kind {
        ExprKind::FnApply { func, args } => {
            out.push(func);
            out.extend(args);
        }
        ExprKind::Qualified { base, args, .. } => {
            out.push(base);
            out.extend(args);
        }
        ExprKind::Field { record, .. } => out.push(record),
        ExprKind::Prefix { operand, .. } | ExprKind::Postfix { operand, .. } => out.push(operand),
        ExprKind::Infix { lhs, rhs, .. } => {
            out.push(lhs);
            out.push(rhs);
        }
        ExprKind::Junction { items, .. } | ExprKind::SetEnum(items) | ExprKind::Tuple(items) => {
            out.extend(items)
        }
        ExprKind::FnSet { domain, codomain } => {
            out.push(domain);
            out.push(codomain);
        }
        ExprKind::RecordLit(fields) | ExprKind::RecordSet(fields) => {
            out.extend(fields.iter().map(|(_, e)| e));
        }
        ExprKind::Except { base, updates } => {
            out.push(base);
            for u in updates {
                for sel in &u.path {
                    if let ExceptSel::Index(idx) = sel {
                        out.extend(idx);
                    }
                }
                out.push(&u.value);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            out.push(cond);
            out.push(then_branch);
            out.push(else_branch);
        }
        ExprKind::Case { arms, other } => {
            for a in arms {
                out.push(&a.guard);
                out.push(&a.value);
            }
            if let Some(o) = other {
                out.push(o);
            }
        }
        ExprKind::Action {
            body, subscript, ..
        } => {
            out.push(body);
            out.push(subscript);
        }
        ExprKind::Fairness {
            subscript, body, ..
        } => {
            out.push(subscript);
            out.push(body);
        }
        ExprKind::AssumeProve { assumptions, goal } => {
            for a in assumptions {
                match a {
                    AssumeItem::Expr(e) => out.push(e),
                    AssumeItem::New { domain, .. } => out.extend(domain.iter()),
                }
            }
            out.push(goal);
        }
        ExprKind::Paren(inner) => out.push(inner),
        ExprKind::Quant { bounds, body, .. } => {
            out.extend(bounds.iter().map(|b| &b.domain));
            out.push(body);
        }
        ExprKind::UnboundedQuant { body, .. }
        | ExprKind::Lambda { body, .. }
        | ExprKind::Label { body, .. } => out.push(body),
        ExprKind::Choose { domain, body, .. } => {
            out.extend(domain.iter().map(AsRef::as_ref));
            out.push(body);
        }
        ExprKind::SetFilter { domain, pred, .. } => {
            out.push(domain);
            out.push(pred);
        }
        ExprKind::SetMap { expr, bounds } => {
            out.extend(bounds.iter().map(|b| &b.domain));
            out.push(expr);
        }
        ExprKind::FnConstruct { bounds, body } => {
            out.extend(bounds.iter().map(|b| &b.domain));
            out.push(body);
        }
        // `Let` is walked by the caller that needs its definitions; the level
        // walk handles it with its own scope frames.
        ExprKind::Let { body, .. } => out.push(body),
        // `expand` handles `Apply` itself (the head's level comes from the
        // scope, not from a child); the arguments are listed here so that
        // `body_lowers_level`, which shares this function, still scans them.
        ExprKind::Apply { args, .. } => out.extend(args),
        ExprKind::Name(_)
        | ExprKind::Int { .. }
        | ExprKind::Real(_)
        | ExprKind::Str(_)
        | ExprKind::At => {}
    }
    out
}

/// Does this body contain a construct that *lowers* a sub-expression's level?
///
/// Everything in TLA+ either preserves the level, raises it to a fixed one, or
/// — in exactly two cases — caps it: `ENABLED A` is a state predicate however
/// high `A` is, and `\cdot` yields an action. For a body free of both, the
/// level really is the maximum over the parts, and the rule used at
/// application sites is exact.
fn body_lowers_level(body: &Expr) -> bool {
    // Iterative, for the same reason the level walk is: this runs over a
    // user-supplied tree.
    let mut stack = vec![body];
    while let Some(e) = stack.pop() {
        match &e.kind {
            ExprKind::Prefix { op, .. } if op == "ENABLED" => return true,
            ExprKind::Infix { op, .. } if op == "\\cdot" => return true,
            _ => {}
        }
        stack.extend(child_exprs(e));
        if let ExprKind::Let { defs, body } = &e.kind {
            stack.push(body);
            for d in defs {
                match &d.kind {
                    UnitKind::OpDef { body, .. } | UnitKind::FnDef { body, .. } => {
                        stack.push(body);
                    }
                    _ => {}
                }
            }
        }
    }
    false
}

fn push_pattern(p: &Pattern, out: &mut Vec<(String, Lvl)>) {
    match p {
        Pattern::Name(id) => out.push((id.name.clone(), Lvl::known(Level::Constant))),
        Pattern::Tuple(ids) => {
            for id in ids {
                out.push((id.name.clone(), Lvl::known(Level::Constant)));
            }
        }
    }
}

fn join_pop(values: &mut Vec<Lvl>, n: usize) -> Lvl {
    let mut acc = Lvl::known(Level::Constant);
    for _ in 0..n {
        match values.pop() {
            Some(v) => acc = acc.join(v),
            // The walk pushes exactly one value per `Expand`, so this cannot
            // happen for a tree this module built. Treating a short stack as
            // "unknown" keeps the impossible case from becoming an `unwrap`.
            None => return Lvl::tainted(acc.level),
        }
    }
    acc
}

/// The key a qualified name is looked up under: its final segment.
fn name_key(q: &QualName) -> &str {
    match q.base() {
        Some(id) => id.name.as_str(),
        None => "",
    }
}
