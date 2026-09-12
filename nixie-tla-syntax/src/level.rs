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

#[allow(unused_imports)]
use crate::ast::QualName;
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
    /// What this module makes visible to a module that `EXTENDS` it: its own
    /// declarations and definitions with their per-parameter level functions,
    /// plus everything it inherited (`EXTENDS` re-exports).
    pub exports: Imports,
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
    // TLC / TLCExt
    "TLCGet",
    "TLCSet",
    "TLCDefer",
    "TLCCache",
    "PickSuccessor",
    "Trace",
    "CounterExample",
    "AssertEq",
    "AssertError",
    // Apalache. Its `Apalache.tla` is often on the search path, but listing
    // the operators means a spec still resolves without it -- 75 corpus files
    // extend it.
    "ApaFoldSet",
    "ApaFoldSeqLeft",
    "MkSeq",
    "Variant",
    "VariantTag",
    "VariantGetUnsafe",
    "VariantGetOrElse",
    "VariantFilter",
    "FunAsSeq",
    "MAX_INT",
    "MIN_INT",
];

/// Names imported into a module, with the levels they were established at.
///
/// Built by [`check_spec`] from the modules a spec extends. `EXTENDS` does no
/// substitution, so an extended definition's level carries over exactly —
/// which is why this is worth doing rather than approximating.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Imports {
    map: HashMap<String, Binding>,
}

impl Imports {
    /// No imports.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record an imported name.
    pub fn insert(&mut self, name: impl Into<String>, binding: Binding) {
        self.map.insert(name.into(), binding);
    }

    /// Look up an imported name's level.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Lvl> {
        self.map.get(name).map(|b| b.lvl)
    }

    /// Look up an imported name's full binding, including its per-parameter
    /// level functions.
    #[must_use]
    pub fn binding(&self, name: &str) -> Option<Binding> {
        self.map.get(name).cloned()
    }

    /// How many names are imported.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether nothing is imported.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// Check a whole spec, following `EXTENDS` so that imported levels are known.
///
/// Modules are checked dependency-first, so each one's imports are already
/// established when it is reached. Returns a report per module, keyed by name.
///
/// This is what makes the level checker useful on real specs: without it,
/// every name a module extends is unresolved and the levels that depend on it
/// are untrusted.
#[must_use]
pub fn check_spec(spec: &crate::module::LoadedSpec) -> Vec<(String, LevelReport)> {
    let mut exports: HashMap<String, Imports> = HashMap::new();
    let mut out = Vec::new();

    for (name, module) in &spec.modules {
        // A module sees everything each extended module exports. `EXTENDS` is
        // transitive, so those export sets are already closed.
        let mut imports = Imports::new();
        for dep in module.extends() {
            if let Some(dep_exports) = exports.get(&dep.name) {
                for (k, v) in &dep_exports.map {
                    imports.map.insert(k.clone(), v.clone());
                }
            }
        }

        let report = check_module_in(module, &imports);

        // `EXTENDS` re-exports, so a module's exports are its own scope on top
        // of everything it inherited.
        let mut exported = imports.clone();
        for (k, v) in &report.exports.map {
            exported.map.insert(k.clone(), v.clone());
        }
        exports.insert(name.clone(), exported);
        out.push((name.clone(), report));
    }
    out
}

/// Check the levels of every definition in `module`.
///
/// Never fails: the outcome is a [`LevelReport`] whose `errors` are the
/// violations that could be established without depending on an unresolved
/// name. See the module docs for why that is the right contract here.
#[must_use]
pub fn check_module(module: &Module) -> LevelReport {
    check_module_in(module, &Imports::new())
}

/// Check `module`'s levels with the given imported names already known.
///
/// Prefer [`check_spec`], which builds the imports by following `EXTENDS`.
#[must_use]
pub fn check_module_in(module: &Module, imports: &Imports) -> LevelReport {
    let mut checker = Checker {
        imports: imports.clone(),
        ..Checker::default()
    };
    checker.run(module);
    let mut unresolved: Vec<String> = checker.unresolved.into_iter().collect();
    unresolved.sort();
    LevelReport {
        definitions: checker.definitions,
        unresolved,
        errors: checker.errors,
        exports: checker.exports,
    }
}

/// What a name is bound to.
///
/// For an operator with parameters, the level is not simply the maximum over
/// its arguments: `SVGElemToString(elem) == TRUE` *ignores* its parameter and
/// stays constant however high the argument goes, while `B(d) == ENABLED d`
/// caps it at state level. `param_fns[i][L]` is the body's level when
/// parameter `i` has level `L` — an exact function on the four-element chain,
/// obtained by evaluating the body once per level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    /// The level of the name itself (an operator's body with its parameters
    /// at constant level).
    pub lvl: Lvl,
    /// For each parameter, the body's level as a function of that parameter's
    /// level, indexed by [`Level`] as `usize`. Empty when the name takes no
    /// parameters, or when the function could not be computed.
    pub param_fns: Vec<[Lvl; 4]>,
}

impl Binding {
    /// A name with no parameters.
    #[must_use]
    pub const fn plain(lvl: Lvl) -> Self {
        Self {
            lvl,
            param_fns: Vec::new(),
        }
    }
}

#[derive(Default)]
struct Checker {
    imports: Imports,
    scopes: Vec<HashMap<String, Binding>>,
    definitions: Vec<(String, Lvl)>,
    unresolved: std::collections::BTreeSet<String>,
    errors: Vec<LevelError>,
    exports: Imports,
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
    BindDef(String, usize, bool),
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
            // The module's top-level scope *is* what it exports. Capture it
            // before it is popped, with the parameter level functions intact:
            // an importer that only learns the level cannot apply
            // `SVGElemToString(elem) == TRUE` correctly.
            if let Some(scope) = self.scopes.last() {
                for (name, binding) in scope {
                    self.exports.map.insert(name.clone(), binding.clone());
                }
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
                let param_fns = self.param_level_functions(params, body);
                self.bind_binding(&name.name, Binding { lvl, param_fns });
                self.definitions.push((name.name.clone(), lvl));
            }
            UnitKind::FnDef {
                name, bounds, body, ..
            } => {
                // A TLA+ function definition is recursive: `f[i \in S] == …f[j]…`
                // refers to itself, so `f` must be in scope while its own body
                // is checked. Its level is the least fixpoint, reached by
                // Kleene iteration — the lattice is a four-element chain, so
                // four rounds suffice and the loop is bounded.
                let mut lvl = Lvl::known(Level::Constant);
                for _ in 0..=(Level::Temporal as usize) {
                    self.bind(&name.name, lvl);
                    let next = self.level_of_definition(&[], core::slice::from_ref(body), bounds);
                    if next == lvl {
                        break;
                    }
                    lvl = lvl.join(next);
                }
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
        self.scopes.push(
            scope
                .into_iter()
                .map(|(n, l)| (n, Binding::plain(l)))
                .collect(),
        );
        for body in bodies {
            acc = acc.join(self.eval(body));
        }
        self.scopes.pop();
        acc
    }

    /// For each parameter, the body's level as a function of that parameter's
    /// level.
    ///
    /// Evaluates the body once per (parameter, level) pair, with the other
    /// parameters held at constant level. Four levels and usually one or two
    /// parameters, so the cost is small and bounded — and it is what makes
    /// `SVGElemToString(elem) == TRUE` come out constant when applied to a
    /// state expression, and `B(d) == ENABLED d` come out state when applied
    /// to an action.
    fn param_level_functions(&mut self, params: &[OpDecl], body: &Expr) -> Vec<[Lvl; 4]> {
        if params.is_empty() {
            return Vec::new();
        }
        const LEVELS: [Level; 4] = [
            Level::Constant,
            Level::State,
            Level::Action,
            Level::Temporal,
        ];
        let mut out = Vec::with_capacity(params.len());
        for i in 0..params.len() {
            let mut row = [Lvl::known(Level::Constant); 4];
            for (slot, probe) in LEVELS.iter().enumerate() {
                let scope: HashMap<String, Binding> = params
                    .iter()
                    .enumerate()
                    .map(|(j, p)| {
                        let lvl = if j == i {
                            Lvl::known(*probe)
                        } else {
                            Lvl::known(Level::Constant)
                        };
                        (p.name.name.clone(), Binding::plain(lvl))
                    })
                    .collect();
                self.scopes.push(scope);
                // Probing must not add to the diagnostics: the same body is
                // walked four times per parameter, and each pass would report
                // the same violations and the same unresolved names again.
                let saved_errors = self.errors.len();
                let saved_unresolved = self.unresolved.clone();
                row[slot] = self.eval(body);
                self.errors.truncate(saved_errors);
                self.unresolved = saved_unresolved;
                self.scopes.pop();
            }
            out.push(row);
        }
        out
    }

    fn bind(&mut self, name: &str, lvl: Lvl) {
        self.bind_binding(name, Binding::plain(lvl));
    }

    fn bind_binding(&mut self, name: &str, binding: Binding) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), binding);
        }
    }

    fn lookup_binding(&self, name: &str) -> Option<Binding> {
        self.bound_binding(name)
            .or_else(|| builtin_operator_binding(name))
    }

    /// A binding introduced by a scope or an import — never a built-in.
    ///
    /// The distinction matters: an operator *parameter* named `-.` shadows the
    /// built-in rule for `-.` and must be applied through its level function,
    /// whereas an ordinary `[]` or `'` must go through its own rule with its
    /// own violation checks.
    fn bound_binding(&self, name: &str) -> Option<Binding> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
            .or_else(|| self.imports.binding(name))
    }

    /// Look up a possibly-qualified name.
    ///
    /// `I!Op` resolves through the final segment, which is right whenever the
    /// module was reached by `EXTENDS`. When it is not — an unresolved
    /// `INSTANCE`, or a subexpression selector such as `A!1` or `R!+` — the
    /// result is unknown, and the *whole path* is what gets reported. Keying
    /// the diagnostic on the last segment alone listed `1` and `+` as
    /// unresolved "names", which is noise rather than information.
    fn lookup_qual(&mut self, q: &QualName) -> Lvl {
        if !q.is_qualified() {
            return self.lookup(name_key(q));
        }
        let key = name_key(q);
        if let Some(b) = self.lookup_binding(key) {
            return b.lvl;
        }
        if let Some(lvl) = self.imports.get(key) {
            return lvl;
        }
        if STANDARD_CONSTANT_OPERATORS.contains(&key) {
            return Lvl::known(Level::Constant);
        }
        let path: Vec<&str> = q.path.iter().map(|i| i.name.as_str()).collect();
        self.unresolved.insert(path.join("!"));
        Lvl::tainted(Level::Constant)
    }

    fn lookup(&mut self, name: &str) -> Lvl {
        if let Some(b) = self.lookup_binding(name) {
            return b.lvl;
        }
        if let Some(lvl) = self.imports.get(name) {
            return lvl;
        }
        if let Some(b) = builtin_operator_binding(name) {
            return b.lvl;
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
                    self.scopes.push(
                        bindings
                            .into_iter()
                            .map(|(n, l)| (n, Binding::plain(l)))
                            .collect(),
                    );
                }
                Frame::PopScope => {
                    self.scopes.pop();
                }
                Frame::BindDef(name, nvals, taint) => {
                    let mut lvl = join_pop(&mut values, nvals);
                    lvl.unresolved |= taint;
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
                let lvl = self.lookup_qual(q);
                values.push(lvl);
            }
            ExprKind::Apply { head, args } => {
                let head_lvl = self.lookup_qual(head);
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
            // `ASSUME NEW T, NEW s \in Seq(T), P PROVE Q` declares names that
            // the later assumptions and the goal can use. Without binding
            // them, `Seq(T)` leaves `T` unresolved and taints the whole
            // sequent — which is what the corpus showed for the allocator
            // proof modules.
            ExprKind::AssumeProve { assumptions, .. } => {
                let scope: Vec<(String, Lvl)> = assumptions
                    .iter()
                    .filter_map(|a| match a {
                        AssumeItem::New { kind, decl, .. } => {
                            Some((decl.name.name.clone(), Lvl::known(level_of_new(*kind))))
                        }
                        AssumeItem::Expr(_) => None,
                    })
                    .collect();
                let children = child_exprs(expr);
                stack.push(Frame::Combine(expr, children.len()));
                stack.push(Frame::PopScope);
                for c in children.into_iter().rev() {
                    stack.push(Frame::Expand(c));
                }
                stack.push(Frame::PushScope(scope));
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
                            // A `LET` operator's level is computed by the max rule, which is
                            // only exact when every parameter is used and nothing in
                            // the body lowers a level. The top-level path computes
                            // exact per-parameter level functions instead; here the
                            // frame walk cannot, so an inexact case is marked unknown
                            // rather than reported wrongly.
                            let taint = !max_rule_is_exact(params, body);
                            stack.push(Frame::BindDef(name.name.clone(), 1, taint));
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
                            // A `LET` function definition is recursive too, but
                            // the frame-based walk cannot iterate to a fixpoint
                            // the way the top-level path does without nesting
                            // evaluations. Bind it unknown rather than guess:
                            // the self-reference resolves, and the result is
                            // marked untrusted instead of wrong.
                            scope.push((name.name.clone(), Lvl::tainted(Level::Constant)));
                            for b in bounds {
                                for p in &b.patterns {
                                    push_pattern(p, &mut scope);
                                }
                            }
                            stack.push(Frame::BindDef(name.name.clone(), bounds.len() + 1, false));
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
            // `Op(a, b)`: combine the operator's own level with each
            // argument through that parameter's level function, rather than
            // taking a plain maximum. `kids[0]` is the operator's base level,
            // pushed by `expand`.
            ExprKind::Apply { head, .. } => {
                let binding = self.lookup_binding(name_key(head));
                let mut out = kids.first().copied().unwrap_or_default();
                for (i, arg) in kids.iter().skip(1).enumerate() {
                    match binding.as_ref().and_then(|b| b.param_fns.get(i)) {
                        Some(f) => {
                            let contributed = f[arg.level as usize];
                            // The argument's *taint* only matters when the
                            // level actually depends on it. An ignored
                            // parameter cannot make the result unknown.
                            let depends = f.iter().any(|v| v.level != f[0].level);
                            out = out.join(Lvl {
                                level: contributed.level,
                                unresolved: contributed.unresolved || (depends && arg.unresolved),
                            });
                        }
                        None => out = out.join(*arg),
                    }
                }
                out
            }
            // An operator *parameter* invoked in operator position:
            // `BoxTest(-._) == -(x = 0)` applies its parameter, so
            // `BoxTest([])` is temporal. The spelling is a bound name here,
            // not a built-in, so its level function applies — the built-in
            // rules below would silently ignore the parameter.
            ExprKind::Prefix { op, .. }
            | ExprKind::Infix { op, .. }
            | ExprKind::Postfix { op, .. }
                if self.bound_binding(op).is_some() =>
            {
                let binding = self
                    .bound_binding(op)
                    .unwrap_or_else(|| Binding::plain(joined));
                let mut out = binding.lvl;
                for (i, arg) in kids.iter().enumerate() {
                    match binding.param_fns.get(i) {
                        Some(f) => {
                            let contributed = f[arg.level as usize];
                            let depends = f.iter().any(|v| v.level != f[0].level);
                            out = out.join(Lvl {
                                level: contributed.level,
                                unresolved: contributed.unresolved || (depends && arg.unresolved),
                            });
                        }
                        None => out = out.join(*arg),
                    }
                }
                out
            }
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

/// Is "the level is the maximum over the arguments" exact for this definition?
///
/// It fails in two ways, both seen in the corpora:
///
/// * the body **caps** a level — `ENABLED A` is a state predicate however high
///   `A` is, and `\cdot` yields an action;
/// * the body **ignores** a parameter — `SVGElemToString(elem) == TRUE` stays
///   constant however high `elem` goes. SANY gets this right and the max rule
///   does not, which is how it was found.
fn max_rule_is_exact(params: &[OpDecl], body: &Expr) -> bool {
    if params.is_empty() {
        return true;
    }
    if body_lowers_level(body) {
        return false;
    }
    params.iter().all(|p| mentions_name(body, &p.name.name))
}

/// Does `body` mention `name` anywhere?
fn mentions_name(body: &Expr, name: &str) -> bool {
    let mut stack = vec![body];
    while let Some(e) = stack.pop() {
        if let ExprKind::Name(q) | ExprKind::Apply { head: q, .. } = &e.kind
            && q.path.iter().any(|i| i.name == name)
        {
            return true;
        }
        stack.extend(child_exprs(e));
        if let ExprKind::Let { defs, .. } = &e.kind {
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

/// Does this body contain a construct that *lowers* a sub-expression's level?
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

/// The level function of a built-in operator *used as a value*.
///
/// TLA+ lets an operator be passed as an argument — `BoxTest([])` hands the
/// temporal `[]` to an operator that applies it. Treating such an argument as
/// an ordinary constant loses exactly the information that decides the
/// result's level, so the built-ins carry their own level functions:
///
/// * `[]`, `<>`, `~>` and `-+->` yield temporal whatever they are applied to;
/// * `ENABLED` caps at state, `UNCHANGED` and `'` at action;
/// * everything else passes its argument's level through.
///
/// Returns `None` for names that are not built-in operators, so an ordinary
/// identifier is unaffected.
fn builtin_operator_binding(name: &str) -> Option<Binding> {
    const CHAIN: [Level; 4] = [
        Level::Constant,
        Level::State,
        Level::Action,
        Level::Temporal,
    ];
    let fixed = |l: Level| [Lvl::known(l); 4];
    let passthrough = || {
        let mut row = [Lvl::known(Level::Constant); 4];
        for (i, l) in CHAIN.iter().enumerate() {
            row[i] = Lvl::known(*l);
        }
        row
    };

    let is_prefix = crate::op::prefix_info(name).is_some();
    let is_infix = crate::op::infix_info(name).is_some();
    let is_postfix = crate::op::postfix_info(name).is_some();
    if !(is_prefix || is_infix || is_postfix) {
        return None;
    }

    let (lvl, row) = match name {
        // `[]`, `<>`, `~>` and `-+->` all yield temporal formulas
        // whatever they are applied to.
        "[]" | "<>" | "~>" | "-+->" => (Level::Temporal, fixed(Level::Temporal)),
        "ENABLED" => (Level::State, fixed(Level::State)),
        "UNCHANGED" | "'" => (Level::Action, fixed(Level::Action)),
        "\\cdot" => (Level::Action, fixed(Level::Action)),
        _ => (Level::Constant, passthrough()),
    };
    let arity = if is_infix { 2 } else { 1 };
    Some(Binding {
        lvl: Lvl::known(lvl),
        param_fns: vec![row; arity],
    })
}

/// The level a `NEW` declaration introduces its name at.
const fn level_of_new(kind: NewKind) -> Level {
    match kind {
        NewKind::Constant => Level::Constant,
        NewKind::Variable | NewKind::State => Level::State,
        NewKind::Action => Level::Action,
        NewKind::Temporal => Level::Temporal,
    }
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
