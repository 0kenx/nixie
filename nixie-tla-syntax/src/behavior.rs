//! Reading the behaviour formula a TLC configuration names (issue #46).
//!
//! A `.cfg` says how the system moves in one of two ways: `INIT Init` with
//! `NEXT Next`, or `SPECIFICATION Spec`, where `Spec` is nearly always
//!
//! ```text
//! Spec == Init /\ [][Next]_vars
//! ```
//!
//! and is often followed by fairness conjuncts (`/\ WF_vars(Next)`). This
//! module reads such a formula for what a bounded check needs – the names of
//! the initial predicate and of the next-state action – and **names every
//! conjunct it cannot preserve**, instead of silently keeping the two it can.
//!
//! # What the two reference tools do
//!
//! * TLC (`tlc2.tool.impl.SpecProcessor.processConfigSpec`) walks the
//!   conjuncts. Each constant- or state-level one becomes an initial
//!   predicate, the single `[A]_v` contributes `A` – the action *inside* the
//!   brackets – as the next-state predicate, any other temporal conjunct is
//!   kept for liveness checking, and an action-level conjunct is an error.
//! * Apalache (`ConfigurationPassImpl.extractFromSpec`) flattens nested
//!   conjunctions, requires exactly one `Init` and one `[][Next]_vars`, both
//!   bare definition names, in either order – and warns while **ignoring**
//!   fairness.
//!
//! # Why `[][Next]_vars` reduces to `Next`
//!
//! `[Next]_vars` is `Next \/ UNCHANGED vars`. A stuttering step leaves the
//! state as it was, so the states a behaviour of `Init /\ [][Next]_vars`
//! visits are exactly the states a behaviour of `Init /\ [][Next]` visits:
//! the same sequence minus the repeats. A state invariant therefore holds of
//! one iff it holds of the other, and so does the deadlock question as both
//! reference tools pose it – a state with no `Next`-successor is reported as
//! a deadlock under `SPECIFICATION Spec` exactly as under `INIT`/`NEXT`
//! (TLC's well-known behaviour for a spec that permits stuttering; Apalache's
//! `--deadlock` default). Checking the two configurations the same way is
//! parity, not an approximation.
//!
//! # What is kept out of the check, and what is said about it
//!
//! A **fairness** conjunct (`WF_vars(Next)`, `\A p \in P : SF_vars(A(p))`)
//! restricts behaviours by their infinite tails. It removes no state from
//! any finite prefix a bounded check examines, so for a state invariant –
//! and for the deadlock question as both reference tools pose it – the
//! safety fragment gives the same answer. That is why TLC checks invariants
//! on the states `Init`/`Next` reach whatever fairness the specification
//! states, and why Apalache *warns and ignores* fairness in a
//! `SPECIFICATION`. The decomposition therefore **reports** the fairness
//! clauses it found ([`SafetyForm::fairness`]) and still returns the two
//! roles; the caller decides what a check may assume them away for. For a
//! **liveness** property it may not: an unfair lasso is not a behaviour of
//! the specification, and a lasso search that ignored the clause would
//! report it as a counterexample. The lasso checker therefore **assumes**
//! each clause there (issue #47), from the syntax the clause carries
//! ([`FairnessClause::expr`]); what it cannot assume faithfully, it declines
//! by name.
//!
//! Any other temporal conjunct is different in kind. `[]P` excludes states,
//! `[]A` excludes steps, `<>P` and `P ~> Q` say things no bounded unrolling
//! reproduces: ignoring one changes the question, so each is **refused by
//! name** – with its text and its place in the module – never dropped. So
//! is an action-level conjunct, a second `[][A]_v` (TLC refuses that too),
//! and a formula with no transition or no initial predicate at all.
//!
//! # Roles written inline
//!
//! TLC does not insist that the two roles be definitions' names: whatever
//! stands inside the brackets is the next-state predicate (`[Next \/
//! Terminate]_v`, the dag-consensus specs' shape) and every state-level
//! conjunct is an initial predicate (`PrintT(R) /\ Spec`, or `x = TRUE /\
//! Init`). Both are returned as [`RoleSource::Expr`], read in the module
//! the conjunct was written in like a name; Apalache's canonical form wants
//! one name for each and refuses the rest.

use crate::ast::{ActionKind, Expr, ExprKind, FairnessKind, Junct, QuantKind, UnitKind};
use crate::span::Span;
use crate::{Level, LevelReport, LoadedSpec, Module};

/// The safety fragment of a behaviour specification, as the roles a bounded
/// check needs them.
///
/// The roles are **not** resolved here: each means what it means in the
/// module its conjunct was written in. A model file that extends the
/// specification and redefines `Init` does not change what `Spec` says, and
/// a checker that resolved the names at its own root would check the model's
/// `Init` against the specification's `Next`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafetyForm<'m> {
    /// The initial predicate: every state-level conjunct of the formula,
    /// conjoined – as TLC reads them. Usually one, a name.
    pub init: Vec<RoleSource<'m>>,
    /// The next-state action: whatever stands inside the `[][A]_v` brackets.
    pub next: RoleSource<'m>,
    /// The fairness conjuncts the formula also carries, in source order.
    ///
    /// A bounded check does not assume them. For a state invariant that costs
    /// nothing (see the module docs); for a liveness property it is the
    /// difference between a counterexample and an unfair behaviour, so the
    /// checker assumes them there (issue #47) – which needs each clause's
    /// syntax, hence [`FairnessClause::expr`].
    pub fairness: Vec<FairnessClause<'m>>,
}

impl<'m> SafetyForm<'m> {
    /// The module the formula's roles are read in: that of the next-state
    /// action, which is where the canonical `Init /\ [][Next]_vars` is
    /// written even through a chain of abbreviations.
    #[must_use]
    pub fn home(&self) -> &'m Module {
        self.next.home()
    }

    /// The initial predicate's one name, when it is a single definition.
    #[must_use]
    pub fn init_name(&self) -> Option<&str> {
        match self.init.as_slice() {
            [RoleSource::Name { name, .. }] => Some(name),
            _ => None,
        }
    }

    /// The next-state action's name, when it is a definition.
    #[must_use]
    pub fn next_name(&self) -> Option<&str> {
        match &self.next {
            RoleSource::Name { name, .. } => Some(name),
            RoleSource::Expr { .. } => None,
        }
    }
}

/// One role of the safety fragment: a definition's name, or a formula the
/// specification writes inline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoleSource<'m> {
    /// A zero-argument definition, read in `home`'s scope.
    Name {
        /// The definition's name.
        name: String,
        /// The module whose scope the name is read in.
        home: &'m Module,
    },
    /// A formula written in the specification itself (`[Next \/ Terminate]_v`
    /// has `Next \/ Terminate` for its action), read in `home`'s scope.
    Expr {
        /// The formula.
        expr: &'m Expr,
        /// The module whose scope its names are read in.
        home: &'m Module,
    },
}

impl<'m> RoleSource<'m> {
    /// The module the role is read in.
    #[must_use]
    pub fn home(&self) -> &'m Module {
        match self {
            Self::Name { home, .. } | Self::Expr { home, .. } => home,
        }
    }

    /// The role as a line names it: the definition's name, or the formula
    /// rendered briefly and marked as written inline.
    #[must_use]
    pub fn describe(&self) -> String {
        match self {
            Self::Name { name, .. } => name.clone(),
            Self::Expr { expr, .. } => format!("{} (written inline)", brief(expr)),
        }
    }
}

/// One fairness conjunct of a behaviour specification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FairnessClause<'m> {
    /// Whether every fairness operator in the clause is `WF` (`SF` mixes in
    /// otherwise).
    pub weak: bool,
    /// Whether the clause is quantified over a set – `\A p \in P :
    /// WF_vars(A(p))`, the per-process idiom.
    pub quantified: bool,
    /// The clause, briefly rendered – `WF_x(Next2)`, `\A … : WF_vars(A(…))`.
    pub rendered: String,
    /// Where it is.
    pub span: Span,
    /// The conjunct's own syntax: the `WF`/`SF` node, or the `\A` that
    /// quantifies one (or a conjunction of several). What a checker that
    /// **assumes** the clause lowers (issue #47).
    pub expr: &'m Expr,
    /// The module the conjunct was written in, where its names resolve.
    pub home: &'m Module,
}

/// A definition visible by bare name in a module, and where it lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VisibleDef<'m> {
    /// The module that defines it – the scope its body's names resolve in.
    pub module: &'m Module,
    /// Its parameters. Empty for the definitions a role can name.
    pub params: &'m [crate::ast::OpDecl],
    /// Its body.
    pub body: &'m Expr,
}

/// The modules whose definitions `module` sees by bare name, **dependency
/// first**: a module appears after everything it transitively extends and
/// `module` itself is last, so a later entry shadows an earlier one.
///
/// `EXTENDS` re-exports, so the closure is transitive. `module` is included
/// even when nothing it extends was loaded (a single parsed file): its own
/// definitions are its.
#[must_use]
pub fn extends_closure<'m>(spec: &'m LoadedSpec, module: &'m Module) -> Vec<&'m Module> {
    // Breadth-first from `module`, then reversed: every module a module
    // extends is discovered after it, so reversing leaves each one after
    // all of its own imports.
    let mut order: Vec<&Module> = Vec::new();
    let mut queue: std::collections::VecDeque<&Module> = Default::default();
    queue.push_back(module);
    let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
    while let Some(cur) = queue.pop_front() {
        if !seen.insert(cur.name.name.as_str()) {
            continue;
        }
        for e in cur.extends() {
            if let Some((_, m)) = spec.modules.iter().find(|(n, _)| n == &e.name) {
                queue.push_back(m);
            }
        }
        order.push(cur);
    }
    order.reverse();
    order
}

/// The definition `name` resolves to in `module`'s scope, when a role may
/// name it: a zero-argument operator definition of the module itself, of an
/// **unnamed** instance, or of a module it transitively extends.
///
/// An unnamed `INSTANCE M WITH …` makes `M`'s members visible without a
/// prefix, which is how model files are written (`MC.tla`: `INSTANCE
/// ChangRoberts`, then `MC.cfg`: `SPECIFICATION Spec`). A member of a
/// *named* instance is not found, deliberately: it is written `I!Spec`, and
/// the roles derived from it would have to resolve through the same
/// substitution. That path this lookup does not take, so the caller declines
/// by name rather than half-resolving.
///
/// The definition's own parameters are returned unchecked: a caller that
/// needs a zero-argument one looks at [`VisibleDef::params`].
#[must_use]
pub fn visible_definition<'m>(
    spec: &'m LoadedSpec,
    module: &'m Module,
    name: &str,
) -> Option<VisibleDef<'m>> {
    let own = |m: &'m Module| -> Option<VisibleDef<'m>> {
        m.units.iter().find_map(|u| match &u.kind {
            UnitKind::OpDef {
                name: n,
                params,
                body,
                ..
            } if n.name == name => Some(VisibleDef {
                module: m,
                params,
                body,
            }),
            _ => None,
        })
    };
    if let Some(d) = own(module) {
        return Some(d);
    }
    for u in &module.units {
        if let UnitKind::Instance { instance, .. } = &u.kind
            && let Some((_, target)) = spec
                .modules
                .iter()
                .find(|(n, _)| *n == instance.module.name)
            && let Some(d) = own(target)
        {
            return Some(d);
        }
    }
    // Nearest first: `module`, then what it extends in source order, then
    // what those extend. TLA+ forbids one name in two extended modules, so
    // the order decides only which is reported, and decides it the same way
    // every time.
    extends_closure(spec, module)
        .iter()
        .rev()
        .find_map(|m| own(m))
}

/// Why a `SPECIFICATION` formula could not be reduced to its safety fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BehaviorFormError {
    /// No visible definition carries the name the configuration gave.
    NoSuchDefinition(String),
    /// The definition takes parameters; a behaviour specification has none.
    HasParameters {
        /// The definition's name.
        name: String,
        /// How many parameters it takes.
        arity: usize,
    },
    /// There is no `[][Next]_vars` conjunct, so there is no transition to
    /// unroll (`Spec == Init`), or no state-level one, so there is no initial
    /// predicate (`Spec == [][Next]_vars` alone).
    NoSafetyPair {
        /// What is missing.
        missing: &'static str,
        /// The formula, briefly rendered.
        rendered: String,
        /// Where the formula is.
        span: Span,
    },
    /// A conjunct a bounded check cannot preserve.
    Unsupported(UnsupportedClause),
}

/// A conjunct of the behaviour formula that an `Init`/`Next` unrolling
/// cannot reproduce.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsupportedClause {
    /// A second `[][A]_v`. TLC refuses this too: two next-state relations
    /// do not say which one the other's states come from.
    TwoNextState {
        /// The first one's action, as a diagnostic names it.
        first: String,
        /// Where the second is.
        span: Span,
    },
    /// Any other conjunct: temporal (`[]P`, `<>P`, `P ~> Q`, `\AA x : …`)
    /// or action-level (`x' # x`, which TLC refuses too), or a name this
    /// lookup does not resolve.
    Other {
        /// The conjunct, briefly rendered.
        rendered: String,
        /// Where it is.
        span: Span,
    },
}

impl core::fmt::Display for BehaviorFormError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.message())
    }
}

impl std::error::Error for BehaviorFormError {}

impl BehaviorFormError {
    /// The diagnostic, naming the offending clause and where it is.
    #[must_use]
    pub fn message(&self) -> String {
        match self {
            Self::NoSuchDefinition(name) => {
                format!("the module has no zero-argument definition named `{name}`")
            }
            Self::HasParameters { name, arity } => {
                format!("`{name}` takes {arity} argument(s); a behaviour specification takes none")
            }
            Self::NoSafetyPair {
                missing,
                rendered,
                span,
            } => format!(
                "no {missing} in `{rendered}` ({span}); the supported form is \
                 `Init /\\ [][Next]_vars`"
            ),
            Self::Unsupported(u) => match u {
                UnsupportedClause::TwoNextState { first, span } => format!(
                    "a second `[][Next]_vars` conjunct ({span}): `{first}` is already the \
                     next-state action"
                ),
                UnsupportedClause::Other { rendered, span } => {
                    format!("the conjunct `{rendered}` ({span})")
                }
            },
        }
    }
}

/// Decompose the behaviour formula `name` into its safety fragment.
///
/// `levels` are the per-module level reports ([`crate::check_spec`]). They
/// are consulted for one distinction only: a bare name that *is* an initial
/// predicate (`Init`) from one that abbreviates a temporal conjunct
/// (`Spec == Init /\ Safety`, with `Safety == [][Next]_vars`). The latter is
/// descended into, as TLC does.
///
/// # Errors
///
/// [`BehaviorFormError::NoSuchDefinition`] when nothing visible carries the
/// name, [`BehaviorFormError::HasParameters`] when it is parametrized;
/// otherwise the first conjunct, in source order, that cannot be preserved –
/// a temporal clause other than fairness, an action-level one – or a formula
/// with no safety pair in it at all. Fairness is not an error: it is
/// reported in [`SafetyForm::fairness`]. A state-level conjunct that is not
/// a name and an action inside the brackets that is not a name are roles
/// too ([`RoleSource::Expr`]), as they are for TLC.
pub fn safety_form<'m>(
    spec: &'m LoadedSpec,
    module: &'m Module,
    levels: &[(String, LevelReport)],
    name: &str,
) -> Result<SafetyForm<'m>, BehaviorFormError> {
    let def = visible_definition(spec, module, name)
        .ok_or_else(|| BehaviorFormError::NoSuchDefinition(name.to_string()))?;
    if !def.params.is_empty() {
        return Err(BehaviorFormError::HasParameters {
            name: name.to_string(),
            arity: def.params.len(),
        });
    }
    // A name's level is read in the report of the module that **defines**
    // it: a module's report lists its own definitions only, and the ones it
    // extends are visible by bare name too. Computed, not only trusted: a
    // level is a lower bound, which is all the walk needs (see `classify`).
    let level_of = |m: &Module, n: &str| -> Option<Level> {
        let def = visible_definition(spec, m, n)?;
        levels
            .iter()
            .find(|(mn, _)| mn == &def.module.name.name)
            .and_then(|(_, r)| r.level_of(n))
    };
    let mut walk = Walk {
        spec,
        level_of: &level_of,
        descended: 0,
    };
    let mut parts = Parts::default();
    walk.conjuncts(def.module, def.body, &mut parts)?;
    parts.finish(def.body)
}

/// The classification of the conjuncts seen so far.
#[derive(Default)]
struct Parts<'m> {
    /// The state-level conjuncts, each with the module it was written in.
    init: Vec<RoleSource<'m>>,
    /// The `[][A]_v` conjunct's action, likewise, when one was seen.
    next: Option<RoleSource<'m>>,
    /// The fairness conjuncts seen, in source order.
    fairness: Vec<FairnessClause<'m>>,
}

impl<'m> Parts<'m> {
    fn finish(self, root: &Expr) -> Result<SafetyForm<'m>, BehaviorFormError> {
        let Self {
            init,
            next,
            fairness,
        } = self;
        // Each role is read where **its** conjunct was written: through a
        // chain of abbreviations (`MC.tla`: `spec_… == Spec`) that is the
        // module holding the canonical formula, not the one naming it – and
        // that module's own `Init` is what the formula means there.
        match (init, next) {
            (init, Some(next)) if !init.is_empty() => Ok(SafetyForm {
                init,
                next,
                fairness,
            }),
            (init, Some(_)) => {
                let _ = init;
                Err(BehaviorFormError::NoSafetyPair {
                    missing: "state-level conjunct to unroll from",
                    rendered: brief(root),
                    span: root.span,
                })
            }
            // No transition: `Spec == Init` on its own is a set of states,
            // not something a bounded check can step.
            (_, None) => Err(BehaviorFormError::NoSafetyPair {
                missing: "`[][Next]_vars` conjunct",
                rendered: brief(root),
                span: root.span,
            }),
        }
    }
}

/// One decomposition pass. `descended` counts the abbreviations
/// (`Safety == [][Next]_v`) walked through: bodies are visited iteratively,
/// but a module whose definition names itself (`Spec == Spec`) must not loop.
struct Walk<'s, 'f> {
    spec: &'s LoadedSpec,
    level_of: &'f dyn Fn(&'s Module, &str) -> Option<Level>,
    descended: usize,
}

/// How many abbreviations one formula may pass through before the walk
/// calls it a cycle and reports the name.
const MAX_ABBREVIATIONS: usize = 32;

impl<'s, 'f> Walk<'s, 'f> {
    /// Flatten `expr` – as written in `module` – into conjuncts, descending
    /// through `/\` lists, parentheses and temporal-level abbreviations, and
    /// classify each. The first unpreservable one, in source order, is the
    /// error.
    fn conjuncts(
        &mut self,
        module: &'s Module,
        expr: &'s Expr,
        parts: &mut Parts<'s>,
    ) -> Result<(), BehaviorFormError> {
        let mut stack: Vec<(&'s Module, &'s Expr)> = vec![(module, expr)];
        while let Some((m, e)) = stack.pop() {
            match &e.kind {
                ExprKind::Paren(inner) => stack.push((m, inner)),
                ExprKind::Junction {
                    kind: Junct::And,
                    items,
                } => stack.extend(items.iter().rev().map(|i| (m, i))),
                ExprKind::Infix { op, lhs, rhs, .. } if op == "/\\" => {
                    // Right then left, so the left is popped first: source
                    // order, for a diagnostic that does not move about.
                    stack.push((m, rhs));
                    stack.push((m, lhs));
                }
                _ => self.classify(m, e, parts, &mut stack)?,
            }
        }
        Ok(())
    }

    fn classify(
        &mut self,
        module: &'s Module,
        e: &'s Expr,
        parts: &mut Parts<'s>,
        stack: &mut Vec<(&'s Module, &'s Expr)>,
    ) -> Result<(), BehaviorFormError> {
        let other = || UnsupportedClause::Other {
            rendered: brief(e),
            span: e.span,
        };
        match &e.kind {
            // `[][Next]_vars`: whatever stands inside the brackets is the
            // next-state action – a definition's name, or a formula the
            // specification writes there (`[Next \/ Terminate]_v`), as TLC
            // takes it. The subscript is not consulted – see the module
            // docs: a stuttering step adds no state, so it changes nothing a
            // bounded check asks, which is why TLC and Apalache both ignore
            // it too.
            ExprKind::Prefix { op, operand, .. } if op == "[]" => match &operand.kind {
                ExprKind::Action {
                    kind: ActionKind::Stuttering,
                    body,
                    ..
                } => {
                    if let Some(first) = &parts.next {
                        return Err(BehaviorFormError::Unsupported(
                            UnsupportedClause::TwoNextState {
                                first: format!("`{}`", first.describe()),
                                span: e.span,
                            },
                        ));
                    }
                    parts.next = Some(role_of(body, module));
                    Ok(())
                }
                // `[]` of an action-level formula that is not `[A]_v`:
                // non-stuttering `<<A>>_v`, or an inline `[]A` with no
                // subscript. Both forbid stuttering where `Init /\ [][Next]`
                // permits it, so they are not the same specification.
                _ => Err(BehaviorFormError::Unsupported(other())),
            },
            // Fairness, plain or over a set of processes. Reported, not
            // refused: the caller decides what a check may assume away.
            ExprKind::Fairness { kind, .. } => {
                parts.fairness.push(FairnessClause {
                    weak: *kind == FairnessKind::Weak,
                    quantified: false,
                    rendered: brief(e),
                    span: e.span,
                    expr: e,
                    home: module,
                });
                Ok(())
            }
            ExprKind::Quant {
                kind: QuantKind::Forall,
                ..
            }
            | ExprKind::UnboundedQuant {
                kind: QuantKind::Forall,
                ..
            } => match fairness_only(e) {
                Some(weak) => {
                    parts.fairness.push(FairnessClause {
                        weak,
                        quantified: true,
                        rendered: brief(e),
                        span: e.span,
                        expr: e,
                        home: module,
                    });
                    Ok(())
                }
                None => Err(BehaviorFormError::Unsupported(other())),
            },
            // A bare name. At state level it is an initial predicate. Above
            // that it abbreviates a temporal conjunct (`Safety == [][Next]_v`,
            // `Fairness == \A p \in P : WF_vars(A(p))`), which TLC descends
            // into – and so does this, when the name resolves. The level is
            // taken as computed even where it depends on an unresolved name:
            // it is a lower bound, and a temporal operator the definition
            // visibly contains lifts it however the unresolved names turn
            // out. A level that stays at or below state level unresolved is
            // not grounds for refusal: the name is taken as an initial
            // predicate, and the role's own lowering refuses a temporal
            // formula by name.
            ExprKind::Name(q) if !q.is_qualified() => {
                let Some(id) = q.base() else {
                    return Err(BehaviorFormError::Unsupported(other()));
                };
                match (self.level_of)(module, &id.name) {
                    Some(Level::Temporal) | Some(Level::Action) => {
                        match visible_definition(self.spec, module, &id.name) {
                            Some(d) if self.descended < MAX_ABBREVIATIONS => {
                                self.descended += 1;
                                stack.push((d.module, d.body));
                                Ok(())
                            }
                            _ => Err(BehaviorFormError::Unsupported(other())),
                        }
                    }
                    Some(Level::Constant) | Some(Level::State) | None => {
                        parts.init.push(RoleSource::Name {
                            name: id.name.clone(),
                            home: module,
                        });
                        Ok(())
                    }
                }
            }
            // A member of a **named** instance (`I!Spec`, `IM(y)!Spec`): the
            // roles behind it would have to resolve through the instance's
            // substitution, a path this lookup does not take. Declined by
            // name rather than half-resolved.
            ExprKind::Name(_) | ExprKind::Qualified { .. } => {
                Err(BehaviorFormError::Unsupported(other()))
            }
            // Anything else. At state level it is an initial predicate like
            // any other (TLC's `processConfigSpec` conjoins every state-level
            // conjunct: `Spec == x = TRUE /\ Init /\ [][Next]_x`); at
            // action level TLC refuses it, and so does this; above that it
            // was already classified above.
            _ => match syntactic_level(e, module, self.level_of) {
                Level::Constant | Level::State => {
                    parts.init.push(role_of(e, module));
                    Ok(())
                }
                Level::Action | Level::Temporal => Err(BehaviorFormError::Unsupported(other())),
            },
        }
    }
}

/// The role a conjunct names: its name when it is a single unqualified
/// identifier, otherwise the formula itself.
fn role_of<'m>(e: &'m Expr, module: &'m Module) -> RoleSource<'m> {
    match bare_name(e) {
        Some(name) => RoleSource::Name {
            name: name.to_string(),
            home: module,
        },
        None => RoleSource::Expr {
            expr: unwrap_parens(e),
            home: module,
        },
    }
}

/// The expression without its outermost parentheses.
fn unwrap_parens(mut e: &Expr) -> &Expr {
    while let ExprKind::Paren(inner) = &e.kind {
        e = inner;
    }
    e
}

/// The level of an expression that is neither a name nor one of the shapes
/// the walk classifies itself: the maximum over what it visibly contains,
/// with names read through `level_of`. `Constant` and `State` are told
/// apart only through names; a formula that is neither is reported at the
/// level its operators impose.
fn syntactic_level<'s>(
    e: &Expr,
    module: &'s Module,
    level_of: &dyn Fn(&'s Module, &str) -> Option<Level>,
) -> Level {
    let mut level = Level::Constant;
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match &cur.kind {
            ExprKind::Postfix { op, .. } if op == "'" => level = level.max(Level::Action),
            ExprKind::Prefix { op, .. } => {
                level = match op.as_str() {
                    "[]" | "<>" => level.max(Level::Temporal),
                    "ENABLED" => level.max(Level::State),
                    "UNCHANGED" => level.max(Level::Action),
                    _ => level,
                };
            }
            ExprKind::Infix { op, .. } => {
                if matches!(op.as_str(), "~>" | "-+->") {
                    level = level.max(Level::Temporal);
                } else if op == "\\cdot" {
                    level = level.max(Level::Action);
                }
            }
            ExprKind::Action { .. } | ExprKind::Fairness { .. } => {
                level = level.max(Level::Action);
            }
            ExprKind::Quant { kind, .. } | ExprKind::UnboundedQuant { kind, .. } => {
                if matches!(kind, QuantKind::TemporalForall | QuantKind::TemporalExists) {
                    level = level.max(Level::Temporal);
                }
            }
            ExprKind::Name(q) if !q.is_qualified() && level < Level::Temporal => {
                if let Some(id) = q.base()
                    && let Some(l) = level_of(module, &id.name)
                {
                    level = level.max(l);
                }
            }
            _ => {}
        }
        stack.extend(cur.subexprs());
    }
    level
}

/// Whether a universal quantifier's body is nothing but fairness – `\A p
/// \in P : WF_vars(A(p))`, or a conjunction of such – and whether every
/// fairness operator in it is weak.
///
/// Quantified fairness is the per-process idiom (`Spec == Init /\
/// [][Next]_vars /\ \A self \in Node : WF_vars(node(self))`) and TLC
/// treats it exactly as a fairness conjunct. Flattened iteratively; `None`
/// as soon as one conjunct is anything else.
fn fairness_only(quant: &Expr) -> Option<bool> {
    let mut all_weak = true;
    let mut stack = vec![quant];
    let mut seen = 0usize;
    while let Some(e) = stack.pop() {
        match &e.kind {
            ExprKind::Paren(inner) => stack.push(inner),
            ExprKind::Junction {
                kind: Junct::And,
                items,
            } => stack.extend(items),
            ExprKind::Infix { op, lhs, rhs, .. } if op == "/\\" => {
                stack.push(lhs);
                stack.push(rhs);
            }
            ExprKind::Quant {
                kind: QuantKind::Forall,
                body,
                ..
            }
            | ExprKind::UnboundedQuant {
                kind: QuantKind::Forall,
                body,
                ..
            } => {
                seen += 1;
                stack.push(body);
            }
            ExprKind::Fairness { kind, .. } => {
                seen += 1;
                all_weak &= *kind == FairnessKind::Weak;
            }
            _ => return None,
        }
    }
    (seen > 0).then_some(all_weak)
}

/// The single unqualified identifier an expression is, if it is one.
fn bare_name(e: &Expr) -> Option<&str> {
    match &e.kind {
        ExprKind::Name(q) if !q.is_qualified() => q.base().map(|i| i.name.as_str()),
        ExprKind::Paren(inner) => bare_name(inner),
        _ => None,
    }
}

/// A formula rendered briefly, for diagnostics.
///
/// Not a pretty-printer: it covers the shapes a behaviour specification's
/// conjuncts take – names, `/\`, `[]`, `[A]_v`, `WF_v(A)`, literals – and
/// writes `…` for anything else. The span beside it is the exact place to
/// look; this is what a reader recognises at a glance.
#[must_use]
pub fn brief(e: &Expr) -> String {
    let names = |q: &crate::ast::QualName| {
        q.path
            .iter()
            .map(|i| i.name.as_str())
            .collect::<Vec<_>>()
            .join("!")
    };
    match &e.kind {
        ExprKind::Name(q) => names(q),
        ExprKind::Qualified {
            base,
            selector,
            args,
            ..
        } => {
            let sel = &selector.name;
            let args_s = if args.is_empty() {
                String::new()
            } else {
                format!(
                    "({})",
                    args.iter().map(brief).collect::<Vec<_>>().join(", ")
                )
            };
            format!("{}!{sel}{args_s}", brief(base))
        }
        ExprKind::Int { digits, .. } => digits.clone(),
        ExprKind::Str(t) => format!("{t:?}"),
        ExprKind::Paren(inner) => format!("({})", brief(inner)),
        ExprKind::Junction { kind, items } => {
            let op = match kind {
                Junct::And => "/\\",
                Junct::Or => "\\/",
            };
            format!(
                "({})",
                items
                    .iter()
                    .map(brief)
                    .collect::<Vec<_>>()
                    .join(&format!(" {op} "))
            )
        }
        ExprKind::Infix { op, lhs, rhs, .. } => match crate::op::infix_info(op) {
            Some(info) => format!(
                "{} {op} {}",
                operand_in(lhs, &info, true),
                operand_in(rhs, &info, false)
            ),
            None => format!("({} {op} {})", brief(lhs), brief(rhs)),
        },
        ExprKind::Prefix { op, operand, .. } => {
            format!("{op}{}", self::operand(operand))
        }
        ExprKind::Postfix { op, operand, .. } => format!("{}{op}", brief(operand)),
        ExprKind::Action {
            kind,
            body,
            subscript,
        } => match kind {
            ActionKind::Stuttering => format!("[{}]_{}", brief(body), brief(subscript)),
            ActionKind::NonStuttering => format!("<<{}>>_{}", brief(body), brief(subscript)),
        },
        ExprKind::Fairness {
            kind,
            subscript,
            body,
        } => format!(
            "{}_{}({})",
            match kind {
                FairnessKind::Weak => "WF",
                FairnessKind::Strong => "SF",
            },
            brief(subscript),
            brief(body)
        ),
        ExprKind::Tuple(items) => format!(
            "<<{}>>",
            items.iter().map(brief).collect::<Vec<_>>().join(", ")
        ),
        ExprKind::Apply { head, args } if !args.is_empty() => format!(
            "{}({})",
            names(head),
            args.iter().map(brief).collect::<Vec<_>>().join(", ")
        ),
        ExprKind::Quant { kind, body, .. } | ExprKind::UnboundedQuant { kind, body, .. } => {
            let q = match kind {
                QuantKind::Forall => "\\A",
                QuantKind::Exists => "\\E",
                QuantKind::TemporalForall => "\\AA",
                QuantKind::TemporalExists => "\\EE",
            };
            format!("{q} … : {}", brief(body))
        }
        _ => "…".to_string(),
    }
}

/// A prefix operator's operand, parenthesized whenever it is itself an
/// infix expression or a junction: over-parenthesizing costs a reader a
/// pair of brackets, under-parenthesizing changes the formula.
fn operand(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Infix { .. } | ExprKind::Junction { .. } => format!("({})", brief(e)),
        _ => brief(e),
    }
}

/// One operand of the infix operator `outer`, parenthesized unless it binds
/// at least as tightly on its own.
///
/// A tighter operator (`x + 1` under `=`) needs nothing. A looser or equal
/// one does, with the single exception TLA+ makes: the same operator chained
/// on its associative side (`a + b + c`, parsed left to right).
fn operand_in(e: &Expr, outer: &crate::op::OpInfo, left: bool) -> String {
    match &e.kind {
        ExprKind::Infix { op, .. } => match crate::op::infix_info(op) {
            Some(inner) if inner.lo > outer.lo => brief(e),
            Some(inner) if inner.canonical == outer.canonical && outer.assoc && left => brief(e),
            _ => format!("({})", brief(e)),
        },
        _ => brief(e),
    }
}
