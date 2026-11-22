//! Bounded model checking of a TLA+ specification.
//!
//! The first point at which the front end answers a question a user would
//! actually ask: *does this invariant hold for the first k steps?*
//!
//! # What the answer means
//!
//! [`Outcome::NoViolationWithin`] says **no counterexample of that length
//! exists**. It does *not* say the invariant holds. Bounded model checking is
//! a bug finder, and a k-step search that finds nothing is silent about step
//! k+1. Saying otherwise would be the model-checking equivalent of a wrong
//! `unsat`, so the name says the bound out loud and there is no `Safe`
//! variant to reach for by accident. Proving an invariant needs O2's CHC
//! lowering to `nixie-spacer`, which is a separate milestone.
//!
//! # How the unrolling works
//!
//! A state variable becomes a family of SMT variables, one per step, and `'`
//! raises the step — so `Next` encoded at step `i` relates `i` to `i + 1`
//! without any rewriting of the term. The check at depth `j` is then
//!
//! ```text
//! Init@0  /\  Next@0  /\ ... /\  Next@(j-1)  /\  ~Inv@j
//! ```
//!
//! and a `Sat` answer *is* the counterexample trace.
//!
//! An action that does not mention `x'` leaves `x@(i+1)` unconstrained. That
//! is not an omission: a TLA+ action which says nothing about a variable does
//! permit it to take any value, and encoding it as unchanged would silently
//! discard behaviours and could turn a real counterexample into a false
//! "no violation".

use std::rc::Rc;

use nixie_core::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};
use nixie_tla::types::Inference;
use nixie_tla::{Kera, KeraRef, Lowerer};
use nixie_tla_syntax::{ConfigValue, LoadedSpec, Module, TlcConfig, UnitKind};

use crate::encode::{EncodeError, Encoder, SetEncoding};
use crate::sorts::sort_of;
use crate::trace::{State, Trace};

/// What a bounded check found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// No counterexample exists with this many steps **or fewer**.
    ///
    /// Deliberately not called "safe": longer traces were not examined.
    NoViolationWithin(u32),
    /// The invariant fails, reachable in this many steps.
    Violation {
        /// The number of `Next` steps taken before the violating state.
        step: u32,
    },
    /// A reachable state exists, at this many steps, that **no transition
    /// leaves**: a deadlock.
    ///
    /// Apalache's `check` looks for deadlocks by default, and its exit code
    /// for one is the same 12 a counterexample gets — the distinction is in
    /// the outcome line, not the code. The no-successor half is a *proof*
    /// (the `Next` query at this step came back `Unsat` over every state
    /// that has one), never a guess: an undecided query makes the whole
    /// verdict [`Outcome::Unknown`].
    Deadlock {
        /// The number of `Next` steps taken before the stuck state.
        step: u32,
    },
    /// No behaviour of the full `--length` exists.
    ///
    /// With deadlock checking off and no violation found, the honest report
    /// is not "no error" but "nothing ran that far": every behaviour stopped
    /// short, which is either a deadlock nobody asked about or a bound past
    /// the specification's lifetime. Apalache's own outcome and exit code
    /// (0) — the message carries the distinction.
    ExecutionsTooShort,
    /// The search could not be completed.
    ///
    /// Carries what stopped it. Never reported as either of the above: an
    /// undecided query is not a proof and not a bug.
    Unknown(String),
    /// The specification's own assumptions are contradictory: it has **no
    /// behaviours at all**.
    ///
    /// TLC and Apalache report a violated assumption and stop, and so does
    /// this — reporting `NoViolationWithin` instead would be technically true
    /// (no counterexample exists) and practically a lie (it reads as "the
    /// invariant holds", when in fact there is nothing to check). Distinguished
    /// from [`Outcome::Unknown`], which is about what the search could not
    /// decide; this is decided, and what it decided is that the question is
    /// empty.
    AssumptionsUnsatisfiable,
}

/// The result of one step's deadlock question.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DeadlockSearch {
    /// No reachable state at this step is stuck.
    None,
    /// A reachable state at this step has no successor.
    Found(u32),
    /// The question could not be answered.
    Unknown(String),
}

/// Why a specification could not be checked at all.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SetupError {
    /// A named definition is not in the module.
    #[error("the module has no zero-argument definition named `{0}`")]
    NoSuchDefinition(String),
    /// The definition could not be lowered to the kernel.
    #[error("`{name}` could not be lowered: {why}")]
    Lower {
        /// The definition.
        name: String,
        /// The lowering diagnostic.
        why: String,
    },
    /// Type inference failed.
    #[error("the specification does not type check: {0}")]
    Types(String),
    /// A name's type has no SMT sort yet.
    #[error("`{name}` is {ty}, which has no SMT sort yet")]
    NoSort {
        /// The name.
        name: String,
        /// Its inferred type.
        ty: String,
    },
    /// A formula is at the wrong TLA+ level to play the role asked of it.
    ///
    /// An invariant must be a **state** predicate. An action used as one —
    /// `Inv == UNCHANGED x` is the shape that found this — is not a
    /// counterexample waiting to be found, it is a malformed specification,
    /// and reporting a `Violation` for it would answer a question nobody
    /// asked. `UnchangedAsInv1663.tla` in Apalache's test suite is exactly
    /// that, and is why this variant exists.
    #[error("`{name}` is a {found} formula, but {role} must be a {wanted} formula")]
    Level {
        /// The definition.
        name: String,
        /// What it is being used as.
        role: &'static str,
        /// The level it has.
        found: String,
        /// The level the role allows.
        wanted: String,
    },
    /// A constant-level assumption **evaluates to FALSE**.
    ///
    /// A specification whose assumptions are contradictory has no behaviours,
    /// and checking one anyway reports counterexamples for a specification
    /// that does not exist. TLC and Apalache report the violated assumption
    /// and stop; so does this. The evaluation runs on the *substituted*
    /// constants — after `.cfg` and `--cinit` pinning — because those are the
    /// constants the check is actually about.
    #[error("assumption violated: `{name}` is FALSE")]
    AssumptionViolated {
        /// Which assumption, by its definition or `ASSUME` position.
        name: String,
    },
    /// A `.cfg` replacement could not be applied.
    ///
    /// Reported rather than skipped. `Ballot <- MCBallot` is usually the only
    /// thing making a specification finite, so proceeding without it checks a
    /// different — and often unencodable — specification.
    #[error("the configuration's `{name} <- {with}` could not be applied: {why}")]
    Replacement {
        /// The name being replaced.
        name: String,
        /// The replacement.
        with: String,
        /// Why not.
        why: String,
    },
    /// A formula could not be encoded.
    #[error("`{name}` could not be encoded: {why}")]
    Encode {
        /// Which formula.
        name: String,
        /// The encoding diagnostic.
        why: String,
    },
}

/// Which definitions play which role in a check.
///
/// A struct rather than four positional `&str`s: `init` and `next` have the
/// same type, and swapping them produces a check that runs happily and answers
/// a different question. Naming them at the call site makes that mistake
/// visible.
#[derive(Debug, Clone, Copy)]
pub struct Roles<'r> {
    /// The initial-state predicate.
    pub init: &'r str,
    /// The next-state action.
    pub next: &'r str,
    /// The invariants to check, conjunctively: the counterexample condition is
    /// the disjunction of their negations, which is `--inv=A,B`'s meaning in
    /// Apalache. A slice, because a single name is the common case and a list
    /// is the contract.
    pub inv: &'r [&'r str],
    /// Extra zero-argument definitions to assume, on top of the module's
    /// `ASSUME`s.
    ///
    /// Apalache's `ConstInit` convention lives here: a specification whose
    /// constants are pinned by `--cinit=ConstInit` puts no `ASSUME` in the
    /// module, so a checker reading only `ASSUME` sees completely arbitrary
    /// constants and reports counterexamples the specification does not have.
    /// `Bug1023.tla` in Apalache's own test suite is exactly that shape.
    pub constraints: &'r [&'r str],
}

/// A specification prepared for checking.
pub struct Bmc {
    /// The module's `ASSUME`s, which constrain the `CONSTANT`s.
    assumptions: Vec<KeraRef>,
    init: KeraRef,
    next: KeraRef,
    /// The invariants, in the order named, with the names they were named by.
    invs: Vec<(String, KeraRef)>,
    encoder: Encoder,
    /// Assumptions that could not be lowered or typed, counted at prepare
    /// time. Encode-time drops are added per check, into
    /// [`Bmc::dropped_assumptions`], which is why the split exists: a check
    /// that re-encodes must not double-count.
    dropped_setup: usize,
    /// Assumptions that could not be lowered, typed or encoded — the split's
    /// published half.
    dropped_assumptions: usize,
    /// `CONSTRAINT`: a state predicate asserted in every state.
    state_constraints: Vec<KeraRef>,
    /// `ACTION_CONSTRAINT`: a predicate asserted over every step.
    action_constraints: Vec<KeraRef>,
    /// Parts of the configuration that were read and not acted on.
    unapplied_config: Vec<String>,
    /// A deterministic per-query budget, in conflicts.
    conflict_limit: Option<u64>,
    /// The counterexample behind the last reported [`Outcome::Violation`].
    ///
    /// Kept beside the verdict rather than inside it: a verdict is compared
    /// and tallied, a trace is read.
    counterexample: Option<Trace>,
    /// Whether that counterexample was confirmed independently.
    verification: Option<Verification>,
    /// Whether the search also looks for **deadlocks** — reachable states no
    /// transition leaves. Apalache's default (`checkDeadlocks = true`).
    check_deadlocks: bool,
    /// The step behind the last reported [`Outcome::Deadlock`].
    deadlock_step: Option<u32>,
    /// The names of the **action** invariants — formulas constraining a step
    /// pair `(s_j, s_{j+1})`, checked over pairs rather than single states.
    action_invariant_names: Vec<String>,
    /// Clauses ruling out counterexamples already reported.
    ///
    /// Asserted on every subsequent query, which is how a *second*
    /// counterexample is found. They only ever narrow the search, so they can
    /// hide a behaviour and never invent one.
    blocked: Vec<TermId>,
    /// Which of the named invariants the last counterexample broke, by name.
    ///
    /// A list, because `--inv=A,B` asks about several at once and a caller
    /// acts on the one that broke. Decided by the *evaluator* over the decoded
    /// last state, not by the solver: which disjunct the search happened to
    /// satisfy first is not an answer, it is an accident of encoding order.
    violated_invariants: Vec<String>,
}

/// What became of the attempt to confirm a counterexample independently.
///
/// The solver says the encoded formula is satisfiable. This says whether the
/// states behind that answer could be read back and shown, by
/// `nixie-tla`'s evaluator, to be a behaviour that really breaks the
/// invariant — a completely separate implementation of TLA+, the one
/// `bench/tla_eval` checks against TLC.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verification {
    /// The trace was read back and replays: `Init` holds in the first state,
    /// `Next` between each pair, the configuration's constraints throughout,
    /// and the invariant is `FALSE` at the end.
    Replayed,
    /// The model could not be read back as TLA+ values, naming the shape.
    ///
    /// Not evidence against the verdict: it says the *reader* fell short.
    NotDecoded(String),
    /// The trace was read back and does not replay, naming what disagreed.
    ///
    /// This is the interesting one. It means the evaluator and the encoding
    /// disagree about the states the solver produced, and every such report is
    /// worth chasing to the bottom before it is explained away.
    NotReplayed(String),
}

impl Bmc {
    /// Prepare `Init`, `Next` and `Inv` from one module.
    ///
    /// `constraints` names extra zero-argument definitions to assume, on top
    /// of the module's `ASSUME`s. Apalache's `ConstInit` convention lives here:
    /// a specification whose constants are pinned by `--cinit=ConstInit` puts
    /// no `ASSUME` in the module, so a checker that reads only `ASSUME` sees
    /// completely arbitrary constants and reports counterexamples the
    /// specification does not have. `Bug1023.tla` in Apalache's own test suite
    /// is exactly that shape, and it is what this parameter exists for.
    ///
    /// # Errors
    ///
    /// Returns the first stage that could not be completed, naming it. A
    /// specification that cannot be prepared is never checked with a guessed
    /// substitute.
    pub fn prepare<'a>(
        spec: &'a LoadedSpec,
        module: &'a Module,
        init: &str,
        next: &str,
        inv: &str,
        constraints: &[&str],
        tm: &mut TermManager,
    ) -> core::result::Result<Self, SetupError> {
        Self::prepare_with_config(
            spec,
            module,
            Roles {
                init,
                next,
                inv: std::slice::from_ref(&inv),
                constraints,
            },
            &TlcConfig::default(),
            tm,
        )
    }

    /// Prepare a specification with its TLC configuration applied.
    ///
    /// The `.cfg` is where a specification's parameters actually live. Without
    /// it a `CONSTANT N` is an arbitrary integer, `1..N` has no enumerable
    /// member list, and the checker is asking a strictly harder question than
    /// the author did. Three parts of the file are acted on here:
    ///
    /// * `CONSTANT x = e` becomes an **assumption** `x = e`, which is also
    ///   what gives `x` its type. A **model value** becomes a string literal
    ///   with a reserved prefix: model values are uninterpreted constants,
    ///   distinct from one another and from everything else, and distinct
    ///   string literals are already exactly that in the solver.
    /// * `CONSTANT x <- Def` rebinds `x` to `Def` in the lowerer, which is
    ///   what TLC does and what makes an infinite specification finite.
    /// * `CONSTRAINT C` becomes a predicate asserted in **every** state of the
    ///   unrolling, and `ACTION_CONSTRAINT A` one asserted over every step.
    ///
    /// What is read and not acted on is listed by
    /// [`Bmc::unapplied_config`] rather than being absorbed silently.
    ///
    /// # Errors
    ///
    /// As [`Bmc::prepare`], plus [`SetupError::Replacement`] when a `<-` names
    /// a definition the module does not have or one of a different arity.
    pub fn prepare_with_config<'a>(
        spec: &'a LoadedSpec,
        module: &'a Module,
        roles: Roles<'_>,
        config: &TlcConfig,
        tm: &mut TermManager,
    ) -> core::result::Result<Self, SetupError> {
        let Roles {
            init,
            next,
            inv: _,
            constraints,
        } = roles;
        // ONE lowerer for all three formulas. Binder renaming uses a counter
        // held by the `Lowerer`, so separate lowerings would each start from
        // zero and could give two unrelated binders — one in `Init`, one in
        // `Next` — the same name. Inference keys its environment by name, so
        // that would silently force two independent variables to one type.
        let mut low = Lowerer::new();
        low.add_spec(spec);
        let mut dropped = 0usize;
        let mut unapplied: Vec<String> = Vec::new();

        // Replacements first: every later stage — levels, lowering, inference
        // — must see the replaced definitions, because that is the
        // specification the author configured.
        for (name, r) in &config.replacements {
            match &r.module {
                // `x <- [M]d` replaces inside an instantiated module, which
                // needs `INSTANCE` substitution the lowering does not do.
                // Recorded, never quietly treated as the unqualified form:
                // the two are different specifications.
                Some(m) => unapplied.push(format!("{name} <- [{m}]{} (INSTANCE)", r.to)),
                None => {
                    low.replace_definition(name, &r.to)
                        .map_err(|e| SetupError::Replacement {
                            name: name.clone(),
                            with: r.to.clone(),
                            why: e.to_string(),
                        })?
                }
            }
        }
        // `CONSTANT x = e` is a **substitution**, not an assumption. TLC's
        // own words are "replace the constant with the constant expression",
        // and the difference is load-bearing: an assumption `N = 3` reaches
        // the solver, but the encoder needs the value earlier than that —
        // `1..N` has no candidate list until `N` is literally `3`. Pinning it
        // as an equation and hoping the encoder catches up was the first
        // attempt, and it leaves the headline case exactly as blocked as it
        // was.
        for (name, value) in &config.assignments {
            match config_value_to_kera(value) {
                Some(v) => low.bind_constant(name, v),
                None => unapplied.push(format!("{name} = … (uninterpreted)")),
            }
        }
        // A `ConstInit` pins the constants too, and it is a **substitution**
        // for exactly the same reason a `.cfg` assignment is. Apalache's
        // convention is `--cinit=CInit` with
        //
        //     CInit == replicas = {"n1", "n2", "n3"}
        //
        // and asserting that leaves `[replicas -> S]` as unencodable as it was
        // — the encoder needs the members before the solver runs, not after.
        // Every top-level conjunct of the shape `name = expr`, where `name` is
        // a `CONSTANT` the module declares, is bound instead. The definition
        // is still asserted afterwards, where it becomes trivially true and
        // costs nothing.
        //
        // Lowered in a **throwaway** `Lowerer`, so that nothing this reads
        // lands in the real one's definition cache before the binding exists:
        // a body cached with the constant still free would be reused with it
        // still free.
        let declared: std::collections::HashSet<&str> = constant_names(module);
        for name in constraints {
            let mut probe = Lowerer::new();
            probe.add_spec(spec);
            let Ok(body) = probe.lower_named(module, name) else {
                continue;
            };
            for (c, value) in ground_bindings(&body, &declared) {
                low.bind_constant(&c, value);
            }
        }
        for (name, module_name, to) in config.module_qualified_assignments() {
            unapplied.push(format!("{name} = [{module_name}]{to} (uninterpreted)"));
        }
        for opt in config.unused_options() {
            unapplied.push(opt.to_string());
        }
        // Level-check before anything else. TLA+ gives `Init` and `Inv` a
        // maximum level, and a formula above it is malformed rather than
        // false. The check is deliberately one-sided: `trusted_level_of`
        // returns `None` when a level depends on a name it could not resolve,
        // and an unproven level is not grounds for rejection.
        // An `INSTANCE` target that never resolved is a defect in the
        // specification, reported by name with the instance's span — not a
        // silent drop that surfaces much later as a name error at some use.
        if let Some((name, _)) = low.missing_instances().first() {
            return Err(SetupError::Lower {
                name: format!("INSTANCE {name}"),
                why: format!(
                    "the instantiated module `{name}` is neither defined in this file nor \
                     loaded from the search path"
                ),
            });
        }
        let levels = nixie_tla_syntax::check_module(module);
        let require = |name: &str, role: &'static str, max: nixie_tla_syntax::Level| match levels
            .trusted_level_of(name)
        {
            Some(l) if l > max => Err(SetupError::Level {
                name: name.to_string(),
                role,
                found: format!("{l:?}"),
                wanted: format!("{max:?}"),
            }),
            _ => Ok(()),
        };
        require(init, "an initial predicate", nixie_tla_syntax::Level::State)?;
        require(next, "a next-state action", nixie_tla_syntax::Level::Action)?;
        // The invariant levels split three ways, and only the temporal one
        // is refused: an action-level invariant is a legitimate thing to ask
        // (Apalache's `ActionInv.tla`), checked over step pairs; a temporal
        // one is a lasso question this bounded loop does not ask, and
        // pretending otherwise would answer a different question silently.
        let levels = nixie_tla_syntax::check_module(module);
        for inv in roles.inv {
            if invariant_kind(&levels, inv) == InvariantKind::Temporal {
                return Err(SetupError::Level {
                    name: (*inv).to_string(),
                    role: "an invariant",
                    found: "a temporal".to_string(),
                    wanted: "a state or action".to_string(),
                });
            }
        }

        let init_k = lower_one(&mut low, module, init)?;
        let next_k = lower_one(&mut low, module, next)?;
        let mut invs = Vec::with_capacity(roles.inv.len());
        for inv in roles.inv {
            invs.push(((*inv).to_string(), lower_one(&mut low, module, inv)?));
        }
        // Positive existentials over the standard infinite sets are
        // skolemized before anything else sees them (`\E no \in Nat : …` is
        // the idiom `HandshakeWithTypes` and the message-passing corpus use).
        // The rewrite is polarity-tracked — see the pass — and runs on every
        // role formula plus the constraint definitions, so a skolem in `Init`
        // and one in `Next` over the same set are still distinct witnesses.
        let init_k = nixie_tla::lower::skolemize_infinite_existentials(&init_k);
        let next_k = nixie_tla::lower::skolemize_infinite_existentials(&next_k);
        let invs: Vec<(String, KeraRef)> = invs
            .into_iter()
            .map(|(n, t)| {
                // The invariant enters the query negated, so its polarity
                // is inverted from the start — see the pass's doc.
                (
                    n,
                    nixie_tla::lower::skolemize_infinite_existentials_at(&t, false),
                )
            })
            .collect();
        // The binder-uniqueness invariant, asserted on every lowered root: a
        // shared binder makes two independent variables read as one — in
        // inference, in substitution, and in the encoder's `bound` map — and
        // the wrong answer it produces would look like anything except its
        // cause. (An `EmptyBag` with a fixed binder name was the first
        // instance; this check is so there is not a second.)
        for (name, root) in std::iter::once((init, &init_k))
            .chain(std::iter::once((next, &next_k)))
            .chain(invs.iter().map(|(n, t)| (n.as_str(), t)))
        {
            if let Err(why) = nixie_tla::lower::binder_uniqueness(root) {
                return Err(SetupError::Lower {
                    name: name.to_string(),
                    why,
                });
            }
        }

        // `ASSUME` is not decoration: a TLA+ specification is only claimed to
        // hold under its assumptions, and they are usually the only thing
        // pinning down a `CONSTANT`. Dropping them leaves every constant
        // completely arbitrary, which turns "this invariant holds for the
        // intended parameters" into "this invariant holds for *every* value
        // of N" — a strictly harder claim that fails on specifications that
        // are perfectly correct. The resulting `Violation` would be a real
        // model of the encoded formula and a false alarm about the spec.
        let mut assumptions: Vec<(String, KeraRef)> = Vec::new();
        for name in constraints {
            let body = lower_one(&mut low, module, name)?;
            assumptions.push((name.to_string(), body));
        }
        // `CONSTRAINT C` bounds the state space TLC explores. Asserting it in
        // every state is the bounded-model-checking reading, and it is the
        // *strengthening* direction — a search that ignores it explores states
        // the author excluded and can report a counterexample outside the
        // intended model.
        let mut state_constraints = Vec::new();
        for name in &config.state_constraints {
            let t = lower_one(&mut low, module, name)?;
            state_constraints.push(nixie_tla::lower::skolemize_infinite_existentials(&t));
        }
        let mut action_constraints = Vec::new();
        for name in &config.action_constraints {
            let t = lower_one(&mut low, module, name)?;
            action_constraints.push(nixie_tla::lower::skolemize_infinite_existentials(&t));
        }
        for (i, unit) in module.units.iter().enumerate() {
            if let UnitKind::Assume { body, .. } = &unit.kind {
                // An assumption that will not lower is skipped rather than
                // fatal — but it is skipped *loudly*, by weakening nothing:
                // see `dropped_assumptions`.
                match low.lower(body) {
                    Ok(k) => assumptions.push((format!("ASSUME #{i}"), k)),
                    Err(_) => dropped += 1,
                }
            }
        }

        let mut assertable: Vec<KeraRef> = Vec::new();
        for (label, a) in &assumptions {
            match nixie_tla::Evaluator::new().eval(a) {
                Ok(nixie_tla::Value::Bool(true)) => {}
                Ok(nixie_tla::Value::Bool(false)) => {
                    return Err(SetupError::AssumptionViolated {
                        name: label.clone(),
                    });
                }
                Ok(_) | Err(_) => assertable.push(Rc::clone(a)),
            }
        }

        // One inference over all three, so a state variable has one type
        // across the whole specification rather than three unrelated ones.
        let mut inf = Inference::new();
        // `@type:` annotations seed it first: they are the author's claim
        // about a name's shape, and everything derived later is *checked
        // against* them — a conflict is the type error it is (exit 120),
        // never a silent override. Only names the roles' formulas could
        // reach matter, but seeding every annotation of the loaded modules
        // is harmless (unification is lazy about unused names) and catches
        // contradictory annotations the way Apalache does.
        let mut uninterpreted: std::collections::HashMap<String, nixie_tla::types::TyId> =
            std::collections::HashMap::new();
        // Operator signatures are **checked**, not seeded: an application
        // has no kernel node to constrain (the body is inlined), so the
        // check is the operator's own body against the signature — the
        // parameters assumed at their annotated types, the result unified.
        // A signature that names no operator, or one of the wrong arity,
        // is a defect in the specification and is reported as such.
        let mut signatures: Vec<(
            &nixie_tla_syntax::module::Annotation,
            nixie_tla::annotations::ParsedSignature,
        )> = Vec::new();
        for ann in &spec.annotations {
            let parsed = match nixie_tla::annotations::parse_type1(&ann.text) {
                Ok(p) => p,
                Err(nixie_tla::annotations::AnnotationError::Unsupported { what }) => {
                    // An operator signature, or another construct this
                    // checker has no type for. A signature is parsed and
                    // checked below; anything else unsupported is an error:
                    // silently ignoring an annotation the author wrote is
                    // the silent-gap pattern.
                    if what.contains("signature") {
                        let sig = nixie_tla::annotations::parse_signature1(&ann.text)
                            .map_err(|e| {
                                SetupError::Types(format!(
                                    "the @type: annotation on `{}` does not parse: {e}",
                                    ann.name
                                ))
                            })?
                            .ok_or_else(|| {
                                SetupError::Types(format!(
                                    "the @type: annotation on `{}` was read as {what} but does \
                                 not parse as one",
                                    ann.name
                                ))
                            })?;
                        signatures.push((ann, sig));
                        continue;
                    }
                    return Err(SetupError::Types(format!(
                        "the @type: annotation on `{}` uses {what}, which this checker has no \
                         type for yet",
                        ann.name
                    )));
                }
                Err(e) => {
                    return Err(SetupError::Types(format!(
                        "the @type: annotation on `{}` does not parse: {e}",
                        ann.name
                    )));
                }
            };
            if let Err(e) =
                nixie_tla::annotations::assume(&mut inf, &ann.name, &parsed, &mut uninterpreted)
            {
                return Err(SetupError::Types(format!(
                    "the @type: annotation on `{}` conflicts: {e}",
                    ann.name
                )));
            }
        }
        // Check each operator signature against its operator's body, in a
        // throwaway lowerer and inference so nothing this reads lands in
        // the real caches (the same discipline the `.cfg` probe uses).
        for (ann, sig) in &signatures {
            // The anchor the attach pass chose is the *definition* this
            // signature belongs to — a module-level operator or a `LET`
            // definition inside a body, whichever the comment precedes.
            let Some((params, body)) =
                nixie_tla_syntax::module::operator_at(module, ann.decl_offset)
            else {
                // The annotated operator is not one this module defines —
                // an `INSTANCE` member substituted by `WITH`, annotated in
                // the module it came from. This checker cannot see that
                // body, so the signature is neither checked nor failed:
                // said out loud, the same way an uncheckable construct is
                // named everywhere else.
                eprintln!(
                    "note: the operator-signature annotation on `{}` is on an operator not \
                     defined in this module; it is not checked",
                    ann.name
                );
                continue;
            };
            let name = &ann.name;
            if params.len() != sig.params.len() {
                return Err(SetupError::Types(format!(
                    "the operator-signature annotation on `{name}` takes {} parameter(s) but \
                     the operator takes {}",
                    sig.params.len(),
                    params.len()
                )));
            }
            let mut probe = Lowerer::new();
            probe.add_spec(spec);
            let Ok(body_k) = probe.lower(body) else {
                // The body that does not lower fails loudly in its own
                // right when the roles reach it; a signature cannot add a
                // verdict here, and declining the check is not that.
                continue;
            };
            let mut check = nixie_tla::types::Inference::new();
            let mut vars: std::collections::HashMap<String, nixie_tla::types::TyId> =
                std::collections::HashMap::new();
            // `TyId`s are local to one inference's arena, so the
            // uninterpreted-name table is per check: an id minted by the
            // previous operator's check would denote an unrelated type
            // here, and the mismatch it produced looked like the
            // annotation's fault. (Cross-spec identity of uninterpreted
            // names is the main inference's business, not this probe's.)
            let mut check_uninterpreted: std::collections::HashMap<String, nixie_tla::types::TyId> =
                std::collections::HashMap::new();
            for (p, ty) in params.iter().zip(sig.params.iter()) {
                let tid = nixie_tla::annotations::intern_for_check(
                    &mut check,
                    ty,
                    &mut vars,
                    &mut check_uninterpreted,
                )
                .map_err(|e| {
                    SetupError::Types(format!(
                        "the operator-signature annotation on `{name}` does not check: {e}"
                    ))
                })?;
                check.assume(&p.name.name, tid).map_err(|e| {
                    SetupError::Types(format!(
                        "the operator-signature annotation on `{name}` does not check: {e}"
                    ))
                })?;
            }
            let got = check.infer(&body_k).map_err(|e| {
                SetupError::Types(format!(
                    "the operator-signature annotation on `{name}` does not check against its \
                 body: {e}"
                ))
            })?;
            let want = nixie_tla::annotations::intern_for_check(
                &mut check,
                &sig.result,
                &mut vars,
                &mut check_uninterpreted,
            )
            .map_err(|e| {
                SetupError::Types(format!(
                    "the operator-signature annotation on `{name}` does not check: {e}"
                ))
            })?;
            check.unify(got, want).map_err(|e| {
                SetupError::Types(format!(
                    "the operator-signature annotation on `{name}` does not match its body: {e}"
                ))
            })?;
        }

        // A fully ground assumption is **evaluated**, not asserted: it has
        // only one value, and asking the solver what that value is would be
        // asking a question already answered. One that is FALSE means the
        // specification has no behaviours at all — TLC and Apalache report
        // that and stop, and so does this, by name. One that is TRUE needs
        // no constraint at all. An assumption the evaluator cannot decide
        // (usually because it still mentions a symbolic `CONSTANT`) falls
        // through to be asserted for the solver to reason about.
        //
        // The evaluation is on the lowered term, which is to say the
        // **substituted** constants: a `.cfg` pinning `N = 3` has already
        // replaced `N` by the time it reaches here, so `ASSUME N \in
        // Nat \ {0}` is checked as `3 \in Nat \ {0}`, not with `N` free.

        for t in [&init_k, &next_k]
            .into_iter()
            .chain(invs.iter().map(|(_, t)| t))
            .chain(state_constraints.iter())
            .chain(action_constraints.iter())
        {
            inf.infer(t).map_err(|e| SetupError::Types(e.to_string()))?;
        }
        // `Init`, `Next` and the invariant must be **Boolean**. TLA+'s level
        // rules above do not catch this: `Inv == (100 - 10) + 5` is a
        // perfectly good constant-level expression and a perfectly useless
        // invariant. Negating a non-Boolean and finding the result satisfiable
        // would report a `Violation` for a specification that never stated a
        // property at all — answering a question nobody asked, which is the
        // same failure `SetupError::Level` exists to prevent.
        //
        // `intent`'s compiler emits exactly this shape when a `.intent` file
        // gives an invariant an arithmetic body, which is how the check came
        // to be written: the trace replay caught the invariant evaluating to
        // `95`, and refusing it up front is where that belongs.
        for (name, term) in std::iter::once((init, &init_k))
            .chain(std::iter::once((next, &next_k)))
            .chain(invs.iter().map(|(n, t)| (n.as_str(), t)))
        {
            let Some(id) = inf.node_ty(term) else {
                continue;
            };
            let Ok(ty) = inf.to_type(id) else {
                continue;
            };
            if ty != nixie_tla::Type::Bool {
                return Err(SetupError::Level {
                    name: name.to_string(),
                    role: "a formula",
                    found: format!("{ty}"),
                    wanted: "BOOLEAN".to_string(),
                });
            }
        }
        // Names reachable from the specification proper. These *must* get a
        // sort: a checker that quietly skipped one would be checking a
        // different specification. Names that only an assumption mentions are
        // not in this set, and are allowed to go unsorted — see below.
        let required: std::collections::HashSet<String> =
            inf.free_names().map(|(n, _)| n.to_string()).collect();
        // Assumptions are typed in the same environment, so a constant they
        // mention gets one type across the whole specification. An assumption
        // that does not type check is dropped rather than failing the setup:
        // it is extra information, and losing it can only make the search
        // report more, never less.
        let mut typed_assumptions = Vec::new();
        for a in assertable {
            if inf.infer(&a).is_ok() {
                typed_assumptions.push(a);
            } else {
                dropped += 1;
            }
        }

        let state = all_state_variables(spec);
        // Native sets, not the arena. A set-valued **state variable** has no
        // statically knowable candidate list — `s@1` holds whatever the
        // transition relation puts there — so the arena cannot represent one
        // at all. The solver's finite-set sort can, which is the whole reason
        // the theory was built.
        let mut encoder = Encoder::new().with_set_encoding(SetEncoding::Native);
        let mut names: Vec<(String, nixie_tla::TyId)> = inf
            .free_names()
            .map(|(n, id)| (n.to_string(), id))
            .collect();
        // Sorted, because `free_names` comes off a `HashMap` and its order
        // varies from process to process. Declaration order decides the order
        // sorts and SMT variables are interned, so an unsorted walk makes
        // every `SortId` and `TermId` in the problem depend on the run — and a
        // corpus measurement that is not reproducible is not a measurement.
        names.sort();
        for (name, id) in names {
            let ty = inf
                .to_type(id)
                .map_err(|e| SetupError::Types(e.to_string()))?;
            let sort = match sort_of(&ty, tm) {
                Ok(s) => s,
                // A constant that only an assumption mentions may go
                // undeclared: the assumption that needs it then fails to
                // encode and is dropped and counted, which weakens the search
                // rather than aborting it. A name the specification itself
                // uses gets no such latitude.
                Err(_) if !required.contains(&name) => continue,
                Err(_) => {
                    return Err(SetupError::NoSort {
                        name: name.clone(),
                        ty: ty.to_string(),
                    });
                }
            };
            if state.iter().any(|v| v == &name) {
                encoder.declare_state(name, sort);
            } else {
                encoder.declare(name, sort);
            }
        }

        // Hand the encoder the sort of every node whose term cannot sort
        // itself. `{}` is the case that matters: an empty set literal has no
        // element to take an element sort from, and an empty set at the wrong
        // element sort is a different value — so it is supplied, not guessed.
        let mut nodes: Vec<KeraRef> = Vec::new();
        for root in [&init_k, &next_k]
            .into_iter()
            .chain(invs.iter().map(|(_, t)| t))
            .chain(typed_assumptions.iter())
            .chain(state_constraints.iter())
            .chain(action_constraints.iter())
        {
            collect_unsortable(root, &mut nodes);
        }
        for node in nodes {
            if let Some(id) = inf.node_ty(&node)
                && let Ok(ty) = inf.to_type(id)
                && let Ok(sort) = sort_of(&ty, tm)
            {
                encoder.declare_node_sort(&node, sort);
            }
        }

        Ok(Self {
            assumptions: typed_assumptions,
            dropped_setup: dropped,
            dropped_assumptions: dropped,
            init: init_k,
            next: next_k,
            invs,
            encoder,
            state_constraints,
            action_constraints,
            unapplied_config: unapplied,
            conflict_limit: None,
            counterexample: None,
            verification: None,
            check_deadlocks: true,
            deadlock_step: None,
            action_invariant_names: roles
                .inv
                .iter()
                .filter(|inv| invariant_kind(&levels, inv) == InvariantKind::Action)
                .map(|inv| (*inv).to_string())
                .collect(),
            blocked: Vec::new(),
            violated_invariants: Vec::new(),
        })
    }

    /// Search for a counterexample of at most `depth` steps.
    ///
    /// # Errors
    ///
    /// Returns a [`SetupError::Encode`] if a formula has no encoding. An
    /// encoding failure is *not* folded into [`Outcome::Unknown`], because
    /// "the solver could not decide" and "we never asked it" are different
    /// facts and only one of them is about the specification.
    pub fn check(
        &mut self,
        depth: u32,
        tm: &mut TermManager,
    ) -> core::result::Result<Outcome, SetupError> {
        let named = |name: &str, e: &EncodeError| SetupError::Encode {
            name: name.to_string(),
            why: e.to_string(),
        };

        // Encoded once: the terms are hash-consed, so re-encoding the same
        // step yields the same `TermId` and the solver sees one formula.
        // Assumptions are constant-level, so one encoding at step 0 serves
        // every step of the unrolling.
        let mut assumed = Vec::new();
        let mut dropped_now = self.dropped_setup;
        for a in &self.assumptions {
            match self.encoder.encode_at(a, 0, tm) {
                Ok(t) => assumed.push(t),
                // An assumption with no encoding is dropped, not approximated.
                // Dropping one only *weakens* what is assumed, so the search
                // explores a superset of the intended states: it can produce a
                // spurious counterexample, never hide a real one — which is
                // why a later `Sat` under drops is reported `Unknown`.
                Err(e) => {
                    if std::env::var_os("NIXIE_TLA_DEBUG_DROPS").is_some() {
                        eprintln!("[dropped assumption] {e}");
                    }
                    dropped_now += 1;
                }
            }
        }
        // Recomputed from `dropped_setup` every call, so a caller that checks
        // repeatedly (the `--max-error` loop) does not count one dropped
        // assumption per query.
        self.dropped_assumptions = dropped_now;

        // The assumptions on their own decide whether the specification has
        // any behaviours. A contradictory assumption set makes every deeper
        // query `Unsat` — indistinguishable from a passing specification —
        // so it is answered here, once, by name. `Sat` and `Unknown` both
        // fall through: an assumption set the solver cannot decide is not
        // evidence of emptiness.
        if !assumed.is_empty() {
            let mut probe = Solver::new();
            if let Some(limit) = self.conflict_limit {
                probe.set_conflict_limit(limit);
            }
            for a in &assumed {
                probe.assert(*a, tm);
            }
            for c in self.encoder.side_constraints().to_vec() {
                probe.assert(c, tm);
            }
            if probe.check(tm) == SolverResult::Unsat {
                return Ok(Outcome::AssumptionsUnsatisfiable);
            }
        }

        let init = self
            .encoder
            .encode_at(&self.init, 0, tm)
            .map_err(|e| named("Init", &e))?;
        // One extra transition when there are action invariants: they are
        // checked over the pair `(s_j, s_{j+1})`, so the last one needs
        // `Next@depth`, which the state-invariant queries never assert.
        let unroll_to = if self.action_invariant_names.is_empty() {
            depth
        } else {
            depth.saturating_add(1)
        };
        let mut transitions = Vec::new();
        for i in 0..unroll_to {
            let t = self
                .encoder
                .encode_at(&self.next, i, tm)
                .map_err(|e| named("Next", &e))?;
            transitions.push(t);
        }

        // **One solver for the whole unrolling.** `Init` and `Trans_k`
        // persist; each depth's `~Inv_j` is asserted under `push`/`pop`, so
        // the query is exactly the formula the fresh-solver path asked — but
        // everything the search *learned* at depth j serves depth j+1, which
        // the fresh path threw away. That is Apalache's incremental context
        // (`IncrementalExecutionContext`) and it is what the corpus's
        // "solver undecided" bucket was paying for: nine-plus specifications
        // re-derived the same reachability at every depth and exhausted the
        // budget on the second pass.
        //
        // What sits **inside** the push is only the negated invariant (and
        // the blocked-trace clauses): everything outside — assumptions,
        // `Init`, the transitions, the `.cfg` constraints, the definitional
        // side constraints — is a fact about the specification, not about
        // the query, and stays asserted for every later depth.
        let mut solver = Solver::new();
        // A **deterministic** budget per query, not a wall-clock timeout.
        // Some specifications now reach the solver with hundreds of set
        // and datatype terms and do not finish in any useful time; a
        // corpus harness that hangs is not a measurement. A clock would
        // bound it too, and would make the verdict depend on machine load
        // — the corpus numbers stopped being reproducible the moment they
        // did. Conflicts are counted by the solver itself, so the same
        // input gives the same answer on any machine, and running out
        // reports `Unknown` like any other undecided query.
        if let Some(limit) = self.conflict_limit {
            solver.set_conflict_limit(limit);
        }
        for a in &assumed {
            solver.assert(*a, tm);
        }
        solver.assert(init, tm);
        // How many of the encoder's definitional side constraints have been
        // asserted already: encoding step j can introduce new ones (a
        // recursive function reached at that step), and facts are asserted
        // once, outside the push.
        let mut side_sent = 0usize;
        for c in self.encoder.side_constraints().to_vec() {
            solver.assert(c, tm);
            side_sent += 1;
        }

        for j in 0..=depth {
            if j > 0 {
                solver.assert(transitions[(j - 1) as usize], tm);
            }
            // A `CONSTRAINT` holds in every state of the trace, including the
            // one being tested, and an `ACTION_CONSTRAINT` over every step
            // taken. Both *narrow* the search to the model the author
            // configured. A constraint with no encoding is refused rather than
            // dropped: unlike an `ASSUME`, dropping one here would widen the
            // search past the configured model, which is the direction that
            // manufactures counterexamples — and it would do so invisibly,
            // because nothing else records that the model was bounded.
            for c in &self.state_constraints {
                let step = j;
                let t = self
                    .encoder
                    .encode_at(c, step, tm)
                    .map_err(|e| named("CONSTRAINT", &e))?;
                solver.assert(t, tm);
            }
            for c in &self.action_constraints {
                let step = j.saturating_sub(1);
                let t = self
                    .encoder
                    .encode_at(c, step, tm)
                    .map_err(|e| named("ACTION_CONSTRAINT", &e))?;
                solver.assert(t, tm);
            }
            // New definitional facts since the last depth.
            let sides = self.encoder.side_constraints().to_vec();
            while side_sent < sides.len() {
                solver.assert(sides[side_sent], tm);
                side_sent += 1;
            }

            // `--inv=A,B` is conjunctive over the invariants, so the
            // counterexample condition is the disjunction of their negations.
            // One query, not one per invariant: the shortest counterexample
            // against *any* of them is what a bounded search must find first,
            // and which one it broke is read back afterwards, from the trace.
            // The state-invariant query. Action-level names are NOT part of
            // it: their `j+1` half would be unconstrained here (the step's
            // transition is not asserted for this query), and a free `s_{j+1}`
            // satisfies any negated action invariant — a counterexample the
            // specification cannot produce. They get their own query below,
            // with the transition asserted.
            let state_invs: Vec<&(String, KeraRef)> = self
                .invs
                .iter()
                .filter(|(n, _)| !self.action_invariant_names.contains(n))
                .collect();
            let mut negated = Vec::with_capacity(state_invs.len());
            for (name, inv) in &state_invs {
                let t = self
                    .encoder
                    .encode_at(inv, j, tm)
                    .map_err(|e| named(name, &e))?;
                negated.push(tm.mk_not(t));
            }
            // Encoding this depth's invariant can itself introduce facts —
            // a `CHOOSE x : x \\notin S` mints its non-membership here —
            // so drain again, before the query is asked rather than at the
            // next depth: one depth late is a different formula.
            let sides = self.encoder.side_constraints().to_vec();
            while side_sent < sides.len() {
                solver.assert(sides[side_sent], tm);
                side_sent += 1;
            }

            if !negated.is_empty() {
                let violated = if negated.len() == 1 {
                    negated[0]
                } else {
                    tm.mk_or(negated)
                };
                solver.push();
                solver.assert(violated, tm);
                for c in &self.blocked {
                    solver.assert(*c, tm);
                }
                let answer = solver.check(tm);
                if answer != SolverResult::Sat {
                    // Pop before any early return: an abandoned scope would leak
                    // its assertions into the *next* `check` call on this `Bmc`
                    // (the `--max-error` loop reuses it), answering a different
                    // question than the one asked.
                    solver.pop();
                }
                match answer {
                    SolverResult::Sat => {
                        // A `Sat` answer is a counterexample **candidate**. It is
                        // only a counterexample once it has been read back as
                        // TLA+ values and replayed by `nixie-tla`'s evaluator —
                        // the independent implementation of TLA+ that
                        // `bench/tla_eval` checks against TLC. Until both succeed
                        // the honest verdict is [`Outcome::Unknown`], never
                        // [`Outcome::Violation`]: exit 12 is what users and tools
                        // act on, and an undecodable or non-replaying trace is
                        // not evidence of a violation. It is evidence that the
                        // pipeline disagrees with itself somewhere — lowering,
                        // encoding or the solver — and every such disagreement
                        // stays visible in [`Bmc::verification`] so it gets
                        // chased rather than explained away.
                        //
                        // The model is read before the pop; the trace extraction
                        // walks it, and a popped scope's model is not one to
                        // read.
                        let (trace, verdict) = match solver.model() {
                            None => (
                                None,
                                Verification::NotDecoded(
                                    "the solver produced no model".to_string(),
                                ),
                            ),
                            Some(model) => match self.extract(model, j, tm) {
                                Err(why) => (None, Verification::NotDecoded(why)),
                                Ok(t) => match self.replay(&t) {
                                    Err(why) => (Some(t), Verification::NotReplayed(why)),
                                    Ok(()) => (Some(t), Verification::Replayed),
                                },
                            },
                        };
                        solver.pop();
                        self.counterexample = trace;
                        self.verification = Some(verdict.clone());
                        // A search that ran with dropped assumptions is a search
                        // over a **superset** of the intended states. A `Sat`
                        // there may be an artefact of exactly the widening, so it
                        // is `Unknown` and says why — the count is what a caller
                        // needs in order to decide whether to trust it.
                        if self.dropped_assumptions > 0 {
                            return Ok(Outcome::Unknown(format!(
                                "a counterexample was found, but {} assumption(s) \
                             could not be encoded, so the search ran over more \
                             states than the specification allows and the trace \
                             may be an artefact",
                                self.dropped_assumptions
                            )));
                        }
                        return match &verdict {
                            Verification::Replayed => Ok(Outcome::Violation { step: j }),
                            Verification::NotDecoded(why) => Ok(Outcome::Unknown(format!(
                                "a counterexample was found but could not be read \
                             back as TLA+ values: {why}"
                            ))),
                            Verification::NotReplayed(why) => Ok(Outcome::Unknown(format!(
                                "a counterexample was read back but does not replay \
                             — the encoding and the evaluator disagree: {why}"
                            ))),
                        };
                    }
                    SolverResult::Unsat => {}
                    SolverResult::Unknown => {
                        return Ok(Outcome::Unknown(format!(
                            "the solver could not decide the {j}-step query"
                        )));
                    }
                }
            } // state-invariant query

            // ---- the action-invariant query, at this step ----
            //
            // Over the executed pair `(s_j, s_{j+1})`: the transition is
            // asserted, so the invariant's primed half reads a state that
            // really follows — no free `s_{j+1}` can satisfy its negation.
            if !self.action_invariant_names.is_empty() {
                // The step's own transition, asserted persistently for the
                // rest of the unrolling (it is a fact about step j+1's
                // reachability, not about this query).
                if j < transitions.len() as u32 {
                    solver.assert(transitions[j as usize], tm);
                }
                let action_invs: Vec<&(String, KeraRef)> = self
                    .invs
                    .iter()
                    .filter(|(n, _)| self.action_invariant_names.contains(n))
                    .collect();
                let mut negated = Vec::with_capacity(action_invs.len());
                for (name, inv) in &action_invs {
                    let t = self
                        .encoder
                        .encode_at(inv, j, tm)
                        .map_err(|e| named(name, &e))?;
                    negated.push(tm.mk_not(t));
                }
                let violated = if negated.len() == 1 {
                    negated[0]
                } else {
                    tm.mk_or(negated)
                };
                solver.push();
                solver.assert(violated, tm);
                for c in &self.blocked {
                    solver.assert(*c, tm);
                }
                let answer = solver.check(tm);
                if answer != SolverResult::Sat {
                    solver.pop();
                }
                match answer {
                    SolverResult::Sat => {
                        // The same read-back-and-replay gate as a state
                        // violation: the trace has `j + 2` states, and the
                        // action invariants replay over its last pair.
                        let (trace, verdict) = match solver.model() {
                            None => (
                                None,
                                Verification::NotDecoded(
                                    "the solver produced no model".to_string(),
                                ),
                            ),
                            Some(model) => match self.extract(model, j.saturating_add(1), tm) {
                                Err(why) => (None, Verification::NotDecoded(why)),
                                Ok(t) => match self.replay(&t) {
                                    Err(why) => (Some(t), Verification::NotReplayed(why)),
                                    Ok(()) => (Some(t), Verification::Replayed),
                                },
                            },
                        };
                        solver.pop();
                        self.counterexample = trace;
                        self.verification = Some(verdict.clone());
                        if self.dropped_assumptions > 0 {
                            return Ok(Outcome::Unknown(format!(
                                "a counterexample was found, but {} assumption(s) \
                                 could not be encoded, so the search ran over more \
                                 states than the specification allows and the trace \
                                 may be an artefact",
                                self.dropped_assumptions
                            )));
                        }
                        return match &verdict {
                            Verification::Replayed => Ok(Outcome::Violation {
                                step: j.saturating_add(1),
                            }),
                            Verification::NotDecoded(why) => Ok(Outcome::Unknown(format!(
                                "a counterexample was found but could not be read \
                                 back as TLA+ values: {why}"
                            ))),
                            Verification::NotReplayed(why) => Ok(Outcome::Unknown(format!(
                                "a counterexample was read back but does not replay \
                                 — the encoding and the evaluator disagree: {why}"
                            ))),
                        };
                    }
                    SolverResult::Unsat => {}
                    SolverResult::Unknown => {
                        return Ok(Outcome::Unknown(format!(
                            "the solver could not decide the {j}-step action-invariant query"
                        )));
                    }
                }
            }
        }

        // ---- the deadlock question, as a post-pass ----
        //
        // Asked per step, but **after** the whole invariant sweep. Apalache
        // interleaves the two per step (their `SeqModelChecker`), and the
        // difference in *reporting order* is documented here deliberately:
        // running the deadlock probes between the invariant queries perturbs
        // the CDCL trajectory (clauses learned in a probe scope are popped,
        // but the activity state legitimately persists), and on exactly the
        // expensive specifications that trajectory decides whether the
        // model-refutation loop converges at all — the PlusCal two-array
        // corpus pin answered `Unknown` at depth 8 with interleaving and
        // checks clean without. Verdict identity for the invariants is the
        // acceptance criterion, so the deadlock queries run against an
        // unmodified invariant trajectory, at the cost of a violation at
        // depth 5 outranking a deadlock at depth 2 in the report. The scan
        // itself still runs at every step `j < depth`: the bound's last
        // state has no encoded successor, and "no transition leaves the last
        // state of the unrolling" is a statement about the *bound*, not the
        // specification.
        if self.check_deadlocks {
            // Its own incremental solver, built step by step: the probe at
            // step `j` must see exactly the prefix through `j` transitions,
            // and the invariant sweep's solver has already asserted them
            // all. Asserting the same hash-consed terms again is cheap; the
            // learning this pass loses is the price of never letting a
            // probe perturb an invariant query's trajectory (see the note
            // above — that perturbation was measurable, not theoretical).
            let mut dl_solver = Solver::new();
            if let Some(limit) = self.conflict_limit {
                dl_solver.set_conflict_limit(limit);
            }
            for a in &assumed {
                dl_solver.assert(*a, tm);
            }
            dl_solver.assert(init, tm);
            for c in self.encoder.side_constraints().to_vec() {
                dl_solver.assert(c, tm);
            }
            for c in &self.state_constraints {
                // The constraints hold in every state; the pass reaches
                // every state the prefix defines.
                for step in 0..depth {
                    if let Ok(t) = self.encoder.encode_at(c, step, tm) {
                        dl_solver.assert(t, tm);
                    }
                }
            }
            for j in 0..depth {
                if j > 0 {
                    dl_solver.assert(transitions[(j - 1) as usize], tm);
                }
                match self.find_deadlock(&mut dl_solver, j, tm) {
                    DeadlockSearch::None => {}
                    DeadlockSearch::Found(step) => {
                        self.deadlock_step = Some(step);
                        return Ok(Outcome::Deadlock { step });
                    }
                    DeadlockSearch::Unknown(why) => return Ok(Outcome::Unknown(why)),
                }
            }
        }

        // With deadlock checking off, "no violation" is only the whole answer
        // when behaviours of the full length exist: a specification whose
        // every behaviour stops short is not error-free, it is *short*, and
        // saying "no error" would misread a bound past the specification's
        // lifetime. Apalache's outcome name and exit code (0) are used as
        // they are; the message carries the distinction.
        if !self.check_deadlocks {
            solver.push();
            let answer = solver.check(tm);
            solver.pop();
            match answer {
                // The prefix through `depth` transitions is satisfiable:
                // some behaviour ran the full length.
                SolverResult::Sat => {}
                SolverResult::Unsat => return Ok(Outcome::ExecutionsTooShort),
                SolverResult::Unknown => {
                    return Ok(Outcome::Unknown(
                        "the solver could not decide whether any behaviour \\
                         reaches the full length"
                            .into(),
                    ));
                }
            }
        }
        Ok(Outcome::NoViolationWithin(depth))
    }

    /// Whether the search looks for deadlocks; see [`Outcome::Deadlock`].
    ///
    /// Apalache's default is on; `--no-deadlock` (and the `.cfg`'s
    /// `CHECK_DEADLOCK FALSE`) turn it off.
    pub fn set_check_deadlocks(&mut self, on: bool) {
        self.check_deadlocks = on;
    }

    /// The step of the last reported [`Outcome::Deadlock`].
    #[must_use]
    pub fn deadlock_step(&self) -> Option<u32> {
        self.deadlock_step
    }

    /// The step-j deadlock question, against the persistent solver.
    ///
    /// Assumes the prefix through `j` transitions is already asserted at
    /// the base scope. Two queries, and both of them cheap:
    ///
    /// 1. `prefix_j /\ Next@j` — if **sat**, some reachable state at this
    ///    step has a successor, and the answer is *not a deadlock*;
    /// 2. if **unsat**, `prefix_j` alone — if still sat, a reachable state
    ///    exists and *none* of them has a successor: a deadlock, and the
    ///    no-successor half is a proof.
    ///
    /// This is the *all-states* reading, and it is a deliberate granularity
    /// choice, not an oversight: the some-state reading ("one reachable
    /// state is stuck while others continue") needs the state-blocking
    /// loop, which costs one `Sat` query with a model readback per
    /// successor-having state — hundreds of rounds on exactly the
    /// specifications that are already expensive. Apalache's symbolic mode
    /// has the same limitation, documented as their issue 712 ("may miss a
    /// deadlock"), and `Deadlock712.tla` is the corpus pin for it. A
    /// partial deadlock that this reading misses cannot become a *false*
    /// verdict: it only leaves the search reporting `NoViolationWithin`,
    /// the same under-approximation Apalache ships.
    fn find_deadlock(
        &mut self,
        solver: &mut Solver,
        j: u32,
        tm: &mut TermManager,
    ) -> DeadlockSearch {
        // `Next` at step j, hash-consed with the unrolling's own term.
        let next_j = match self.encoder.encode_at(&self.next, j, tm) {
            Ok(t) => t,
            Err(_) => {
                return DeadlockSearch::Unknown(
                    "the deadlock query could not encode the next-state action".into(),
                );
            }
        };
        solver.push();
        solver.assert(next_j, tm);
        let with_successor = solver.check(tm);
        solver.pop();
        match with_successor {
            SolverResult::Sat => DeadlockSearch::None,
            SolverResult::Unsat => {
                // Nothing at this step moves. Does anything at this step
                // *exist*? Only then is it a deadlock.
                solver.push();
                let reachable = solver.check(tm);
                solver.pop();
                match reachable {
                    SolverResult::Sat => DeadlockSearch::Found(j),
                    SolverResult::Unsat => DeadlockSearch::None,
                    SolverResult::Unknown => DeadlockSearch::Unknown(format!(
                        "the solver could not decide whether a reachable state remains at step {j}"
                    )),
                }
            }
            SolverResult::Unknown => DeadlockSearch::Unknown(format!(
                "the solver could not decide the {j}-step successor query"
            )),
        }
    }

    /// The counterexample behind the last [`Outcome::Violation`].
    ///
    /// Present when the model could be read back, whether or not it replayed;
    /// [`Bmc::verification`] says which.
    #[must_use]
    pub fn counterexample(&self) -> Option<&Trace> {
        self.counterexample.as_ref()
    }

    /// Rule out the last counterexample, so the next check finds a different
    /// one.
    ///
    /// This is what `--max-error=N` needs: a bounded query has one shortest
    /// counterexample, and asking again without saying "not that one" returns
    /// it again forever.
    ///
    /// Returns `false` when the trace could not be expressed as a constraint
    /// at all, which is a signal to **stop** rather than loop: asking again
    /// would hand back the same states.
    ///
    /// # What a partial block means
    ///
    /// A state may contain values with no term form — a set or a function,
    /// whose value lives in the query's membership and `select` terms rather
    /// than in anything [`crate::trace::encode_value`] can rebuild. Those
    /// conjuncts are left out, which makes the clause *stronger* and rules out
    /// more than the one trace. That is a loss of completeness and not of
    /// soundness: every counterexample still reported is still a real model of
    /// the encoded formula, and is still replayed before it is reported. The
    /// alternative — dropping the block and asking again — returns the same
    /// trace and never terminates.
    pub fn block_counterexample(&mut self, tm: &mut TermManager) -> bool {
        let Some(trace) = self.counterexample.as_ref() else {
            return false;
        };
        let mut conj: Vec<TermId> = Vec::new();
        for (step, state) in trace.states.iter().enumerate() {
            let Ok(step) = u32::try_from(step) else {
                return false;
            };
            for (name, value) in state {
                let Some(t) = self.encoder.var_at(name, step) else {
                    continue;
                };
                let Some(sort) = tm.get(t).map(|d| d.sort) else {
                    continue;
                };
                if let Some(v) = crate::trace::encode_value(value, sort, tm) {
                    let eq = tm.mk_eq(t, v);
                    conj.push(eq);
                }
            }
        }
        if conj.is_empty() {
            return false;
        }
        let same = tm.mk_and(conj);
        let clause = tm.mk_not(same);
        self.blocked.push(clause);
        true
    }

    /// The last counterexample as an **ITF** trace object (Apalache's
    /// ADR-015 JSON counterexample format).
    ///
    /// This is the form downstream tools read: `itf-rs`, the VSCode trace
    /// viewer, and `tla-connect`'s model-based testing, which collects
    /// `*.itf.json` from a checker and replays each trace against a `Driver`.
    ///
    /// `source` names the specification, for the trace's `#meta`.
    ///
    /// The `VARIABLE`s become ITF `vars` and the `CONSTANT`s become `params`,
    /// which is the distinction ADR-015 draws and the one the encoder already
    /// keeps: a variable has an SMT term per step, a constant has one for the
    /// whole unrolling.
    #[must_use]
    pub fn counterexample_itf(&self, source: &str) -> Option<serde_json::Value> {
        let trace = self.counterexample.as_ref()?;
        let mut vars: Vec<String> = self
            .encoder
            .state_names()
            .map(std::string::ToString::to_string)
            .collect();
        let mut params: Vec<String> = self
            .encoder
            .declared_names()
            .filter(|n| !self.encoder.state_names().any(|s| s == *n))
            .map(std::string::ToString::to_string)
            .collect();
        // Sorted so two runs over the same specification produce the same
        // file, byte for byte. A trace that shuffles its own field order is
        // useless to diff and useless to check in.
        vars.sort();
        params.sort();
        Some(crate::itf::to_itf(
            trace,
            &vars,
            &params,
            &crate::itf::Meta {
                description: "Generated by Nixie".to_string(),
                source: source.to_string(),
                violated: self.violated_invariants.clone(),
            },
        ))
    }

    /// Whether the last counterexample was confirmed independently.
    #[must_use]
    pub fn verification(&self) -> Option<&Verification> {
        self.verification.as_ref()
    }

    /// Which named invariants the last counterexample broke.
    ///
    /// Empty until a replayed counterexample exists. A caller printing a
    /// report or writing `#meta` puts these names on it: with several
    /// invariants, "exit 12" without the name is half an answer.
    #[must_use]
    pub fn violated_invariants(&self) -> &[String] {
        &self.violated_invariants
    }

    /// Read the model back as a trace.
    fn extract(
        &mut self,
        model: &nixie_solver::Model,
        steps: u32,
        tm: &mut TermManager,
    ) -> core::result::Result<Trace, String> {
        let names: Vec<String> = self
            .encoder
            .declared_names()
            .map(std::string::ToString::to_string)
            .collect();
        let mut states = Vec::with_capacity(steps as usize + 1);
        for step in 0..=steps {
            let mut st = State::new();
            for n in &names {
                // A name the encoding never needed has no term and no value.
                // That is not a hole in the trace: nothing in `Init`, `Next`
                // or the invariant mentioned it, so the replay cannot ask for
                // it either — and if it does, the replay fails loudly rather
                // than reading a value that was never constrained.
                let Some(t) = self.encoder.var_at(n, step) else {
                    continue;
                };
                let d = self.encoder.domain_at(n, step);
                let v = crate::trace::decode(t, d, model, tm)
                    .map_err(|e| format!("`{n}` in state {step}: {e}"))?;
                st.insert(n.clone(), v);
            }
            states.push(st);
        }
        Ok(Trace { states })
    }

    /// Check a trace really is a counterexample, with the evaluator.
    ///
    /// This is the independent half. The solver said the encoded formula is
    /// satisfiable; this asks `nixie-tla`'s evaluator — a completely separate
    /// implementation of TLA+, the one `bench/tla_eval` checks against TLC —
    /// whether the states it produced actually form a behaviour that breaks
    /// the invariant. Everything the verdict depends on is re-examined:
    /// lowering, because the evaluator walks the same kernel term; the
    /// encoding, because a mis-encoding yields states the evaluator rejects;
    /// and the solver, because a wrong `sat` yields states that do not satisfy
    /// `Init` or `Next`.
    ///
    /// The configuration's constraints are checked too, not only the three
    /// formulas. A `CONSTRAINT` narrows the model the author asked about, and
    /// a trace that leaves it is a counterexample to a different question.
    fn replay(&mut self, trace: &Trace) -> core::result::Result<(), String> {
        let mut ev = nixie_tla::Evaluator::new();
        let Some(first) = trace.states.first() else {
            return Err("the trace has no states".into());
        };
        let Some(last) = trace.states.last() else {
            return Err("the trace has no states".into());
        };
        let holds = |what: &str, r: nixie_tla::eval::Result<nixie_tla::Value>| match r {
            Ok(nixie_tla::Value::Bool(true)) => Ok(()),
            Ok(nixie_tla::Value::Bool(false)) => Err(format!("{what} is FALSE")),
            Ok(v) => Err(format!("{what} evaluated to {v}, which is not a Boolean")),
            Err(e) => Err(format!("{what} could not be evaluated: {e}")),
        };
        // The assumptions constrain the `CONSTANT`s, and they are checked in
        // the first state because that is where the constants are. One that
        // was *dropped* was never asserted, so it is not checked here either —
        // `dropped_assumptions` is what says the search was weakened.
        for (i, a) in self.assumptions.iter().enumerate() {
            holds(&format!("`ASSUME` #{i}"), ev.eval_state(a, first))?;
        }
        holds("`Init`", ev.eval_state(&self.init, first))?;
        for (k, pair) in trace.states.windows(2).enumerate() {
            holds(
                &format!("`Next` from state {k}"),
                ev.eval_action(&self.next, &pair[0], &pair[1]),
            )?;
        }
        for (i, c) in self.state_constraints.iter().enumerate() {
            for (k, st) in trace.states.iter().enumerate() {
                holds(
                    &format!("`CONSTRAINT` #{i} in state {k}"),
                    ev.eval_state(c, st),
                )?;
            }
        }
        for (i, c) in self.action_constraints.iter().enumerate() {
            for (k, pair) in trace.states.windows(2).enumerate() {
                holds(
                    &format!("`ACTION_CONSTRAINT` #{i} from state {k}"),
                    ev.eval_action(c, &pair[0], &pair[1]),
                )?;
            }
        }
        // And the point of the whole thing: at least one named invariant
        // must actually fail, and the ones that do are recorded by name —
        // the disjunction the search violated is an encoding detail; the
        // specification's question is *which* invariant broke.
        //
        // An **action** invariant constrains a step pair, so it is evaluated
        // over the last pair of states, not the last state — the encoder
        // reads its `'` at step `j+1`, and the replay reads the same pair.
        let mut violated = Vec::new();
        for (name, inv) in &self.invs {
            let result = if self.action_invariant_names.contains(name) {
                match trace.states.windows(2).next_back() {
                    Some([a, b]) => ev.eval_action(inv, a, b).map_err(|e| e.to_string()),
                    _ => Err("the trace has no step pair to read an action invariant over".into()),
                }
            } else {
                ev.eval_state(inv, last).map_err(|e| e.to_string())
            };
            match result {
                Ok(nixie_tla::Value::Bool(false)) => violated.push(name.clone()),
                Ok(nixie_tla::Value::Bool(true)) => {}
                Ok(v) => {
                    return Err(format!(
                        "`{name}` evaluated to {v} in the last state, which is not a Boolean"
                    ));
                }
                Err(e) => {
                    return Err(format!("`{name}` could not be evaluated: {e}"));
                }
            }
        }
        if violated.is_empty() {
            return Err("every named invariant holds in the last state".into());
        }
        self.violated_invariants = violated;
        Ok(())
    }

    /// How many `ASSUME`s were dropped because they could not be lowered,
    /// typed or encoded.
    ///
    /// **A non-zero count weakens the search.** Fewer assumptions means more
    /// states are considered reachable, so a reported [`Outcome::Violation`]
    /// may be an artefact of a constant the specification actually pins down.
    /// It is surfaced rather than logged because a caller deciding whether to
    /// trust a counterexample needs it.
    #[must_use]
    pub fn dropped_assumptions(&self) -> usize {
        self.dropped_assumptions
    }

    /// Bound each solver query to `conflicts`, deterministically.
    ///
    /// Off by default, because a bound turns a decidable query into `Unknown`
    /// and a checker should not do that unasked. A harness running a whole
    /// corpus wants one; a caller checking a single specification usually does
    /// not.
    pub fn set_conflict_limit(&mut self, conflicts: u64) {
        self.conflict_limit = Some(conflicts);
    }

    /// What the configuration said that this check did not act on.
    ///
    /// Empty is the good case. A non-empty list means the verdict is about a
    /// specification that differs from the configured one in a named way —
    /// surfaced for the same reason [`Bmc::dropped_assumptions`] is, because
    /// a caller deciding whether to trust a trace needs it.
    #[must_use]
    pub fn unapplied_config(&self) -> &[String] {
        &self.unapplied_config
    }

    /// The encoder, for inspecting the variables a counterexample mentions.
    #[must_use]
    pub fn encoder(&self) -> &Encoder {
        &self.encoder
    }
}

/// What kind of invariant a name is, by its trusted level.
///
/// State invariants are checked in each state; **action** invariants
/// (Apalache's `maybeActionInvariants`) mention `'` and constrain a step
/// pair, so they are checked over `(s_j, s_{j+1})`; **temporal** ones are a
/// different kind of question entirely (a lasso, not a state property) and
/// are refused — Apalache's own exit code for `--inv=<temporal>` is 255.
fn invariant_kind(levels: &nixie_tla_syntax::LevelReport, name: &str) -> InvariantKind {
    use nixie_tla_syntax::Level;
    match levels.trusted_level_of(name) {
        Some(Level::Constant) | Some(Level::State) | None => InvariantKind::State,
        Some(Level::Action) => InvariantKind::Action,
        Some(Level::Temporal) => InvariantKind::Temporal,
    }
}

/// The kind of one named invariant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InvariantKind {
    /// Holds or fails in a single state.
    State,
    /// Constrains a step pair `(s_j, s_{j+1})`.
    Action,
    /// A temporal property — refused for `--inv`.
    Temporal,
}

/// Lower one zero-argument definition, naming what went wrong.
fn lower_one<'a>(
    low: &mut Lowerer<'a>,
    module: &'a Module,
    name: &str,
) -> core::result::Result<KeraRef, SetupError> {
    if !has_definition(module, name) {
        return Err(SetupError::NoSuchDefinition(name.to_string()));
    }
    low.lower_named(module, name)
        .map_err(|e| SetupError::Lower {
            name: name.to_string(),
            why: e.to_string(),
        })
}

/// Every empty-set literal reachable from `root`.
///
/// Explicit stack and pointer-deduplicated: a lowered term is a shared DAG.
fn collect_unsortable(root: &KeraRef, out: &mut Vec<KeraRef>) {
    let mut seen: std::collections::HashSet<*const Kera> = std::collections::HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(t) = stack.pop() {
        if !seen.insert(std::rc::Rc::as_ptr(&t)) {
            continue;
        }
        // `{}` is the motivating case — an empty set literal has no element
        // to take a sort from. `<<…>>` is here for a different reason: a tuple
        // literal *is* a sequence in TLA+, and which of the two it encodes to
        // is a question only the inferred type can answer.
        // `{}` is the motivating case — an empty set literal has no element
        // to take a sort from. `<<…>>` is here for a different reason: a tuple
        // literal *is* a sequence in TLA+, and which of the two it encodes to
        // is a question only the inferred type can answer. A recursive
        // function is here for a third: its sort has to be known *before* its
        // body is encoded, and the body is the only thing that would otherwise
        // reveal it.
        // A `FunAsSeq` node joins them for the same reason a `CHOOSE`'s
        // empty filter does: its element sort comes from the inferred
        // `Seq(a)` of the cast, not from anything the encoding can read off
        // the function value.
        if matches!(t.as_ref(), Kera::Opaque(n, _) if n.as_str() == "FunAsSeq") {
            out.push(t.clone());
        }
        if matches!(t.as_ref(), Kera::SetEnum(xs) | Kera::Tuple(xs) if xs.is_empty())
            || matches!(
                t.as_ref(),
                Kera::Tuple(_)
                    | Kera::RecFun { .. }
                    | Kera::FunDef { .. }
                    // A `CHOOSE` whose filter came out empty has no member to
                    // take an element sort from; its own inferred type is the
                    // element type.
                    | Kera::Choose { .. }
                    | Kera::ChooseUnbounded { .. }
            )
        {
            out.push(t.clone());
        }
        stack.extend(t.as_ref().children().into_iter().cloned());
    }
}

/// Whether the module defines `name` with no parameters.
fn has_definition(module: &Module, name: &str) -> bool {
    module.units.iter().any(|u| {
        matches!(&u.kind, UnitKind::OpDef { name: n, params, .. }
            if params.is_empty() && n.name == name)
    })
}

/// The `VARIABLE`-declared names of a module.
/// The `VARIABLE`-declared names of **every** module a specification loads,
/// not only the root: `test47.tla` EXTENDS `test47a`, which is where `x` is
/// declared, and a checker that only read the root's declarations would
/// treat `x` as a rigid `CONSTANT`. That misclassification is not cosmetic:
/// `x'` encodes to the same variable as `x`, the transition becomes a
/// self-loop, `Init /\ Next` is contradictory, and the deadlock check
/// (correctly, given that formula!) reported a step-0 deadlock — the first
/// wrong verdict of the pass, found by the corpus on the day it landed.
fn all_state_variables(spec: &LoadedSpec) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for (_, module) in &spec.modules {
        for unit in &module.units {
            if let UnitKind::VariableDecl(ids) = &unit.kind {
                for id in ids {
                    if !out.iter().any(|n| n == &id.name) {
                        out.push(id.name.clone());
                    }
                }
            }
        }
    }
    out
}

/// Whether a kernel term mentions `'` anywhere.
///
/// Useful for telling an `Init` predicate from an action.
#[must_use]
pub fn mentions_prime(term: &KeraRef) -> bool {
    let mut seen: std::collections::HashSet<*const Kera> = std::collections::HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(std::rc::Rc::as_ptr(t)) {
            continue;
        }
        if matches!(t.as_ref(), Kera::Prime(_)) {
            return true;
        }
        stack.extend(t.as_ref().children());
    }
    false
}

/// A configuration constant as a kernel term.
///
/// `None` for a value with no kernel form — only
/// [`ConfigValue::ModuleQualified`], which is recorded uninterpreted by the
/// parser precisely so that this decision is explicit here rather than
/// implied by a missing match arm.
///
/// # Model values
///
/// A bare identifier is a TLC **model value**: an uninterpreted constant,
/// distinct from every other model value and from every integer, string and
/// set (*Specifying Systems* §14.5.3). It becomes a string literal under a
/// reserved prefix, which is Apalache's encoding and costs nothing here
/// because distinct string literals are already distinct values in the
/// solver — the same mechanism floating-point literals use. The prefix is what
/// keeps a model value `n1` apart from a specification that genuinely writes
/// the string `"n1"`.
fn config_value_to_kera(v: &ConfigValue) -> Option<KeraRef> {
    use std::rc::Rc;
    Some(match v {
        ConfigValue::Int(digits) => Rc::new(Kera::Int(digits.clone())),
        ConfigValue::Bool(b) => Rc::new(Kera::Bool(*b)),
        ConfigValue::Str(text) => Rc::new(Kera::Str(text.clone())),
        ConfigValue::ModelValue(name) => Rc::new(Kera::Str(format!("{MODEL_VALUE_PREFIX}{name}"))),
        ConfigValue::Set(items) => {
            let mut out = Vec::with_capacity(items.len());
            for i in items {
                out.push(config_value_to_kera(i)?);
            }
            Rc::new(Kera::SetEnum(out))
        }
        ConfigValue::ModuleQualified { .. } => return None,
    })
}

/// The prefix that keeps a model value apart from a string of the same name.
///
/// Matches Apalache's `ConfigModelValue.STR_PREFIX`, so a specification read
/// by both tools sees the same distinctions.
pub const MODEL_VALUE_PREFIX: &str = "ModelValue_";

/// The `CONSTANT`-declared names of a module.
fn constant_names(module: &Module) -> std::collections::HashSet<&str> {
    module
        .constants()
        .into_iter()
        .map(|d| d.name.name.as_str())
        .collect()
}

/// The `name = expr` conjuncts of a lowered `ConstInit`, for the constants
/// `declared` names.
///
/// Only the *top level* of the conjunction, and only a bare name on one side.
/// A constant pinned by something less direct — `Cardinality(S) = 3` — is left
/// to the solver, which is where it belongs: this is substitution, and there
/// is nothing to substitute.
fn ground_bindings(
    body: &KeraRef,
    declared: &std::collections::HashSet<&str>,
) -> Vec<(String, KeraRef)> {
    let mut out = Vec::new();
    let mut stack = vec![body.clone()];
    while let Some(t) = stack.pop() {
        match t.as_ref() {
            Kera::And(xs) => stack.extend(xs.iter().cloned()),
            Kera::Eq(a, b) => {
                let named = |x: &KeraRef| match x.as_ref() {
                    Kera::Var(n) if declared.contains(n.as_str()) => Some(n.0.clone()),
                    _ => None,
                };
                if let Some(n) = named(a) {
                    out.push((n, b.clone()));
                } else if let Some(n) = named(b) {
                    out.push((n, a.clone()));
                }
            }
            _ => {}
        }
    }
    out
}
