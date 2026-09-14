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

use nixie_core::TermManager;
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
    /// The search could not be completed.
    ///
    /// Carries what stopped it. Never reported as either of the above: an
    /// undecided query is not a proof and not a bug.
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
    /// The invariant to check.
    pub inv: &'r str,
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
    inv: KeraRef,
    encoder: Encoder,
    /// Assumptions that could not be lowered, typed or encoded.
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
                inv,
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
            inv,
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
        require(inv, "an invariant", nixie_tla_syntax::Level::State)?;
        require(next, "a next-state action", nixie_tla_syntax::Level::Action)?;

        let init_k = lower_one(&mut low, module, init)?;
        let next_k = lower_one(&mut low, module, next)?;
        let inv_k = lower_one(&mut low, module, inv)?;

        // `ASSUME` is not decoration: a TLA+ specification is only claimed to
        // hold under its assumptions, and they are usually the only thing
        // pinning down a `CONSTANT`. Dropping them leaves every constant
        // completely arbitrary, which turns "this invariant holds for the
        // intended parameters" into "this invariant holds for *every* value
        // of N" — a strictly harder claim that fails on specifications that
        // are perfectly correct. The resulting `Violation` would be a real
        // model of the encoded formula and a false alarm about the spec.
        let mut assumptions = Vec::new();
        for name in constraints {
            assumptions.push(lower_one(&mut low, module, name)?);
        }
        // `CONSTRAINT C` bounds the state space TLC explores. Asserting it in
        // every state is the bounded-model-checking reading, and it is the
        // *strengthening* direction — a search that ignores it explores states
        // the author excluded and can report a counterexample outside the
        // intended model.
        let mut state_constraints = Vec::new();
        for name in &config.state_constraints {
            state_constraints.push(lower_one(&mut low, module, name)?);
        }
        let mut action_constraints = Vec::new();
        for name in &config.action_constraints {
            action_constraints.push(lower_one(&mut low, module, name)?);
        }
        for unit in &module.units {
            if let UnitKind::Assume { body, .. } = &unit.kind {
                // An assumption that will not lower is skipped rather than
                // fatal — but it is skipped *loudly*, by weakening nothing:
                // see `dropped_assumptions`.
                match low.lower(body) {
                    Ok(k) => assumptions.push(k),
                    Err(_) => dropped += 1,
                }
            }
        }

        // One inference over all three, so a state variable has one type
        // across the whole specification rather than three unrelated ones.
        let mut inf = Inference::new();
        for t in [&init_k, &next_k, &inv_k]
            .into_iter()
            .chain(state_constraints.iter())
            .chain(action_constraints.iter())
        {
            inf.infer(t).map_err(|e| SetupError::Types(e.to_string()))?;
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
        for a in assumptions {
            if inf.infer(&a).is_ok() {
                typed_assumptions.push(a);
            } else {
                dropped += 1;
            }
        }

        let state = state_variables(module);
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
        for root in [&init_k, &next_k, &inv_k]
            .into_iter()
            .chain(typed_assumptions.iter())
            .chain(state_constraints.iter())
            .chain(action_constraints.iter())
        {
            collect_empty_sets(root, &mut nodes);
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
            dropped_assumptions: dropped,
            init: init_k,
            next: next_k,
            inv: inv_k,
            encoder,
            state_constraints,
            action_constraints,
            unapplied_config: unapplied,
            conflict_limit: None,
            counterexample: None,
            verification: None,
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
        for a in &self.assumptions {
            match self.encoder.encode_at(a, 0, tm) {
                Ok(t) => assumed.push(t),
                // An assumption with no encoding is dropped, not approximated.
                // Dropping one only *weakens* what is assumed, so the search
                // explores a superset of the intended states: it can produce a
                // spurious counterexample, never hide a real one.
                Err(_) => self.dropped_assumptions += 1,
            }
        }

        let init = self
            .encoder
            .encode_at(&self.init, 0, tm)
            .map_err(|e| named("Init", &e))?;
        let mut transitions = Vec::new();
        for i in 0..depth {
            let t = self
                .encoder
                .encode_at(&self.next, i, tm)
                .map_err(|e| named("Next", &e))?;
            transitions.push(t);
        }

        for j in 0..=depth {
            let inv = self
                .encoder
                .encode_at(&self.inv, j, tm)
                .map_err(|e| named("Inv", &e))?;
            let violated = tm.mk_not(inv);

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
            for t in transitions.iter().take(j as usize) {
                solver.assert(*t, tm);
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
                for step in 0..=j {
                    let t = self
                        .encoder
                        .encode_at(c, step, tm)
                        .map_err(|e| named("CONSTRAINT", &e))?;
                    solver.assert(t, tm);
                }
            }
            for c in &self.action_constraints {
                for step in 0..j {
                    let t = self
                        .encoder
                        .encode_at(c, step, tm)
                        .map_err(|e| named("ACTION_CONSTRAINT", &e))?;
                    solver.assert(t, tm);
                }
            }
            solver.assert(violated, tm);
            match solver.check(tm) {
                SolverResult::Sat => {
                    // A `Sat` answer is a counterexample. Read it back and
                    // replay it: every hop from the specification to here —
                    // lowering, typing, encoding — is cross-checked against
                    // `nixie-tla`'s evaluator already, and this is the hop
                    // that was not.
                    //
                    // The result is *surfaced*, not enforced. Making the
                    // verdict conditional on replaying is the goal and is
                    // deliberately not done yet: the two things that stop a
                    // trace replaying today are gaps in reading a model, not
                    // evidence against the verdict, and turning them into
                    // `Unknown` would trade a measured weakness for an
                    // unmeasured one. `Bmc::verification` says which happened,
                    // so the number is visible rather than assumed.
                    let (trace, verdict) = match solver.model() {
                        None => (
                            None,
                            Verification::NotDecoded("the solver produced no model".to_string()),
                        ),
                        Some(model) => match self.extract(model, j, tm) {
                            Err(why) => (None, Verification::NotDecoded(why)),
                            Ok(t) => match self.replay(&t) {
                                Err(why) => (Some(t), Verification::NotReplayed(why)),
                                Ok(()) => (Some(t), Verification::Replayed),
                            },
                        },
                    };
                    self.counterexample = trace;
                    self.verification = Some(verdict);
                    return Ok(Outcome::Violation { step: j });
                }
                SolverResult::Unsat => {}
                SolverResult::Unknown => {
                    return Ok(Outcome::Unknown(format!(
                        "the solver could not decide the {j}-step query"
                    )));
                }
            }
        }
        Ok(Outcome::NoViolationWithin(depth))
    }

    /// The counterexample behind the last [`Outcome::Violation`].
    ///
    /// Present when the model could be read back, whether or not it replayed;
    /// [`Bmc::verification`] says which.
    #[must_use]
    pub fn counterexample(&self) -> Option<&Trace> {
        self.counterexample.as_ref()
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
            },
        ))
    }

    /// Whether the last counterexample was confirmed independently.
    #[must_use]
    pub fn verification(&self) -> Option<&Verification> {
        self.verification.as_ref()
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
    fn replay(&self, trace: &Trace) -> core::result::Result<(), String> {
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
        // And the point of the whole thing: the invariant must actually fail.
        match ev.eval_state(&self.inv, last) {
            Ok(nixie_tla::Value::Bool(false)) => Ok(()),
            Ok(nixie_tla::Value::Bool(true)) => Err("the invariant holds in the last state".into()),
            Ok(v) => Err(format!(
                "the invariant evaluated to {v} in the last state, which is not a Boolean"
            )),
            Err(e) => Err(format!("the invariant could not be evaluated: {e}")),
        }
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
fn collect_empty_sets(root: &KeraRef, out: &mut Vec<KeraRef>) {
    let mut seen: std::collections::HashSet<*const Kera> = std::collections::HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(t) = stack.pop() {
        if !seen.insert(std::rc::Rc::as_ptr(&t)) {
            continue;
        }
        if matches!(t.as_ref(), Kera::SetEnum(xs) if xs.is_empty()) {
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
fn state_variables(module: &Module) -> Vec<String> {
    let mut out = Vec::new();
    for unit in &module.units {
        if let UnitKind::VariableDecl(ids) = &unit.kind {
            out.extend(ids.iter().map(|i| i.name.clone()));
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
