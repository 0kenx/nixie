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
use nixie_tla_syntax::{LoadedSpec, Module, UnitKind};

use crate::encode::{EncodeError, Encoder};
use crate::sorts::sort_of;

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
    /// A formula could not be encoded.
    #[error("`{name}` could not be encoded: {why}")]
    Encode {
        /// Which formula.
        name: String,
        /// The encoding diagnostic.
        why: String,
    },
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
        // ONE lowerer for all three formulas. Binder renaming uses a counter
        // held by the `Lowerer`, so separate lowerings would each start from
        // zero and could give two unrelated binders — one in `Init`, one in
        // `Next` — the same name. Inference keys its environment by name, so
        // that would silently force two independent variables to one type.
        let mut low = Lowerer::new();
        low.add_spec(spec);
        let mut dropped = 0usize;
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
        for t in [&init_k, &next_k, &inv_k] {
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
        let mut encoder = Encoder::new();
        let names: Vec<(String, nixie_tla::TyId)> = inf
            .free_names()
            .map(|(n, id)| (n.to_string(), id))
            .collect();
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

        Ok(Self {
            assumptions: typed_assumptions,
            dropped_assumptions: dropped,
            init: init_k,
            next: next_k,
            inv: inv_k,
            encoder,
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
            for a in &assumed {
                solver.assert(*a, tm);
            }
            solver.assert(init, tm);
            for t in transitions.iter().take(j as usize) {
                solver.assert(*t, tm);
            }
            solver.assert(violated, tm);
            match solver.check(tm) {
                SolverResult::Sat => return Ok(Outcome::Violation { step: j }),
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
