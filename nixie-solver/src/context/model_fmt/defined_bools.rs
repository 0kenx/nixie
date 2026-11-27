//! The conjunct-level Boolean definitions of a model render, collected once.
//!
//! Split out of `model_fmt` when the completion arm's definition map became
//! a render-local structure; the two walks are the arm's former per-row
//! collection and resolution, unchanged except for being paid once per
//! render.

use super::*;

/// Conjunct-level `(= b φ)` definitions of the asserted goal, and their
/// truth under the model being printed.
///
/// The default-completion arm of [`Context::model_rows`] asks, for every
/// declared Boolean the model left unassigned, whether the assertions
/// DEFINE it (`(= b φ)` at conjunct level) and what its definition
/// evaluates to under the model (`#P2b-39`: a defined Boolean must never
/// be defaulted to `false` in a model whose own values make its
/// definition `true` – the QF_NIA/VeryMax invalid-model class).  Each
/// row used to re-collect the definition map from the assertions before
/// looking its constant up, so U unassigned rows over A conjuncts cost
/// Θ(UA) before any definition was found – a script with 2,048 asserted
/// and 2,048 unconstrained Booleans took 4,176.8 M instructions, against
/// 148.8 M now, where most rows have no definition at all.  One render
/// now shares one lazily built map: collection is paid once, on the
/// first row that reaches the arm, and each row's lookup is expected
/// O(1) (`docs/studies/2026-11-27-five-walks-paid-once.md`).
///
/// The map is render-local on purpose – `model_rows` takes `&self`, and
/// the answer depends on the solver model being printed, which a later
/// render may replace.
#[derive(Default)]
pub(super) struct DefinedBools {
    /// `b → φ`, collected on the first row that asks.
    definitions: Option<crate::prelude::HashMap<nixie_core::TermId, nixie_core::TermId>>,
    /// Definition Booleans whose `φ` evaluates to a definite truth
    /// under `solver_model`, with the chains between definitions
    /// resolved, `b → truth`.  Resolved on the first row that has a
    /// definition: every definition is evaluated under one
    /// interpretation, so a row's answer does not depend on which rows
    /// asked before it.
    resolved: Option<crate::prelude::HashMap<nixie_core::TermId, bool>>,
}

impl DefinedBools {
    /// The value `(get-model)` reports for the Boolean constant `b`:
    /// `Some` only when the assertions define `b` at conjunct level and
    /// its definition evaluates to a definite truth value under
    /// `solver_model` (numeric entries and already-printed Booleans).
    pub(super) fn value(
        &mut self,
        ctx: &Context,
        b: nixie_core::TermId,
        solver_model: &crate::solver::Model,
    ) -> Option<String> {
        if self.definitions.is_none() {
            self.definitions = Some(ctx.collect_bool_definitions());
        }
        if !self.definitions.as_ref()?.contains_key(&b) {
            return None;
        }
        if self.resolved.is_none() {
            self.resolved =
                Some(ctx.resolve_bool_definitions(self.definitions.as_ref()?, solver_model));
        }
        self.resolved
            .as_ref()?
            .get(&b)
            .map(|&truth| if truth { "true" } else { "false" }.to_string())
    }
}

impl Context {
    /// Conjunct-level `(= b φ)` definitions of the asserted goal, `b → φ`,
    /// collected exactly like the nonlinear search's grounding (descend
    /// `and` only).  A Boolean defined twice keeps its first definition.
    fn collect_bool_definitions(
        &self,
    ) -> crate::prelude::HashMap<nixie_core::TermId, nixie_core::TermId> {
        use nixie_core::TermKind;
        let bool_sort = self.terms.sorts.bool_sort;

        let mut defs: crate::prelude::HashMap<nixie_core::TermId, nixie_core::TermId> =
            crate::prelude::HashMap::new();
        let mut stack: Vec<nixie_core::TermId> = self.assertions.clone();
        let mut seen = crate::prelude::HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(n) = self.terms.get(id) else {
                continue;
            };
            match &n.kind {
                TermKind::And(xs) => stack.extend(xs.iter().copied()),
                TermKind::Eq(a, c) => {
                    let bool_var = |t: nixie_core::TermId| {
                        self.terms.get(t).is_some_and(|m| {
                            m.sort == bool_sort && matches!(m.kind, TermKind::Var(_))
                        })
                    };
                    let bool_sorted = |t: nixie_core::TermId| {
                        self.terms.get(t).is_some_and(|m| m.sort == bool_sort)
                    };
                    if bool_var(*a) && bool_sorted(*c) {
                        defs.entry(*a).or_insert(*c);
                    } else if bool_var(*c) && bool_sorted(*a) {
                        defs.entry(*c).or_insert(*a);
                    }
                }
                _ => {}
            }
        }
        defs
    }

    /// The truth of every definition in `defs` under the model being
    /// printed, `b → truth`, for the definitions that evaluate to a
    /// definite truth value (numeric entries and Boolean entries alike).
    fn resolve_bool_definitions(
        &self,
        defs: &crate::prelude::HashMap<nixie_core::TermId, nixie_core::TermId>,
        solver_model: &crate::solver::Model,
    ) -> crate::prelude::HashMap<nixie_core::TermId, bool> {
        use nixie_core::TermKind;
        // Interpretation = the model being printed: numeric entries and
        // Boolean entries (true/false terms) alike.
        let mut interp = nixie_theories::nl_eval::Interpretation::empty();
        for (&t, &v) in solver_model.assignments() {
            let Some(node) = self.terms.get(v) else {
                continue;
            };
            match &node.kind {
                TermKind::IntConst(n) => {
                    interp.pin_num(t, num_rational::BigRational::from(n.clone()));
                }
                TermKind::RealConst(r) => {
                    interp.pin_num(
                        t,
                        num_rational::BigRational::new(
                            num_bigint::BigInt::from(*r.numer()),
                            num_bigint::BigInt::from(*r.denom()),
                        ),
                    );
                }
                TermKind::True => {
                    interp.pin_truth(t, true);
                }
                TermKind::False => {
                    interp.pin_truth(t, false);
                }
                _ => {}
            }
        }
        // Definition chains: resolve in dependency order (a `φ` that names
        // another definition Boolean evaluates once that one is pinned).
        // Pinning a Boolean only ever lets more definitions evaluate, so
        // the fixed point is the same whatever order a round visits them
        // in, and every definition is then read under that one fixed point.
        for _ in 0..defs.len().saturating_add(1) {
            let mut changed = false;
            for (&db, &dphi) in defs {
                if interp.truth_of(db).is_some() {
                    continue;
                }
                if let Some(nixie_theories::nl_eval::Value::Truth(v)) =
                    nixie_theories::nl_eval::evaluate(dphi, &self.terms, &interp)
                {
                    interp.pin_truth(db, v);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut resolved = crate::prelude::HashMap::with_capacity(defs.len());
        for (&db, &dphi) in defs {
            if let Some(nixie_theories::nl_eval::Value::Truth(v)) =
                nixie_theories::nl_eval::evaluate(dphi, &self.terms, &interp)
            {
                resolved.insert(db, v);
            }
        }
        resolved
    }
}
