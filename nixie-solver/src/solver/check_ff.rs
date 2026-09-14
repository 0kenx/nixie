//! Eager whole-problem finite-field dispatch (`QF_FF`, Phase 3 of
//! `docs/FF_THEORY_DESIGN.md` §7): decides pure conjunctive goals by
//! handing every field's literal slice to
//! [`nixie_theories::ff_theory::check_conjunction`], modelled on
//! `dispatch_nl_solver`. Goals with Boolean structure beyond a
//! conjunction of literals are *declined* here (`None`) — the CDCL(T)
//! path takes them (Phase 4), and its honesty gate answers `Unknown`
//! for the FF atoms it does not own.

use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_theories::ff_theory::{FfOutcome, check_conjunction, validate_model};
use num_bigint::BigUint;

use super::Solver;
use super::types::{Model, SolverResult};

/// The FF dispatch's per-field step budget. A tick counter (encoding
/// steps, S-pairs, reductions, search nodes, root-finding work); never
/// wall-clock.
const FF_BUDGET_STEPS: u64 = 1 << 26;

impl Solver {
    /// Whether any assertion mentions finite-field structure.
    fn goal_uses_finite_fields(&self, manager: &TermManager) -> bool {
        self.assertions.iter().any(|&a| term_uses_ff(a, manager))
    }

    /// The set of distinct fields the assertions mention (a mixed-field
    /// goal checks each field's slice independently — no inference
    /// relates 𝔽_p and 𝔽_q).
    fn goal_fields(&self, manager: &TermManager) -> Vec<FieldId> {
        let mut fields: Vec<FieldId> = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.assertions.clone();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(term) = manager.get(t) else {
                continue;
            };
            match &term.kind {
                TermKind::FfConst { field, .. } => {
                    if !fields.contains(field) {
                        fields.push(*field);
                    }
                }
                _ => {
                    stack.extend(nixie_core::ast::get_children(&term.kind));
                }
            }
        }
        fields.sort_by_key(|f| f.raw());
        fields
    }

    /// Decide a conjunctive `QF_FF` goal eagerly.
    ///
    /// Returns `None` when the goal is not this dispatcher's to answer:
    /// no FF structure, quantifiers present, or an assertion that is not
    /// (a conjunction of) FF literals — those fall through to CDCL(T),
    /// whose honesty gate keeps the answer `Unknown` until Phase 4.
    pub(super) fn dispatch_ff_solver(&mut self, manager: &mut TermManager) -> Option<SolverResult> {
        if !self.goal_uses_finite_fields(manager) {
            return None;
        }
        if self.has_quantifiers {
            return None;
        }

        // Flatten the assertions into literals (and-conjunctions only;
        // `true` contributes nothing).
        let mut literals: Vec<TermId> = Vec::new();
        for &assertion in &self.assertions {
            let term = manager.get(assertion)?;
            match &term.kind {
                TermKind::True => {}
                TermKind::And(children) => {
                    let mut work: Vec<TermId> = children.iter().rev().copied().collect();
                    while let Some(t) = work.pop() {
                        let node = manager.get(t)?;
                        match &node.kind {
                            TermKind::True => {}
                            TermKind::And(inner) => {
                                work.extend(inner.iter().rev().copied());
                            }
                            _ => literals.push(t),
                        }
                    }
                }
                _ => literals.push(assertion),
            }
        }

        // Every literal must be an FF literal (`=`, `not =`, `true`,
        // `false`) over one field's terms. Anything else (Boolean
        // structure, foreign theories) declines.
        for &lit in &literals {
            if !is_ff_literal(lit, manager) {
                return None;
            }
        }

        let fields = self.goal_fields(manager);
        if fields.is_empty() {
            return None;
        }

        // Multiplexed per field: the conjunction splits across fields.
        let mut combined_model = Model::new();
        let mut core: Vec<usize> = Vec::new();
        for field in fields {
            // The slice for this field: literals mentioning it (plus
            // globally-true literals, which check_conjunction skips).
            let slice: Vec<TermId> = literals
                .iter()
                .copied()
                .filter(|&l| literal_mentions_field(l, field, manager))
                .collect();
            let outcome = check_conjunction(manager, field, &slice, FF_BUDGET_STEPS);
            match outcome {
                FfOutcome::Model(model) => {
                    // Step 5: validate, always. A failing validation is an
                    // internal error — fall through to the honest Unknown
                    // of the CDCL path, never a `Sat`.
                    if validate_model(manager, field, &slice, &model).is_err() {
                        return None;
                    }
                    for (var, value) in model.assignments() {
                        let value_term = manager
                            .mk_ff_const(field, into_bigint(value))
                            .expect("the field is interned and prime");
                        combined_model.set(*var, value_term);
                    }
                }
                FfOutcome::Unsat(ff_core) => {
                    // Map the slice indices back to the global literal list.
                    for &i in &ff_core.fact_indices {
                        if let Some(&lit) = slice.get(i) {
                            if let Some(global) = literals.iter().position(|&l| l == lit) {
                                core.push(global);
                            }
                        }
                    }
                    // An empty core cannot happen (check_conjunction
                    // guarantees one), but an unwarranted whole-goal Unsat
                    // is worse than a missed dispatch: only answer Unsat
                    // with a nonempty core.
                    if !core.is_empty() {
                        self.install_ff_core(&literals, &core);
                        return Some(SolverResult::Unsat);
                    }
                    return None;
                }
                FfOutcome::Exhausted => {
                    // The branching closed the search space: genuine UNSAT
                    // (no certificate available — see §8's branch-exhaustion
                    // case).
                    self.install_ff_core(&literals, &[]);
                    return Some(SolverResult::Unsat);
                }
                FfOutcome::OutOfBudget { where_ } => {
                    tracing::debug!("ff dispatch: budget exhausted at {where_}");
                    return None;
                }
                FfOutcome::InvalidModel(reason) => {
                    tracing::warn!("ff dispatch declined: {reason}");
                    return None;
                }
            }
        }
        self.model = Some(combined_model);
        Some(SolverResult::Sat)
    }

    /// Record the unsat core as the asserted-literal subset (the solver's
    /// core mechanism consumes named assertions; the literal indices here
    /// feed diagnostics and the future CDCL(T) lemma path).
    fn install_ff_core(&mut self, literals: &[TermId], core: &[usize]) {
        // Phase 3: cores are recorded for `get-unsat-core` support in the
        // solver's named-assertion machinery when it lands with Phase 4's
        // trail wiring. The literal list is kept out of hot paths.
        let _ = (literals, core);
    }
}

/// Exact `BigUint → BigInt` (the residue is already in `[0, p)`).
fn into_bigint(v: &BigUint) -> num_bigint::BigInt {
    num_bigint::BigInt::from_biguint(num_bigint::Sign::Plus, v.clone())
}

/// Whether a term's DAG contains finite-field structure (explicit stack).
fn term_uses_ff(root: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        match &term.kind {
            TermKind::FfConst { .. }
            | TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_) => return true,
            TermKind::Var(_) => {
                if matches!(
                    manager.sorts.get(term.sort).map(|s| &s.kind),
                    Some(SortKind::FiniteField(_))
                ) {
                    return true;
                }
            }
            _ => stack.extend(nixie_core::ast::get_children(&term.kind)),
        }
    }
    false
}

/// Whether a term is an FF literal: `=`, `not =`, `true`, `false` — the
/// signature has exactly one predicate.
fn is_ff_literal(lit: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(lit) else {
        return false;
    };
    match &term.kind {
        TermKind::True | TermKind::False => true,
        TermKind::Eq(a, b) => {
            // An FF equality: at least one side mentions FF structure and,
            // when so, both sides are pure FF terms (the parser rejects
            // mixed sorts, so the second clause is a shape guard). A
            // non-FF equality (Int, BV, …) declines: not this dispatcher's.
            let fa = term_uses_ff(*a, manager);
            let fb = term_uses_ff(*b, manager);
            if !fa && !fb {
                return false;
            }
            is_pure_ff(*a, manager) && is_pure_ff(*b, manager)
        }
        TermKind::Not(inner) => {
            let Some(t) = manager.get(*inner) else {
                return false;
            };
            matches!(t.kind, TermKind::Eq(_, _)) && is_ff_literal(*inner, manager)
        }
        _ => false,
    }
}

/// Whether a term is built ONLY from FF structure (no foreign-theory
/// leaves) — an `=` mixing an FF side with a non-FF side is a type error
/// the parser rejects, so this is a shape guard, not a semantic one.
fn is_pure_ff(root: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            return false;
        };
        match &term.kind {
            TermKind::FfConst { .. }
            | TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_) => {}
            TermKind::Var(_) => {
                if !matches!(
                    manager.sorts.get(term.sort).map(|s| &s.kind),
                    Some(SortKind::FiniteField(_))
                ) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// Whether a literal's DAG mentions a specific field.
fn literal_mentions_field(lit: TermId, field: FieldId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![lit];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        if let TermKind::FfConst { field: id, .. } = &term.kind {
            if *id == field {
                return true;
            }
            // A literal naming another field still belongs to that other
            // field's slice; keep walking for this one only if some
            // subterm names it.
        }
        // FF-sorted variables: resolve their field through the sort.
        if let TermKind::Var(_) = &term.kind
            && let Some(SortKind::FiniteField(id)) =
                manager.sorts.get(term.sort).map(|s| s.kind.clone())
            && id == field
        {
            return true;
        }
        stack.extend(nixie_core::ast::get_children(&term.kind));
    }
    false
}
