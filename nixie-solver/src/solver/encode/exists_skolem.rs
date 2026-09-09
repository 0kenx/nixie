//! Skolemization of the existentials an assertion states *unconditionally* –
//! including the ones in disguise as negated universals.
//!
//! # Why
//!
//! `(assert (exists ((y Int)) φ(y)))` says "some `y` satisfies `φ`".  Left as a
//! quantifier it reaches MBQI, which can only *guess* a witness: it instantiates
//! `y` with candidate ground terms and adds `φ(c)` to the SAT core as a hard
//! unit clause.  Every such guess is a strengthening – sound for `sat` (a model
//! of `φ(c)` is a model of `∃y. φ(y)`) but hopeless for completeness, because a
//! witness outside the candidate pool is never tried, and outright dangerous
//! when several guesses for the *same* existential are asserted together (their
//! conjunction can be unsatisfiable while the existential is not).
//!
//! Skolemization replaces the guess with a *symbol*: `∃y. φ(y)` becomes
//! `φ(sk)` for a fresh constant `sk`.  This is the textbook equisatisfiability
//! rewrite – any model of `φ(sk)` yields a model of `∃y. φ(y)` by forgetting
//! `sk`, and any model of `∃y. φ(y)` extends to one of `φ(sk)` by interpreting
//! `sk` as the witness – so the ordinary ground solver now *searches* for the
//! witness instead of guessing it, and the assertion carries no quantifier at
//! all when `φ` is quantifier-free.
//!
//! # Negated quantifier conjuncts (the false-`sat` shapes)
//!
//! A conjunct headed by a *negated* quantifier is the same obligation in
//! disguise, and before this module owned them they had **no engine at all**:
//! the Tseitin encoder binds every quantifier term to a free Boolean,
//! `register_asserted_quantifiers` deliberately refuses quantifiers behind a
//! polarity boundary (registering `(not (forall ((x Int)) (P x)))` as
//! `∀x. P(x)` historically turned a satisfiable goal unsatisfiable), and MBQI
//! only ever consults what was registered.  The result was a fabricated `sat`:
//! the free Boolean is set to whatever the ground layer likes,
//! `MBQIResult::Satisfied` / `NoQuantifiers` verify the registered quantifiers
//! only, and the negated one is forgotten (the funcprobs/U48 and
//! `¬∃z. z ≥ 0` false-`sat`s, September 2026).
//!
//! Both shapes become the cases above after one NNF step, with the negation
//! *pushed inside* (never dropped):
//!
//! * `(not (forall x φ))` ≡ `∃x. ¬φ`   → `¬φ(sk)` – ground, witness searched;
//! * `(not (exists x φ))` ≡ `∀x. ¬φ` – stays a universal, now sitting at
//!   *positive* polarity on the asserted spine, where
//!   [`Solver::register_asserted_quantifiers`](super::super::Solver) registers
//!   it and MBQI/E-matching own it like any other asserted universal.
//!
//! NNF is an equivalence (not merely equisatisfiability) on the Boolean
//! connectives, and Skolemization of an unconditionally asserted conjunct is
//! equisatisfiable for the whole conjunction because the fresh symbol occurs
//! nowhere else.
//!
//! # Where the rewrite is legal
//!
//! Only at **positive polarity on the asserted spine**.  `(assert (not (exists
//! ((y Int)) φ)))` is `∀y. ¬φ`, whose Skolemization would be a *weakening*, and
//! an existential under a disjunction / implication / `ite` branch is not
//! asserted at all.  This module therefore rewrites exactly the conjuncts of
//! the assertion's top-level `And` spine: a conjunct of an unconditionally
//! asserted conjunction is itself unconditionally asserted, at positive
//! polarity, and rebuilding the conjunction replaces that one occurrence
//! without touching any other position the same sub-term may appear in.
//!
//! An existential nested deeper (inside a `forall` body) keeps its usual path:
//! [`Solver::register_asserted_forall`](super::super::Solver) Skolemizes
//! `∀x. ∃y. φ` into `∀x. φ(x, sk(x))` for MBQI.
//!
//! Reference: Z3's `ast/normal_forms/nnf.cpp` / `qe` Skolemization of asserted
//! existentials.

use nixie_core::ast::{TermId, TermKind, TermManager};

use crate::skolemization::SkolemizationContext;

/// Maximum number of top-level conjuncts scanned for an asserted existential.
///
/// The scan is linear and the rewrite only fires on `Exists`-headed conjuncts,
/// so this cap exists purely to keep a pathological assertion (a machine-
/// generated conjunction of hundreds of thousands of literals) from paying for
/// a rewrite that will not fire.  Declining costs completeness only: the
/// assertion keeps its unchanged MBQI path.
const MAX_SPINE_CONJUNCTS: usize = 4096;

/// Replace every unconditionally asserted existential in `term` by its
/// Skolemization, or return `None` when `term` has none.
///
/// `next_skolem_id` is the caller's monotone fresh-symbol counter; it is
/// advanced past every symbol minted here.  Threading it is mandatory: Skolem
/// symbols are named positionally and interned, so two rewrites that both
/// started from zero would make two unrelated existentials share one witness
/// symbol – a strengthening that can turn `sat` into `unsat`.
pub(crate) fn skolemize_asserted_existentials(
    term: TermId,
    manager: &mut TermManager,
    next_skolem_id: &mut u64,
) -> Option<TermId> {
    let conjuncts = flatten_asserted_conjuncts(term, manager)?;

    let mut rewritten: Vec<TermId> = Vec::with_capacity(conjuncts.len());
    let mut changed = false;
    for conjunct in conjuncts {
        if !head_is_rewritable_quantifier(conjunct, manager) {
            rewritten.push(conjunct);
            continue;
        }
        let mut context = SkolemizationContext::with_first_id(*next_skolem_id);
        let result = context.skolemize(manager, conjunct);
        *next_skolem_id = context.skolem_count();
        match result {
            // Skolemization is an equisatisfiability rewrite, so a failure
            // costs completeness only: keep the original conjunct and let it
            // take the unchanged MBQI path.
            Ok(skolemized) if skolemized != conjunct => {
                rewritten.push(skolemized);
                changed = true;
            }
            Ok(_) | Err(_) => rewritten.push(conjunct),
        }
    }

    if !changed {
        return None;
    }
    match rewritten.len() {
        0 => None,
        1 => rewritten.first().copied(),
        _ => Some(manager.mk_and(rewritten)),
    }
}

/// Whether a conjunct's head is a quantifier obligation this module owns:
/// a plain `Exists`, or a negated `Forall` / `Exists` (an existential in
/// disguise, and a polarity-flipped universal, respectively – see the module
/// docs).
fn head_is_rewritable_quantifier(term: TermId, manager: &TermManager) -> bool {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::Exists { .. }) => true,
        Some(TermKind::Not(inner)) => matches!(
            manager.get(*inner).map(|t| &t.kind),
            Some(TermKind::Forall { .. } | TermKind::Exists { .. })
        ),
        _ => false,
    }
}

/// Flatten the assertion's top-level `And` spine into its conjuncts, or return
/// `None` when no conjunct is a rewritable quantifier obligation (nothing to
/// rewrite).
///
/// Iterative with an explicit heap stack: the spine shape is caller-controlled
/// input, and a depth cap on a native recursion could only have silently
/// dropped conjuncts – which would drop assertions from the encoded problem.
/// Children are pushed in reverse so the conjunct order is preserved, and the
/// rebuilt conjunction is structurally the same formula.
fn flatten_asserted_conjuncts(term: TermId, manager: &TermManager) -> Option<Vec<TermId>> {
    let mut out: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = vec![term];
    let mut saw_rewritable = false;

    while let Some(current) = stack.pop() {
        if out.len() >= MAX_SPINE_CONJUNCTS {
            return None;
        }
        match manager.get(current).map(|t| &t.kind) {
            Some(TermKind::And(args)) => {
                for &arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
            Some(_) if head_is_rewritable_quantifier(current, manager) => {
                saw_rewritable = true;
                out.push(current);
            }
            _ => out.push(current),
        }
    }

    if saw_rewritable { Some(out) } else { None }
}
