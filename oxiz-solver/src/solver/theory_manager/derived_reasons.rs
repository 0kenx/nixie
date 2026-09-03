//! Explanations for theory assertions whose reason tag names a *derived*
//! equality instead of a Boolean atom.
//!
//! [`ArithSolver`](oxiz_theories::ArithSolver) records exactly one `TermId` per
//! assertion, so an equality propagated out of congruence closure – `f(a) =
//! f(b)` because `a = b` – can only be tagged with one of its own operands, a
//! term that names no literal.  `TheoryManager::terms_to_conflict_clause`
//! expands such a tag back into the literals that justify it, and this table is
//! where those literals live.
//!
//! # Why this is not a plain map inside `TheoryManager`
//!
//! An entry is valid for exactly as long as the theory assertion it explains,
//! and that lifetime is governed by the *theory scope stack*, not by the manager
//! that happened to record it.  Two consequences, each of which was a real
//! soundness defect when it was missing:
//!
//! * **The table outlives the manager.**  `Solver::check` builds a fresh
//!   `TheoryManager` for every MBQI round while deliberately keeping the EUF /
//!   arithmetic / bit-vector solvers' state ("the theory state accumulates
//!   correctly across iterations").  A per-manager map therefore started empty
//!   in front of a tableau that still held the previous round's derived
//!   equalities, and the first conflict citing one of them lost that part of its
//!   justification.  The table is owned by the `Solver` alongside the theory
//!   solvers so the two can never diverge.
//! * **Entries are pruned by scope depth, not cleared wholesale.**  A backtrack
//!   to level `l` pops only the scopes *above* `l`; every assertion made at or
//!   below `l` stays in the tableau.  Dropping all explanations on any backtrack
//!   therefore orphaned the surviving assertions.  Each justifying literal is
//!   stamped with the scope depth it was recorded at and survives precisely as
//!   long as that scope does.
//!
//! The depth counter lives here for the same reason the entries do.  A
//! `TheoryManager` numbers scopes from its own `level_stack`, which restarts at
//! the base scope for every manager – but a CDCL(T) search that ends in `Sat`
//! never backtracks, so it hands the next manager theory solvers that are still
//! several scopes deep.  Counting from the manager would therefore stamp the
//! next round's shallow scopes with the same numbers as the previous round's
//! deep ones and prune live explanations.  This counter is absolute: it tracks
//! the real depth of the EUF / arithmetic / bit-vector scope stacks across
//! every manager that drives them.
//!
//! A tag with an explanation recorded but *no* literals is meaningful and must
//! be preserved: it is an equality that holds structurally and rests on no
//! assertion, so it contributes nothing to a conflict clause – which is a very
//! different statement from "the justification was lost".

use oxiz_core::ast::TermId;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

/// One tag's explanation: the literal terms that justify the derived equality,
/// each stamped with the theory scope depth it was recorded at.
#[derive(Debug, Default, Clone)]
struct Explanation {
    /// Shallowest scope depth at which this tag was recorded.  The entry itself
    /// survives until that scope is popped, even when it carries no literals.
    depth: usize,
    /// Justifying literal terms with the scope depth each was recorded at.
    literals: SmallVec<[(TermId, usize); 4]>,
}

/// Scope-tracked explanations for derived-equality reason tags.
///
/// See the [module documentation](self) for why this is owned by the `Solver`
/// and pruned by depth.
#[derive(Debug, Default, Clone)]
pub(crate) struct DerivedReasons {
    entries: FxHashMap<TermId, Explanation>,
    /// Current depth of the EUF / arithmetic / bit-vector scope stacks, counted
    /// from their base scope.  Absolute: maintained across every
    /// `TheoryManager` that drives those solvers (see the module docs).
    depth: usize,
    /// Candidate theory lemmas recorded during the current search — each a
    /// clause body over `Eq` atoms as `(atom term, literal polarity)` pairs
    /// (see `TheoryCallback::record_lemma` in oxiz-sat).  Solver-owned
    /// because the `TheoryManager` is a per-search local; never cleared on
    /// theory reset (a recorded lemma stays a valid clause).  Consumed by
    /// certified mode's independently verified EUF lemma pass
    /// (`solver/certification.rs`), which re-verifies every entry before
    /// trusting it.
    pub theory_lemmas: Vec<Vec<(TermId, bool)>>,
    /// Set when a lemma was observed whose literals are not all `Eq` atoms
    /// over non-Bool operands (non-QF_UF content): the certified gate then
    /// declines to use the log rather than guess at a semantics it cannot
    /// check.
    pub lemma_log_poisoned: bool,
    /// Dedup keys for [`Self::theory_lemmas`] (sorted atom/polarity pairs,
    /// hashed).
    lemma_keys: std::collections::HashSet<u64>,
}

impl DerivedReasons {
    /// Record a deduplicated theory lemma (atom/polarity pairs, order
    /// normalized). Returns `true` when the lemma is new.
    pub(crate) fn push_theory_lemma(&mut self, lemma: Vec<(TermId, bool)>) -> bool {
        let mut key_terms = lemma.clone();
        key_terms.sort_unstable_by_key(|(t, _)| t.0);
        let mut hash = 0xcbf2_9ce4_8422_2325u64;
        for (term, pol) in &key_terms {
            hash ^= u64::from(term.0) << 1 ^ u64::from(*pol);
            hash = hash.wrapping_mul(0x1000_0000_01b3);
        }
        if !self.lemma_keys.insert(hash) {
            return false;
        }
        self.theory_lemmas.push(lemma);
        true
    }

    /// Drop every recorded theory lemma (called at `check_core` entry so a
    /// goal's certification sees that goal's lemmas).
    pub(crate) fn clear_theory_lemmas(&mut self) {
        self.theory_lemmas.clear();
        self.lemma_keys.clear();
        self.lemma_log_poisoned = false;
    }

    /// Note that the theory solvers have opened one more scope.
    pub(crate) fn push_scope(&mut self) {
        self.depth += 1;
    }

    /// Note that the theory solvers have closed one scope, and drop every
    /// explanation that belonged to it.
    ///
    /// The explanations pruned here justify assertions the pop has just
    /// retracted; keeping them would let a later conflict cite literals that
    /// are no longer asserted.
    pub(crate) fn pop_scope(&mut self) {
        self.depth = self.depth.saturating_sub(1);
        self.prune_to_current_depth();
    }

    /// Record that the equality tagged `tag`, asserted into a theory solver at
    /// the current scope depth, is justified by `literals`.
    ///
    /// Re-recording a tag keeps the **shallowest** depth seen for it and for
    /// each of its literals: a shallower recording explains the same equality
    /// and outlives the deeper one, so it is the depth that governs how long
    /// the explanation stays valid.
    pub(crate) fn record(&mut self, tag: TermId, literals: impl IntoIterator<Item = TermId>) {
        let depth = self.depth;
        let slot = self.entries.entry(tag).or_insert(Explanation {
            depth,
            literals: SmallVec::new(),
        });
        slot.depth = slot.depth.min(depth);
        for term in literals {
            match slot.literals.iter_mut().find(|(t, _)| *t == term) {
                Some((_, recorded)) => *recorded = (*recorded).min(depth),
                None => slot.literals.push((term, depth)),
            }
        }
    }

    /// The literal terms justifying `tag`, or `None` when this table holds no
    /// explanation for it.
    ///
    /// An empty iterator and `None` mean opposite things: the former is a fully
    /// accounted-for equality that depends on no literal, the latter is a tag
    /// whose justification is unknown – which callers must treat as a bug
    /// rather than silently drop.
    pub(crate) fn literals(&self, tag: TermId) -> Option<impl Iterator<Item = TermId> + '_> {
        self.entries
            .get(&tag)
            .map(|slot| slot.literals.iter().map(|&(term, _depth)| term))
    }

    /// Drop everything recorded in a scope deeper than the current one.
    fn prune_to_current_depth(&mut self) {
        let depth = self.depth;
        self.entries.retain(|_tag, slot| {
            if slot.depth > depth {
                return false;
            }
            slot.literals.retain(|&mut (_term, d)| d <= depth);
            true
        });
    }

    /// The absolute scope depth of the EUF / arithmetic / bit-vector solvers.
    ///
    /// Test-only: this counter is the one place the solvers' true depth is
    /// tracked across `TheoryManager` lifetimes, so it is what
    /// `crate::solver::scope_rebase_tests` reads to assert that
    /// `Solver::rebase_theory_state` really did return them to the base scope.
    #[cfg(test)]
    pub(crate) fn depth(&self) -> usize {
        self.depth
    }

    /// Forget every explanation and return to the base scope.
    ///
    /// Only correct where the theory solvers themselves are reset, so that no
    /// assertion survives to be explained.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.depth = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term(id: u32) -> TermId {
        TermId::new(id)
    }

    /// Open `count` scopes.
    fn push_scopes(reasons: &mut DerivedReasons, count: usize) {
        for _ in 0..count {
            reasons.push_scope();
        }
    }

    /// Close `count` scopes.
    fn pop_scopes(reasons: &mut DerivedReasons, count: usize) {
        for _ in 0..count {
            reasons.pop_scope();
        }
    }

    #[test]
    fn records_and_expands_a_justification() {
        let mut reasons = DerivedReasons::default();
        push_scopes(&mut reasons, 3);
        reasons.record(term(1), [term(10), term(11)]);
        let literals: Vec<TermId> = reasons
            .literals(term(1))
            .expect("tag was recorded")
            .collect();
        assert_eq!(literals, vec![term(10), term(11)]);
        assert!(reasons.literals(term(2)).is_none());
    }

    #[test]
    fn an_empty_explanation_is_kept_and_is_not_a_miss() {
        let mut reasons = DerivedReasons::default();
        reasons.record(term(1), []);
        let literals: Vec<TermId> = reasons
            .literals(term(1))
            .expect("an empty explanation is still an explanation")
            .collect();
        assert!(literals.is_empty());
    }

    #[test]
    fn popping_drops_deeper_scopes_and_keeps_shallower_ones() {
        let mut reasons = DerivedReasons::default();
        reasons.push_scope();
        reasons.record(term(1), [term(10)]);
        push_scopes(&mut reasons, 4);
        reasons.record(term(1), [term(11)]);
        reasons.record(term(2), [term(12)]);

        pop_scopes(&mut reasons, 2);

        let literals: Vec<TermId> = reasons
            .literals(term(1))
            .expect("the depth-1 recording survives")
            .collect();
        assert_eq!(literals, vec![term(10)]);
        assert!(
            reasons.literals(term(2)).is_none(),
            "a tag recorded only above the surviving depth is dropped"
        );
    }

    #[test]
    fn a_base_scope_explanation_outlives_every_pop() {
        let mut reasons = DerivedReasons::default();
        reasons.record(term(1), [term(10)]);
        push_scopes(&mut reasons, 5);
        pop_scopes(&mut reasons, 5);
        // Popping past the base scope must not underflow or forget.
        pop_scopes(&mut reasons, 3);

        let literals: Vec<TermId> = reasons
            .literals(term(1))
            .expect("a base-scope assertion is never retracted by a pop")
            .collect();
        assert_eq!(literals, vec![term(10)]);
    }

    #[test]
    fn re_recording_keeps_the_shallowest_depth() {
        let mut reasons = DerivedReasons::default();
        push_scopes(&mut reasons, 7);
        reasons.record(term(1), [term(10)]);
        pop_scopes(&mut reasons, 5);
        assert!(
            reasons.literals(term(1)).is_none(),
            "the depth-7 recording goes with its scope"
        );

        push_scopes(&mut reasons, 5);
        reasons.record(term(1), [term(10)]);
        pop_scopes(&mut reasons, 5);
        reasons.record(term(1), [term(10)]);
        push_scopes(&mut reasons, 4);
        pop_scopes(&mut reasons, 4);

        let literals: Vec<TermId> = reasons
            .literals(term(1))
            .expect("the shallower re-recording governs the lifetime")
            .collect();
        assert_eq!(literals, vec![term(10)]);
    }

    #[test]
    fn clear_forgets_everything_and_returns_to_the_base_scope() {
        let mut reasons = DerivedReasons::default();
        push_scopes(&mut reasons, 3);
        reasons.record(term(1), [term(10)]);
        reasons.clear();
        assert!(reasons.literals(term(1)).is_none());

        // The depth went back to the base scope with the entries, so a fresh
        // base-scope recording survives a pop.
        reasons.record(term(2), [term(11)]);
        reasons.pop_scope();
        assert!(reasons.literals(term(2)).is_some());
    }
}
