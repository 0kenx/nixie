//! Constructor injectivity and distinctness **through the congruence
//! closure** (`#P2b-76`).
//!
//! The datatype axioms ([`super::dt_axioms`]) are ground lemmas over the terms
//! the assertions spell, and they stop one level below that set (their own
//! termination argument).  `TermManager::mk_eq` decides an equality of two
//! constructor applications at every depth where both sides are written out
//! (`nixie_core`'s `dt_eq`), but two applications the congruence closure merged
//! *through an opaque term* never meet in an atom:
//!
//! ```smt2
//! (assert (= l3 (cons 1 (cons 2 nil))))
//! (assert (= l3 (cons 1 (cons 2 (cons 3 nil)))))
//! ```
//!
//! puts both lists in `l3`'s class, the selector congruence of the axioms
//! reaches `(tail l3)` and stops, and the search answered `sat` on every build
//! (and printed one list for both, the `d03` model of recheck 14).
//!
//! This is the missing half, as a refinement round at the candidate model
//! (the shared theory refinement seam): every congruence class
//! holding two constructor applications `u = C(a⃗)` and `v = D(b⃗)` is checked,
//! and a violation becomes a guarded datatype theorem:
//!
//! * `C ≠ D` — `¬(u = v)` (constructors are distinct);
//! * `C = D`, a field pair `aᵢ`, `bᵢ` not merged — `¬(u = v) ∨ aᵢ = bᵢ`
//!   (constructors are injective), where `aᵢ = bᵢ` is built by `mk_eq`, so a
//!   pair of literal applications that differ deeper folds it to `false`.
//!
//! We retain equalities as explicit EUF guard atoms instead of expanding
//! candidate merge reasons into SAT literals. This follows Z3's equality-pair
//! datatype justifications, represented here as conditional ground axioms:
//! `C(a) = C(b) => a = b`, and the negation of equalities closing a constructor
//! cycle. These are valid independently of why a candidate merged the terms;
//! unexplained/stale theory reasons can never manufacture an unconditional
//! conflict. Guard equalities deliberately bypass constructor folding, while
//! conclusions retain it. Scope journals and the shared refinement budget are
//! the same ones used by existing datatype and array lemmas.

use nixie_core::ast::{TermId, TermKind, TermManager};
use rustc_hash::FxHashMap;

use super::Solver;

/// Acyclicity through the congruence closure (`#P2b-83`).
mod occurs;

impl Solver {
    /// Inspect one immutable candidate snapshot, then assert new scoped lemmas.
    /// An invalid term, repeated violation, or exhausted scan/axiom budget is
    /// uncertified, never a justification for a Sat or Unsat answer.
    pub(super) fn refine_datatype_classes(
        &mut self,
        manager: &mut TermManager,
    ) -> Result<bool, ()> {
        if !manager.sorts.has_datatypes() {
            return Ok(false);
        }
        let mut lemmas = self.constructor_class_lemmas(manager).ok_or(())?;
        lemmas.extend(self.constructor_cycle_lemmas(manager).ok_or(())?);
        lemmas.sort_unstable();
        lemmas.dedup();
        if lemmas.is_empty() {
            return Ok(false);
        }
        let fresh: Vec<_> = lemmas
            .into_iter()
            .filter(|lemma| !self.dt_axiom_instances.contains(lemma))
            .collect();
        if fresh.is_empty() || fresh.len() > 100_000 {
            return Err(());
        }
        for lemma in fresh {
            self.assert_dt_lemma(lemma, manager);
        }
        if self.dt_axioms_incomplete {
            Err(())
        } else {
            Ok(true)
        }
    }

    /// The lemmas of every congruence class that holds two constructor
    /// applications violating distinctness or injectivity, in term-id order;
    /// `None` when a term is invalid or the scan exceeds its budget.
    fn constructor_class_lemmas(&mut self, manager: &mut TermManager) -> Option<Vec<TermId>> {
        let mut by_class: FxHashMap<u32, Vec<(u32, TermId)>> = FxHashMap::default();
        let mut declarations = FxHashMap::default();
        for (visited, node) in self.euf.all_node_indices().enumerate() {
            if visited >= 100_000 {
                return None;
            }
            let term = self.euf.node_term(node)?;
            let data = manager.get(term)?;
            if let TermKind::DtConstructor { constructor, args } = &data.kind {
                if let std::collections::hash_map::Entry::Vacant(entry) =
                    declarations.entry(data.sort)
                {
                    entry.insert(super::dt_axioms::resolve_decl(data.sort, manager)?);
                }
                let declaration = declarations.get(&data.sort)?;
                let name = manager.resolve_str(*constructor);
                let info = declaration.constructors.iter().find(|c| c.name == name)?;
                if info.fields.len() != args.len()
                    || info
                        .fields
                        .iter()
                        .zip(args)
                        .any(|(field, &arg)| manager.get(arg).is_none_or(|n| n.sort != field.sort))
                {
                    return None;
                }
                by_class
                    .entry(self.euf.find_immutable(node))
                    .or_default()
                    .push((node, term));
            }
        }
        let mut classes: Vec<Vec<(u32, TermId)>> = by_class
            .into_values()
            .filter(|members| members.len() > 1)
            .collect();
        for members in &mut classes {
            members.sort_unstable_by_key(|&(_, term)| term.raw());
        }
        classes.sort_unstable_by_key(|members| members.first().map(|&(_, term)| term.raw()));

        let mut lemmas: Vec<TermId> = Vec::new();
        for members in classes {
            let Some(&(_, first)) = members.first() else {
                continue;
            };
            for &(_, other) in members.iter().skip(1) {
                let conclusions = self.constructor_pair_conclusions(first, other, manager)?;
                if conclusions.is_empty() {
                    continue;
                }
                // Keep the equality as an EUF atom: mk_eq would fold two
                // constructors into their fields and erase the guard that the
                // current candidate actually holds. No merge explanation is
                // needed for this universally valid conditional theorem.
                let equality =
                    manager.intern_term(TermKind::Eq(first, other), manager.sorts.bool_sort);
                let guard = manager.mk_not(equality);
                for conclusion in conclusions {
                    lemmas.push(manager.mk_or([guard, conclusion]));
                    if lemmas.len() > 100_000 {
                        return None;
                    }
                }
            }
        }
        Some(lemmas)
    }

    /// What `u = v` entails that the congruence closure does not already
    /// hold: `[false]` for two different constructors, one field equality per
    /// field pair not merged for the same constructor, `[]` when nothing.
    fn constructor_pair_conclusions(
        &self,
        u: TermId,
        v: TermId,
        manager: &mut TermManager,
    ) -> Option<Vec<TermId>> {
        let (
            Some(TermKind::DtConstructor {
                constructor: c1,
                args: a1,
            }),
            Some(TermKind::DtConstructor {
                constructor: c2,
                args: a2,
            }),
        ) = (
            manager.get(u).map(|d| d.kind.clone()),
            manager.get(v).map(|d| d.kind.clone()),
        )
        else {
            return None;
        };
        let sort = manager.get(u)?.sort;
        if manager.get(v)?.sort != sort {
            return None;
        }
        if c1 != c2 {
            return Some(vec![manager.mk_false()]);
        }
        let mut out: Vec<TermId> = Vec::new();
        for (&x, &y) in a1.iter().zip(a2.iter()) {
            if self.euf_merged(x, y) {
                continue;
            }
            let equality = manager.mk_eq(x, y);
            if !self.datatype_conclusion_holds(equality, manager) {
                out.push(equality);
            }
        }
        Some(out)
    }

    /// Numeric/Boolean fields may already satisfy their equality in their
    /// owning theory without being merged as EUF nodes. A positive (or full)
    /// encoding set true entails the conclusion; a negative-only PG encoding
    /// does not, and an unassigned literal is no evidence. This check prevents
    /// re-emitting a satisfied injection axiom until the round limit is hit.
    fn datatype_conclusion_holds(&self, term: TermId, manager: &TermManager) -> bool {
        if term == manager.true_id {
            return true;
        }
        let Some(&(literal, polarity)) = self.encoded_terms.get(&term) else {
            return false;
        };
        if polarity == super::types::Polarity::Negative {
            return false;
        }
        match self.sat.model_value(literal.var()) {
            nixie_sat::LBool::True => literal.is_pos(),
            nixie_sat::LBool::False => literal.is_neg(),
            nixie_sat::LBool::Undef => false,
        }
    }

    /// Whether the congruence closure holds `x` and `y` in one class.
    fn euf_merged(&self, x: TermId, y: TermId) -> bool {
        if x == y {
            return true;
        }
        match (self.euf.term_to_node(x), self.euf.term_to_node(y)) {
            (Some(a), Some(b)) => self.euf.are_equal_immutable(a, b),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests;
