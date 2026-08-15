//! Eager EUF internalization and equality-atom theory propagation.
//!
//! Z3 internalizes every UF term into the e-graph when the formula is asserted
//! (`euf_egraph::mk`), so congruence can fire on applications the SAT core has
//! not yet assigned.  OxiZ previously interned a term only when its equality
//! atom was assigned, so `a = b` could not force `(= (f a) (f b))` until SAT
//! branched on that atom.
//!
//! Propagation is *watch-based* (see `EufSolver::watch_eq_atom`): every
//! equality atom is registered on the e-graph classes of its two endpoints, so
//! a merge (or a fresh asserted disequality between the classes) revisits only
//! the atoms whose sides' classes actually changed – the OxiZ analogue of Z3
//! keeping `=`-applications as e-graph parents, where a merge re-inserts the
//! parents and `add_literal` propagates the equality atom's value.  The
//! previous implementation cloned and rescanned the *entire* atom list after
//! every merge, which dominated QF_UF runtime on all-different-heavy inputs.
//! An unexplainable fact is skipped, never fabricated.

use super::TheoryManager;
use crate::prelude::*;
use oxiz_core::ast::TermId;
use oxiz_sat::{Lit, Var};
use smallvec::SmallVec;

impl TheoryManager<'_> {
    pub(super) fn unique_uf_func_count(&self) -> usize {
        let mut funcs: FxHashSet<u32> = FxHashSet::default();
        let mut stack: Vec<TermId> = Vec::new();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        for &(_, l, r, _) in &self.euf_eq_atoms {
            stack.push(l);
            stack.push(r);
        }
        for &(_, t) in &self.euf_bool_atoms {
            stack.push(t);
        }
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let Some((func, args)) = Self::intern_operands(t, self.manager) {
                funcs.insert(func);
                stack.extend(args.iter().copied());
            }
        }
        funcs.len()
    }

    pub(super) fn intern_all_euf_terms(&mut self) {
        let manager = self.manager;
        let mut endpoints: Vec<TermId> = Vec::with_capacity(
            self.euf_eq_atoms.len().saturating_mul(2) + self.euf_bool_atoms.len(),
        );
        for &(_, l, r, _) in &self.euf_eq_atoms {
            endpoints.push(l);
            endpoints.push(r);
        }
        for &(_, t) in &self.euf_bool_atoms {
            endpoints.push(t);
        }
        for term in endpoints {
            let _ = self.intern_term_for_congruence(term, manager);
        }
    }

    /// Register an e-graph watch for every equality/disequality atom, on the
    /// classes of its two endpoints.  After this, merges and fresh disequality
    /// assertions enqueue exactly the atoms whose forced value may have
    /// changed; see [`Self::drain_forced_eq_atoms`].
    pub(super) fn register_eq_atom_watches(&mut self) {
        for &(var, lhs, rhs, is_eq) in &self.euf_eq_atoms {
            let (Some(nl), Some(nr)) = (self.euf.term_to_node(lhs), self.euf.term_to_node(rhs))
            else {
                continue;
            };
            self.euf.watch_eq_atom(nl, nr, var, is_eq);
        }
    }

    /// Convert the atoms whose endpoints the e-graph just made equal or proven
    /// disequal into SAT propagations with explanations.
    ///
    /// Drains the watch-triggered queue (see `EufSolver::drain_forced_eq_atoms`).
    /// Each entry is re-validated at conversion time – `forced_eq_lit` recomputes
    /// the equal/disequal status from the live e-graph – so an entry that went
    /// stale across a backtrack is dropped rather than propagated.  The whole
    /// drain is converted: the EUF-side per-epoch stamp already deduplicates
    /// re-delivery, so every entry the queue hands over is a genuinely new
    /// forced atom (equality-atom propagation is search guidance only, so a
    /// queue overflow drop just delays the atom to the decision machinery –
    /// it never changes the verdict).
    pub(super) fn drain_forced_eq_atoms(&mut self) -> Option<Vec<(Lit, SmallVec<[Lit; 8]>)>> {
        let forced = self.euf.drain_forced_eq_atoms();
        if forced.is_empty() {
            return None;
        }
        let mut props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
        for w in forced {
            if self.is_level_assigned(w.var) {
                continue;
            }
            if let Some((lit, reasons)) = self.forced_eq_lit(w.var, w.a, w.b, w.is_eq) {
                props.push((lit, reasons));
            }
        }
        if props.is_empty() { None } else { Some(props) }
    }

    fn forced_eq_lit(
        &mut self,
        var: Var,
        nl: u32,
        nr: u32,
        is_eq: bool,
    ) -> Option<(Lit, SmallVec<[Lit; 8]>)> {
        let (sides_equal, reasons) = if self.euf.are_equal_immutable(nl, nr) {
            (true, self.cheap_eq_reason(nl, nr)?)
        } else if self.euf.are_proven_disequal(nl, nr) {
            (false, self.euf.try_explain_diseq(nl, nr)?)
        } else {
            return None;
        };
        let reason_lits = self.terms_to_propagation_reason(&reasons)?;
        let lit = match (is_eq, sides_equal) {
            (true, true) | (false, false) => Lit::pos(var),
            (true, false) | (false, true) => Lit::neg(var),
        };
        let reason_lits: SmallVec<[Lit; 8]> =
            reason_lits.into_iter().filter(|l| l.var() != var).collect();
        Some((lit, reason_lits))
    }

    fn cheap_eq_reason(&mut self, a: u32, b: u32) -> Option<Vec<TermId>> {
        if a == b {
            return Some(Vec::new());
        }
        if let (Some(fa), Some(fb)) = (self.euf.node_func(a), self.euf.node_func(b))
            && fa == fb
            && let (Some(aa), Some(ab)) = (
                self.euf.node_args(a).cloned(),
                self.euf.node_args(b).cloned(),
            )
            && aa.len() == ab.len()
        {
            let mut reasons = Vec::new();
            let mut ok = true;
            for (&x, &y) in aa.iter().zip(ab.iter()) {
                if self.euf.are_equal_immutable(x, y) {
                    reasons.extend(self.euf.try_explain_eq(x, y)?);
                } else {
                    ok = false;
                    break;
                }
            }
            if ok {
                return Some(reasons);
            }
        }
        self.euf.try_explain_eq(a, b)
    }

    fn terms_to_propagation_reason(&self, terms: &[TermId]) -> Option<SmallVec<[Lit; 8]>> {
        let mut out: SmallVec<[Lit; 8]> = SmallVec::new();
        let mut pending: Vec<TermId> = terms.to_vec();
        let mut expanded: FxHashSet<TermId> = FxHashSet::default();
        let mut emitted: FxHashSet<Var> = FxHashSet::default();
        while let Some(term) = pending.pop() {
            if let Some(&var) = self.term_to_var.get(&term) {
                if !self.reason_literal_is_live(term) {
                    return None;
                }
                if emitted.insert(var) {
                    let lit = match self.assigned_pol_of(var) {
                        Some(true) => Lit::pos(var),
                        Some(false) => Lit::neg(var),
                        None => return None,
                    };
                    out.push(lit);
                }
                continue;
            }
            if let Some(justification) = self.derived_reasons.literals(term) {
                if expanded.insert(term) {
                    pending.extend(justification);
                }
                continue;
            }
            if self.tautological_reasons.contains(&term) {
                continue;
            }
            return None;
        }
        Some(out)
    }
}
