//! Eager EUF internalization and equality-atom theory propagation.
//!
//! Z3 internalizes every UF term into the e-graph when the formula is asserted
//! (`euf_egraph::mk`), so congruence can fire on applications the SAT core has
//! not yet assigned.  OxiZ previously interned a term only when its equality
//! atom was assigned, so `a = b` could not force `(= (f a) (f b))` until SAT
//! branched on that atom.
//!
//! After a merge that changes the e-graph, unassigned `(= (f s) (f t))` atoms
//! whose sides now share a class are propagated to SAT.  Only application-
//! application pairs are considered: hardware encodings have thousands of
//! boolean/ITE equalities, and explaining those dominates runtime.  An
//! unexplainable fact is skipped, never fabricated.

use super::TheoryManager;
use crate::prelude::*;
use oxiz_core::ast::TermId;
use oxiz_sat::{Lit, Var};
use smallvec::SmallVec;

use super::super::types::Constraint;

const MAX_EUF_PROPS: usize = 16;

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

    pub(super) fn euf_assignment_is_news(
        &self,
        constraint: &Constraint,
        is_positive: bool,
    ) -> bool {
        match *constraint {
            Constraint::Eq(l, r) => self.eq_news(l, r, is_positive),
            Constraint::Diseq(l, r) => self.eq_news(l, r, !is_positive),
            Constraint::BoolApp(t) => {
                let Some(n) = self.euf.term_to_node(t) else {
                    return true;
                };
                let (Some(tn), Some(fn_)) = (self.bool_true_node, self.bool_false_node) else {
                    return true;
                };
                if is_positive {
                    !self.euf.are_equal_immutable(n, tn)
                } else {
                    !self.euf.are_equal_immutable(n, fn_)
                }
            }
            _ => false,
        }
    }

    fn eq_news(&self, l: TermId, r: TermId, want_eq: bool) -> bool {
        let (Some(a), Some(b)) = (self.euf.term_to_node(l), self.euf.term_to_node(r)) else {
            return true;
        };
        if want_eq {
            !self.euf.are_equal_immutable(a, b)
        } else {
            !self.euf.are_proven_disequal(a, b)
        }
    }

    pub(super) fn euf_constraint_nodes(&self, constraint: &Constraint) -> Option<(u32, u32)> {
        match *constraint {
            Constraint::Eq(l, r) | Constraint::Diseq(l, r) => {
                Some((self.euf.term_to_node(l)?, self.euf.term_to_node(r)?))
            }
            Constraint::BoolApp(t) => {
                let n = self.euf.term_to_node(t)?;
                Some((n, n))
            }
            _ => None,
        }
    }

    pub(super) fn propagate_euf_eq_atoms(
        &mut self,
        touch: Option<(u32, u32)>,
    ) -> Option<Vec<(Lit, SmallVec<[Lit; 8]>)>> {
        let (ta, tb) = touch?;
        let ra = self.euf.find_immutable(ta);
        let rb = self.euf.find_immutable(tb);
        let mut props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
        let atoms = self.euf_eq_atoms.clone();
        for (var, lhs, rhs, is_eq) in atoms {
            if props.len() >= MAX_EUF_PROPS {
                break;
            }
            if self.assigned_level.contains_key(&var) {
                continue;
            }
            let (Some(nl), Some(nr)) = (self.euf.term_to_node(lhs), self.euf.term_to_node(rhs))
            else {
                continue;
            };
            let sl = self.euf.find_immutable(nl);
            let sr = self.euf.find_immutable(nr);
            if sl != ra && sl != rb && sr != ra && sr != rb {
                continue;
            }
            let Some((lit, reasons)) = self.forced_eq_lit(var, nl, nr, is_eq) else {
                continue;
            };
            props.push((lit, reasons));
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
                self.euf.node_args(a).map(|v| v.clone()),
                self.euf.node_args(b).map(|v| v.clone()),
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
