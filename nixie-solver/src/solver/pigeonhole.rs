//! Pigeonhole principle encoding and integer domain clause generation.
//!
//! This module provides SAT-level encodings for:
//! - Pigeonhole exclusion clauses for integer-domain terms
//! - Select equality splits for array theory reasoning
//! - Integer domain enumeration clauses for bounded variables

use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use super::Solver;

impl Solver {
    /// Add pigeonhole exclusion clauses from pre-collected domains and disequalities.
    pub(super) fn add_pigeonhole_exclusions_from(
        &mut self,
        domains: &FxHashMap<TermId, (i64, i64)>,
        diseq_pairs: &[(TermId, TermId)],
        manager: &mut TermManager,
    ) {
        for &(x, y) in diseq_pairs {
            let x_domain = domains.get(&x).copied();
            let y_domain = domains.get(&y).copied();
            if let (Some((x_lo, x_hi)), Some((y_lo, y_hi))) = (x_domain, y_domain) {
                let lo = x_lo.max(y_lo);
                let hi = x_hi.min(y_hi);
                if hi >= lo && (hi - lo) <= 20 {
                    for v in lo..=hi {
                        let val = manager.mk_int(BigInt::from(v));
                        let eq_x = manager.mk_eq(x, val);
                        let eq_y = manager.mk_eq(y, val);
                        let lit_x = self.encode(eq_x, manager);
                        let lit_y = self.encode(eq_y, manager);
                        // At most one of x and y can equal k
                        let _ = self.sat.add_clause([lit_x.negate(), lit_y.negate()]);
                    }
                }
            }
        }
    }

    /// Add pigeonhole exclusion clauses for integer-domain terms.
    ///
    /// For every pair of terms (x, y) where we have an active disequality
    /// `not(= x y)` and both have bounded integer domains [L, U],
    /// add `Not(Eq(x, k)) OR Not(Eq(y, k))` for each value k in the domain.
    /// This SAT-level encoding directly captures the pigeonhole principle.
    #[allow(dead_code)]
    pub(super) fn add_pigeonhole_exclusions(&mut self, manager: &mut TermManager) {
        // Collect domain information: term -> (lo, hi)
        let mut domains: FxHashMap<TermId, (i64, i64)> = FxHashMap::default();
        // Collect disequality pairs
        let mut diseq_pairs: Vec<(TermId, TermId)> = Vec::new();

        // Scan all encoded terms for domain bounds and disequalities
        for &tid in self.arith_terms.iter() {
            // Already tracked -- skip
            let _ = tid;
        }

        // Scan assertions for the patterns we need
        for &aterm in &self.assertions {
            self.scan_for_pigeonhole(aterm, manager, &mut domains, &mut diseq_pairs);
        }

        // Also scan SAT clause implications -- check unit-propagated terms
        // by scanning the term->var mapping for known domain/diseq patterns
        for (&tid, _) in self.term_to_var.iter() {
            self.scan_for_pigeonhole(tid, manager, &mut domains, &mut diseq_pairs);
        }

        // For each disequality pair where both have domains, add exclusion
        for &(x, y) in &diseq_pairs {
            let x_domain = domains.get(&x).copied();
            let y_domain = domains.get(&y).copied();
            if let (Some((x_lo, x_hi)), Some((y_lo, y_hi))) = (x_domain, y_domain) {
                let lo = x_lo.max(y_lo);
                let hi = x_hi.min(y_hi);
                if hi >= lo && (hi - lo) <= 20 {
                    for v in lo..=hi {
                        let val = manager.mk_int(BigInt::from(v));
                        let eq_x = manager.mk_eq(x, val);
                        let eq_y = manager.mk_eq(y, val);
                        let lit_x = self.encode(eq_x, manager);
                        let lit_y = self.encode(eq_y, manager);
                        // Not(Eq(x, k)) OR Not(Eq(y, k))
                        let _ = self.sat.add_clause([lit_x.negate(), lit_y.negate()]);
                    }
                }
            }
        }
    }

    /// Scan `term` for bounded integer domains and disequality pairs that a
    /// pigeonhole encoding can exploit.
    ///
    /// Iterative (explicit task stack), so the `Implies` / `And` nesting of the
    /// assertion is bounded by memory rather than by the native call stack.
    /// The task ordering reproduces the recursive traversal exactly, including
    /// the fact that an `And`'s own `domains.insert` runs *after* the scans of
    /// its nested elements – so an inner domain for the same variable is
    /// overwritten by the enclosing `And`, as before.
    pub(super) fn scan_for_pigeonhole(
        &self,
        term: TermId,
        manager: &TermManager,
        domains: &mut FxHashMap<TermId, (i64, i64)>,
        diseq_pairs: &mut Vec<(TermId, TermId)>,
    ) {
        /// One pending unit of the scan.
        enum ScanTask {
            /// Scan this term.
            Scan(TermId),
            /// Record the domain an `And` established, after its nested
            /// elements have been scanned.
            RecordDomain { var: TermId, lo: i64, hi: i64 },
        }

        let mut stack: Vec<ScanTask> = vec![ScanTask::Scan(term)];
        while let Some(task) = stack.pop() {
            let term = match task {
                ScanTask::RecordDomain { var, lo, hi } => {
                    domains.insert(var, (lo, hi));
                    continue;
                }
                ScanTask::Scan(term) => term,
            };
            let Some(t) = manager.get(term) else { continue };
            match &t.kind {
                // Descend into Implies -- the consequent typically holds the
                // constraint after guard filtering.
                TermKind::Implies(_guard, consequent) => {
                    stack.push(ScanTask::Scan(*consequent));
                }
                // And(Ge(x, L), Le(x, U)) -> domain for x
                // Nested elements are scanned for the same patterns.
                TermKind::And(args) => {
                    let mut lower: Option<(TermId, i64)> = None;
                    let mut upper: Option<(TermId, i64)> = None;
                    // Nested elements, in source order; collected first and
                    // pushed in reverse so they pop left to right.
                    let mut nested: Vec<TermId> = Vec::new();
                    for &a in args.iter() {
                        if let Some(at) = manager.get(a) {
                            match &at.kind {
                                TermKind::Ge(lhs, rhs) => {
                                    if let Some(rt) = manager.get(*rhs) {
                                        if let TermKind::IntConst(n) = &rt.kind {
                                            if let Some(v) = n.to_i64() {
                                                lower = Some((*lhs, v));
                                            }
                                        }
                                    }
                                    // Also check Ge(IntConst, x) -> upper bound
                                    if let Some(lt) = manager.get(*lhs) {
                                        if let TermKind::IntConst(n) = &lt.kind {
                                            if let Some(v) = n.to_i64() {
                                                upper = Some((*rhs, v));
                                            }
                                        }
                                    }
                                }
                                TermKind::Le(lhs, rhs) => {
                                    if let Some(rt) = manager.get(*rhs) {
                                        if let TermKind::IntConst(n) = &rt.kind {
                                            if let Some(v) = n.to_i64() {
                                                upper = Some((*lhs, v));
                                            }
                                        }
                                    }
                                    // Also check Le(IntConst, x) -> lower bound
                                    if let Some(lt) = manager.get(*lhs) {
                                        if let TermKind::IntConst(n) = &lt.kind {
                                            if let Some(v) = n.to_i64() {
                                                lower = Some((*rhs, v));
                                            }
                                        }
                                    }
                                }
                                _ => nested.push(a),
                            }
                        }
                    }
                    // Pushed first, so it runs after every nested scan below.
                    if let (Some((lx, lo)), Some((ux, hi))) = (lower, upper)
                        && lx == ux
                    {
                        stack.push(ScanTask::RecordDomain { var: lx, lo, hi });
                    }
                    stack.extend(nested.into_iter().rev().map(ScanTask::Scan));
                }
                // Not(Eq(x, y)) -> disequality pair
                TermKind::Not(inner) => {
                    if let Some(it) = manager.get(*inner) {
                        if let TermKind::Eq(lhs, rhs) = &it.kind {
                            diseq_pairs.push((*lhs, *rhs));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Add explicit pairwise equality decisions for all select terms
    /// tracked by the arithmetic solver.  For each pair of select terms
    /// `select(a, i)` and `select(a, j)` with the same array, add the
    /// tautological clause `Eq(s_i, s_j) OR Not(Eq(s_i, s_j))`.  This
    /// forces the SAT solver to decide the equality, enabling theory
    /// propagation for pigeonhole-style contradictions.
    #[allow(dead_code)]
    pub(super) fn add_select_equality_splits(&mut self, manager: &mut TermManager) {
        // Collect all select terms from the arith terms set
        let select_terms: Vec<(TermId, TermId, TermId)> = self
            .arith_terms
            .iter()
            .filter_map(|&tid| {
                let t = manager.get(tid)?;
                if let TermKind::Select(array, index) = &t.kind {
                    Some((tid, *array, *index))
                } else {
                    None
                }
            })
            .collect();

        // For each pair of selects on the same array, add equality split
        for i in 0..select_terms.len() {
            for j in (i + 1)..select_terms.len() {
                let (s_i, arr_i, _) = select_terms[i];
                let (s_j, arr_j, _) = select_terms[j];
                if arr_i != arr_j {
                    continue;
                }
                // Add: Eq(s_i, s_j) OR Not(Eq(s_i, s_j))
                // This is a tautology, but it forces the SAT solver to
                // assign a truth value to Eq(s_i, s_j), enabling the
                // theory solver to detect conflicts.
                let eq = manager.mk_eq(s_i, s_j);
                let eq_lit = self.encode(eq, manager);
                // The tautological clause is always satisfied, but the
                // important side effect is that Eq(s_i, s_j) now has a
                // SAT variable. The SAT solver must decide it.
                let _ = self.sat.add_clause([eq_lit, eq_lit.negate()]);

                // Also add the disequality split: if they're unequal,
                // they must be ordered.
                let lt = manager.mk_lt(s_i, s_j);
                let gt = manager.mk_gt(s_i, s_j);
                let lt_lit = self.encode(lt, manager);
                let gt_lit = self.encode(gt, manager);
                let neq_lit = eq_lit.negate();
                // Not(Eq(s_i, s_j)) => Lt(s_i, s_j) OR Gt(s_i, s_j)
                let _ = self.sat.add_clause([eq_lit, lt_lit, gt_lit]);
                let _ = neq_lit;
            }
        }
    }

    /// For a conjunction `And(Ge(x, L), Le(x, U))` on integer terms,
    /// add the clause `Eq(x, L) OR Eq(x, L+1) OR ... OR Eq(x, U)`.
    ///
    /// This forces the SAT solver to pick a concrete integer value for x,
    /// which is required for pigeonhole reasoning (the simplex over rationals
    /// cannot detect integer pigeonhole violations).
    pub(super) fn add_int_domain_clauses(&mut self, term: TermId, manager: &mut TermManager) {
        let Some(t) = manager.get(term).cloned() else {
            return;
        };
        if let TermKind::And(args) = &t.kind {
            // Look for Ge(x, IntConst(L)) / Le(IntConst(L), x) and
            //          Le(x, IntConst(U)) / Ge(IntConst(U), x) pairs.
            // deep_simplify may convert Ge(a,b) -> Le(b,a), so both forms
            // must be recognized.
            let mut lower: Option<(TermId, i64)> = None;
            let mut upper: Option<(TermId, i64)> = None;
            for &a in args.iter() {
                if let Some(at) = manager.get(a).cloned() {
                    match &at.kind {
                        // Ge(x, IntConst(L)) -> lower bound L for x
                        TermKind::Ge(lhs, rhs) => {
                            if let Some(rt) = manager.get(*rhs) {
                                if let TermKind::IntConst(n) = &rt.kind {
                                    if let Some(v) = n.to_i64() {
                                        lower = Some((*lhs, v));
                                    }
                                }
                            }
                            // Ge(IntConst(U), x) -> upper bound U for x
                            if let Some(lt) = manager.get(*lhs) {
                                if let TermKind::IntConst(n) = &lt.kind {
                                    if let Some(v) = n.to_i64() {
                                        upper = Some((*rhs, v));
                                    }
                                }
                            }
                        }
                        TermKind::Le(lhs, rhs) => {
                            // Le(x, IntConst(U)) -> upper bound U for x
                            if let Some(rt) = manager.get(*rhs) {
                                if let TermKind::IntConst(n) = &rt.kind {
                                    if let Some(v) = n.to_i64() {
                                        upper = Some((*lhs, v));
                                    }
                                }
                            }
                            // Le(IntConst(L), x) -> lower bound L for x
                            if let Some(lt) = manager.get(*lhs) {
                                if let TermKind::IntConst(n) = &lt.kind {
                                    if let Some(v) = n.to_i64() {
                                        lower = Some((*rhs, v));
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            if let (Some((lx, lo)), Some((ux, hi))) = (lower, upper) {
                if lx == ux && hi >= lo && (hi - lo) <= 10 {
                    // Add: Eq(x, lo) OR Eq(x, lo+1) OR ... OR Eq(x, hi)
                    let mut domain_lits = Vec::new();
                    for v in lo..=hi {
                        let val = manager.mk_int(BigInt::from(v));
                        let eq = manager.mk_eq(lx, val);
                        let lit = self.encode(eq, manager);
                        domain_lits.push(lit);
                    }
                    if !domain_lits.is_empty() {
                        self.sat.add_clause(domain_lits);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod s8_iterative_tests {
    use super::*;
    use nixie_core::ast::TermManager;

    /// Nesting depth that would overflow the native stack under the previous
    /// recursive walk; the assertion is that the call **returns**.
    ///
    /// This depth and [`SMALL_STACK`] were scaled down together by a factor
    /// of 8 (from 60 000 on 1 MiB).  What these tests pin is the ~17 bytes of
    /// stack available per level – far under any native frame – not the
    /// absolute depth, and the smaller pair costs a fraction of the memory
    /// the interner has to keep live.  Never raise one without the other.
    const DEEP: usize = 7_500;

    /// Worker stack for the deep-nesting tests; see [`DEEP`].
    const SMALL_STACK: usize = 1 << 17;

    #[test]
    fn s8_scan_for_pigeonhole_deep_implies_chain_returns() {
        let handle = std::thread::Builder::new()
            .stack_size(SMALL_STACK)
            .spawn(|| {
                let mut tm = TermManager::new();
                let int_sort = tm.sorts.int_sort;
                let bool_sort = tm.sorts.bool_sort;
                let x = tm.mk_var("x", int_sort);
                let y = tm.mk_var("y", int_sort);
                let guard = tm.mk_var("g", bool_sort);
                let eq = tm.mk_eq(x, y);
                let mut current = tm.mk_not(eq);
                for _ in 0..DEEP {
                    current = tm.mk_implies(guard, current);
                }
                let solver = Solver::new();
                let mut domains = FxHashMap::default();
                let mut diseqs = Vec::new();
                solver.scan_for_pigeonhole(current, &tm, &mut domains, &mut diseqs);
                (domains.len(), diseqs)
            })
            .expect("spawn deep-nesting worker");
        let (domain_count, diseqs) = handle.join().expect("deep scan must return");
        assert_eq!(domain_count, 0);
        assert_eq!(diseqs.len(), 1, "the innermost disequality is still found");
    }

    /// Deeply nested `and`s: each level's non-`Ge`/`Le` element is scanned.
    #[test]
    fn s8_scan_for_pigeonhole_deep_and_nesting_returns() {
        let handle = std::thread::Builder::new()
            .stack_size(SMALL_STACK)
            .spawn(|| {
                let mut tm = TermManager::new();
                let int_sort = tm.sorts.int_sort;
                let x = tm.mk_var("x", int_sort);
                let y = tm.mk_var("y", int_sort);
                let eq = tm.mk_eq(x, y);
                let mut current = tm.mk_not(eq);
                for _ in 0..DEEP {
                    current = tm.mk_and(vec![current]);
                }
                let solver = Solver::new();
                let mut domains = FxHashMap::default();
                let mut diseqs = Vec::new();
                solver.scan_for_pigeonhole(current, &tm, &mut domains, &mut diseqs);
                diseqs.len()
            })
            .expect("spawn deep-nesting worker");
        assert_eq!(handle.join().ok(), Some(1));
    }

    /// Semantic pin: bounds are still recognised in both operand orders, and
    /// an *enclosing* `and`'s domain still wins over a nested one – the
    /// post-order the recursive version had.
    #[test]
    fn s8_scan_for_pigeonhole_outer_domain_overrides_nested() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let y = tm.mk_var("y", int_sort);

        let zero = tm.mk_int(BigInt::from(0));
        let three = tm.mk_int(BigInt::from(3));
        let one = tm.mk_int(BigInt::from(1));
        let two = tm.mk_int(BigInt::from(2));

        // Inner: 1 <= x <= 2, written with the constant on the left of `Le`
        // (`Le(1, x)` is a lower bound) to pin both operand orders.  It is
        // wrapped in an `implies` so `mk_and`'s flattening cannot merge it
        // into the enclosing conjunction – the nesting is the point here.
        let inner_lo = tm.mk_le(one, x);
        let inner_hi = tm.mk_le(x, two);
        let inner = tm.mk_and(vec![inner_lo, inner_hi]);
        let guard = tm.mk_var("g", tm.sorts.bool_sort);
        let nested = tm.mk_implies(guard, inner);

        // Outer: 0 <= x <= 3, plus the nested conjunction above and `x != y`.
        let outer_lo = tm.mk_ge(x, zero);
        let outer_hi = tm.mk_le(x, three);
        let eq = tm.mk_eq(x, y);
        let diseq = tm.mk_not(eq);
        let outer = tm.mk_and(vec![outer_lo, outer_hi, nested, diseq]);

        let solver = Solver::new();
        let mut domains = FxHashMap::default();
        let mut diseqs = Vec::new();
        solver.scan_for_pigeonhole(outer, &tm, &mut domains, &mut diseqs);

        assert_eq!(
            domains.get(&x),
            Some(&(0, 3)),
            "the enclosing `and` records its domain last and therefore wins"
        );
        assert_eq!(diseqs, vec![(x, y)]);
    }
}
