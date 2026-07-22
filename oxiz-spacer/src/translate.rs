//! Faithful re-interning of a CHC system into a fresh, independent
//! [`TermManager`].
//!
//! Spacer borrows `&mut TermManager` for the whole of a solve, and term
//! interning is not thread-safe, so genuinely parallel solving requires each
//! worker thread to own a *private* term arena. A [`ChcSystem`] is not `Clone`
//! (it holds atomic id counters) and its rule terms live in one specific
//! arena, so to hand a worker an independent copy we must rebuild every rule
//! term in a brand-new arena — which is exactly what this module does.
//!
//! The translation is **fail-closed**: it only handles the linear
//! arithmetic / boolean fragment that the Spacer engine solves soundly
//! (`is_supported_fragment` in `pdr.rs`). Any term or sort outside that
//! fragment (bit-vectors, arrays, strings, floating-point, uninterpreted
//! functions, quantifiers) makes [`translate_system`] return `None`, so the
//! caller can fall back to the sound single-arena sequential engine rather
//! than risk an unfaithful copy.
//!
//! Predicates and rules are rebuilt in their original insertion order, so the
//! translated [`ChcSystem`] reproduces the exact same [`crate::chc::PredId`]/
//! [`crate::chc::RuleId`] numbering — the copy is structurally identical to
//! the original and yields the same verdict.
//!
//! Reference: Z3's `ast_translation` (`src/ast/ast_translation.cpp`).

use crate::chc::{ChcSystem, PredicateApp, RuleBody, RuleHead};
use oxiz_core::ast::TermKind;
use oxiz_core::{SortId, SortKind, TermId, TermManager};
use rustc_hash::FxHashMap;

/// Rebuild `(src_terms, src_system)` as an independent `(TermManager,
/// ChcSystem)` pair whose terms live in a fresh arena.
///
/// Returns `None` if any predicate sort, rule variable sort, or rule term
/// falls outside the translatable linear-arithmetic/boolean fragment, or if
/// the rebuilt system fails to reproduce the original id numbering (a
/// defensive invariant check). On `None` the caller must not assume any
/// parallel copy is available.
#[must_use]
pub fn translate_system(
    src_terms: &TermManager,
    src_system: &ChcSystem,
) -> Option<(TermManager, ChcSystem)> {
    let mut dest_terms = TermManager::new();
    let mut dest_system = ChcSystem::new();
    let mut tr = Translator {
        src: src_terms,
        memo: FxHashMap::default(),
    };

    // Rebuild predicate declarations in insertion order so ids line up.
    for pred in src_system.predicates() {
        let mut params: Vec<SortId> = Vec::with_capacity(pred.params.len());
        for &sort in &pred.params {
            params.push(tr.sort(&mut dest_terms, sort)?);
        }
        let id = dest_system.declare_predicate(pred.name.clone(), params);
        if id != pred.id {
            return None;
        }
    }

    // Rebuild rules in insertion order so ids line up.
    for rule in src_system.rules() {
        let mut vars: Vec<(String, SortId)> = Vec::with_capacity(rule.vars.len());
        for (name, sort) in &rule.vars {
            vars.push((name.clone(), tr.sort(&mut dest_terms, *sort)?));
        }

        let mut body_preds: Vec<PredicateApp> = Vec::with_capacity(rule.body.predicates.len());
        for app in &rule.body.predicates {
            let mut args: Vec<TermId> = Vec::with_capacity(app.args.len());
            for &arg in &app.args {
                args.push(tr.term(&mut dest_terms, arg)?);
            }
            body_preds.push(PredicateApp::new(app.pred, args));
        }
        let constraint = tr.term(&mut dest_terms, rule.body.constraint)?;
        let body = RuleBody::new(body_preds, constraint);

        let head = match &rule.head {
            RuleHead::Query => RuleHead::Query,
            RuleHead::Predicate(app) => {
                let mut args: Vec<TermId> = Vec::with_capacity(app.args.len());
                for &arg in &app.args {
                    args.push(tr.term(&mut dest_terms, arg)?);
                }
                RuleHead::Predicate(PredicateApp::new(app.pred, args))
            }
        };

        let rid = dest_system.add_rule(vars, body, head, rule.name.clone());
        if rid != rule.id {
            return None;
        }
    }

    Some((dest_terms, dest_system))
}

/// Stateful helper that memoizes translated terms so shared subterms are
/// rebuilt once (preserving structural sharing and avoiding exponential
/// blow-up on DAG-shaped terms).
struct Translator<'s> {
    src: &'s TermManager,
    memo: FxHashMap<TermId, TermId>,
}

impl Translator<'_> {
    /// Translate a sort id from the source arena into the destination arena.
    ///
    /// Only the base sorts the Spacer engine reasons about are supported;
    /// everything else fails closed with `None`.
    fn sort(&self, dest: &mut TermManager, sort: SortId) -> Option<SortId> {
        match self.src.sorts.get(sort)?.kind {
            SortKind::Bool => Some(dest.sorts.bool_sort),
            SortKind::Int => Some(dest.sorts.int_sort),
            SortKind::Real => Some(dest.sorts.real_sort),
            _ => None,
        }
    }

    /// Translate a term id from the source arena into the destination arena,
    /// returning `None` for any kind outside the supported fragment.
    fn term(&mut self, dest: &mut TermManager, t: TermId) -> Option<TermId> {
        if let Some(&cached) = self.memo.get(&t) {
            return Some(cached);
        }

        let kind = self.src.get(t)?.kind.clone();
        let out = match kind {
            TermKind::True => dest.mk_true(),
            TermKind::False => dest.mk_false(),
            TermKind::IntConst(v) => dest.mk_int(v),
            TermKind::RealConst(r) => dest.mk_real(r),
            TermKind::Var(spur) => {
                let name = self.src.resolve_str(spur).to_string();
                let sort = self.sort(dest, self.src.get(t)?.sort)?;
                dest.mk_var(&name, sort)
            }
            TermKind::Not(a) => {
                let a = self.term(dest, a)?;
                dest.mk_not(a)
            }
            TermKind::And(args) => {
                let v = self.terms(dest, &args)?;
                dest.mk_and(v)
            }
            TermKind::Or(args) => {
                let v = self.terms(dest, &args)?;
                dest.mk_or(v)
            }
            TermKind::Xor(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_xor(a, b)
            }
            TermKind::Implies(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_implies(a, b)
            }
            TermKind::Ite(c, t1, e) => {
                let c = self.term(dest, c)?;
                let t1 = self.term(dest, t1)?;
                let e = self.term(dest, e)?;
                dest.mk_ite(c, t1, e)
            }
            TermKind::Eq(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_eq(a, b)
            }
            TermKind::Distinct(args) => {
                let v = self.terms(dest, &args)?;
                dest.mk_distinct(v)
            }
            TermKind::Neg(a) => {
                let a = self.term(dest, a)?;
                dest.mk_neg(a)
            }
            TermKind::Add(args) => {
                let v = self.terms(dest, &args)?;
                dest.mk_add(v)
            }
            TermKind::Sub(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_sub(a, b)
            }
            TermKind::Mul(args) => {
                let v = self.terms(dest, &args)?;
                dest.mk_mul(v)
            }
            TermKind::Div(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_div(a, b)
            }
            TermKind::Mod(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_mod(a, b)
            }
            TermKind::Lt(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_lt(a, b)
            }
            TermKind::Le(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_le(a, b)
            }
            TermKind::Gt(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_gt(a, b)
            }
            TermKind::Ge(a, b) => {
                let a = self.term(dest, a)?;
                let b = self.term(dest, b)?;
                dest.mk_ge(a, b)
            }
            // Anything else (bit-vectors, arrays, strings, floating-point,
            // uninterpreted functions, quantifiers) is outside the fragment
            // this translator (and the Spacer engine) handles soundly.
            _ => return None,
        };

        self.memo.insert(t, out);
        Some(out)
    }

    /// Translate a slice of terms, short-circuiting to `None` if any element
    /// is untranslatable.
    fn terms(&mut self, dest: &mut TermManager, args: &[TermId]) -> Option<Vec<TermId>> {
        let mut out = Vec::with_capacity(args.len());
        for &a in args {
            out.push(self.term(dest, a)?);
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chc::PredicateApp;

    #[test]
    fn test_translate_preserves_structure_and_ids() {
        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();

        let inv = system.declare_predicate("Inv", [terms.sorts.int_sort, terms.sorts.int_sort]);
        let x = terms.mk_var("x", terms.sorts.int_sort);
        let y = terms.mk_var("y", terms.sorts.int_sort);
        let zero = terms.mk_int(0);
        let eq_x = terms.mk_eq(x, zero);
        let eq_y = terms.mk_eq(y, zero);
        let init = terms.mk_and([eq_x, eq_y]);
        system.add_init_rule(
            [
                ("x".to_string(), terms.sorts.int_sort),
                ("y".to_string(), terms.sorts.int_sort),
            ],
            init,
            inv,
            [x, y],
        );
        let neg = terms.mk_lt(x, zero);
        system.add_query(
            [
                ("x".to_string(), terms.sorts.int_sort),
                ("y".to_string(), terms.sorts.int_sort),
            ],
            [PredicateApp::new(inv, [x, y])],
            neg,
        );

        let (dest_terms, dest_system) =
            translate_system(&terms, &system).expect("int fragment must translate");

        // Structural identity: same predicate/rule counts and ids.
        assert_eq!(dest_system.num_predicates(), system.num_predicates());
        assert_eq!(dest_system.num_rules(), system.num_rules());
        assert_eq!(dest_system.queries().count(), 1);
        assert_eq!(dest_system.entries().count(), 1);

        // Independent arena: the translated Inv predicate exists with the same
        // arity, and its terms are valid in the fresh manager.
        let dest_inv = dest_system
            .get_predicate_by_name("Inv")
            .expect("Inv must survive translation");
        assert_eq!(dest_inv.arity(), 2);
        // The fresh manager is genuinely separate.
        assert!(dest_terms.get(dest_terms.mk_true()).is_some());
    }

    #[test]
    fn test_translate_rejects_unsupported_sort() {
        // A bit-vector variable is outside the supported fragment, so
        // translation must fail closed rather than silently drop it.
        let mut terms = TermManager::new();
        let mut system = ChcSystem::new();
        let bv_sort = terms.sorts.bitvec(8);
        let p = system.declare_predicate("P", [bv_sort]);
        let bv = terms.mk_var("b", bv_sort);
        let zero = terms.mk_bitvec(0, 8);
        let c = terms.mk_eq(bv, zero);
        system.add_query(
            [("b".to_string(), bv_sort)],
            [PredicateApp::new(p, [bv])],
            c,
        );

        assert!(
            translate_system(&terms, &system).is_none(),
            "bit-vector sorts must make translation fail closed"
        );
    }
}
