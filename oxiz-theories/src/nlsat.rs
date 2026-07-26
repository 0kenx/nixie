//! NLSAT Theory Wrapper
//!
//! This module wraps the NLSAT solver (from oxiz-nlsat) to provide Theory trait
//! implementation for nonlinear arithmetic (QF_NIA and QF_NRA).
//!
//! ## Architecture
//!
//! - `NlsatTheory`: Main wrapper implementing `Theory` trait
//! - Handles both Real (QF_NRA) and Integer (QF_NIA) nonlinear arithmetic
//! - Delegates to `NlsatSolver` (real) or `NiaSolver` (integer)
//! - `TermPolyTranslator`: Converts `TermId` AST nodes to `Polynomial` representations
//! - `dispatch_nia_constraints`: Runs `NiaSolver` over a set of NIA assertions
//! - `dispatch_nra_constraints`: Runs `NlsatSolver` over a set of NRA assertions
//!
//! ## Reference
//!
//! - Z3's NLSAT integration in nlsat/nlsat_explain.cpp
//! - NLSAT solver: oxiz-nlsat::solver::NlsatSolver
//! - Integer solver: oxiz-nlsat::nia::NiaSolver

#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{Theory, TheoryId, TheoryResult};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::error::Result;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::nia::{NiaConfig, NiaSolver, VarType};
use oxiz_nlsat::solver::{NlsatSolver, SolverResult};
use oxiz_nlsat::types::AtomKind;
use std::collections::HashMap;

// ─────────────────────────────────────────────────────────────────────────────
// Public result type for dispatch functions
// ─────────────────────────────────────────────────────────────────────────────

/// Concrete arithmetic assignment produced by a nonlinear decision procedure.
///
/// Keys are free arithmetic terms (`Var`, purified `select` constants, …);
/// values are the rational witnesses found by NIA/NRA/ANIA ground search.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NlSatModel {
    /// TermId → rational value for every free arithmetic variable assigned.
    pub assignments: HashMap<TermId, BigRational>,
}

/// The definitive result from a nonlinear dispatch call.
///
/// `Unknown` is not included: `dispatch_*` functions return `None` to signal
/// "fall through to CDCL(T)" instead of wrapping Unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NlDispatchResult {
    /// The constraint set is satisfiable, with a concrete model witness.
    Sat(NlSatModel),
    /// The constraint set is unsatisfiable.
    Unsat,
}

impl NlDispatchResult {
    /// Satisfiable with an empty assignment map (defaults fill gaps).
    #[must_use]
    pub fn sat_empty() -> Self {
        Self::Sat(NlSatModel::default())
    }

    /// Satisfiable with the given term→value map.
    #[must_use]
    pub fn sat_with(assignments: HashMap<TermId, BigRational>) -> Self {
        Self::Sat(NlSatModel { assignments })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Term→Polynomial translator
// ─────────────────────────────────────────────────────────────────────────────

/// Translates `TermId` AST nodes to `Polynomial` values for use with
/// the NLSAT / NIA solver.
///
/// Maintains a cache of `TermId → polynomial variable index` so that each
/// unique variable term receives a stable index.
///
/// Integer `div`/`mod` are encoded with fresh quotient/remainder variables and
/// the Euclidean identities `a = q·b + r`, `0 ≤ r < |b|` (constant positive
/// divisors only for the strict upper bound; otherwise extraction is marked
/// incomplete). Side-constraint atoms are buffered in [`Self::pending_atoms`].
pub struct TermPolyTranslator<'a> {
    manager: &'a TermManager,
    nlsat: &'a mut NiaSolver,
    var_cache: HashMap<TermId, u32>,
    integer_mode: bool,
    /// Fresh poly var for each `(div a b)` / `(mod a b)` term pair key.
    divmod_cache: HashMap<(TermId, TermId), (u32, u32)>,
    /// Side constraints emitted while translating div/mod.
    pending_atoms: Vec<PolyAtom>,
    /// Set when a div/mod could not be fully encoded (non-constant divisor, …).
    divmod_incomplete: bool,
}

impl<'a> TermPolyTranslator<'a> {
    /// Create a new translator.
    pub fn new(manager: &'a TermManager, nlsat: &'a mut NiaSolver, integer_mode: bool) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
            integer_mode,
            divmod_cache: HashMap::new(),
            pending_atoms: Vec::new(),
            divmod_incomplete: false,
        }
    }

    /// Translate a term into a `Polynomial`.
    ///
    /// Returns `None` for sub-expressions that cannot be expressed as a
    /// polynomial (e.g. uninterpreted functions, non-constant real division).
    pub fn translate(&mut self, term_id: TermId) -> Option<Polynomial> {
        let term = self.manager.get(term_id)?;
        match &term.kind.clone() {
            TermKind::IntConst(n) => {
                let r = BigRational::from_integer(n.clone());
                Some(Polynomial::constant(r))
            }
            TermKind::RealConst(r) => {
                let big = BigRational::new(
                    BigInt::from(r.numer().to_i64().unwrap_or(0)),
                    BigInt::from(r.denom().to_i64().unwrap_or(1)),
                );
                Some(Polynomial::constant(big))
            }
            TermKind::Var(_) => {
                let v = self.get_or_create_var(term_id);
                Some(Polynomial::from_var(v))
            }
            TermKind::Neg(inner) => {
                let p = self.translate(*inner)?;
                Some(Polynomial::neg(&p))
            }
            TermKind::Add(args) => {
                let mut acc = Polynomial::zero();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::add(&acc, &p);
                }
                Some(acc)
            }
            TermKind::Sub(lhs, rhs) => {
                let lp = self.translate(*lhs)?;
                let rp = self.translate(*rhs)?;
                Some(Polynomial::sub(&lp, &rp))
            }
            TermKind::Mul(args) => {
                let mut acc = Polynomial::one();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::mul(&acc, &p);
                }
                Some(acc)
            }
            TermKind::Div(lhs, rhs) | TermKind::Mod(lhs, rhs) => {
                let (q, r) = self.ensure_divmod(*lhs, *rhs)?;
                match &term.kind {
                    TermKind::Div(_, _) => Some(Polynomial::from_var(q)),
                    _ => Some(Polynomial::from_var(r)),
                }
            }
            // After assert-time purification, foreign numeric leaves are
            // already fresh Vars. Keep a defensive opaque mapping only for
            // residual Select/Apply that somehow bypassed purification.
            TermKind::Select(_, _) | TermKind::Apply { .. } => {
                let term = self.manager.get(term_id)?;
                if term.sort != self.manager.sorts.int_sort
                    && term.sort != self.manager.sorts.real_sort
                {
                    return None;
                }
                let v = self.get_or_create_var(term_id);
                Some(Polynomial::from_var(v))
            }
            _ => None,
        }
    }

    /// Ensure Euclidean `div`/`mod` witnesses for `(lhs, rhs)`.
    ///
    /// Emits `lhs = q·rhs + r` and, when `rhs` is a positive integer constant
    /// `b`, `0 ≤ r < b`. Returns `(q_var, r_var)`.
    fn ensure_divmod(&mut self, lhs: TermId, rhs: TermId) -> Option<(u32, u32)> {
        if let Some(&pair) = self.divmod_cache.get(&(lhs, rhs)) {
            return Some(pair);
        }
        let a = self.translate(lhs)?;
        let b_poly = self.translate(rhs)?;

        let q = self.nlsat.nlsat_mut().new_arith_var();
        let r = self.nlsat.nlsat_mut().new_arith_var();
        if self.integer_mode {
            self.nlsat.set_var_type(q, VarType::Integer);
            self.nlsat.set_var_type(r, VarType::Integer);
        } else {
            // Sort-based: div/mod are integer ops in SMT-LIB.
            self.nlsat.set_var_type(q, VarType::Integer);
            self.nlsat.set_var_type(r, VarType::Integer);
        }

        let q_poly = Polynomial::from_var(q);
        let r_poly = Polynomial::from_var(r);
        // a - (q*b + r) = 0
        let qb = Polynomial::mul(&q_poly, &b_poly);
        let qb_r = Polynomial::add(&qb, &r_poly);
        self.pending_atoms.push(PolyAtom {
            poly: Polynomial::sub(&a, &qb_r),
            kind: AtomKind::Eq,
            positive: true,
        });
        // r >= 0  ⇔  NOT(r < 0)
        self.pending_atoms.push(PolyAtom {
            poly: r_poly.clone(),
            kind: AtomKind::Lt,
            positive: false,
        });

        // 0 ≤ r < |b|. For constant b use a linear bound; for variable b use
        // the polynomial encoding r² < b² (equivalent under r ≥ 0, b ≠ 0).
        if b_poly.is_constant() {
            let b_const = b_poly.constant_value();
            if b_const.is_zero() {
                self.divmod_incomplete = true;
                return None;
            }
            let abs_b = if b_const < BigRational::zero() {
                -b_const
            } else {
                b_const
            };
            // r - |b| < 0  ⇔  r < |b|
            self.pending_atoms.push(PolyAtom {
                poly: Polynomial::sub(&r_poly, &Polynomial::constant(abs_b)),
                kind: AtomKind::Lt,
                positive: true,
            });
        } else {
            // r*r - b*b < 0
            let r2 = Polynomial::mul(&r_poly, &r_poly);
            let b2 = Polynomial::mul(&b_poly, &b_poly);
            self.pending_atoms.push(PolyAtom {
                poly: Polynomial::sub(&r2, &b2),
                kind: AtomKind::Lt,
                positive: true,
            });
        }

        self.divmod_cache.insert((lhs, rhs), (q, r));
        Some((q, r))
    }

    fn get_or_create_var(&mut self, term_id: TermId) -> u32 {
        if let Some(&v) = self.var_cache.get(&term_id) {
            return v;
        }
        let v = self.nlsat.nlsat_mut().new_arith_var();
        // Assign integrality from the variable's *actual* sort, not the global
        // `integer_mode` flag. In mixed QF_NIRA problems only genuinely
        // Int-sorted variables may carry the integrality constraint; Real
        // variables must stay real (the NiaSolver default), otherwise a
        // satisfiable non-integral real assignment is spuriously rejected and
        // the solver reports a false UNSAT.
        // Reference: Z3's mixed Int/Real handling in nlsat/nlsat_solver.cpp.
        let is_int_var = self
            .manager
            .get(term_id)
            .map(|t| t.sort == self.manager.sorts.int_sort)
            .unwrap_or(self.integer_mode);
        if is_int_var {
            self.nlsat.set_var_type(v, VarType::Integer);
        }
        self.var_cache.insert(term_id, v);
        v
    }

    /// Return the variable mapping (for model extraction).
    pub fn var_cache(&self) -> &HashMap<TermId, u32> {
        &self.var_cache
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper: nonlinearity detection
// ─────────────────────────────────────────────────────────────────────────────

/// Returns `true` if `term_id` (recursively) contains a `Mul` node where at
/// least two non-constant operands are multiplied together.
pub fn term_is_nonlinear(term_id: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(term_id) else {
        return false;
    };
    match &term.kind {
        TermKind::Mul(args) => {
            let non_const_count = args.iter().filter(|&&a| !is_const_term(a, manager)).count();
            if non_const_count >= 2 {
                return true;
            }
            args.iter().any(|&a| term_is_nonlinear(a, manager))
        }
        TermKind::Add(args) | TermKind::And(args) => {
            args.iter().any(|&a| term_is_nonlinear(a, manager))
        }
        TermKind::Sub(lhs, rhs)
        | TermKind::Eq(lhs, rhs)
        | TermKind::Gt(lhs, rhs)
        | TermKind::Ge(lhs, rhs)
        | TermKind::Lt(lhs, rhs)
        | TermKind::Le(lhs, rhs) => {
            term_is_nonlinear(*lhs, manager) || term_is_nonlinear(*rhs, manager)
        }
        TermKind::Neg(inner) => term_is_nonlinear(*inner, manager),
        _ => false,
    }
}

fn is_const_term(term_id: TermId, manager: &TermManager) -> bool {
    manager
        .get(term_id)
        .map(|t| matches!(&t.kind, TermKind::IntConst(_) | TermKind::RealConst(_)))
        .unwrap_or(false)
}

fn term_contains_divmod(term_id: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(term_id) else {
        return false;
    };
    match &term.kind {
        TermKind::Div(_, _) | TermKind::Mod(_, _) => true,
        TermKind::Neg(inner) | TermKind::Not(inner) => term_contains_divmod(*inner, manager),
        TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Distinct(args) => args.iter().any(|&a| term_contains_divmod(a, manager)),
        TermKind::Ite(c, t, e) => {
            term_contains_divmod(*c, manager)
                || term_contains_divmod(*t, manager)
                || term_contains_divmod(*e, manager)
        }
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b) => {
            term_contains_divmod(*a, manager) || term_contains_divmod(*b, manager)
        }
        _ => false,
    }
}

fn is_numeric_sort(manager: &TermManager, sort: oxiz_core::sort::SortId) -> bool {
    sort == manager.sorts.int_sort || sort == manager.sorts.real_sort
}

fn contains_non_polynomial_ops(term_id: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(term_id) else {
        return false;
    };

    match &term.kind {
        // Div/Mod are encoded via Euclidean auxiliaries in the NIA translator
        // when the divisor is a nonzero constant; still walk children.
        TermKind::Div(lhs, rhs) | TermKind::Mod(lhs, rhs) => {
            contains_non_polynomial_ops(*lhs, manager) || contains_non_polynomial_ops(*rhs, manager)
        }
        // Numeric `select` / uninterpreted apply are opaque poly variables.
        // Non-numeric applies and array `store` are out of the pure poly layer.
        TermKind::Select(arr, idx) => {
            if !is_numeric_sort(manager, term.sort) {
                return true;
            }
            contains_non_polynomial_ops(*arr, manager) || contains_non_polynomial_ops(*idx, manager)
        }
        TermKind::Apply { args, .. } => {
            if !is_numeric_sort(manager, term.sort) {
                return true;
            }
            args.iter()
                .any(|&a| contains_non_polynomial_ops(a, manager))
        }
        // `store` only matters for array theory; it is not an arith op. When
        // it appears solely inside array-sorted equalities the NIA dispatcher
        // skips those assertions entirely.
        TermKind::Store(a, i, v) => {
            contains_non_polynomial_ops(*a, manager)
                || contains_non_polynomial_ops(*i, manager)
                || contains_non_polynomial_ops(*v, manager)
        }
        TermKind::Forall { .. }
        | TermKind::Exists { .. }
        | TermKind::Let { .. }
        | TermKind::Match { .. } => true,
        TermKind::Neg(inner) | TermKind::Not(inner) => contains_non_polynomial_ops(*inner, manager),
        TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Distinct(args) => args
            .iter()
            .any(|&arg| contains_non_polynomial_ops(arg, manager)),
        TermKind::Ite(cond, then_term, else_term) => {
            contains_non_polynomial_ops(*cond, manager)
                || contains_non_polynomial_ops(*then_term, manager)
                || contains_non_polynomial_ops(*else_term, manager)
        }
        TermKind::Xor(lhs, rhs) | TermKind::Implies(lhs, rhs) => {
            contains_non_polynomial_ops(*lhs, manager) || contains_non_polynomial_ops(*rhs, manager)
        }
        TermKind::Sub(lhs, rhs)
        | TermKind::Eq(lhs, rhs)
        | TermKind::Gt(lhs, rhs)
        | TermKind::Ge(lhs, rhs)
        | TermKind::Lt(lhs, rhs)
        | TermKind::Le(lhs, rhs) => {
            contains_non_polynomial_ops(*lhs, manager) || contains_non_polynomial_ops(*rhs, manager)
        }
        _ => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Polynomial atom (internal representation)
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
struct PolyAtom {
    poly: Polynomial,
    kind: AtomKind,
    /// `true` → atom appears positively; `false` → negated literal.
    positive: bool,
}

// ─────────────────────────────────────────────────────────────────────────────
// Assertion-level translation (integer mode)
// ─────────────────────────────────────────────────────────────────────────────

fn is_array_sort_id(manager: &TermManager, sort: oxiz_core::sort::SortId) -> bool {
    manager
        .sorts
        .get(sort)
        .is_some_and(|s| matches!(s.kind, oxiz_core::sort::SortKind::Array { .. }))
}

/// Array-equality assertions (e.g. `A = store(...)`) belong to the array
/// theory, not the polynomial layer. Skipping them is not a relaxation of the
/// arithmetic fragment.
fn is_array_structural_eq(manager: &TermManager, lhs: TermId, rhs: TermId) -> bool {
    let ls = manager.get(lhs).map(|t| t.sort);
    let rs = manager.get(rhs).map(|t| t.sort);
    ls.is_some_and(|s| is_array_sort_id(manager, s))
        || rs.is_some_and(|s| is_array_sort_id(manager, s))
}

/// Assertion contributes nothing to the pure arithmetic fragment.
fn assertion_is_array_only(term_id: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(term_id) else {
        return false;
    };
    match &term.kind {
        TermKind::Eq(a, b) => {
            is_array_structural_eq(manager, *a, *b) || is_arith_interface_eq(manager, *a, *b)
        }
        TermKind::And(args) => args.iter().all(|&a| assertion_is_array_only(a, manager)),
        TermKind::True => true,
        _ => false,
    }
}

fn is_arith_interface_eq(manager: &TermManager, lhs: TermId, rhs: TermId) -> bool {
    fn is_var(manager: &TermManager, t: TermId) -> bool {
        manager
            .get(t)
            .is_some_and(|n| matches!(n.kind, TermKind::Var(_)))
    }
    fn is_foreign_numeric(manager: &TermManager, t: TermId) -> bool {
        let Some(n) = manager.get(t) else {
            return false;
        };
        if n.sort != manager.sorts.int_sort && n.sort != manager.sorts.real_sort {
            return false;
        }
        matches!(
            n.kind,
            TermKind::Select(_, _)
                | TermKind::Apply { .. }
                | TermKind::Store(_, _, _)
                | TermKind::Ite(_, _, _)
        )
    }
    (is_var(manager, lhs) && is_foreign_numeric(manager, rhs))
        || (is_var(manager, rhs) && is_foreign_numeric(manager, lhs))
}

/// Extract polynomial atoms from a top-level assertion.
///
/// `incomplete` is set to `true` whenever some part of the assertion could
/// **not** be captured as a pure conjunction of polynomial atoms — an
/// unrecognized top-level connective (`Or`/`Not`/`Distinct`/`Ite`/…) or a
/// comparison whose operand does not translate to a polynomial. Array
/// structural equalities are skipped (not incomplete): after assert-time
/// purification they are separate from the pure arith fragment.
fn extract_poly_atoms(
    term_id: TermId,
    manager: &TermManager,
    translator: &mut TermPolyTranslator<'_>,
    out: &mut Vec<PolyAtom>,
    incomplete: &mut bool,
) {
    let Some(term) = manager.get(term_id) else {
        *incomplete = true;
        return;
    };
    match &term.kind.clone() {
        TermKind::Eq(lhs, rhs) => {
            if is_array_structural_eq(manager, *lhs, *rhs) {
                return;
            }
            // Interface naming from purification: `c = select(...)` / `c = f(...)`.
            // The pure arith fragment already uses `c`; encoding the foreign side
            // as a second poly var would leave it unbounded and break B&B/enum.
            if is_arith_interface_eq(manager, *lhs, *rhs) {
                return;
            }
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Eq,
                    positive: true,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Lt(lhs, rhs) => {
            // lhs < rhs → rhs - lhs > 0
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Le(lhs, rhs) => {
            // lhs <= rhs → rhs - lhs >= 0 → NOT(rhs - lhs < 0)
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Gt(lhs, rhs) => {
            // lhs > rhs → lhs - rhs > 0
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Ge(lhs, rhs) => {
            // lhs >= rhs → NOT(lhs - rhs < 0)
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::And(args) => {
            for &arg in args.iter() {
                extract_poly_atoms(arg, manager, translator, out, incomplete);
            }
        }
        // Interface equalities that collapsed to reflexivity after purification
        // (`c = c`) are no-ops for the arithmetic fragment.
        TermKind::True => {}
        TermKind::False => {
            // Explicit false in the conjunction → arith fragment is unsat.
            // Encode as 0 = 1.
            out.push(PolyAtom {
                poly: Polynomial::constant(BigRational::from_integer(1.into())),
                kind: AtomKind::Eq,
                positive: true,
            });
        }
        _ => {
            // Any other top-level shape (Or/Not/Distinct/Ite/…) belongs to the
            // boolean abstraction layer, not to this pure-conjunction fast
            // path. Dropping it silently would let the solver "prove" Sat on a
            // relaxed problem, so flag the extraction as incomplete instead.
            *incomplete = true;
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NIA dispatch: public entry point
// ─────────────────────────────────────────────────────────────────────────────

/// Dispatch nonlinear integer arithmetic assertions to the `NiaSolver`.
///
/// Returns:
/// - `Some(NlDispatchResult::Unsat)` if the system is provably UNSAT,
/// - `Some(NlDispatchResult::Sat(_))` if NiaSolver finds an integer model,
/// - `None` if translation yields no atoms or the solver returns Unknown.
///
/// Both linear and nonlinear assertions are passed so the solver has full context.
pub fn dispatch_nia_constraints(
    assertions: &[TermId],
    manager: &TermManager,
    integer_mode: bool,
) -> Option<NlDispatchResult> {
    let has_nl = assertions.iter().any(|&a| term_is_nonlinear(a, manager));
    let has_divmod = assertions.iter().any(|&a| term_contains_divmod(a, manager));
    // Engage for nonlinear products *or* integer div/mod (encoded via
    // Euclidean auxiliaries below). Pure linear problems stay with LIA.
    if !has_nl && !has_divmod {
        return None;
    }

    // Ground store-chains + finite index boxes: decide by evaluating selects
    // (sound for QF_ANIA). Runs before the pure-arith relaxation so we never
    // report Sat from free select-vars when stores constrain them.
    if crate::ania_ground::assertions_contain_store(assertions, manager)
        && let Some(r) = crate::ania_ground::try_decide_ground_ania(assertions, manager)
    {
        return Some(r);
    }

    // Unsupported ops only count on the *arithmetic* fragment. Array
    // `store` trees that only appear in array-sorted equalities are not
    // part of that fragment (see `is_array_structural_eq`).
    let has_unsupported_ops = assertions.iter().any(|&a| {
        !assertion_is_array_only(a, manager) && contains_non_polynomial_ops(a, manager)
    });
    let has_array_stores =
        crate::ania_ground::assertions_contain_store(assertions, manager);

    let config = NiaConfig {
        enable_cutting_planes: true,
        ..NiaConfig::default()
    };
    let mut nia = NiaSolver::with_config(config);
    let mut translator = TermPolyTranslator::new(manager, &mut nia, integer_mode);

    let mut poly_atoms: Vec<PolyAtom> = Vec::new();
    let mut incomplete = false;
    for &assertion in assertions {
        if assertion_is_array_only(assertion, manager) {
            continue;
        }
        extract_poly_atoms(
            assertion,
            manager,
            &mut translator,
            &mut poly_atoms,
            &mut incomplete,
        );
    }
    // Euclidean div/mod side constraints collected during translation.
    poly_atoms.extend(translator.pending_atoms.iter().cloned());
    if translator.divmod_incomplete {
        incomplete = true;
    }

    if poly_atoms.is_empty() {
        return None;
    }

    // Unsat of the pure arith *relaxation* is always sound (extra array
    // constraints can only remove models). Sat is sound only when we did not
    // drop anything and there are no store-definitions that further constrain
    // purified select constants — otherwise free select-vars over-approx.
    let unsat_is_trustworthy = true;
    let sat_is_trustworthy = !incomplete && !has_unsupported_ops && !has_array_stores;

    for atom in &poly_atoms {
        let atom_id = translator
            .nlsat
            .nlsat_mut()
            .new_ineq_atom(atom.poly.clone(), atom.kind);
        let lit = translator
            .nlsat
            .nlsat()
            .atom_literal(atom_id, atom.positive);
        translator.nlsat.nlsat_mut().add_clause(vec![lit]);
    }

    match translator.nlsat.solve() {
        SolverResult::Sat if sat_is_trustworthy => {
            let model = extract_nia_model(&translator);
            Some(NlDispatchResult::sat_with(model))
        }
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Sat | SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

/// Map NIA poly-var indices back to TermIds via the translator cache.
fn extract_nia_model(translator: &TermPolyTranslator<'_>) -> HashMap<TermId, BigRational> {
    let mut out = HashMap::new();
    let Some(nlsat_model) = translator.nlsat.nlsat().get_model() else {
        return out;
    };
    for (&term, &poly_var) in translator.var_cache() {
        if let Some(val) = nlsat_model.arith_value(poly_var) {
            out.insert(term, val.clone());
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// NRA dispatch (real arithmetic)
// ─────────────────────────────────────────────────────────────────────────────

struct RealPolyTranslator<'a> {
    manager: &'a TermManager,
    nlsat: &'a mut NlsatSolver,
    var_cache: HashMap<TermId, u32>,
}

impl<'a> RealPolyTranslator<'a> {
    fn new(manager: &'a TermManager, nlsat: &'a mut NlsatSolver) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
        }
    }

    fn translate(&mut self, term_id: TermId) -> Option<Polynomial> {
        let term = self.manager.get(term_id)?;
        match &term.kind.clone() {
            TermKind::IntConst(n) => {
                Some(Polynomial::constant(BigRational::from_integer(n.clone())))
            }
            TermKind::RealConst(r) => {
                let big = BigRational::new(
                    BigInt::from(r.numer().to_i64().unwrap_or(0)),
                    BigInt::from(r.denom().to_i64().unwrap_or(1)),
                );
                Some(Polynomial::constant(big))
            }
            TermKind::Var(_) => {
                let v = self.get_or_create_var(term_id);
                Some(Polynomial::from_var(v))
            }
            TermKind::Neg(inner) => {
                let p = self.translate(*inner)?;
                Some(Polynomial::neg(&p))
            }
            TermKind::Add(args) => {
                let mut acc = Polynomial::zero();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::add(&acc, &p);
                }
                Some(acc)
            }
            TermKind::Sub(lhs, rhs) => {
                let lp = self.translate(*lhs)?;
                let rp = self.translate(*rhs)?;
                Some(Polynomial::sub(&lp, &rp))
            }
            TermKind::Mul(args) => {
                let mut acc = Polynomial::one();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::mul(&acc, &p);
                }
                Some(acc)
            }
            TermKind::Select(_, _) | TermKind::Apply { .. } => {
                let term = self.manager.get(term_id)?;
                let int_s = self.manager.sorts.int_sort;
                let real_s = self.manager.sorts.real_sort;
                if term.sort != int_s && term.sort != real_s {
                    return None;
                }
                let v = self.get_or_create_var(term_id);
                Some(Polynomial::from_var(v))
            }
            _ => None,
        }
    }

    fn get_or_create_var(&mut self, term_id: TermId) -> u32 {
        if let Some(&v) = self.var_cache.get(&term_id) {
            return v;
        }
        let v = self.nlsat.new_arith_var();
        self.var_cache.insert(term_id, v);
        v
    }

    fn var_cache(&self) -> &HashMap<TermId, u32> {
        &self.var_cache
    }
}

/// Map NRA poly-var indices back to TermIds via the translator cache.
fn extract_nra_model(translator: &RealPolyTranslator<'_>) -> HashMap<TermId, BigRational> {
    let mut out = HashMap::new();
    let Some(nlsat_model) = translator.nlsat.get_model() else {
        return out;
    };
    for (&term, &poly_var) in translator.var_cache() {
        if let Some(val) = nlsat_model.arith_value(poly_var) {
            out.insert(term, val.clone());
        }
    }
    out
}

/// Real-arithmetic analogue of [`extract_poly_atoms`]. See its documentation
/// for the meaning of `incomplete`.
fn extract_real_poly_atoms(
    term_id: TermId,
    manager: &TermManager,
    translator: &mut RealPolyTranslator<'_>,
    out: &mut Vec<PolyAtom>,
    incomplete: &mut bool,
) {
    let Some(term) = manager.get(term_id) else {
        *incomplete = true;
        return;
    };
    match &term.kind.clone() {
        TermKind::Eq(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Eq,
                    positive: true,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Lt(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Le(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Gt(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::Ge(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
            } else {
                *incomplete = true;
            }
        }
        TermKind::And(args) => {
            for &arg in args.iter() {
                extract_real_poly_atoms(arg, manager, translator, out, incomplete);
            }
        }
        _ => {
            *incomplete = true;
        }
    }
}

/// Dispatch nonlinear real arithmetic assertions to `NlsatSolver`.
pub fn dispatch_nra_constraints(
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<NlDispatchResult> {
    let has_nl = assertions.iter().any(|&a| term_is_nonlinear(a, manager));
    if !has_nl {
        return None;
    }

    let mut nlsat = NlsatSolver::new();
    let mut translator = RealPolyTranslator::new(manager, &mut nlsat);

    let mut poly_atoms: Vec<PolyAtom> = Vec::new();
    let mut incomplete = false;
    for &assertion in assertions {
        extract_real_poly_atoms(
            assertion,
            manager,
            &mut translator,
            &mut poly_atoms,
            &mut incomplete,
        );
    }

    if poly_atoms.is_empty() {
        return None;
    }

    let unsat_is_trustworthy = poly_atoms.iter().all(|atom| atom.kind != AtomKind::Eq);
    // See `dispatch_nia_constraints`: trusting Sat under a dropped (relaxed)
    // constraint is unsound, so only accept Sat when extraction was complete.
    let sat_is_trustworthy = !incomplete;

    for atom in &poly_atoms {
        let atom_id = translator.nlsat.new_ineq_atom(atom.poly.clone(), atom.kind);
        let lit = translator.nlsat.atom_literal(atom_id, atom.positive);
        translator.nlsat.add_clause(vec![lit]);
    }

    match translator.nlsat.solve() {
        SolverResult::Sat if sat_is_trustworthy => {
            let model = extract_nra_model(&translator);
            Some(NlDispatchResult::sat_with(model))
        }
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Sat | SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NlsatTheory – Theory trait wrapper
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
struct NlsatContextState {
    level: usize,
}

enum NlsatSolverWrapper {
    Real(NlsatSolver),
    Integer(NiaSolver),
}

impl core::fmt::Debug for NlsatSolverWrapper {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Real(_) => write!(f, "NlsatSolverWrapper::Real(..)"),
            Self::Integer(_) => write!(f, "NlsatSolverWrapper::Integer(..)"),
        }
    }
}

impl NlsatSolverWrapper {
    fn new(integer: bool) -> Self {
        if integer {
            Self::Integer(NiaSolver::new())
        } else {
            Self::Real(NlsatSolver::new())
        }
    }

    fn solve(&mut self) -> SolverResult {
        match self {
            Self::Real(s) => s.solve(),
            Self::Integer(s) => s.solve(),
        }
    }
}

/// NLSAT Theory Solver for nonlinear arithmetic.
///
/// Supports both real (QF_NRA) and integer (QF_NIA) nonlinear arithmetic.
/// Full constraint translation happens in `dispatch_nia_constraints` /
/// `dispatch_nra_constraints`; this wrapper integrates with the `Theory` trait.
#[derive(Debug)]
pub struct NlsatTheory {
    solver: NlsatSolverWrapper,
    context_stack: Vec<NlsatContextState>,
    is_integer: bool,
    last_result: Option<SolverResult>,
    asserted_terms: Vec<TermId>,
}

impl NlsatTheory {
    /// Create a new NLSAT theory solver.
    ///
    /// * `integer` – true for QF_NIA, false for QF_NRA.
    pub fn new(integer: bool) -> Self {
        Self {
            solver: NlsatSolverWrapper::new(integer),
            context_stack: Vec::new(),
            is_integer: integer,
            last_result: None,
            asserted_terms: Vec::new(),
        }
    }
}

impl Theory for NlsatTheory {
    fn id(&self) -> TheoryId {
        if self.is_integer {
            TheoryId::NIA
        } else {
            TheoryId::NRA
        }
    }

    fn name(&self) -> &str {
        if self.is_integer { "NIA" } else { "NRA" }
    }

    fn can_handle(&self, _term: TermId) -> bool {
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        self.asserted_terms.push(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        self.asserted_terms.push(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        let result = self.solver.solve();
        self.last_result = Some(result);
        match result {
            SolverResult::Sat => Ok(TheoryResult::Sat),
            SolverResult::Unsat => {
                let conflict = self.asserted_terms.clone();
                Ok(TheoryResult::Unsat(conflict))
            }
            SolverResult::Unknown => Ok(TheoryResult::Unknown),
        }
    }

    fn push(&mut self) {
        self.context_stack.push(NlsatContextState {
            level: self.asserted_terms.len(),
        });
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            self.asserted_terms.truncate(state.level);
        }
    }

    fn reset(&mut self) {
        *self = Self::new(self.is_integer);
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        Vec::new()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Unit tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::ast::TermManager;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    // ── Theory trait tests ────────────────────────────────────────────────────

    #[test]
    fn test_nlsat_theory_new() {
        let theory_nia = NlsatTheory::new(true);
        assert_eq!(theory_nia.id(), TheoryId::NIA);
        assert_eq!(theory_nia.name(), "NIA");
        assert!(theory_nia.is_integer);

        let theory_nra = NlsatTheory::new(false);
        assert_eq!(theory_nra.id(), TheoryId::NRA);
        assert_eq!(theory_nra.name(), "NRA");
        assert!(!theory_nra.is_integer);
    }

    #[test]
    fn test_nlsat_theory_push_pop() {
        let mut theory = NlsatTheory::new(false);
        assert_eq!(theory.context_stack.len(), 0);
        theory.push();
        assert_eq!(theory.context_stack.len(), 1);
        theory.push();
        assert_eq!(theory.context_stack.len(), 2);
        theory.pop();
        assert_eq!(theory.context_stack.len(), 1);
        theory.pop();
        assert_eq!(theory.context_stack.len(), 0);
    }

    #[test]
    fn test_nlsat_theory_reset() {
        let mut theory = NlsatTheory::new(false);
        let term = TermId::new(1);
        let _ = theory.assert_true(term);
        assert!(!theory.asserted_terms.is_empty());
        theory.reset();
        assert!(theory.asserted_terms.is_empty());
        assert!(theory.context_stack.is_empty());
    }

    #[test]
    fn test_nlsat_theory_can_handle() {
        let theory = NlsatTheory::new(false);
        assert!(theory.can_handle(TermId::new(1)));
    }

    #[test]
    fn test_nlsat_theory_check_placeholder() {
        let mut theory = NlsatTheory::new(false);
        let result = theory.check().expect("check should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    // ── Translator unit tests ──────────────────────────────────────────────────

    #[test]
    fn test_translator_constant() {
        let mut manager = TermManager::new();
        let five = manager.mk_int(5);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(five).expect("constant should translate");
        assert!(poly.is_constant());
        assert_eq!(poly.constant_value(), rat(5));
    }

    #[test]
    fn test_translator_variable() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(x).expect("variable should translate");
        assert!(poly.is_linear());
        assert_eq!(poly.num_terms(), 1);
    }

    #[test]
    fn test_translator_add() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let sum = manager.mk_add(vec![x, y]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(sum).expect("add should translate");
        assert_eq!(poly.num_terms(), 2);
    }

    #[test]
    fn test_translator_mul_vars() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let product = manager.mk_mul(vec![x, y]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(product).expect("mul should translate");
        // x * y is a single monomial of degree 2
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 2);
    }

    #[test]
    fn test_translator_square() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(square).expect("x*x should translate");
        // x^2 — single term, degree 2
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 2);
    }

    #[test]
    fn test_translator_neg() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let neg_x = manager.mk_neg(x);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(neg_x).expect("neg should translate");
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.leading_coeff(), rat(-1));
    }

    #[test]
    fn test_translator_sub() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let two = manager.mk_int(2);
        let x_minus_2 = manager.mk_sub(x, two);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(x_minus_2).expect("sub should translate");
        // x - 2 → two terms: x and -2
        assert_eq!(poly.num_terms(), 2);
    }

    #[test]
    fn test_translator_triple_product() {
        // (* x y z) — degree-3 monomial
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let z = manager.mk_var("z", int_sort);
        let triple = manager.mk_mul(vec![x, y, z]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t
            .translate(triple)
            .expect("triple product should translate");
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 3);
    }

    #[test]
    fn test_translator_factored_product() {
        // (* (+ x 1) (- y 2)) → xy - 2x + y - 2
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let xp1 = manager.mk_add(vec![x, one]);
        let ym2 = manager.mk_sub(y, two);
        let product = manager.mk_mul(vec![xp1, ym2]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t
            .translate(product)
            .expect("factored product should translate");
        // (x+1)(y-2) = xy - 2x + y - 2  → 4 terms
        assert_eq!(poly.num_terms(), 4);
        assert_eq!(poly.total_degree(), 2);
    }

    // ── term_is_nonlinear tests ────────────────────────────────────────────────

    #[test]
    fn test_term_is_nonlinear_square() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        assert!(term_is_nonlinear(square, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_product_xy() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let xy = manager.mk_mul(vec![x, y]);
        assert!(term_is_nonlinear(xy, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_linear_is_false() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let three = manager.mk_int(3);
        let three_x = manager.mk_mul(vec![three, x]);
        assert!(!term_is_nonlinear(three_x, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_constant() {
        let mut manager = TermManager::new();
        let c = manager.mk_int(42);
        assert!(!term_is_nonlinear(c, &manager));
    }

    // ── dispatch integration tests ─────────────────────────────────────────────

    #[test]
    fn test_dispatch_nia_x_squared_eq_4_sat() {
        // x * x = 4 → SAT (x=2 or x=-2)
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let four = manager.mk_int(4);
        let eq = manager.mk_eq(square, four);
        let result = dispatch_nia_constraints(&[eq], &manager, true);
        // SAT or Unknown (unknown means solver fell through)
        assert!(
            matches!(result, Some(NlDispatchResult::Sat(_)) | None),
            "x*x=4 should be SAT or unknown, got {:?}",
            result
        );
    }

    #[test]
    fn test_dispatch_nia_x_squared_neg_unsat() {
        // x * x = -1 → UNSAT (no integer square is negative)
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let neg_one = manager.mk_int(-1);
        let eq = manager.mk_eq(square, neg_one);
        let result = dispatch_nia_constraints(&[eq], &manager, true);
        assert!(
            matches!(result, Some(NlDispatchResult::Unsat) | None),
            "x*x=-1 should be UNSAT or unknown, got {:?}",
            result
        );
    }

    #[test]
    fn test_dispatch_nra_x_squared_neg_unsat() {
        // x * x < 0 → UNSAT (no real square is negative)
        let mut manager = TermManager::new();
        let real_sort = manager.sorts.real_sort;
        let x = manager.mk_var("x", real_sort);
        let square = manager.mk_mul(vec![x, x]);
        let zero = manager.mk_int(0);
        let lt = manager.mk_lt(square, zero);
        let result = dispatch_nra_constraints(&[lt], &manager);
        assert!(
            matches!(result, Some(NlDispatchResult::Unsat) | None),
            "x*x<0 should be UNSAT or unknown, got {:?}",
            result
        );
    }
}
