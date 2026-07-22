//! Shared linear real-arithmetic (LRA) primitives for quantifier elimination.
//!
//! The Ferrante–Rackoff and Loos–Weispfenning virtual-substitution eliminators
//! both operate on the same underlying object: a quantifier-free boolean
//! combination of linear comparison atoms over the reals. This module factors
//! out the machinery they share — linear-form parsing with exact rational
//! arithmetic, boundary/test-point construction, the `x → ±∞` limit rewrite,
//! and the infinitesimal `x → t + ε` virtual substitution — so each eliminator
//! only has to express its own test set.
//!
//! All internal arithmetic is carried out in exact [`BigRational`]; conversion
//! to the term representation's [`Rational64`] happens only when a constant is
//! materialised, and reports an honest `None`/`Err` on `i64` overflow rather
//! than silently truncating.
//!
//! Reference: Z3's `qe_arith.cpp` (linear real-arithmetic projection used by
//! `qe_lite`/`nlqsat`).

use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
use crate::prelude::FxHashMap;
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, ToPrimitive, Zero};

/// A comparison relation `expr REL 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rel {
    /// `< 0`
    Lt,
    /// `≤ 0`
    Le,
    /// `> 0`
    Gt,
    /// `≥ 0`
    Ge,
    /// `= 0`
    Eq,
    /// `≠ 0`
    Ne,
}

impl Rel {
    /// Logical negation of the relation (resolves polarity under `Not`).
    pub(crate) fn negate(self) -> Self {
        match self {
            Rel::Lt => Rel::Ge,
            Rel::Le => Rel::Gt,
            Rel::Gt => Rel::Le,
            Rel::Ge => Rel::Lt,
            Rel::Eq => Rel::Ne,
            Rel::Ne => Rel::Eq,
        }
    }

    /// Swap `<`/`>` and `≤`/`≥` (used when isolating `x` divides by a negative
    /// coefficient, which reverses the inequality direction).
    pub(crate) fn flip(self) -> Self {
        match self {
            Rel::Lt => Rel::Gt,
            Rel::Le => Rel::Ge,
            Rel::Gt => Rel::Lt,
            Rel::Ge => Rel::Le,
            Rel::Eq => Rel::Eq,
            Rel::Ne => Rel::Ne,
        }
    }
}

/// A linear form `x_coeff·x + Σ others + constant` with exact rational
/// coefficients. `others` maps an opaque, `x`-free sub-term to its coefficient.
#[derive(Debug, Clone)]
pub(crate) struct LinForm {
    /// Coefficient of the eliminated variable `x`.
    pub(crate) x_coeff: BigRational,
    /// Coefficients of the remaining (`x`-free) sub-terms.
    pub(crate) others: FxHashMap<TermId, BigRational>,
    /// Constant term.
    pub(crate) constant: BigRational,
}

impl LinForm {
    fn zero() -> Self {
        Self {
            x_coeff: BigRational::zero(),
            others: FxHashMap::default(),
            constant: BigRational::zero(),
        }
    }

    fn constant_val(c: BigRational) -> Self {
        Self {
            x_coeff: BigRational::zero(),
            others: FxHashMap::default(),
            constant: c,
        }
    }

    fn x() -> Self {
        Self {
            x_coeff: BigRational::one(),
            others: FxHashMap::default(),
            constant: BigRational::zero(),
        }
    }

    fn atom(id: TermId) -> Self {
        let mut others = FxHashMap::default();
        others.insert(id, BigRational::one());
        Self {
            x_coeff: BigRational::zero(),
            others,
            constant: BigRational::zero(),
        }
    }

    fn is_constant(&self) -> bool {
        self.x_coeff.is_zero() && self.others.values().all(BigRational::is_zero)
    }

    fn neg(mut self) -> Self {
        self.x_coeff = -self.x_coeff;
        self.constant = -self.constant;
        for v in self.others.values_mut() {
            *v = -core::mem::replace(v, BigRational::zero());
        }
        self
    }

    fn add(mut self, other: Self) -> Self {
        self.x_coeff += other.x_coeff;
        self.constant += other.constant;
        for (k, v) in other.others {
            let entry = self.others.entry(k).or_insert_with(BigRational::zero);
            *entry += v;
        }
        self
    }

    fn sub(self, other: Self) -> Self {
        self.add(other.neg())
    }

    fn scale(mut self, k: &BigRational) -> Self {
        self.x_coeff *= k;
        self.constant *= k;
        for v in self.others.values_mut() {
            *v *= k;
        }
        self
    }
}

/// A parsed comparison atom `x_coeff·x + Σ others + constant  REL  0` in which
/// the eliminated variable occurs with a non-zero coefficient.
#[derive(Debug, Clone)]
pub(crate) struct XAtom {
    /// Coefficient of `x` (guaranteed non-zero).
    pub(crate) x_coeff: BigRational,
    /// Coefficients of the remaining (`x`-free) sub-terms.
    pub(crate) others: FxHashMap<TermId, BigRational>,
    /// Constant term.
    pub(crate) constant: BigRational,
    /// The relation of `form REL 0`.
    pub(crate) rel: Rel,
}

/// Convert a [`Rational64`] to an exact [`BigRational`].
fn rational64_to_big(r: Rational64) -> BigRational {
    BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
}

/// Whether `id` syntactically mentions the eliminated variable `x`.
pub(crate) fn mentions_var(id: TermId, x: Spur, tm: &TermManager) -> bool {
    let Some(term) = tm.get(id) else {
        return false;
    };
    if let TermKind::Var(s) = term.kind {
        return s == x;
    }
    let children = crate::ast::traversal::get_children(&term.kind);
    children.iter().any(|&c| mentions_var(c, x, tm))
}

/// Sort of the first syntactic occurrence of `x` in `id`, if any.
pub(crate) fn find_var_sort(id: TermId, x: Spur, tm: &TermManager) -> Option<crate::sort::SortId> {
    let term = tm.get(id)?;
    if let TermKind::Var(s) = term.kind {
        return if s == x { Some(term.sort) } else { None };
    }
    let children = crate::ast::traversal::get_children(&term.kind);
    for c in children {
        if let Some(sort) = find_var_sort(c, x, tm) {
            return Some(sort);
        }
    }
    None
}

/// Parse `id` into a [`LinForm`] over `x`, or `None` if `x` occurs non-linearly
/// (e.g. `x*x`, `x` under an uninterpreted symbol) or the term is unsupported.
pub(crate) fn to_linear(id: TermId, x: Spur, tm: &TermManager) -> Option<LinForm> {
    let term = tm.get(id)?;
    match &term.kind {
        TermKind::IntConst(n) => Some(LinForm::constant_val(BigRational::from_integer(n.clone()))),
        TermKind::RealConst(r) => Some(LinForm::constant_val(rational64_to_big(*r))),
        TermKind::Var(s) => {
            if *s == x {
                Some(LinForm::x())
            } else {
                Some(LinForm::atom(id))
            }
        }
        TermKind::Neg(a) => Some(to_linear(*a, x, tm)?.neg()),
        TermKind::Add(args) => {
            let mut acc = LinForm::zero();
            for &a in args {
                acc = acc.add(to_linear(a, x, tm)?);
            }
            Some(acc)
        }
        TermKind::Sub(a, b) => {
            let la = to_linear(*a, x, tm)?;
            let lb = to_linear(*b, x, tm)?;
            Some(la.sub(lb))
        }
        TermKind::Mul(args) => {
            let mut const_prod = BigRational::one();
            let mut nonconst: Option<LinForm> = None;
            for &a in args {
                let lf = to_linear(a, x, tm)?;
                if lf.is_constant() {
                    const_prod *= lf.constant;
                } else if nonconst.is_none() {
                    nonconst = Some(lf);
                } else {
                    // Product of two non-constant factors → non-linear in x.
                    return None;
                }
            }
            Some(match nonconst {
                Some(lf) => lf.scale(&const_prod),
                None => LinForm::constant_val(const_prod),
            })
        }
        TermKind::Div(a, b) => {
            // Real division by a non-zero constant: `a / c`.
            let lb = to_linear(*b, x, tm)?;
            if !lb.is_constant() || lb.constant.is_zero() {
                return None;
            }
            let la = to_linear(*a, x, tm)?;
            let inv = lb.constant.recip();
            Some(la.scale(&inv))
        }
        _ => {
            // Any other term is acceptable only as an opaque atom that does not
            // mention `x`; otherwise `x` occurs in an unsupported position.
            if mentions_var(id, x, tm) {
                None
            } else {
                Some(LinForm::atom(id))
            }
        }
    }
}

/// Materialise a rational constant as a real term, or `None` on `i64` overflow.
pub(crate) fn mk_real_const(tm: &mut TermManager, r: &BigRational) -> Option<TermId> {
    let num = r.numer().to_i64()?;
    let den = r.denom().to_i64()?;
    Some(tm.mk_real(Rational64::new(num, den)))
}

/// A real zero constant.
fn zero_real(tm: &mut TermManager) -> TermId {
    tm.mk_real(Rational64::new(0, 1))
}

/// Materialise `Σ others + constant` (guaranteed `x`-free) as a real term, or
/// `None` if any coefficient overflows `i64`.
pub(crate) fn mk_lin_term(
    others: &FxHashMap<TermId, BigRational>,
    constant: &BigRational,
    tm: &mut TermManager,
) -> Option<TermId> {
    let mut entries: Vec<(TermId, BigRational)> = others
        .iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(k, v)| (*k, v.clone()))
        .collect();
    entries.sort_by_key(|(k, _)| k.0);

    let mut parts: Vec<TermId> = Vec::new();
    for (atom, coeff) in entries {
        if coeff.is_one() {
            parts.push(atom);
        } else {
            let c = mk_real_const(tm, &coeff)?;
            parts.push(tm.mk_mul(vec![c, atom]));
        }
    }
    if !constant.is_zero() || parts.is_empty() {
        let c = mk_real_const(tm, constant)?;
        parts.push(c);
    }
    Some(if parts.len() == 1 {
        parts[0]
    } else {
        tm.mk_add(parts)
    })
}

/// The boundary value `-（Σ others + constant) / x_coeff` of an atom (the point
/// at which its linear form equals zero), materialised as an `x`-free real term.
pub(crate) fn boundary_term(
    x_coeff: &BigRational,
    others: &FxHashMap<TermId, BigRational>,
    constant: &BigRational,
    tm: &mut TermManager,
) -> Option<TermId> {
    let factor = -x_coeff.recip(); // -1/c
    let scaled_others: FxHashMap<TermId, BigRational> =
        others.iter().map(|(k, v)| (*k, v * &factor)).collect();
    let scaled_const = constant * &factor;
    mk_lin_term(&scaled_others, &scaled_const, tm)
}

/// Emit a comparison `lhs REL rhs`.
fn emit_cmp(lhs: TermId, rhs: TermId, rel: Rel, tm: &mut TermManager) -> TermId {
    match rel {
        Rel::Lt => tm.mk_lt(lhs, rhs),
        Rel::Le => tm.mk_le(lhs, rhs),
        Rel::Gt => tm.mk_gt(lhs, rhs),
        Rel::Ge => tm.mk_ge(lhs, rhs),
        Rel::Eq => tm.mk_eq(lhs, rhs),
        Rel::Ne => {
            let e = tm.mk_eq(lhs, rhs);
            tm.mk_not(e)
        }
    }
}

/// Truth value of `form REL 0` when `form` tends to `+∞` (`to_pos_inf = true`)
/// or `-∞` (`to_pos_inf = false`).
fn inf_truth(rel: Rel, to_pos_inf: bool) -> bool {
    if to_pos_inf {
        matches!(rel, Rel::Gt | Rel::Ge | Rel::Ne)
    } else {
        matches!(rel, Rel::Lt | Rel::Le | Rel::Ne)
    }
}

/// Collect every comparison atom mentioning `x` into `out`, or return `Err` if
/// `x` appears in a position outside the supported linear fragment.
///
/// Atoms in which `x` cancels (zero net coefficient) are skipped: they are
/// `x`-free and contribute no boundary.
pub(crate) fn collect_x_atoms(
    formula: TermId,
    x: Spur,
    tm: &TermManager,
    out: &mut Vec<XAtom>,
) -> Result<(), String> {
    if !mentions_var(formula, x, tm) {
        return Ok(());
    }
    let Some(term) = tm.get(formula) else {
        return Err("lra: term not found".to_string());
    };
    match &term.kind {
        TermKind::Not(a) => collect_x_atoms(*a, x, tm, out),
        TermKind::And(args) | TermKind::Or(args) => {
            for &a in args {
                collect_x_atoms(a, x, tm, out)?;
            }
            Ok(())
        }
        TermKind::Implies(a, b) => {
            collect_x_atoms(*a, x, tm, out)?;
            collect_x_atoms(*b, x, tm, out)
        }
        TermKind::Xor(a, b) => {
            collect_x_atoms(*a, x, tm, out)?;
            collect_x_atoms(*b, x, tm, out)
        }
        TermKind::Ite(c, t, e) => {
            collect_x_atoms(*c, x, tm, out)?;
            collect_x_atoms(*t, x, tm, out)?;
            collect_x_atoms(*e, x, tm, out)
        }
        TermKind::Lt(a, b) => push_cmp_atom(*a, *b, Rel::Lt, x, tm, out),
        TermKind::Le(a, b) => push_cmp_atom(*a, *b, Rel::Le, x, tm, out),
        TermKind::Gt(a, b) => push_cmp_atom(*a, *b, Rel::Gt, x, tm, out),
        TermKind::Ge(a, b) => push_cmp_atom(*a, *b, Rel::Ge, x, tm, out),
        TermKind::Eq(a, b) => push_cmp_atom(*a, *b, Rel::Eq, x, tm, out),
        _ => Err("lra: unsupported term mentioning the eliminated variable".to_string()),
    }
}

fn push_cmp_atom(
    a: TermId,
    b: TermId,
    rel: Rel,
    x: Spur,
    tm: &TermManager,
    out: &mut Vec<XAtom>,
) -> Result<(), String> {
    let fa = to_linear(a, x, tm).ok_or("lra: non-linear comparison operand")?;
    let fb = to_linear(b, x, tm).ok_or("lra: non-linear comparison operand")?;
    let form = fa.sub(fb);
    if form.x_coeff.is_zero() {
        // `x` cancels out — the atom is effectively `x`-free.
        return Ok(());
    }
    out.push(XAtom {
        x_coeff: form.x_coeff,
        others: form.others,
        constant: form.constant,
        rel,
    });
    Ok(())
}

/// Rewrite `formula` to its truth value as `x → +∞` (`at_plus_inf = true`) or
/// `x → -∞` (`at_plus_inf = false`), producing an `x`-free equivalent of the
/// formula on the corresponding unbounded interval.
///
/// The limit commutes with the boolean connectives, so the rewrite is purely
/// structural: each comparison atom mentioning `x` collapses to a boolean
/// constant, while `x`-free atoms are preserved.
pub(crate) fn inf_rewrite(
    formula: TermId,
    x: Spur,
    at_plus_inf: bool,
    tm: &mut TermManager,
) -> Result<TermId, String> {
    if !mentions_var(formula, x, tm) {
        return Ok(formula);
    }
    let kind = tm.get(formula).ok_or("lra: term not found")?.kind.clone();
    match kind {
        TermKind::Not(a) => {
            let a = inf_rewrite(a, x, at_plus_inf, tm)?;
            Ok(tm.mk_not(a))
        }
        TermKind::And(args) => {
            let mut out = Vec::with_capacity(args.len());
            for a in args {
                out.push(inf_rewrite(a, x, at_plus_inf, tm)?);
            }
            Ok(tm.mk_and(out))
        }
        TermKind::Or(args) => {
            let mut out = Vec::with_capacity(args.len());
            for a in args {
                out.push(inf_rewrite(a, x, at_plus_inf, tm)?);
            }
            Ok(tm.mk_or(out))
        }
        TermKind::Implies(a, b) => {
            let a = inf_rewrite(a, x, at_plus_inf, tm)?;
            let b = inf_rewrite(b, x, at_plus_inf, tm)?;
            Ok(tm.mk_implies(a, b))
        }
        TermKind::Xor(a, b) => {
            let a = inf_rewrite(a, x, at_plus_inf, tm)?;
            let b = inf_rewrite(b, x, at_plus_inf, tm)?;
            Ok(tm.mk_xor(a, b))
        }
        TermKind::Ite(c, t, e) => {
            let c = inf_rewrite(c, x, at_plus_inf, tm)?;
            let t = inf_rewrite(t, x, at_plus_inf, tm)?;
            let e = inf_rewrite(e, x, at_plus_inf, tm)?;
            Ok(tm.mk_ite(c, t, e))
        }
        TermKind::Lt(a, b) => atom_inf(a, b, Rel::Lt, x, at_plus_inf, tm),
        TermKind::Le(a, b) => atom_inf(a, b, Rel::Le, x, at_plus_inf, tm),
        TermKind::Gt(a, b) => atom_inf(a, b, Rel::Gt, x, at_plus_inf, tm),
        TermKind::Ge(a, b) => atom_inf(a, b, Rel::Ge, x, at_plus_inf, tm),
        TermKind::Eq(a, b) => atom_inf(a, b, Rel::Eq, x, at_plus_inf, tm),
        _ => Err("lra: unsupported term mentioning the eliminated variable".to_string()),
    }
}

fn atom_inf(
    a: TermId,
    b: TermId,
    rel: Rel,
    x: Spur,
    at_plus_inf: bool,
    tm: &mut TermManager,
) -> Result<TermId, String> {
    let fa = to_linear(a, x, tm).ok_or("lra: non-linear comparison operand")?;
    let fb = to_linear(b, x, tm).ok_or("lra: non-linear comparison operand")?;
    let form = fa.sub(fb);
    if form.x_coeff.is_zero() {
        let rest = mk_lin_term(&form.others, &form.constant, tm)
            .ok_or("lra: coefficient too large to eliminate")?;
        let zero = zero_real(tm);
        return Ok(emit_cmp(rest, zero, rel, tm));
    }
    // `form` tends to +∞ when its `x`-coefficient sign agrees with the
    // direction in which `x` grows.
    let to_pos_inf = at_plus_inf == form.x_coeff.is_positive();
    Ok(tm.mk_bool(inf_truth(rel, to_pos_inf)))
}

/// Virtually substitute `x := s + ε` (with `ε` a positive infinitesimal) into
/// `formula`, eliminating `ε` symbolically through the Loos–Weispfenning atom
/// rewriting rules. The result is an `x`-free (and `ε`-free) formula equivalent
/// to `φ` holding on an open interval immediately above `s`.
pub(crate) fn eps_rewrite(
    formula: TermId,
    x: Spur,
    s: TermId,
    tm: &mut TermManager,
) -> Result<TermId, String> {
    if !mentions_var(formula, x, tm) {
        return Ok(formula);
    }
    let kind = tm.get(formula).ok_or("lra: term not found")?.kind.clone();
    match kind {
        TermKind::Not(a) => {
            let a = eps_rewrite(a, x, s, tm)?;
            Ok(tm.mk_not(a))
        }
        TermKind::And(args) => {
            let mut out = Vec::with_capacity(args.len());
            for a in args {
                out.push(eps_rewrite(a, x, s, tm)?);
            }
            Ok(tm.mk_and(out))
        }
        TermKind::Or(args) => {
            let mut out = Vec::with_capacity(args.len());
            for a in args {
                out.push(eps_rewrite(a, x, s, tm)?);
            }
            Ok(tm.mk_or(out))
        }
        TermKind::Implies(a, b) => {
            let a = eps_rewrite(a, x, s, tm)?;
            let b = eps_rewrite(b, x, s, tm)?;
            Ok(tm.mk_implies(a, b))
        }
        TermKind::Xor(a, b) => {
            let a = eps_rewrite(a, x, s, tm)?;
            let b = eps_rewrite(b, x, s, tm)?;
            Ok(tm.mk_xor(a, b))
        }
        TermKind::Ite(c, t, e) => {
            let c = eps_rewrite(c, x, s, tm)?;
            let t = eps_rewrite(t, x, s, tm)?;
            let e = eps_rewrite(e, x, s, tm)?;
            Ok(tm.mk_ite(c, t, e))
        }
        TermKind::Lt(a, b) => atom_eps(a, b, Rel::Lt, x, s, tm),
        TermKind::Le(a, b) => atom_eps(a, b, Rel::Le, x, s, tm),
        TermKind::Gt(a, b) => atom_eps(a, b, Rel::Gt, x, s, tm),
        TermKind::Ge(a, b) => atom_eps(a, b, Rel::Ge, x, s, tm),
        TermKind::Eq(a, b) => atom_eps(a, b, Rel::Eq, x, s, tm),
        _ => Err("lra: unsupported term mentioning the eliminated variable".to_string()),
    }
}

fn atom_eps(
    a: TermId,
    b: TermId,
    rel: Rel,
    x: Spur,
    s: TermId,
    tm: &mut TermManager,
) -> Result<TermId, String> {
    let fa = to_linear(a, x, tm).ok_or("lra: non-linear comparison operand")?;
    let fb = to_linear(b, x, tm).ok_or("lra: non-linear comparison operand")?;
    let form = fa.sub(fb); // c·x + rest
    let c = form.x_coeff.clone();
    let rest = mk_lin_term(&form.others, &form.constant, tm)
        .ok_or("lra: coefficient too large to eliminate")?;
    let zero = zero_real(tm);
    if c.is_zero() {
        // `x`-free atom: value is `rest REL 0`, unaffected by the ε shift.
        return Ok(emit_cmp(rest, zero, rel, tm));
    }
    // q = form[x := s] = c·s + rest, so form[x := s+ε] = q + c·ε.
    let c_term = mk_real_const(tm, &c).ok_or("lra: coefficient too large to eliminate")?;
    let cs = tm.mk_mul(vec![c_term, s]);
    let q = tm.mk_add(vec![cs, rest]);
    let c_pos = c.is_positive();
    // Evaluate `q + c·ε REL 0` in the limit ε → 0⁺ (c is a known non-zero
    // rational, so the sign of the infinitesimal term is decided statically).
    let out = match (rel, c_pos) {
        (Rel::Lt, true) => emit_cmp(q, zero, Rel::Lt, tm),
        (Rel::Lt, false) => emit_cmp(q, zero, Rel::Le, tm),
        (Rel::Le, true) => emit_cmp(q, zero, Rel::Lt, tm),
        (Rel::Le, false) => emit_cmp(q, zero, Rel::Le, tm),
        (Rel::Gt, true) => emit_cmp(q, zero, Rel::Ge, tm),
        (Rel::Gt, false) => emit_cmp(q, zero, Rel::Gt, tm),
        (Rel::Ge, true) => emit_cmp(q, zero, Rel::Ge, tm),
        (Rel::Ge, false) => emit_cmp(q, zero, Rel::Gt, tm),
        // c·ε ≠ 0 is infinitesimal, so equality can never hold on an interval.
        (Rel::Eq, _) => tm.mk_false(),
        (Rel::Ne, _) => tm.mk_true(),
    };
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn real_var(tm: &mut TermManager, name: &str) -> TermId {
        let real_sort = tm.sorts.real_sort;
        tm.mk_var(name, real_sort)
    }

    #[test]
    fn to_linear_parses_affine_term() {
        // 3*x - 5  over the reals.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let three = tm.mk_real(Rational64::new(3, 1));
        let three_x = tm.mk_mul(vec![three, x]);
        let five = tm.mk_real(Rational64::new(5, 1));
        let expr = tm.mk_sub(three_x, five);

        let x_spur = tm.intern_str("x");
        let form = to_linear(expr, x_spur, &tm).expect("linear");
        assert_eq!(form.x_coeff, BigRational::from_integer(BigInt::from(3)));
        assert_eq!(form.constant, BigRational::from_integer(BigInt::from(-5)));
        assert!(form.others.is_empty());
    }

    #[test]
    fn to_linear_rejects_nonlinear() {
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let xx = tm.mk_mul(vec![x, x]);
        let x_spur = tm.intern_str("x");
        assert!(to_linear(xx, x_spur, &tm).is_none());
    }

    #[test]
    fn inf_truth_table() {
        assert!(inf_truth(Rel::Lt, false));
        assert!(!inf_truth(Rel::Lt, true));
        assert!(inf_truth(Rel::Gt, true));
        assert!(!inf_truth(Rel::Gt, false));
        assert!(!inf_truth(Rel::Eq, true));
        assert!(!inf_truth(Rel::Eq, false));
        assert!(inf_truth(Rel::Ne, true));
        assert!(inf_truth(Rel::Ne, false));
    }
}
