//! Cooper's Algorithm for Presburger Arithmetic QE.
//!
//! Implements Cooper's method for quantifier elimination in linear
//! integer arithmetic (Presburger arithmetic).
//!
//! Given `∃x. φ(x)` with φ quantifier-free over linear integer arithmetic,
//! the procedure returns an equivalent quantifier-free formula in which `x`
//! no longer occurs. The construction follows the classic "minus infinity"
//! elimination (Cooper 1972; see also Bradley & Manna, *The Calculus of
//! Computation*, §7.3):
//!
//! 1. Normalise the matrix to negation normal form, tracking polarity.
//! 2. Isolate `x` in every literal and scale coefficients to a common
//!    absolute value `L` (`lcm` of all coefficients of `x`), introducing the
//!    global divisibility constraint `L | x` for the renamed unit-coefficient
//!    variable.
//! 3. Compute `δ = lcm` of all divisibility moduli.
//! 4. Return `⋁_{j=1}^{δ} φ_{-∞}(j)  ∨  ⋁_{b∈B} ⋁_{j=1}^{δ} φ(b + j)` where
//!    `φ_{-∞}` replaces each bound literal by its truth value as `x → -∞`,
//!    and `B` is the set of lower-bound boundary terms.
//!
//! Formulae that fall outside the supported linear-integer fragment (a
//! non-linear occurrence of `x`, `x` under an uninterpreted function, a real
//! sort, etc.) are reported as an explicit `Err` rather than silently
//! returning a wrong or unchanged result.

use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// Maximum period `δ` before Cooper elimination gives up (returns `Err`).
const MAX_DELTA: i64 = 100_000;
/// Maximum number of generated disjuncts before giving up (returns `Err`).
const MAX_DISJUNCTS: i64 = 500_000;

/// Cooper's algorithm QE engine.
pub struct CooperEliminator {
    /// Statistics
    stats: CooperStats,
}

/// Cooper elimination statistics.
#[derive(Debug, Clone, Default)]
pub struct CooperStats {
    /// Number of quantifiers eliminated
    pub quantifiers_eliminated: usize,
    /// Number of boundary test cases generated
    pub test_cases: usize,
    /// Number of infinity (minus-infinity period) tests generated
    pub infinity_tests: usize,
}

/// A relation `expr REL 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CmpRel {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl CmpRel {
    /// Logical negation of the relation.
    fn negate(self) -> Self {
        match self {
            CmpRel::Lt => CmpRel::Ge,
            CmpRel::Le => CmpRel::Gt,
            CmpRel::Gt => CmpRel::Le,
            CmpRel::Ge => CmpRel::Lt,
            CmpRel::Eq => CmpRel::Ne,
            CmpRel::Ne => CmpRel::Eq,
        }
    }

    /// Swap the roles of `<`/`>` and `≤`/`≥` (used when the coefficient of the
    /// eliminated variable is negative and the inequality is multiplied by -1).
    fn flip_lg(self) -> Self {
        match self {
            CmpRel::Lt => CmpRel::Gt,
            CmpRel::Le => CmpRel::Ge,
            CmpRel::Gt => CmpRel::Lt,
            CmpRel::Ge => CmpRel::Le,
            CmpRel::Eq => CmpRel::Eq,
            CmpRel::Ne => CmpRel::Ne,
        }
    }
}

/// A linear expression `x_coeff·x + Σ others + constant`, where `x` is the
/// variable being eliminated and `others` are opaque sub-terms (other
/// variables or `x`-free compound terms) keyed by their `TermId`.
#[derive(Debug, Clone)]
struct LinearForm {
    x_coeff: BigInt,
    others: FxHashMap<TermId, BigInt>,
    constant: BigInt,
}

impl LinearForm {
    fn zero() -> Self {
        Self {
            x_coeff: BigInt::zero(),
            others: FxHashMap::default(),
            constant: BigInt::zero(),
        }
    }

    fn constant_val(c: BigInt) -> Self {
        Self {
            x_coeff: BigInt::zero(),
            others: FxHashMap::default(),
            constant: c,
        }
    }

    fn x() -> Self {
        Self {
            x_coeff: BigInt::one(),
            others: FxHashMap::default(),
            constant: BigInt::zero(),
        }
    }

    fn atom(id: TermId) -> Self {
        let mut others = FxHashMap::default();
        others.insert(id, BigInt::one());
        Self {
            x_coeff: BigInt::zero(),
            others,
            constant: BigInt::zero(),
        }
    }

    fn is_constant(&self) -> bool {
        self.x_coeff.is_zero() && self.others.values().all(BigInt::is_zero)
    }

    fn neg(mut self) -> Self {
        self.x_coeff = -self.x_coeff;
        self.constant = -self.constant;
        for v in self.others.values_mut() {
            *v = -core::mem::take(v);
        }
        self
    }

    fn add(mut self, other: Self) -> Self {
        self.x_coeff += other.x_coeff;
        self.constant += other.constant;
        for (k, v) in other.others {
            let entry = self.others.entry(k).or_insert_with(BigInt::zero);
            *entry += v;
        }
        self
    }

    fn sub(self, other: Self) -> Self {
        self.add(other.neg())
    }

    fn scale(mut self, k: &BigInt) -> Self {
        self.x_coeff *= k;
        self.constant *= k;
        for v in self.others.values_mut() {
            *v *= k;
        }
        self
    }
}

/// Intermediate boolean tree, produced before coefficient normalisation.
enum Raw {
    And(Vec<Raw>),
    Or(Vec<Raw>),
    Const(bool),
    /// An `x`-free literal, kept verbatim.
    Free(TermId),
    /// A comparison `form REL 0` where `form` mentions `x`.
    Cmp {
        form: LinearForm,
        rel: CmpRel,
    },
    /// A divisibility `modulus | form` (or its negation), `form` mentions `x`.
    Divis {
        modulus: BigInt,
        form: LinearForm,
        negated: bool,
    },
}

/// A normalised literal (coefficient of the eliminated variable is `±1`).
enum NLit {
    /// `bound < x`
    Lower(TermId),
    /// `x < bound`
    Upper(TermId),
    /// `modulus | (x + off)`
    Div { modulus: BigInt, off: TermId },
    /// `¬(modulus | (x + off))`
    NotDiv { modulus: BigInt, off: TermId },
    /// `x`-free literal.
    Free(TermId),
    /// Boolean constant.
    Const(bool),
}

/// Normalised boolean tree over [`NLit`].
enum Node {
    And(Vec<Node>),
    Or(Vec<Node>),
    Lit(NLit),
}

/// How to instantiate the eliminated variable when materialising a [`Node`].
enum XVal<'a> {
    /// Behaviour as `x → -∞`, with divisibilities evaluated at `x = j`.
    MinusInf(&'a BigInt),
    /// Substitute the (x-free) term `v` for `x`.
    At(TermId),
}

impl CooperEliminator {
    /// Create a new Cooper eliminator.
    pub fn new() -> Self {
        Self {
            stats: CooperStats::default(),
        }
    }

    /// Eliminate an existential quantifier: `∃var. formula(var)`.
    ///
    /// On success returns a quantifier-free formula equivalent to
    /// `∃var. formula` in which `var` does not occur. Returns `Err` for
    /// formulae outside the supported linear-integer fragment (soundness is
    /// preserved: no wrong or `var`-containing result is ever returned as
    /// `Ok`).
    pub fn eliminate_exists(
        &mut self,
        var: String,
        formula: TermId,
        tm: &mut TermManager,
    ) -> Result<TermId, String> {
        let x_spur = tm.intern_str(&var);

        // If x does not occur, ∃x.φ ≡ φ.
        if !self.mentions_x(formula, x_spur, tm) {
            self.stats.quantifiers_eliminated += 1;
            return Ok(formula);
        }

        // x must be of integer sort: the ±1 boundary offsets are only valid
        // over the integers.
        if !self.var_is_int(formula, x_spur, tm) {
            return Err("cooper: eliminated variable is not of integer sort".to_string());
        }

        // Pass 1: build the polarity-resolved boolean tree.
        let raw = self.build_raw(formula, x_spur, true, tm)?;

        // Compute L = lcm of |coefficient of x| over all x-literals.
        let mut lcm_coeff = BigInt::one();
        Self::collect_x_coeff_lcm(&raw, &mut lcm_coeff);

        // Pass 2: normalise coefficients to ±1 and build the Node tree.
        let mut node = self.convert(&raw, &lcm_coeff, tm)?;

        // Renaming L·x → u introduces the constraint L | u (off = 0).
        if lcm_coeff > BigInt::one() {
            let zero = tm.mk_int(0);
            node = Node::And(vec![
                node,
                Node::Lit(NLit::Div {
                    modulus: lcm_coeff.clone(),
                    off: zero,
                }),
            ]);
        }

        // δ = lcm of all divisibility moduli.
        let mut delta = BigInt::one();
        Self::collect_moduli_lcm(&node, &mut delta);

        if delta > BigInt::from(MAX_DELTA) {
            return Err("cooper: divisibility period too large to eliminate".to_string());
        }
        let delta_i64 = delta
            .to_i64()
            .ok_or_else(|| "cooper: divisibility period overflow".to_string())?;

        // Lower-bound boundary set.
        let mut bset = Vec::new();
        Self::collect_lower_bounds(&node, &mut bset);

        let total = delta_i64
            .checked_mul(bset.len() as i64 + 1)
            .ok_or_else(|| "cooper: elimination too large".to_string())?;
        if total > MAX_DISJUNCTS {
            return Err("cooper: elimination too large".to_string());
        }

        self.stats.quantifiers_eliminated += 1;

        let mut disjuncts: Vec<TermId> = Vec::new();

        // Minus-infinity part: ⋁_{j=1}^{δ} φ_{-∞}(j).
        for j in 1..=delta_i64 {
            let jb = BigInt::from(j);
            let t = self.materialize(&node, &XVal::MinusInf(&jb), tm);
            disjuncts.push(t);
            self.stats.infinity_tests += 1;
        }

        // Boundary part: ⋁_{b∈B} ⋁_{j=1}^{δ} φ(b + j).
        for &b in &bset {
            for j in 1..=delta_i64 {
                let jt = tm.mk_int(j);
                let v = tm.mk_add(vec![b, jt]);
                let t = self.materialize(&node, &XVal::At(v), tm);
                disjuncts.push(t);
                self.stats.test_cases += 1;
            }
        }

        Ok(tm.mk_or(disjuncts))
    }

    /// Whether `id` syntactically contains the eliminated variable.
    fn mentions_x(&self, id: TermId, x_spur: crate::interner::Spur, tm: &TermManager) -> bool {
        let Some(term) = tm.get(id) else {
            return false;
        };
        if let TermKind::Var(s) = term.kind {
            return s == x_spur;
        }
        let children = crate::ast::traversal::get_children(&term.kind);
        children.iter().any(|&c| self.mentions_x(c, x_spur, tm))
    }

    /// Whether the first occurrence of `x` has integer sort.
    fn var_is_int(&self, id: TermId, x_spur: crate::interner::Spur, tm: &mut TermManager) -> bool {
        let int_sort = {
            let z = tm.mk_int(0);
            tm.get(z).map(|t| t.sort)
        };
        let Some(int_sort) = int_sort else {
            return false;
        };
        self.find_var_sort(id, x_spur, tm) == Some(int_sort)
    }

    fn find_var_sort(
        &self,
        id: TermId,
        x_spur: crate::interner::Spur,
        tm: &TermManager,
    ) -> Option<crate::sort::SortId> {
        let term = tm.get(id)?;
        if let TermKind::Var(s) = term.kind {
            if s == x_spur {
                return Some(term.sort);
            }
            return None;
        }
        let children = crate::ast::traversal::get_children(&term.kind);
        for c in children {
            if let Some(sort) = self.find_var_sort(c, x_spur, tm) {
                return Some(sort);
            }
        }
        None
    }

    /// Parse `id` into a [`LinearForm`], or `None` if `x` occurs non-linearly.
    fn to_linear(
        &self,
        id: TermId,
        x_spur: crate::interner::Spur,
        tm: &TermManager,
    ) -> Option<LinearForm> {
        let term = tm.get(id)?;
        match &term.kind {
            TermKind::IntConst(n) => Some(LinearForm::constant_val(n.clone())),
            TermKind::Var(s) => {
                if *s == x_spur {
                    Some(LinearForm::x())
                } else {
                    Some(LinearForm::atom(id))
                }
            }
            TermKind::Neg(a) => Some(self.to_linear(*a, x_spur, tm)?.neg()),
            TermKind::Add(args) => {
                let mut acc = LinearForm::zero();
                for &a in args {
                    acc = acc.add(self.to_linear(a, x_spur, tm)?);
                }
                Some(acc)
            }
            TermKind::Sub(a, b) => {
                let la = self.to_linear(*a, x_spur, tm)?;
                let lb = self.to_linear(*b, x_spur, tm)?;
                Some(la.sub(lb))
            }
            TermKind::Mul(args) => {
                let mut const_prod = BigInt::one();
                let mut nonconst: Option<LinearForm> = None;
                for &a in args {
                    let lf = self.to_linear(a, x_spur, tm)?;
                    if lf.is_constant() {
                        const_prod *= lf.constant;
                    } else if nonconst.is_none() {
                        nonconst = Some(lf);
                    } else {
                        // product of two non-constant factors → non-linear
                        return None;
                    }
                }
                Some(match nonconst {
                    Some(lf) => lf.scale(&const_prod),
                    None => LinearForm::constant_val(const_prod),
                })
            }
            _ => {
                // Any other term: acceptable only if it does not mention x
                // (then it is an opaque atom); otherwise x occurs non-linearly.
                if self.mentions_x(id, x_spur, tm) {
                    None
                } else {
                    Some(LinearForm::atom(id))
                }
            }
        }
    }

    /// Build the polarity-resolved [`Raw`] tree.
    fn build_raw(
        &self,
        id: TermId,
        x_spur: crate::interner::Spur,
        positive: bool,
        tm: &mut TermManager,
    ) -> Result<Raw, String> {
        let kind = match tm.get(id) {
            Some(t) => t.kind.clone(),
            None => return Err("cooper: term not found".to_string()),
        };

        match kind {
            TermKind::True => Ok(Raw::Const(positive)),
            TermKind::False => Ok(Raw::Const(!positive)),
            TermKind::Not(a) => self.build_raw(a, x_spur, !positive, tm),
            TermKind::And(args) => {
                let mut subs = Vec::with_capacity(args.len());
                for a in args.iter() {
                    subs.push(self.build_raw(*a, x_spur, positive, tm)?);
                }
                Ok(if positive {
                    Raw::And(subs)
                } else {
                    Raw::Or(subs)
                })
            }
            TermKind::Or(args) => {
                let mut subs = Vec::with_capacity(args.len());
                for a in args.iter() {
                    subs.push(self.build_raw(*a, x_spur, positive, tm)?);
                }
                Ok(if positive {
                    Raw::Or(subs)
                } else {
                    Raw::And(subs)
                })
            }
            TermKind::Implies(a, b) => {
                // a → b  ≡  ¬a ∨ b
                let ra = self.build_raw(a, x_spur, !positive, tm)?;
                let rb = self.build_raw(b, x_spur, positive, tm)?;
                Ok(if positive {
                    Raw::Or(vec![ra, rb])
                } else {
                    Raw::And(vec![ra, rb])
                })
            }
            TermKind::Xor(a, b) => {
                if positive {
                    // (a ∧ ¬b) ∨ (¬a ∧ b)
                    let l = Raw::And(vec![
                        self.build_raw(a, x_spur, true, tm)?,
                        self.build_raw(b, x_spur, false, tm)?,
                    ]);
                    let r = Raw::And(vec![
                        self.build_raw(a, x_spur, false, tm)?,
                        self.build_raw(b, x_spur, true, tm)?,
                    ]);
                    Ok(Raw::Or(vec![l, r]))
                } else {
                    // a ↔ b  ≡  (a ∧ b) ∨ (¬a ∧ ¬b)
                    let l = Raw::And(vec![
                        self.build_raw(a, x_spur, true, tm)?,
                        self.build_raw(b, x_spur, true, tm)?,
                    ]);
                    let r = Raw::And(vec![
                        self.build_raw(a, x_spur, false, tm)?,
                        self.build_raw(b, x_spur, false, tm)?,
                    ]);
                    Ok(Raw::Or(vec![l, r]))
                }
            }
            TermKind::Ite(c, t, e) => {
                // (c ∧ t) ∨ (¬c ∧ e), with polarity applied to the branches.
                let l = Raw::And(vec![
                    self.build_raw(c, x_spur, true, tm)?,
                    self.build_raw(t, x_spur, positive, tm)?,
                ]);
                let r = Raw::And(vec![
                    self.build_raw(c, x_spur, false, tm)?,
                    self.build_raw(e, x_spur, positive, tm)?,
                ]);
                Ok(Raw::Or(vec![l, r]))
            }
            TermKind::Lt(a, b) => self.classify_cmp(id, a, b, CmpRel::Lt, x_spur, positive, tm),
            TermKind::Le(a, b) => self.classify_cmp(id, a, b, CmpRel::Le, x_spur, positive, tm),
            TermKind::Gt(a, b) => self.classify_cmp(id, a, b, CmpRel::Gt, x_spur, positive, tm),
            TermKind::Ge(a, b) => self.classify_cmp(id, a, b, CmpRel::Ge, x_spur, positive, tm),
            TermKind::Eq(a, b) => self.classify_cmp(id, a, b, CmpRel::Eq, x_spur, positive, tm),
            _ => {
                // Any other atom.
                if self.mentions_x(id, x_spur, tm) {
                    Err("cooper: unsupported term mentioning the eliminated variable".to_string())
                } else if positive {
                    Ok(Raw::Free(id))
                } else {
                    Ok(Raw::Free(tm.mk_not(id)))
                }
            }
        }
    }

    /// Classify a comparison atom `lhs REL rhs` (with `REL = rel0`).
    #[allow(clippy::too_many_arguments)]
    fn classify_cmp(
        &self,
        atom: TermId,
        lhs: TermId,
        rhs: TermId,
        rel0: CmpRel,
        x_spur: crate::interner::Spur,
        positive: bool,
        tm: &mut TermManager,
    ) -> Result<Raw, String> {
        // x-free comparison: keep verbatim (respecting polarity).
        if !self.mentions_x(atom, x_spur, tm) {
            return if positive {
                Ok(Raw::Free(atom))
            } else {
                Ok(Raw::Free(tm.mk_not(atom)))
            };
        }

        // Divisibility pattern: (mod E d) = 0  with d a positive constant.
        if rel0 == CmpRel::Eq
            && let Some((modulus, inner)) = self.match_mod_zero(lhs, rhs, tm)
        {
            let form = self
                .to_linear(inner, x_spur, tm)
                .ok_or_else(|| "cooper: non-linear divisibility argument".to_string())?;
            if form.x_coeff.is_zero() {
                // x cancelled inside the divisibility → x-free literal.
                return if positive {
                    Ok(Raw::Free(atom))
                } else {
                    Ok(Raw::Free(tm.mk_not(atom)))
                };
            }
            return Ok(Raw::Divis {
                modulus,
                form,
                negated: !positive,
            });
        }

        let lf_l = self
            .to_linear(lhs, x_spur, tm)
            .ok_or_else(|| "cooper: non-linear comparison operand".to_string())?;
        let lf_r = self
            .to_linear(rhs, x_spur, tm)
            .ok_or_else(|| "cooper: non-linear comparison operand".to_string())?;
        let form = lf_l.sub(lf_r);
        let rel = if positive { rel0 } else { rel0.negate() };

        if form.x_coeff.is_zero() {
            // x cancelled out: materialise the x-free comparison directly.
            let t = self.mk_linear_term(&form.others, &form.constant, tm);
            let zero = tm.mk_int(0);
            let lit = match rel {
                CmpRel::Lt => tm.mk_lt(t, zero),
                CmpRel::Le => tm.mk_le(t, zero),
                CmpRel::Gt => tm.mk_gt(t, zero),
                CmpRel::Ge => tm.mk_ge(t, zero),
                CmpRel::Eq => tm.mk_eq(t, zero),
                CmpRel::Ne => {
                    let e = tm.mk_eq(t, zero);
                    tm.mk_not(e)
                }
            };
            return Ok(Raw::Free(lit));
        }

        Ok(Raw::Cmp { form, rel })
    }

    /// Recognise `(mod E d) = 0` (in either argument order) with `d > 0`.
    fn match_mod_zero(&self, a: TermId, b: TermId, tm: &TermManager) -> Option<(BigInt, TermId)> {
        let try_side = |m: TermId, z: TermId| -> Option<(BigInt, TermId)> {
            let mt = tm.get(m)?;
            let TermKind::Mod(inner, d) = &mt.kind else {
                return None;
            };
            let dt = tm.get(*d)?;
            let TermKind::IntConst(dv) = &dt.kind else {
                return None;
            };
            if dv <= &BigInt::zero() {
                return None;
            }
            let zt = tm.get(z)?;
            if let TermKind::IntConst(zv) = &zt.kind
                && zv.is_zero()
            {
                return Some((dv.clone(), *inner));
            }
            None
        };
        try_side(a, b).or_else(|| try_side(b, a))
    }

    /// Materialise a linear combination `Σ others + constant` as a term (the
    /// eliminated variable is guaranteed absent from `others`).
    fn mk_linear_term(
        &self,
        others: &FxHashMap<TermId, BigInt>,
        constant: &BigInt,
        tm: &mut TermManager,
    ) -> TermId {
        let mut entries: Vec<(TermId, BigInt)> = others
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
                let c = tm.mk_int(coeff);
                parts.push(tm.mk_mul(vec![c, atom]));
            }
        }
        if !constant.is_zero() || parts.is_empty() {
            let c = tm.mk_int(constant.clone());
            parts.push(c);
        }
        if parts.len() == 1 {
            parts[0]
        } else {
            tm.mk_add(parts)
        }
    }

    /// `lcm` accumulation over all `x`-coefficients in a [`Raw`] tree.
    fn collect_x_coeff_lcm(raw: &Raw, acc: &mut BigInt) {
        match raw {
            Raw::And(subs) | Raw::Or(subs) => {
                for s in subs {
                    Self::collect_x_coeff_lcm(s, acc);
                }
            }
            Raw::Cmp { form, .. } | Raw::Divis { form, .. } => {
                if !form.x_coeff.is_zero() {
                    *acc = acc.lcm(&form.x_coeff.abs());
                }
            }
            Raw::Const(_) | Raw::Free(_) => {}
        }
    }

    /// Convert a [`Raw`] tree into a normalised [`Node`] tree, scaling every
    /// `x`-literal so the coefficient of `x` becomes `±1` (with `|x_coeff| = L`
    /// renamed to the unit variable `u`).
    fn convert(&self, raw: &Raw, lcm_coeff: &BigInt, tm: &mut TermManager) -> Result<Node, String> {
        match raw {
            Raw::And(subs) => {
                let mut out = Vec::with_capacity(subs.len());
                for s in subs {
                    out.push(self.convert(s, lcm_coeff, tm)?);
                }
                Ok(Node::And(out))
            }
            Raw::Or(subs) => {
                let mut out = Vec::with_capacity(subs.len());
                for s in subs {
                    out.push(self.convert(s, lcm_coeff, tm)?);
                }
                Ok(Node::Or(out))
            }
            Raw::Const(b) => Ok(Node::Lit(NLit::Const(*b))),
            Raw::Free(t) => Ok(Node::Lit(NLit::Free(*t))),
            Raw::Cmp { form, rel } => self.convert_cmp(form, *rel, lcm_coeff, tm),
            Raw::Divis {
                modulus,
                form,
                negated,
            } => self.convert_divis(modulus, form, *negated, lcm_coeff, tm),
        }
    }

    fn convert_cmp(
        &self,
        form: &LinearForm,
        rel: CmpRel,
        lcm_coeff: &BigInt,
        tm: &mut TermManager,
    ) -> Result<Node, String> {
        let c = &form.x_coeff;
        let m = lcm_coeff / c.abs();
        let scaled = form.clone().scale(&m);
        let sign_pos = !c.is_negative();

        // rest' = scaled form without the x term (materialised).
        let rest = self.mk_linear_term(&scaled.others, &scaled.constant, tm);

        // base = threshold value for x, eff = orientation relation.
        let (base, eff) = if sign_pos {
            (tm.mk_neg(rest), rel)
        } else {
            (rest, rel.flip_lg())
        };

        let node = match eff {
            CmpRel::Lt => Node::Lit(NLit::Upper(base)),
            CmpRel::Le => {
                let b = self.shift(base, 1, tm);
                Node::Lit(NLit::Upper(b))
            }
            CmpRel::Gt => Node::Lit(NLit::Lower(base)),
            CmpRel::Ge => {
                let b = self.shift(base, -1, tm);
                Node::Lit(NLit::Lower(b))
            }
            CmpRel::Eq => {
                let lo = self.shift(base, -1, tm);
                let hi = self.shift(base, 1, tm);
                Node::And(vec![Node::Lit(NLit::Lower(lo)), Node::Lit(NLit::Upper(hi))])
            }
            CmpRel::Ne => Node::Or(vec![
                Node::Lit(NLit::Upper(base)),
                Node::Lit(NLit::Lower(base)),
            ]),
        };
        Ok(node)
    }

    fn convert_divis(
        &self,
        modulus: &BigInt,
        form: &LinearForm,
        negated: bool,
        lcm_coeff: &BigInt,
        tm: &mut TermManager,
    ) -> Result<Node, String> {
        let c = &form.x_coeff;
        let m = lcm_coeff / c.abs();
        let scaled = form.clone().scale(&m);
        let new_modulus = modulus * &m;
        let sign_pos = !c.is_negative();

        // off = sign · rest'   (so that new_modulus | (u + off)).
        let rest = self.mk_linear_term(&scaled.others, &scaled.constant, tm);
        let off = if sign_pos { rest } else { tm.mk_neg(rest) };

        Ok(Node::Lit(if negated {
            NLit::NotDiv {
                modulus: new_modulus,
                off,
            }
        } else {
            NLit::Div {
                modulus: new_modulus,
                off,
            }
        }))
    }

    /// Build `term + k` (with `k` a small integer offset).
    fn shift(&self, term: TermId, k: i64, tm: &mut TermManager) -> TermId {
        if k == 0 {
            return term;
        }
        let kt = tm.mk_int(k);
        tm.mk_add(vec![term, kt])
    }

    /// `lcm` accumulation over all divisibility moduli in a [`Node`] tree.
    fn collect_moduli_lcm(node: &Node, acc: &mut BigInt) {
        match node {
            Node::And(subs) | Node::Or(subs) => {
                for s in subs {
                    Self::collect_moduli_lcm(s, acc);
                }
            }
            Node::Lit(NLit::Div { modulus, .. }) | Node::Lit(NLit::NotDiv { modulus, .. }) => {
                *acc = acc.lcm(modulus);
            }
            Node::Lit(_) => {}
        }
    }

    /// Collect all lower-bound boundary terms.
    fn collect_lower_bounds(node: &Node, out: &mut Vec<TermId>) {
        match node {
            Node::And(subs) | Node::Or(subs) => {
                for s in subs {
                    Self::collect_lower_bounds(s, out);
                }
            }
            Node::Lit(NLit::Lower(b)) => out.push(*b),
            Node::Lit(_) => {}
        }
    }

    /// Materialise a [`Node`] under a given instantiation of `x`.
    fn materialize(&self, node: &Node, xval: &XVal, tm: &mut TermManager) -> TermId {
        match node {
            Node::And(subs) => {
                let parts: Vec<TermId> =
                    subs.iter().map(|s| self.materialize(s, xval, tm)).collect();
                tm.mk_and(parts)
            }
            Node::Or(subs) => {
                let parts: Vec<TermId> =
                    subs.iter().map(|s| self.materialize(s, xval, tm)).collect();
                tm.mk_or(parts)
            }
            Node::Lit(lit) => self.materialize_lit(lit, xval, tm),
        }
    }

    fn materialize_lit(&self, lit: &NLit, xval: &XVal, tm: &mut TermManager) -> TermId {
        match lit {
            NLit::Lower(b) => match xval {
                XVal::MinusInf(_) => tm.mk_false(),
                XVal::At(v) => tm.mk_lt(*b, *v),
            },
            NLit::Upper(a) => match xval {
                XVal::MinusInf(_) => tm.mk_true(),
                XVal::At(v) => tm.mk_lt(*v, *a),
            },
            NLit::Div { modulus, off } => self.materialize_div(modulus, *off, xval, false, tm),
            NLit::NotDiv { modulus, off } => self.materialize_div(modulus, *off, xval, true, tm),
            NLit::Free(t) => *t,
            NLit::Const(b) => tm.mk_bool(*b),
        }
    }

    /// Materialise `modulus | (x + off)` (or its negation) at the given `x`.
    fn materialize_div(
        &self,
        modulus: &BigInt,
        off: TermId,
        xval: &XVal,
        negated: bool,
        tm: &mut TermManager,
    ) -> TermId {
        let x_term = match xval {
            XVal::MinusInf(j) => tm.mk_int((*j).clone()),
            XVal::At(v) => *v,
        };
        let arg = tm.mk_add(vec![x_term, off]);
        let m = tm.mk_int(modulus.clone());
        let modterm = tm.mk_mod(arg, m);
        let zero = tm.mk_int(0);
        let eq = tm.mk_eq(modterm, zero);
        if negated { tm.mk_not(eq) } else { eq }
    }

    /// Get statistics.
    pub fn stats(&self) -> &CooperStats {
        &self.stats
    }
}

impl Default for CooperEliminator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_var(tm: &mut TermManager, name: &str) -> TermId {
        let z = tm.mk_int(0);
        let int_sort = tm.get(z).expect("int const has a sort").sort;
        tm.mk_var(name, int_sort)
    }

    #[test]
    fn test_cooper_eliminator() {
        let eliminator = CooperEliminator::new();
        assert_eq!(eliminator.stats.quantifiers_eliminated, 0);
    }

    #[test]
    fn test_result_is_x_free_even_predicate() {
        // ∃x. 2*x = y   ≡   y even
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "x");
        let y = int_var(&mut tm, "y");
        let two = tm.mk_int(2);
        let two_x = tm.mk_mul(vec![two, x]);
        let phi = tm.mk_eq(two_x, y);

        let mut elim = CooperEliminator::new();
        let result = elim
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");

        // The quantified variable must no longer occur.
        let x_spur = tm.intern_str("x");
        assert!(
            !elim.mentions_x(result, x_spur, &tm),
            "eliminated variable x still occurs in the result"
        );
        // And it must not simply be the input formula.
        assert_ne!(result, phi, "result equals the input (unsound stub)");
    }

    /// Minimal ground evaluator over the fragment Cooper emits (no free vars).
    fn eval_ground(tm: &TermManager, id: TermId) -> bool {
        fn int(tm: &TermManager, id: TermId) -> i128 {
            match &tm.get(id).expect("term").kind {
                TermKind::IntConst(n) => n.to_string().parse::<i128>().expect("fits"),
                TermKind::Neg(a) => -int(tm, *a),
                TermKind::Add(args) => args.iter().map(|&a| int(tm, a)).sum(),
                TermKind::Sub(a, b) => int(tm, *a) - int(tm, *b),
                TermKind::Mul(args) => args.iter().map(|&a| int(tm, a)).product(),
                TermKind::Mod(a, b) => int(tm, *a).rem_euclid(int(tm, *b)),
                other => panic!("unexpected int term {other:?}"),
            }
        }
        match &tm.get(id).expect("term").kind {
            TermKind::True => true,
            TermKind::False => false,
            TermKind::Not(a) => !eval_ground(tm, *a),
            TermKind::And(args) => args.iter().all(|&a| eval_ground(tm, a)),
            TermKind::Or(args) => args.iter().any(|&a| eval_ground(tm, a)),
            TermKind::Lt(a, b) => int(tm, *a) < int(tm, *b),
            TermKind::Le(a, b) => int(tm, *a) <= int(tm, *b),
            TermKind::Gt(a, b) => int(tm, *a) > int(tm, *b),
            TermKind::Ge(a, b) => int(tm, *a) >= int(tm, *b),
            TermKind::Eq(a, b) => int(tm, *a) == int(tm, *b),
            other => panic!("unexpected bool term {other:?}"),
        }
    }

    #[test]
    fn test_bounded_true() {
        // ∃x. (2 < x) ∧ (x < 4)  is true (x = 3).
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "x");
        let two = tm.mk_int(2);
        let four = tm.mk_int(4);
        let c1 = tm.mk_lt(two, x);
        let c2 = tm.mk_lt(x, four);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut elim = CooperEliminator::new();
        let result = elim
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(!elim.mentions_x(result, x_spur, &tm), "x still present");
        assert!(eval_ground(&tm, result), "expected the result to be true");
    }

    #[test]
    fn test_bounded_false() {
        // ∃x. (4 < x) ∧ (x < 4)  is false (empty interval).
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "x");
        let four = tm.mk_int(4);
        let c1 = tm.mk_lt(four, x);
        let c2 = tm.mk_lt(x, four);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut elim = CooperEliminator::new();
        let result = elim
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(!elim.mentions_x(result, x_spur, &tm), "x still present");
        assert!(!eval_ground(&tm, result), "expected the result to be false");
    }

    #[test]
    fn test_nonlinear_is_rejected() {
        // ∃x. x*x = y  is outside the linear fragment → honest Err.
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "x");
        let y = int_var(&mut tm, "y");
        let xx = tm.mk_mul(vec![x, x]);
        let phi = tm.mk_eq(xx, y);

        let mut elim = CooperEliminator::new();
        let result = elim.eliminate_exists("x".to_string(), phi, &mut tm);
        assert!(
            result.is_err(),
            "non-linear input must be rejected, not faked"
        );
    }

    #[test]
    fn test_x_free_formula_returned() {
        // ∃x. (y < 3)  with x absent ≡ (y < 3).
        let mut tm = TermManager::new();
        let y = int_var(&mut tm, "y");
        let three = tm.mk_int(3);
        let phi = tm.mk_lt(y, three);

        let mut elim = CooperEliminator::new();
        let result = elim
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        assert_eq!(result, phi);
    }
}
