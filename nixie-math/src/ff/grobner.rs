//! Gröbner bases over 𝔽_p (`docs/FF_THEORY_DESIGN.md` §4.5–4.7): Buchberger
//! with the Gebauer–Möller pair criteria and the normal selection strategy,
//! degrevlex for the UNSAT test; a **cofactor tracer** threading
//! `g = Σ cᵢ fᵢ` through every S-polynomial and reduction step; the
//! zero-dimensionality test; and minimal polynomials of variables modulo a
//! zero-dimensional ideal (Krylov/Gaussian elimination over the quotient's
//! standard monomials).
//!
//! ## Budget, not wall-clock
//!
//! The step counter counts S-pairs processed and reduction steps
//! performed. Exceeding the budget surfaces as [`GrobnerError::Budget`] —
//! never a silently wrong basis, and never a seconds-based cutoff
//! (determinism requirement, `AGENTS.md`).
//!
//! ## Determinism
//!
//! Variable order and generator order fix the entire computation. Neither
//! is derived from hash-map iteration: every list fed to the loop is
//! monomial- or index-sorted.
//!
//! ## Soundness of the tracer
//!
//! Every operation on a [`TracedPoly`] transforms the polynomial and the
//! cofactor row by the *same* linear combination, so the identity
//! `poly = Σ cofactors[i] · inputs[i]` is an invariant. It is re-verified
//! by an independent pass in tests (and in certified mode), because a
//! tracer that is asserted but never checked is exactly the
//! "unjustified conflict" the soundness rules forbid.

use super::field::{FieldCtx, Limbs};
use super::poly::{MPoly, cmp_monomials, monomial_div, monomial_lcm};
use crate::polynomial::{Monomial, MonomialOrder, Var};
use num_bigint::BigUint;

/// The degrevlex order used for the (UNSAT-oriented) basis computations —
/// the cheapest order for the `1 ∈ I` test.
pub const DEGREVLEX: MonomialOrder = MonomialOrder::GRevLex;

/// Why a basis computation stopped without a definitive answer. This must
/// be carried in the return type, not inferred (`AGENTS.md` → *No
/// fabrication*): a budget-cut basis is not a basis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum GrobnerError {
    /// The S-pair/reduction budget ran out.
    #[error("Gröbner basis budget exhausted")]
    Budget,
}

/// A step budget for basis computations: S-pairs processed + reduction
/// steps. Tick counter, never wall-clock.
#[derive(Debug, Clone)]
pub struct GrobnerBudget {
    remaining: u64,
}

impl GrobnerBudget {
    /// A budget of `n` steps.
    #[must_use]
    pub fn new(n: u64) -> Self {
        Self { remaining: n }
    }

    fn charge(&mut self, units: u64) -> Result<(), GrobnerError> {
        if units > self.remaining {
            return Err(GrobnerError::Budget);
        }
        self.remaining -= units;
        Ok(())
    }
}

/// One basis element with its cofactors against the *input* generators:
/// `poly = Σ cofactors[i] · inputs[i]`. This is the tracer's payload — the
/// checkable object that turns "UNSAT because the GB is {1}" into a
/// verifiable certificate (`Σ cᵢ fᵢ = 1`).
#[derive(Debug, Clone)]
pub struct TracedPoly {
    /// The basis element.
    pub poly: MPoly,
    /// Cofactors against the input generators, index-aligned.
    pub cofactors: Vec<MPoly>,
}

impl TracedPoly {
    /// The zero polynomial with all-zero cofactors.
    #[must_use]
    pub fn zero(n_inputs: usize) -> Self {
        Self {
            poly: MPoly::zero(),
            cofactors: vec![MPoly::zero(); n_inputs],
        }
    }

    /// Monomial-multiply both the polynomial and every cofactor.
    fn mul_monomial(&self, f: &FieldCtx, m: &Monomial) -> Self {
        Self {
            poly: mul_by_monomial(f, &self.poly, m),
            cofactors: self
                .cofactors
                .iter()
                .map(|c| mul_by_monomial(f, c, m))
                .collect(),
        }
    }

    /// Add another traced polynomial (combining cofactor rows).
    fn add(&self, f: &FieldCtx, other: &Self) -> Self {
        Self {
            poly: self.poly.add(f, &other.poly),
            cofactors: self
                .cofactors
                .iter()
                .zip(other.cofactors.iter())
                .map(|(a, b)| a.add(f, b))
                .collect(),
        }
    }

    /// Traced subtraction.
    fn sub(&self, f: &FieldCtx, other: &Self) -> Self {
        self.add(f, &other.neg(f))
    }

    /// Traced negation.
    fn neg(&self, f: &FieldCtx) -> Self {
        Self {
            poly: self.poly.neg(f),
            cofactors: self.cofactors.iter().map(|c| c.neg(f)).collect(),
        }
    }

    /// Scale by a field element.
    fn scale(&self, f: &FieldCtx, s: &Limbs) -> Self {
        Self {
            poly: self.poly.scale(f, s),
            cofactors: self.cofactors.iter().map(|c| c.scale(f, s)).collect(),
        }
    }

    /// Monic normalization of a *traced* element: the leading coefficient
    /// divides both the polynomial and every cofactor, preserving
    /// `poly = Σ cofactors[i]·inputs[i]`. Scaling only `poly` was the
    /// tracer-invariant break that made the UNSAT certificate unverifiable.
    fn monic_traced(&self, f: &FieldCtx) -> Self {
        match self.poly.lc(DEGREVLEX) {
            None => Self::zero(self.cofactors.len()),
            Some(lc) => match f.inv(lc) {
                Some(inv) => self.scale(f, &inv),
                None => Self::zero(self.cofactors.len()),
            },
        }
    }

    /// Verify the cofactor identity against the inputs: recompute
    /// `Σ cofactors[i]·inputs[i]` and compare with `poly`. One pass of
    /// polynomial arithmetic, orders of magnitude cheaper than the basis
    /// computation — the point of the certificate.
    #[must_use]
    pub fn verify(&self, f: &FieldCtx, inputs: &[MPoly]) -> bool {
        let mut acc = MPoly::zero();
        for (c, input) in self.cofactors.iter().zip(inputs.iter()) {
            acc = acc.add(f, &c.mul(f, input));
        }
        acc == self.poly
    }
}

/// Multiply a polynomial by a monomial (a traced step shared by the
/// S-polynomial setup and reduction).
fn mul_by_monomial(f: &FieldCtx, p: &MPoly, m: &Monomial) -> MPoly {
    let mut out = MPoly::zero();
    for (mm, c) in p.terms_iter() {
        out.add_term(f, mm.mul(m), c);
    }
    out
}

/// The computed basis (with tracers).
#[derive(Debug, Clone)]
pub struct GrobnerBasis {
    /// The basis elements, traced against the inputs.
    pub basis: Vec<TracedPoly>,
    /// The input generators, index-aligned with every `cofactors` row.
    pub inputs: Vec<MPoly>,
}

/// Compute a Gröbner basis of `⟨inputs⟩` over 𝔽_p, degrevlex, with the
/// Gebauer–Möller criteria and cofactor tracing.
///
/// Errors on budget exhaustion (the caller must answer `Unknown`, never
/// `Unsat`/`Sat` from a partial basis).
pub fn grobner_basis(
    f: &FieldCtx,
    inputs: &[MPoly],
    budget: &mut GrobnerBudget,
) -> Result<GrobnerBasis, GrobnerError> {
    // Deterministic generator order: sort by leading-monomial degree, then
    // term count, then input index (index-stable for ties).
    let mut order: Vec<usize> = (0..inputs.len()).collect();
    order.sort_by_key(|&i| {
        (
            inputs[i].lm(DEGREVLEX).map(|m| m.total_degree()),
            inputs[i].n_terms(),
            i,
        )
    });

    // The tracer is index-aligned with the ORIGINAL input order; the sort
    // permutes construction, not indices.
    let mut basis: Vec<TracedPoly> = Vec::with_capacity(inputs.len());
    for &i in &order {
        let mut cofactors = vec![MPoly::zero(); inputs.len()];
        cofactors[i] = MPoly::constant(f, &f.one());
        basis.push(
            TracedPoly {
                poly: inputs[i].clone(),
                cofactors,
            }
            .monic_traced(f),
        );
    }
    // Deliberately NO inter-reduction of the inputs here: Buchberger's
    // pair criteria reason about the generators as given, and
    // leading-term-reducing them first turns structured generators
    // (`x² − x`) into cross-terms (`xs`, `xy`) that blow the loop up. The
    // basis is inter-reduced once, after the pair loop.

    // Pair list with Gebauer–Möller criteria. Pairs are (i, j), i < j.
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            if !criterion_applies(&basis, i, j) {
                pairs.push((i, j));
            }
        }
    }

    let mut next_pair = 0usize;
    loop {
        if next_pair >= pairs.len() {
            break;
        }
        // Normal selection strategy: the pair minimizing the total degree
        // of the lcm of leading monomials (then the lcm itself).
        let mut best = next_pair;
        let mut best_key = pair_key(&basis, pairs[next_pair]);
        for (cand, pair) in pairs.iter().enumerate().skip(next_pair + 1) {
            let key = pair_key(&basis, *pair);
            let better = best_key.0 > key.0
                || (best_key.0 == key.0
                    && cmp_monomials(DEGREVLEX, &best_key.1, &key.1)
                        == std::cmp::Ordering::Greater);
            if better {
                best = cand;
                best_key = key;
            }
        }
        pairs.swap(next_pair, best);
        let (i, j) = pairs[next_pair];
        next_pair += 1;

        budget.charge(1)?;
        let spoly = s_polynomial(f, &basis[i], &basis[j]);
        let (reduced, _) = reduce_traced(f, &spoly, &basis, budget)?;
        if reduced.poly.is_zero() {
            continue;
        }
        // Reduce the new element fully against the current basis before
        // admitting it: keeps intermediate elements small and drops
        // duplicates early (a remainder already spanned by the basis never
        // enters). In-place on the new element only — existing indices
        // stay valid.
        let mut reduced = reduced.monic_traced(f);
        let mut guard = 0;
        loop {
            guard += 1;
            if guard > 10_000 {
                break;
            }
            let (again, changed) = reduce_traced(f, &reduced, &basis, budget)?;
            if !changed {
                break;
            }
            reduced = if again.poly.is_zero() {
                again
            } else {
                again.monic_traced(f)
            };
            if reduced.poly.is_zero() {
                break;
            }
        }
        if reduced.poly.is_zero() {
            continue;
        }
        basis.push(reduced);
        let n = basis.len() - 1;
        for k in 0..n {
            if !criterion_applies(&basis, k, n) {
                pairs.push((k, n));
            }
        }
        // No inter-reduction inside the loop: `reduce_all` *shrinks* the
        // basis (dropping elements that reduce to zero), which would
        // invalidate the pair list's indices mid-flight — the index-out-of-
        // bounds crash. Inter-reduction happens once, after the loop.
    }

    reduce_all(f, &mut basis, budget)?;
    Ok(GrobnerBasis {
        basis,
        inputs: inputs.to_vec(),
    })
}

/// The selection key of a pair: (deg lcm(lm_i, lm_j), lcm) — the normal
/// strategy.
fn pair_key(basis: &[TracedPoly], pair: (usize, usize)) -> (u32, Monomial) {
    let (a, b) = (&basis[pair.0].poly, &basis[pair.1].poly);
    match (a.lm(DEGREVLEX), b.lm(DEGREVLEX)) {
        (Some(x), Some(y)) => {
            let l = monomial_lcm(&x, &y);
            (l.total_degree(), l)
        }
        _ => (u32::MAX, Monomial::unit()),
    }
}

/// Gebauer–Möller discard test for the pair (i, j):
/// 1. Buchberger's first criterion — relatively prime leading monomials:
///    the S-polynomial reduces to zero.
/// 2. The third-element criterion — some other leading monomial strictly
///    divides the pair's lcm.
fn criterion_applies(basis: &[TracedPoly], i: usize, j: usize) -> bool {
    let (Some(lmi), Some(lmj)) = (basis[i].poly.lm(DEGREVLEX), basis[j].poly.lm(DEGREVLEX)) else {
        return false;
    };
    // 1. Relatively prime: no shared variable.
    let coprime = lmi.vars().iter().all(|vp| lmj.degree(vp.var) == 0);
    if coprime {
        return true;
    }
    // 2. Third element.
    let lcm = monomial_lcm(&lmi, &lmj);
    basis.iter().enumerate().any(|(k, g)| {
        if k == i || k == j {
            return false;
        }
        g.poly
            .lm(DEGREVLEX)
            .is_some_and(|lmk| lcm.div(&lmk).is_some() && lmk != lcm)
    })
}

/// The S-polynomial of two traced basis elements:
/// `S = (lcm/lm_i)·(1/lc_i)·g_i − (lcm/lm_j)·(1/lc_j)·g_j`, traced.
fn s_polynomial(f: &FieldCtx, gi: &TracedPoly, gj: &TracedPoly) -> TracedPoly {
    let (Some(lmi), Some(lmj)) = (gi.poly.lm(DEGREVLEX), gj.poly.lm(DEGREVLEX)) else {
        return TracedPoly::zero(gi.cofactors.len());
    };
    let lcm = monomial_lcm(&lmi, &lmj);
    let mi = monomial_div(&lcm, &lmi).unwrap_or_else(Monomial::unit);
    let mj = monomial_div(&lcm, &lmj).unwrap_or_else(Monomial::unit);
    let lci = gi.poly.lc(DEGREVLEX).cloned().unwrap_or_else(|| f.one());
    let lcj = gj.poly.lc(DEGREVLEX).cloned().unwrap_or_else(|| f.one());
    let inv_i = f.inv(&lci).unwrap_or_else(|| f.one());
    let inv_j = f.inv(&lcj).unwrap_or_else(|| f.one());
    let left = gi.mul_monomial(f, &mi).scale(f, &inv_i);
    let right = gj.mul_monomial(f, &mj).scale(f, &inv_j);
    left.sub(f, &right)
}

/// Multivariate division of `p` by `basis`, tracing cofactors: repeatedly
/// cancel the leading term with the first basis element whose leading
/// monomial divides it. Returns the (fully reduced) remainder and whether
/// anything changed.
fn reduce_traced(
    f: &FieldCtx,
    p: &TracedPoly,
    basis: &[TracedPoly],
    budget: &mut GrobnerBudget,
) -> Result<(TracedPoly, bool), GrobnerError> {
    let mut current = p.clone();
    let mut changed = false;
    while !current.poly.is_zero() {
        let Some(lt) = current.poly.lm(DEGREVLEX) else {
            break;
        };
        let mut cancelled = false;
        for g in basis {
            let Some(lmg) = g.poly.lm(DEGREVLEX) else {
                continue;
            };
            let Some(q) = monomial_div(&lt, &lmg) else {
                continue;
            };
            let Some(lc_cur) = current.poly.lc(DEGREVLEX).cloned() else {
                continue;
            };
            let Some(lc_g) = g.poly.lc(DEGREVLEX).cloned() else {
                continue;
            };
            let Some(inv_g) = f.inv(&lc_g) else {
                continue;
            };
            let factor = f.mul(&lc_cur, &inv_g);
            let sub = g.mul_monomial(f, &q).scale(f, &factor);
            current = current.sub(f, &sub);
            budget.charge(1)?;
            cancelled = true;
            changed = true;
            break;
        }
        if !cancelled {
            break;
        }
    }
    Ok((current, changed))
}

/// Inter-reduce the basis in place to the *reduced* Gröbner basis: each
/// element's leading term reduced against the others (deterministic
/// left-to-right), then every tail term reduced too — the tail pass is
/// what turns `x + 2y − 3` into `x − c` once `y − c'` is present, i.e.
/// the shape the model extraction reads.
fn reduce_all(
    f: &FieldCtx,
    basis: &mut Vec<TracedPoly>,
    budget: &mut GrobnerBudget,
) -> Result<(), GrobnerError> {
    basis.retain(|g| !g.poly.is_zero());
    for i in 0..basis.len() {
        let others: Vec<TracedPoly> = basis
            .iter()
            .enumerate()
            .filter(|&(j, _)| j != i)
            .map(|(_, g)| g.clone())
            .collect();
        let g = basis[i].clone();
        let (reduced, _changed) = reduce_traced(f, &g, &others, budget)?;
        // Tail reduction: cancel any remaining reducible non-leading term.
        let reduced = tail_reduce_traced(f, reduced, &others, budget)?;
        // The monic re-normalization applies whether or not the leading-
        // term reduction changed anything (tail reduction may have).
        {
            basis[i] = if reduced.poly.is_zero() {
                reduced
            } else {
                reduced.monic_traced(f)
            };
        }
    }
    basis.retain(|g| !g.poly.is_zero());
    Ok(())
}

/// Cancel every reducible term (not just the leading one) against the
/// other elements' leading monomials, tracing the cofactors. Terminates:
/// each cancellation replaces one term by strictly order-smaller monomials.
fn tail_reduce_traced(
    f: &FieldCtx,
    p: TracedPoly,
    others: &[TracedPoly],
    budget: &mut GrobnerBudget,
) -> Result<TracedPoly, GrobnerError> {
    let mut current = p;
    let mut progress = true;
    while progress {
        progress = false;
        let Some(terms) = Some(current.poly.sorted_terms(DEGREVLEX)) else {
            break;
        };
        'outer: for (m, _c) in terms.iter().rev() {
            // smallest-first so leading terms keep priority in shape.
            for g in others {
                let Some(lmg) = g.poly.lm(DEGREVLEX) else {
                    continue;
                };
                // No `m == lmg` skip here: a tail term that *equals*
                // another element's leading monomial is exactly the case
                // to cancel (the earlier guard inverted that and left
                // `y + a·x + c` unreduced beside `x − c'`). `others`
                // already excludes the element being reduced.
                let Some(q) = monomial_div(m, &lmg) else {
                    continue;
                };
                let lc_g = g.poly.lc(DEGREVLEX).cloned();
                let Some(lc_g) = lc_g else {
                    continue;
                };
                let Some(inv_g) = f.inv(&lc_g) else {
                    continue;
                };
                let Some(c_m) = current.poly.get_term(m).cloned() else {
                    continue;
                };
                let factor = f.mul(&c_m, &inv_g);
                let sub = g.mul_monomial(f, &q).scale(f, &factor);
                current = current.sub(f, &sub);
                budget.charge(1)?;
                progress = true;
                break 'outer;
            }
        }
    }
    Ok(current)
}

impl GrobnerBasis {
    /// Whether the ideal is the whole ring: some basis element is a
    /// nonzero constant — the OKTB23 UNSAT test.
    #[must_use]
    pub fn contains_nonzero_constant(&self) -> bool {
        self.basis.iter().any(|g| g.poly.is_nonzero_constant())
    }

    /// The traced element witnessing `1 ∈ I`, if any.
    #[must_use]
    pub fn constant_witness(&self) -> Option<&TracedPoly> {
        self.basis.iter().find(|g| g.poly.is_nonzero_constant())
    }

    /// Whether the ideal is zero-dimensional: with a degrevlex basis, iff
    /// every variable has some basis element whose leading monomial is a
    /// pure power of it.
    #[must_use]
    pub fn is_zero_dimensional(&self, variables: &[Var]) -> bool {
        variables.iter().all(|&x| {
            self.basis.iter().any(|g| {
                g.poly
                    .lm(DEGREVLEX)
                    .is_some_and(|m| m.vars().len() == 1 && m.vars()[0].var == x)
            })
        })
    }

    /// The linear univariate elements `x − c` of the basis. When every
    /// variable of a zero-dimensional ideal has one, the model is that
    /// single point.
    #[must_use]
    pub fn linear_univariates(&self, f: &FieldCtx) -> Vec<(Var, Limbs)> {
        let mut out = Vec::new();
        for g in &self.basis {
            let Some(lm) = g.poly.lm(DEGREVLEX) else {
                continue;
            };
            if lm.vars().len() == 1 && lm.vars()[0].power == 1 && g.poly.n_terms() == 2 {
                // x + c with leading coefficient 1 (basis elements are
                // monic): the root is -c — the negation is the whole point.
                let c = g.poly.constant_term(f);
                out.push((lm.vars()[0].var, f.neg(&c)));
            }
        }
        out
    }
}

/// The standard monomials of a basis (those divisible by no leading
/// monomial), degrevlex-ascending. For a zero-dimensional ideal this is
/// the quotient's vector-space basis. Returns an empty vector if the
/// enumeration exceeds the sanity cap (the caller must treat that as
/// "cannot decide", never as "small").
#[must_use]
pub fn standard_monomials(basis: &GrobnerBasis, cap: usize) -> Vec<Monomial> {
    let leadings: Vec<Monomial> = basis
        .basis
        .iter()
        .filter_map(|g| g.poly.lm(DEGREVLEX))
        .collect();
    // Variables and per-variable exponent caps: a pure-power leading
    // monomial bounds that variable; a variable without one means the
    // ideal is not zero-dimensional — the BFS cap bounds the work.
    let mut vars: Vec<Var> = Vec::new();
    for lm in &leadings {
        for vp in lm.vars() {
            if !vars.contains(&vp.var) {
                vars.push(vp.var);
            }
        }
    }
    vars.sort_unstable();
    let mut max_pow: rustc_hash::FxHashMap<Var, u32> = rustc_hash::FxHashMap::default();
    for lm in &leadings {
        if lm.vars().len() == 1 {
            let v = lm.vars()[0].var;
            let p = lm.vars()[0].power;
            max_pow
                .entry(v)
                .and_modify(|c| *c = (*c).max(p))
                .or_insert(p);
        }
    }
    for &v in &vars {
        // A zero-dimensional ideal has every variable pure-powered; for
        // the positive-dimensional case the BFS must stop somewhere. The
        // cap on total output size is the real bound.
        max_pow.entry(v).or_insert(8);
    }

    // Worklist over exponent tuples, deduplicated, standard-only. The
    // enumeration is bounded by the per-variable caps, and the output is
    // sorted by the monomial order (a heap is unusable: `Monomial` has no
    // `Ord`, and deriving one would invite order-vs-canonicalization
    // confusion; explicit `sort_by` it is).
    let mut out: Vec<Monomial> = Vec::new();
    let mut seen: rustc_hash::FxHashSet<Monomial> = rustc_hash::FxHashSet::default();
    let mut queue: Vec<Monomial> = vec![Monomial::unit()];
    while let Some(m) = queue.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        if leadings.iter().any(|l| m.div(l).is_some()) {
            continue;
        }
        out.push(m.clone());
        if out.len() > cap {
            return Vec::new();
        }
        for &v in &vars {
            let pow = m.degree(v) + 1;
            if pow <= max_pow.get(&v).copied().unwrap_or(8) {
                queue.push(m.mul(&Monomial::from_var_power(v, 1)));
            }
        }
    }
    out.sort_by(|a, b| cmp_monomials(DEGREVLEX, a, b));
    out
}

/// Reduce a polynomial to its normal form modulo the basis. `None` = budget
/// exhausted (→ Unknown, never a fabricated remainder).
pub fn normal_form(
    f: &FieldCtx,
    p: &MPoly,
    basis: &GrobnerBasis,
    budget: &mut GrobnerBudget,
) -> Option<MPoly> {
    let mut current = p.clone();
    while !current.is_zero() {
        let lt = current.lm(DEGREVLEX)?;
        let mut cancelled = false;
        for g in &basis.basis {
            let Some(lmg) = g.poly.lm(DEGREVLEX) else {
                continue;
            };
            let Some(q) = monomial_div(&lt, &lmg) else {
                continue;
            };
            let lc_cur = current.lc(DEGREVLEX).cloned()?;
            let lc_g = g.poly.lc(DEGREVLEX).cloned()?;
            let inv_g = f.inv(&lc_g)?;
            let factor = f.mul(&lc_cur, &inv_g);
            let sub = mul_by_monomial(f, &g.poly, &q).scale(f, &factor);
            current = current.sub(f, &sub);
            budget.charge(1).ok()?;
            cancelled = true;
            break;
        }
        if !cancelled {
            return Some(current);
        }
    }
    Some(current)
}

/// The minimal polynomial of `x` modulo a zero-dimensional ideal: find the
/// first linear dependency among `1, x, x², …` in the quotient ring (as
/// vectors over the standard monomials) by Gaussian elimination.
///
/// Returns `None` when the ideal is not zero-dimensional over `x`, when
/// the standard-monomial enumeration exceeds its cap, or when the budget
/// runs out — in every case the caller must answer `Unknown`.
#[must_use]
pub fn minimal_polynomial(
    f: &FieldCtx,
    basis: &GrobnerBasis,
    x: Var,
    variables: &[Var],
    budget: &mut GrobnerBudget,
) -> Option<super::uni_poly::UniPoly> {
    use super::uni_poly::UniPoly;

    if !basis.is_zero_dimensional(variables) {
        return None;
    }
    let std_monomials = standard_monomials(basis, 4096);
    if std_monomials.is_empty() {
        return None;
    }
    let index_of: rustc_hash::FxHashMap<Monomial, usize> = std_monomials
        .iter()
        .enumerate()
        .map(|(i, m)| (m.clone(), i))
        .collect();
    let n = std_monomials.len();

    // Multiply a quotient element by x and renormalize. Takes the budget
    // per call (a capturing closure would hold the `&mut` across the
    // loop's own charges).
    fn mul_by_x(
        f: &FieldCtx,
        basis: &GrobnerBasis,
        std_monomials: &[Monomial],
        x: Var,
        vec: &[Limbs],
        budget: &mut GrobnerBudget,
    ) -> Option<Vec<Limbs>> {
        let mut poly = MPoly::zero();
        for (m, c) in std_monomials.iter().zip(vec.iter()) {
            poly.add_term(f, m.mul(&Monomial::from_var(x)), c);
        }
        let reduced = normal_form(f, &poly, basis, budget)?;
        let mut out = vec![f.zero(); std_monomials.len()];
        for (m, c) in reduced.terms_iter() {
            let pos = std_monomials.iter().position(|s| s == m)?;
            out[pos] = c.clone();
        }
        Some(out)
    }

    let unit_pos = index_of.get(&Monomial::unit()).copied()?;
    let mut current = {
        let mut v = vec![f.zero(); n];
        v[unit_pos] = f.one();
        v
    };
    // Row-echelon accumulation of 1, x, x², ...; a dependency among d+1
    // vectors of an n-dimensional space appears by d = n.
    // Each row records (pivot position, reduced row, power of x it came
    // from) — the power is what turns a linear dependency into the
    // minimal polynomial's coefficients.
    let mut rows: Vec<(usize, Vec<Limbs>, usize)> = Vec::new();
    for d in 0..=n {
        budget.charge(1).ok()?;
        let mut acc = current.clone();
        let mut deps: Vec<(usize, Limbs)> = Vec::new();
        for (row_idx, (pivot, row, _)) in rows.iter().enumerate() {
            if f.is_zero(&acc[*pivot]) {
                continue;
            }
            let Some(row_inv) = f.inv(&row[*pivot]) else {
                continue;
            };
            let ratio = f.mul(&acc[*pivot], &row_inv);
            for (i, c) in row.iter().enumerate() {
                let sub = f.mul(c, &ratio);
                acc[i] = f.sub(&acc[i], &sub);
            }
            deps.push((row_idx, ratio));
        }
        if acc.iter().all(|c| f.is_zero(c)) {
            // x^d − Σ (ratio · x^{row power}) = 0 in the quotient.
            let mut coeffs: Vec<Limbs> = vec![f.zero(); d + 1];
            coeffs[d] = f.one();
            for (row_idx, ratio) in deps {
                let deg = rows[row_idx].2;
                coeffs[deg] = f.sub(&coeffs[deg], &ratio);
            }
            return Some(UniPoly::from_coeffs(coeffs));
        }
        let pivot = acc.iter().position(|c| !f.is_zero(c))?;
        rows.push((pivot, acc, d));
        current = mul_by_x(f, basis, &std_monomials, x, &current, budget)?;
    }
    None
}

/// Whether `p` reduces to a nonzero constant modulo `basis`.
#[must_use]
pub fn reduces_to_nonzero_constant(f: &FieldCtx, p: &MPoly, basis: &GrobnerBasis) -> Option<bool> {
    let mut budget = GrobnerBudget::new(u64::MAX / 4);
    let nf = normal_form(f, p, basis, &mut budget)?;
    Some(nf.is_nonzero_constant())
}

/// A constant polynomial from an exact integer.
#[must_use]
pub fn constant_poly(f: &FieldCtx, v: &BigUint) -> MPoly {
    MPoly::constant(f, &f.from_biguint(v))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::VarPower;

    fn ctx() -> FieldCtx {
        FieldCtx::new(BigUint::from(97u32)).expect("97 is prime")
    }

    fn mono(vars: &[(u32, u32)]) -> Monomial {
        Monomial::from_powers(vars.iter().map(|&(v, p)| (v, p)))
    }

    fn poly(f: &FieldCtx, terms: &[(i64, &[(u32, u32)])]) -> MPoly {
        let mut p = MPoly::zero();
        for &(v, m) in terms {
            p.add_term(f, mono(m), &f.from_bigint(&num_bigint::BigInt::from(v)));
        }
        p
    }

    fn basis_of(f: &FieldCtx, inputs: &[MPoly]) -> GrobnerBasis {
        let mut budget = GrobnerBudget::new(1 << 24);
        grobner_basis(f, inputs, &mut budget).expect("budget is generous")
    }

    #[test]
    fn every_cofactor_certificate_verifies() {
        let f = ctx();
        let inputs = vec![
            poly(&f, &[(1, &[(0, 2)]), (-1, &[(1, 1)])]), // x² - y
            poly(&f, &[(1, &[(1, 2)]), (-1, &[])]),       // y² - 1
        ];
        let g = basis_of(&f, &inputs);
        assert!(!g.basis.is_empty());
        for tp in &g.basis {
            assert!(
                tp.verify(&f, &inputs),
                "cofactor identity must hold for every basis element"
            );
        }
    }

    #[test]
    fn inputs_reduce_to_zero_modulo_basis() {
        // The basis generates the same ideal: every input reduces to 0.
        let f = ctx();
        let inputs = vec![
            poly(&f, &[(1, &[(0, 2)]), (-2, &[(0, 1)]), (1, &[])]), // (x-1)²
            poly(&f, &[(1, &[(0, 3)]), (-1, &[])]),                 // x³ - 1
        ];
        let g = basis_of(&f, &inputs);
        for input in &inputs {
            assert_eq!(reduces_to_nonzero_constant(&f, input, &g), Some(false));
            let mut budget = GrobnerBudget::new(1 << 24);
            let nf = normal_form(&f, input, &g, &mut budget).expect("budget");
            assert!(
                nf.is_zero(),
                "input must reduce to 0, got non-zero remainder"
            );
        }
    }

    #[test]
    fn unsat_system_yields_constant_one_with_certificate() {
        // x² = 1 ∧ x = 0 is unsatisfiable: 1 ∈ I.
        let f = ctx();
        let inputs = vec![
            poly(&f, &[(1, &[(0, 2)]), (-1, &[])]), // x² - 1
            poly(&f, &[(1, &[(0, 1)])]),            // x
        ];
        let g = basis_of(&f, &inputs);
        assert!(g.contains_nonzero_constant());
        let witness = g.constant_witness().expect("witness exists");
        // The certificate: Σ cᵢ fᵢ = the constant (a nonzero one).
        assert!(witness.verify(&f, &inputs));
        assert!(witness.poly.is_nonzero_constant());
    }

    #[test]
    fn sat_system_has_no_constant_in_basis() {
        let f = ctx();
        let inputs = vec![
            poly(&f, &[(1, &[(0, 2)]), (-1, &[])]), // x² - 1
        ];
        let g = basis_of(&f, &inputs);
        assert!(!g.contains_nonzero_constant());
    }

    #[test]
    fn zero_dimensionality_detection() {
        let f = ctx();
        // ⟨y - x², y - 1⟩ is zero-dimensional (one point).
        let inputs = vec![
            poly(&f, &[(-1, &[(0, 2)]), (1, &[(1, 1)])]),
            poly(&f, &[(1, &[(1, 1)]), (-1, &[])]),
        ];
        let g = basis_of(&f, &inputs);
        assert!(g.is_zero_dimensional(&[0, 1]));
        // ⟨y - x²⟩ alone is positive-dimensional (a parabola).
        let g2 = basis_of(&f, &[inputs[0].clone()]);
        assert!(!g2.is_zero_dimensional(&[0, 1]));
    }

    #[test]
    fn linear_univariates_give_the_point() {
        // ⟨x - 3, y - 5⟩: the point (3, 5).
        let f = ctx();
        let inputs = vec![
            poly(&f, &[(1, &[(0, 1)]), (-3, &[])]),
            poly(&f, &[(1, &[(1, 1)]), (-5, &[])]),
        ];
        let g = basis_of(&f, &inputs);
        let mut points = g.linear_univariates(&f);
        points.sort_by_key(|(v, _)| *v);
        assert_eq!(points.len(), 2);
        assert_eq!(points[0].0, 0);
        assert_eq!(f.to_biguint(&points[0].1.clone()), BigUint::from(3u8));
        assert_eq!(points[1].0, 1);
        assert_eq!(f.to_biguint(&points[1].1.clone()), BigUint::from(5u8));
    }

    #[test]
    fn minimal_polynomial_of_a_variable() {
        // ⟨x² - 4⟩ over F_97: minpoly of x is x² - 4.
        let f = ctx();
        let inputs = vec![poly(&f, &[(1, &[(0, 2)]), (-4, &[])])];
        let g = basis_of(&f, &inputs);
        let mut budget = GrobnerBudget::new(1 << 24);
        let minpoly = minimal_polynomial(&f, &g, 0, &[0], &mut budget).expect("minpoly exists");
        // Evaluate x² - 4 at a root and vice versa: the minpoly must
        // divide x² - 4 (they are equal up to monic).
        let x2m4 = super::super::uni_poly::UniPoly::from_coeffs(vec![
            f.from_bigint(&num_bigint::BigInt::from(-4)),
            f.zero(),
            f.one(),
        ]);
        let (_, rem) = x2m4.divrem(&f, &minpoly).expect("minpoly nonzero");
        assert!(rem.is_zero(), "x²-4 must be divisible by the minpoly");
        assert_eq!(minpoly.degree(), Some(2));
    }

    #[test]
    fn minimal_polynomial_of_zero_dimensional_point() {
        // ⟨x - 3⟩: minpoly of x is x - 3.
        let f = ctx();
        let inputs = vec![poly(&f, &[(1, &[(0, 1)]), (-3, &[])])];
        let g = basis_of(&f, &inputs);
        let mut budget = GrobnerBudget::new(1 << 24);
        let minpoly = minimal_polynomial(&f, &g, 0, &[0], &mut budget).expect("minpoly");
        assert_eq!(minpoly.degree(), Some(1));
        let root = f.neg(&minpoly.coeffs()[0].clone());
        assert_eq!(f.to_biguint(&root), BigUint::from(3u8));
    }

    #[test]
    fn budget_exhaustion_is_an_error_not_a_wrong_basis() {
        let f = ctx();
        // A system whose first S-pair is kept (shared variable, no third
        // element): with a zero budget the very first charge must fire.
        let inputs = vec![
            poly(&f, &[(1, &[(0, 2)]), (-1, &[])]),
            poly(&f, &[(1, &[(0, 1)])]),
        ];
        let mut tiny = GrobnerBudget::new(0);
        let verdict = grobner_basis(&f, &inputs, &mut tiny);
        assert!(
            matches!(verdict, Err(GrobnerError::Budget)),
            "a cut-off computation must report Budget, not return a basis"
        );
    }

    #[test]
    fn determinism_repeat_computations_agree() {
        let f = ctx();
        let inputs = vec![
            poly(&f, &[(1, &[(0, 2)]), (-1, &[(1, 1)])]),
            poly(&f, &[(1, &[(1, 2)]), (-1, &[])]),
            poly(&f, &[(1, &[(0, 1), (2, 1)]), (-6, &[])]),
        ];
        let a = basis_of(&f, &inputs);
        let b = basis_of(&f, &inputs);
        assert_eq!(a.basis.len(), b.basis.len());
        for (x, y) in a.basis.iter().zip(b.basis.iter()) {
            assert_eq!(x.poly, y.poly, "identical inputs give identical bases");
        }
    }

    #[test]
    fn standard_monomials_of_a_point_ideal() {
        // ⟨x - 3, y - 5⟩: quotient dimension 1, standard monomials {1}.
        let f = ctx();
        let inputs = vec![
            poly(&f, &[(1, &[(0, 1)]), (-3, &[])]),
            poly(&f, &[(1, &[(1, 1)]), (-5, &[])]),
        ];
        let g = basis_of(&f, &inputs);
        let std = standard_monomials(&g, 1024);
        assert_eq!(std, vec![Monomial::unit()]);
    }

    #[test]
    fn standard_monomials_of_x_squared_minus_one() {
        // ⟨x² - 1⟩: standard monomials {1, x}.
        let f = ctx();
        let inputs = vec![poly(&f, &[(1, &[(0, 2)]), (-1, &[])])];
        let g = basis_of(&f, &inputs);
        let std = standard_monomials(&g, 1024);
        assert_eq!(std.len(), 2);
        assert_eq!(std[0], Monomial::unit());
        assert_eq!(std[1], Monomial::from_var_power(0, 1));
    }

    #[test]
    fn varpower_import_is_used() {
        // `VarPower` is exercised through `Monomial::from_powers`; keep a
        // direct pin so the import cannot silently rot.
        let vp = VarPower::new(3, 2);
        let m = Monomial::from_powers(std::iter::once((vp.var, vp.power)));
        assert_eq!(m.degree(3), 2);
    }
}

#[cfg(test)]
mod agreement_tests {
    use super::*;

    /// The complete oracle for Phase 2: for random systems over a small
    /// prime, every 𝔽_p-point satisfies the input system **iff** it
    /// satisfies the computed basis (the ideals agree as *solution sets*),
    /// and every tracer row verifies. Enumerating all p^n points makes
    /// this exact — the finite-field analogue of the BV exhaustive
    /// certification study.
    #[test]
    fn basis_and_inputs_agree_on_all_points() {
        let f = FieldCtx::new(BigUint::from(7u32)).expect("7 is prime");
        // A deterministic pseudo-random generator (xorshift, fixed seed):
        // coverage without nondeterminism.
        let mut seed: u64 = 0x2545_F491_4F6C_DD1D;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _round in 0..30 {
            let n_vars = 2u32;
            let mut inputs: Vec<MPoly> = Vec::new();
            for _g in 0..2 {
                let mut p = MPoly::zero();
                for _t in 0..2 + (next() % 3) {
                    let var = (next() % u64::from(n_vars)) as u32;
                    let power = 1 + (next() % 2);
                    let coeff = (next() % 7).to_string();
                    let c: i64 = coeff.parse().expect("digit");
                    p.add_term(
                        &f,
                        Monomial::from_powers([(var, power as u32)]),
                        &f.from_bigint(&num_bigint::BigInt::from(c)),
                    );
                }
                // Every generator gets a constant term so 0 is not always
                // a trivial solution of everything.
                p.add_term(
                    &f,
                    Monomial::unit(),
                    &f.from_bigint(&num_bigint::BigInt::from((next() % 7) as i64)),
                );
                if !p.is_zero() {
                    inputs.push(p);
                }
            }
            if inputs.is_empty() {
                continue;
            }
            let mut budget = GrobnerBudget::new(1 << 22);
            let Ok(g) = grobner_basis(&f, &inputs, &mut budget) else {
                continue;
            };
            // Tracer verification, every element.
            for tp in &g.basis {
                assert!(tp.verify(&f, &inputs), "tracer must verify");
            }
            // Point-set agreement over all 49 points.
            for x in 0..7i64 {
                for y in 0..7i64 {
                    let mut assignment: rustc_hash::FxHashMap<Var, Limbs> =
                        rustc_hash::FxHashMap::default();
                    assignment.insert(0, f.from_bigint(&num_bigint::BigInt::from(x)));
                    assignment.insert(1, f.from_bigint(&num_bigint::BigInt::from(y)));
                    let inputs_sat = inputs
                        .iter()
                        .all(|p| f.is_zero(&p.eval_all(&f, &assignment)));
                    let basis_sat = g
                        .basis
                        .iter()
                        .all(|tp| f.is_zero(&tp.poly.eval_all(&f, &assignment)));
                    assert_eq!(
                        inputs_sat, basis_sat,
                        "solution sets must agree: inputs {inputs:?} point ({x},{y})"
                    );
                }
            }
        }
    }

    /// UNSAT by the basis ⟺ UNSAT by enumeration (the p^n oracle).
    #[test]
    fn constant_in_basis_iff_no_point_satisfies() {
        let f = FieldCtx::new(BigUint::from(5u32)).expect("5 is prime");
        let build = |terms: &[(i64, u32, u32)]| -> MPoly {
            let mut p = MPoly::zero();
            for &(c, v, d) in terms {
                p.add_term(
                    &f,
                    Monomial::from_powers([(v, d)]),
                    &f.from_bigint(&num_bigint::BigInt::from(c)),
                );
            }
            p
        };
        // x² + 1 over F_5 has roots (±2), so it is SAT.
        let sat_inputs = vec![build(&[(1, 0, 2), (1, 99, 0)])];
        // (x² + 1) ∧ (x - 1): x = 1 gives 2 ≠ 0 → UNSAT.
        let unsat_inputs = vec![
            build(&[(1, 0, 2), (1, 99, 0)]),
            build(&[(1, 0, 1), (-1, 99, 0)]),
        ];

        for (inputs, expect_unsat) in [(sat_inputs, false), (unsat_inputs, true)] {
            let mut budget = GrobnerBudget::new(1 << 22);
            let g = grobner_basis(&f, &inputs, &mut budget).expect("budget");
            assert_eq!(
                g.contains_nonzero_constant(),
                expect_unsat,
                "1 ∈ I must match point enumeration"
            );
            // Cross-check by enumeration.
            let any_point = (0..5i64).any(|x| {
                let mut assignment: rustc_hash::FxHashMap<Var, Limbs> =
                    rustc_hash::FxHashMap::default();
                assignment.insert(0, f.from_bigint(&num_bigint::BigInt::from(x)));
                assignment.insert(99, f.zero());
                inputs
                    .iter()
                    .all(|p| f.is_zero(&p.eval_all(&f, &assignment)))
            });
            assert_eq!(any_point, !expect_unsat);
        }
    }
}
