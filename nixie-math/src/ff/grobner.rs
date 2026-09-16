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

// Matrix echelonization indexes its columns explicitly (column-major
// pivot order over row-major sparse rows) — the same rationale as the
// rational F4 module's module-level allow.
#[allow(clippy::needless_range_loop)]
/// Faugère's F4 over 𝔽_p (the Phase-7 lever; see
/// `docs/studies/2026-09-18-ff-f4.md` for the pre-registration, the
/// engine bug the validation surfaced, and the prototype's bug log).
/// Computes the same object as [`grobner_basis`] — a degrevlex Gröbner
/// basis of `⟨inputs⟩` — by replacing the per-pair S-polynomial loop
/// with degree-batched matrices: all selected pairs' rows plus their
/// reducer closure are placed in one sparse matrix over the monomial
/// columns, echelonized by one linear-algebra kernel, and the rows
/// with NEW leading monomials become basis elements.
///
/// **Soundness**: every matrix row is an explicit 𝔽_p combination
/// `Σ cₖ·(mₖ·gₖ)` of monomial multiples of current basis elements, so
/// every row — hence every extracted element — lies in the ideal the
/// basis generates, inductively the input ideal. A constant row is
/// the whole-ring witness (unchanged detection). v1 is UNTRACED: no
/// certificate is minted from an F4 basis.
///
/// **Determinism**: columns sorted by degrevlex descending; rows in
/// construction order; pivot = the first eligible unused row in index
/// order; selection = all pairs of minimal lcm degree (ties by pair
/// index). The sparse row layout (`Vec<(col, coeff)>`, sorted) is the
/// flat structure any later SIMD vectorization of the kernel wants —
/// exact modular arithmetic is order-independent, so vectorizing the
/// axpy kernel could not change results even in principle.
pub fn f4_basis(
    f: &FieldCtx,
    inputs: &[MPoly],
    budget: &mut GrobnerBudget,
) -> Result<GrobnerBasis, GrobnerError> {
    /// A sparse matrix row: (column, coefficient) pairs, column-sorted.
    type Row = Vec<(usize, Limbs)>;

    const MAX_COLUMNS: usize = 1 << 16;
    const MAX_ROWS: usize = 1 << 16;

    // Deterministic input order (mirrors `grobner_basis_inner`).
    let mut order: Vec<usize> = (0..inputs.len()).collect();
    order.sort_by_key(|&i| {
        (
            inputs[i].lm(DEGREVLEX).map(|m| m.total_degree()),
            inputs[i].n_terms(),
            i,
        )
    });
    let mut basis: Vec<MPoly> = order
        .iter()
        .map(|&i| inputs[i].monic(f, DEGREVLEX))
        .collect();
    basis.retain(|p| !p.is_zero());

    // Seed leading-term deduplication (the GM discard — and F4's own
    // pair discard — is unsound over duplicate-lm seeds; see the
    // Buchberger engine's init for the measured story).
    {
        let mut i = 0;
        while i < basis.len() {
            let others: Vec<MPoly> = basis
                .iter()
                .enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, g)| g.clone())
                .collect();
            let others_lms = lm_cache_mp(&others);
            let mut cur = basis[i].clone();
            // Reduce the leading term against the others (leading-term
            // chain, like reduce_traced's loop).
            loop {
                let Some(lt) = cur.lm(DEGREVLEX) else { break };
                let red = others
                    .iter()
                    .enumerate()
                    .find(|(_, g)| g.lm(DEGREVLEX).is_some_and(|lmg| lt.div(&lmg).is_some()));
                let Some((gi, _)) = red else { break };
                let lmg = others_lms[gi].clone();
                let Some(q) = lt.div(&lmg) else { break };
                let lc_cur = cur.lc(DEGREVLEX).cloned().unwrap_or_else(|| f.one());
                let lc_g = others[gi].lc(DEGREVLEX).cloned().unwrap_or_else(|| f.one());
                let Some(inv_g) = f.inv(&lc_g) else { break };
                let factor = f.mul(&lc_cur, &inv_g);
                let scaled = mul_by_monomial(f, &others[gi].clone().monic(f, DEGREVLEX), &q)
                    .scale(f, &factor);
                budget.charge(
                    u64::try_from(scaled.n_terms() + cur.n_terms()).unwrap_or(u64::MAX / 2),
                )?;
                cur = cur.sub(f, &scaled);
                if cur.is_zero() {
                    break;
                }
            }
            if cur.is_zero() {
                basis.swap_remove(i);
                continue;
            }
            basis[i] = cur.monic(f, DEGREVLEX);
            i += 1;
        }
    }
    let inputs_len = inputs.len();

    // Stable-index bookkeeping: dead-marking (no compaction), so pair
    // endpoints stay valid. Pairs are maintained INCREMENTALLY and a
    // processed pair never resurrects.
    let mut lms: Vec<Monomial> = basis
        .iter()
        .map(|p| p.lm(DEGREVLEX).unwrap_or_else(Monomial::unit))
        .collect();
    let mut dead = vec![false; basis.len()];
    fn live(dead: &[bool]) -> impl Iterator<Item = usize> + '_ {
        (0..dead.len()).filter(|&i| !dead[i])
    }

    let mut pairs: Vec<(usize, usize)> = Vec::new();
    {
        let live_idx: Vec<usize> = live(&dead).collect();
        for &i in &live_idx {
            for &j in &live_idx {
                if i < j && !criterion_applies_lms(&lms, i, j) {
                    pairs.push((i, j));
                }
            }
        }
    }

    loop {
        if live(&dead).count() > 8 * inputs_len + 64 {
            return Err(GrobnerError::Budget);
        }
        if pairs.is_empty() {
            break;
        }
        // Selection: ALL pairs of minimal lcm degree.
        let sel_deg = pairs
            .iter()
            .map(|&(i, j)| monomial_lcm(&lms[i], &lms[j]).total_degree())
            .min()
            .unwrap_or(0);
        let selected: Vec<(usize, usize)> = pairs
            .iter()
            .copied()
            .filter(|&(i, j)| monomial_lcm(&lms[i], &lms[j]).total_degree() == sel_deg)
            .collect();
        for _ in &selected {
            budget.charge(1)?;
        }
        let sel_set: std::collections::BTreeSet<(usize, usize)> =
            selected.iter().copied().collect();
        pairs.retain(|p| !sel_set.contains(p));

        // --- Symbolic preprocessing ---
        let mut rows: Vec<(Monomial, usize)> = Vec::new();
        let mut queued: rustc_hash::FxHashSet<Monomial> = rustc_hash::FxHashSet::default();
        let mut queue: Vec<Monomial> = Vec::new();
        for &(i, j) in &selected {
            let lcm = monomial_lcm(&lms[i], &lms[j]);
            let (Some(qi), Some(qj)) = (monomial_div(&lcm, &lms[i]), monomial_div(&lcm, &lms[j]))
            else {
                continue;
            };
            rows.push((qi.clone(), i));
            rows.push((qj.clone(), j));
            for (which, q) in [(i, &qi), (j, &qj)] {
                for (m, _) in basis[which].terms_iter() {
                    let shifted = m.mul(q);
                    if queued.insert(shifted.clone()) {
                        queue.push(shifted);
                    }
                }
            }
        }
        let mut row_of_mono: rustc_hash::FxHashMap<Monomial, (Monomial, usize)> =
            rustc_hash::FxHashMap::default();
        while let Some(m) = queue.pop() {
            budget.charge(1)?;
            // Reducer scan over the CACHED leading monomials — an `lm()`
            // call is a full terms-map scan, and calling it per candidate
            // per monomial was the prototype's dominant cost (the same
            // trap the budget-honesty study documented for the selection
            // scan; `lms` sits right there).
            let red = live(&dead).find(|&g| m.div(&lms[g]).is_some());
            let Some(gi) = red else {
                continue;
            };
            let Some(q) = m.div(&lms[gi]) else {
                continue;
            };
            row_of_mono.insert(m.clone(), (q.clone(), gi));
            for (mm, _) in basis[gi].terms_iter() {
                let shifted = mm.mul(&q);
                if queued.insert(shifted.clone()) {
                    queue.push(shifted);
                }
            }
        }
        rows.extend(row_of_mono.into_values());
        let mut columns: Vec<Monomial> = queued.into_iter().collect();
        if columns.len() > MAX_COLUMNS || rows.len() > MAX_ROWS {
            return Err(GrobnerError::Budget);
        }
        columns.sort_by(|a, b| cmp_monomials(DEGREVLEX, b, a));
        let col_index: rustc_hash::FxHashMap<&Monomial, usize> =
            columns.iter().enumerate().map(|(c, m)| (m, c)).collect();

        // --- Matrix construction ---
        // FUSED: iterate the basis element's terms directly and look up
        // `q·term` in the column index — no intermediate scaled MPoly
        // (each `mul_by_monomial` rebuilt a whole terms hash map per
        // row, only for it to be iterated once and dropped).
        let mut matrix: Vec<Row> = Vec::with_capacity(rows.len());
        for (q, gi) in &rows {
            let src = &basis[*gi];
            let mut row: Row = Vec::with_capacity(src.n_terms());
            for (m, c) in src.terms_iter() {
                if let Some(&col) = col_index.get(&m.mul(q)) {
                    row.push((col, c.clone()));
                    budget.charge(1)?;
                }
            }
            row.sort_by_key(|(col, _)| *col);
            matrix.push(row);
        }

        // --- Echelonization ---
        // Column-ascending; the first live UNUSED row with a nonzero
        // entry pivots (a row pivots exactly once, at its first nonzero
        // column), is normalized, and the column is eliminated from
        // every other unused row.
        let ncols = columns.len();
        let mut pivots: Vec<Option<usize>> = vec![None; ncols];
        let mut alive: Vec<bool> = matrix.iter().map(|r| !r.is_empty()).collect();
        let mut used: Vec<bool> = vec![false; matrix.len()];
        for c in 0..ncols {
            let pr =
                (0..matrix.len()).find(|&r| alive[r] && !used[r] && entry(&matrix[r], c).is_some());
            let Some(pr) = pr else {
                continue;
            };
            let lead = entry(&matrix[pr], c).cloned().unwrap_or_else(|| f.one());
            let inv = f.inv(&lead).unwrap_or_else(|| f.one());
            for (cc, v) in matrix[pr].iter_mut() {
                if *cc == c {
                    *v = f.one();
                } else {
                    *v = f.mul(v, &inv);
                }
            }
            pivots[c] = Some(pr);
            used[pr] = true;
            let pivot_row = matrix[pr].clone();
            for r in 0..matrix.len() {
                if used[r] || !alive[r] {
                    continue;
                }
                let Some(fc) = entry(&matrix[r], c).cloned() else {
                    continue;
                };
                budget.charge(
                    u64::try_from(pivot_row.len() + matrix[r].len()).unwrap_or(u64::MAX / 2),
                )?;
                let neg = f.neg(&fc);
                let merged = axpy(f, &matrix[r], &neg, &pivot_row);
                if merged.is_empty() {
                    alive[r] = false;
                }
                matrix[r] = merged;
            }
        }

        // --- Extraction ---
        // Every pivot row whose column monomial is not a live leading
        // monomial is a CANDIDATE. THE FIX (the prototype's fourth bug):
        // the candidate is REDUCED against the live basis before the
        // admission decision — the first version SKIPPED candidates
        // whose lm was divisible by an existing lm, silently dropping
        // elements whose reduction would have surfaced a new leading
        // monomial (the measured incompleteness vs Buchberger). After
        // the reduction: zero ⇒ skip; else admit the reduced form (its
        // lm is now irreducible — the minimal-GB property for free) and
        // kill superseded elements.
        for (c, pr_slot) in pivots.iter().enumerate() {
            let Some(pr) = pr_slot.as_ref().copied() else {
                continue;
            };
            if !alive[pr] {
                continue;
            }
            let Some(lm_new) = columns.get(c) else {
                continue;
            };
            if live(&dead).any(|i| &lms[i] == lm_new) {
                continue;
            }
            let mut p = MPoly::zero();
            if let Some(row) = matrix.get(pr) {
                for (cc, v) in row {
                    if let Some(m) = columns.get(*cc) {
                        p.add_term(f, m.clone(), v);
                    }
                }
            }
            if p.is_zero() {
                continue;
            }
            // Full reduction against the live basis (leading-term
            // chain), charged like every reduction. Bisect form: the
            // per-candidate snapshot (the round cache is the suspect).
            {
                let live_basis: Vec<MPoly> =
                    live(&dead).filter_map(|i| basis.get(i).cloned()).collect();
                let live_lms = lm_cache_mp(&live_basis);
                let mut cur = p;
                'reduce: loop {
                    let Some(lt) = cur.lm(DEGREVLEX) else {
                        break 'reduce;
                    };
                    let red = live_basis
                        .iter()
                        .enumerate()
                        .find(|(_, g)| g.lm(DEGREVLEX).is_some_and(|lmg| lt.div(&lmg).is_some()));
                    let Some((gi, _)) = red else {
                        break 'reduce;
                    };
                    let lmg = live_lms[gi].clone();
                    let Some(q) = lt.div(&lmg) else {
                        break 'reduce;
                    };
                    let lc_cur = cur.lc(DEGREVLEX).cloned().unwrap_or_else(|| f.one());
                    let lc_g = live_basis[gi]
                        .lc(DEGREVLEX)
                        .cloned()
                        .unwrap_or_else(|| f.one());
                    let Some(inv_g) = f.inv(&lc_g) else {
                        break 'reduce;
                    };
                    let factor = f.mul(&lc_cur, &inv_g);
                    let scaled =
                        mul_by_monomial(f, &live_basis[gi].clone().monic(f, DEGREVLEX), &q)
                            .scale(f, &factor);
                    budget.charge(
                        u64::try_from(scaled.n_terms() + cur.n_terms()).unwrap_or(u64::MAX / 2),
                    )?;
                    cur = cur.sub(f, &scaled);
                    if cur.is_zero() {
                        break 'reduce;
                    }
                }
                p = cur;
            }
            if p.is_zero() {
                continue;
            }
            let p = p.monic(f, DEGREVLEX);
            let lm_final = p.lm(DEGREVLEX).unwrap_or_else(Monomial::unit);
            if live(&dead).any(|i| lms[i] == lm_final || lm_final.div(&lms[i]).is_some()) {
                // After a FULL reduction this should be impossible (the
                // lm is irreducible); the guard stays as a fail-safe.
                continue;
            }
            for i in 0..lms.len() {
                if !dead[i] && lms[i].div(&lm_final).is_some() {
                    dead[i] = true;
                }
            }
            pairs.retain(|&(i, j)| !dead[i] && !dead[j]);
            let n = basis.len();
            lms.push(lm_final);
            basis.push(p);
            dead.push(false);
            for k in 0..n {
                if !dead[k] && !criterion_applies_lms(&lms, k, n) {
                    pairs.push((k, n));
                }
            }
        }
    }

    // Final inter-reduction through the engine's own reducer.
    let mut traced: Vec<TracedPoly> = live(&dead)
        .filter_map(|i| basis.get(i).cloned())
        .map(|p| TracedPoly {
            poly: p,
            cofactors: Vec::new(),
        })
        .collect();
    reduce_all(f, &mut traced, budget)?;
    Ok(GrobnerBasis {
        basis: traced,
        inputs: inputs.to_vec(),
    })
}

/// The entry of a sorted sparse row at column `c`, if nonzero.
fn entry(row: &[(usize, Limbs)], c: usize) -> Option<&Limbs> {
    row.binary_search_by(|(cc, _)| cc.cmp(&c))
        .ok()
        .map(|i| &row[i].1)
}

/// `dst + c·src` over sorted sparse rows (the axpy kernel; flat layout
/// by design — see f4_basis's doc comment on later vectorization).
fn axpy(
    f: &FieldCtx,
    dst: &[(usize, Limbs)],
    c: &Limbs,
    src: &[(usize, Limbs)],
) -> Vec<(usize, Limbs)> {
    let mut out = Vec::with_capacity(dst.len() + src.len());
    let (mut i, mut j) = (0, 0);
    while i < dst.len() && j < src.len() {
        match dst[i].0.cmp(&src[j].0) {
            std::cmp::Ordering::Less => {
                out.push(dst[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                let v = f.mul(&src[j].1, c);
                out.push((src[j].0, v));
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                let v = f.add(&dst[i].1, &f.mul(&src[j].1, c));
                if !f.is_zero(&v) {
                    out.push((dst[i].0, v));
                }
                i += 1;
                j += 1;
            }
        }
    }
    while i < dst.len() {
        out.push(dst[i].clone());
        i += 1;
    }
    while j < src.len() {
        let v = f.mul(&src[j].1, c);
        out.push((src[j].0, v));
        j += 1;
    }
    out
}

/// The leading monomials of an MPoly slice.
fn lm_cache_mp(basis: &[MPoly]) -> Vec<Monomial> {
    basis
        .iter()
        .map(|p| p.lm(DEGREVLEX).unwrap_or_else(Monomial::unit))
        .collect()
}

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

    /// Charge `units` of work. The unit is ONE MONOMIAL OPERATION (a
    /// single coefficient multiply/add), not a step: a reduction between
    /// s-term polynomials costs ~s units. Step-counting made a 2^24
    /// budget worth hours on big-polynomial cascades — the budget never
    /// noticed the polynomials growing — so a goal refused in principle
    /// but ground in practice. Monomial-operation charging keeps the
    /// budget a faithful work bound (deterministic: sizes are functions
    /// of the computation, never of the clock).
    pub fn charge(&mut self, units: u64) -> Result<(), GrobnerError> {
        if units > self.remaining {
            return Err(GrobnerError::Budget);
        }
        self.remaining -= units;
        Ok(())
    }

    /// The unconsumed step count (instrumentation for the Phase-5
    /// step-count reporting; not a policy input).
    #[must_use]
    pub fn remaining(&self) -> Option<u64> {
        Some(self.remaining)
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

    /// Monomial-multiply both the polynomial and every cofactor. An
    /// UNTRACED element (empty cofactor row — see
    /// [`grobner_basis_untraced`]) stays untraced: the row work is the
    /// measured ~n_inputs× cost on wide cascades, and it is skipped
    /// entirely when no certificate will be minted from this run.
    fn mul_monomial(&self, f: &FieldCtx, m: &Monomial) -> Self {
        Self {
            poly: mul_by_monomial(f, &self.poly, m),
            cofactors: if self.cofactors.is_empty() {
                Vec::new()
            } else {
                self.cofactors
                    .iter()
                    .map(|c| mul_by_monomial(f, c, m))
                    .collect()
            },
        }
    }

    /// Add another traced polynomial (combining cofactor rows).
    fn add(&self, f: &FieldCtx, other: &Self) -> Self {
        Self {
            poly: self.poly.add(f, &other.poly),
            cofactors: if self.cofactors.is_empty() && other.cofactors.is_empty() {
                Vec::new()
            } else {
                self.cofactors
                    .iter()
                    .zip(other.cofactors.iter())
                    .map(|(a, b)| a.add(f, b))
                    .collect()
            },
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
            cofactors: if self.cofactors.is_empty() {
                Vec::new()
            } else {
                self.cofactors.iter().map(|c| c.neg(f)).collect()
            },
        }
    }

    /// Scale by a field element.
    fn scale(&self, f: &FieldCtx, s: &Limbs) -> Self {
        Self {
            poly: self.poly.scale(f, s),
            cofactors: if self.cofactors.is_empty() {
                Vec::new()
            } else {
                self.cofactors.iter().map(|c| c.scale(f, s)).collect()
            },
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

/// Public wrapper: multiply a polynomial by a monomial (test-oracle
/// support — the regression batteries construct reference S-polynomials
/// with it).
pub fn mul_by_monomial_pub(f: &FieldCtx, p: &MPoly, m: &Monomial) -> MPoly {
    mul_by_monomial(f, p, m)
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
    grobner_basis_inner(f, inputs, budget, true)
}

/// The UNTRACED fast path: the same deterministic cascade with NO cofactor
/// rows (empty `cofactors` propagates through every traced op — the row
/// maintenance was the measured ~1 s-per-S-pair cost on 96-input cascades).
/// Use when the caller will not mint a certificate from this run's basis;
/// reductions, pair selection, and the resulting basis are IDENTICAL (rows
/// never influence the trajectory), so a traced re-run reproduces it.
pub fn grobner_basis_untraced(
    f: &FieldCtx,
    inputs: &[MPoly],
    budget: &mut GrobnerBudget,
) -> Result<GrobnerBasis, GrobnerError> {
    grobner_basis_inner(f, inputs, budget, false)
}

fn grobner_basis_inner(
    f: &FieldCtx,
    inputs: &[MPoly],
    budget: &mut GrobnerBudget,
    track: bool,
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
        let cofactors = if track {
            let mut rows = vec![MPoly::zero(); inputs.len()];
            rows[i] = MPoly::constant(f, &f.one());
            rows
        } else {
            Vec::new()
        };
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
    //
    // EXCEPTION (2026-09-18): LEADING-TERM-DEDUPLICATION of the inputs.
    // The Gebauer–Möller discard is UNSOUND when two basis elements
    // share a leading monomial (the duplicate trivially divides every
    // lcm of its own multiples, discarding pairs whose S-polynomials do
    // not reduce to zero): a whole-ring ideal — an UNSAT goal with a
    // verified `1 = Σ cᵢ·fᵢ` witness — returned a 9-element non-basis
    // with `is_gb = true`, missing the refutation entirely (the
    // reproducer class in tests/ff_gb_seed_dedup_regression.rs). Each
    // input's LEADING TERM is reduced against the others so the seed
    // lms are distinct — not full inter-reduction (`x² − x` survives
    // unless another seed's lm divides `x²`); admitted elements are
    // already lm-irreducible by the pre-admission reduction, so the
    // seeds are the only duplicate source.
    {
        let mut i = 0;
        while i < basis.len() {
            let others: Vec<TracedPoly> = basis
                .iter()
                .enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, g)| g.clone())
                .collect();
            let others_lms = lm_cache(&others);
            let cur = basis[i].clone();
            let old_lm = cur.poly.lm(DEGREVLEX);
            let (red, _) = reduce_traced(f, &cur, &others, &others_lms, budget)?;
            if red.poly.is_zero() {
                basis.swap_remove(i);
                continue;
            }
            let red = red.monic_traced(f);
            let new_lm = red.poly.lm(DEGREVLEX);
            basis[i] = red;
            if old_lm == new_lm {
                i += 1;
            }
            // else: the lm shrank — re-reduce this slot against the
            // updated basis (swap_remove may also have moved a fresh
            // element into this slot).
        }
    }

    // Pair list with Gebauer–Möller criteria. Pairs are (i, j), i < j.
    //
    // The chain criterion is carried as EXPLICIT BOOKKEEPING of
    // provably-zero pairs — the sound form of Buchberger's second
    // criterion: sp(i,j) reduces to zero if some k has lm_k |
    // lcm(lm_i,lm_j) AND the pairs (i,k), (j,k) are THEMSELVES provably
    // zero (processed-to-zero, coprime, or recursively chain-verified).
    let mut zero_pairs: rustc_hash::FxHashSet<(usize, usize)> = rustc_hash::FxHashSet::default();
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            if !criterion_applies(&basis, i, j) {
                pairs.push((i, j));
            } else {
                // Coprime lms: the first criterion is an unconditional
                // theorem — a provably-zero pair.
                zero_pairs.insert((i, j));
            }
        }
    }

    let mut next_pair = 0usize;
    // The bloat circuit breaker: a cascade whose basis has far outgrown
    // its inputs, or whose elements have exploded in term count, is the
    // pathological shape the caller's fallback engines (the split basis)
    // exist for. Aborting early hands them the remaining time INSTEAD of
    // burning it all on a hopeless monolithic run — deterministic and
    // purely a capacity decision (Err(Budget) → the caller's honest
    // Unknown-or-fallback, never a verdict).
    let inputs_len = inputs.len();
    let mut max_terms_seen = 0usize;
    let mut lms = lm_cache(&basis);
    loop {
        if next_pair >= pairs.len() {
            break;
        }
        if basis.len() > 8 * inputs_len + 64 || max_terms_seen > 512 {
            if std::env::var_os("NIXIE_FF_STATS").is_some() {
                eprintln!(
                    "[ff-stats] bloat breaker: basis {} (cap {}), max terms {max_terms_seen}",
                    basis.len(),
                    8 * inputs_len + 64
                );
            }
            return Err(GrobnerError::Budget);
        }
        // Normal selection strategy: the pair minimizing the total degree
        // of the lcm of leading monomials (then the lcm itself).
        let mut best = next_pair;
        let mut best_key = pair_key_lms(&lms, pairs[next_pair]);
        for (cand, pair) in pairs.iter().enumerate().skip(next_pair + 1) {
            // Selection scans are WORK: each candidate costs one LCM,
            // and the scan is O(#pairs) per selection — quadratic over
            // the cascade. Uncharged, a blowup's pair bookkeeping alone
            // outran the budget by an order of magnitude (the chain
            // 64×96 profile: the monolithic attempt spent 700 s in
            // scan-side LCM/monomial churn before ever exhausting its
            // tick budget — T5's "charge what runs" violated at the
            // selection layer).
            budget.charge(1)?;
            let key = pair_key_lms(&lms, *pair);
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

        // The SOUND chain criterion, at selection time (the processed-
        // zero information is maximally available there).
        let mut chain_verified = false;
        let lcm_ij = monomial_lcm(&lms[i], &lms[j]);
        // Index both `lms` and `zero_pairs` by element index; the
        // range loop is the clearest shape for the indexed scan.
        #[allow(clippy::needless_range_loop)]
        for k in 0..basis.len() {
            if k == i || k == j {
                continue;
            }
            budget.charge(1)?;
            if lcm_ij.div(&lms[k]).is_none() {
                continue;
            }
            let (a, b) = (k.min(i), k.max(i));
            let (c, d) = (k.min(j), k.max(j));
            if zero_pairs.contains(&(a, b)) && zero_pairs.contains(&(c, d)) {
                chain_verified = true;
                break;
            }
        }
        if chain_verified {
            zero_pairs.insert((i, j));
            continue;
        }

        let cost = u64::try_from(basis[i].poly.n_terms() + basis[j].poly.n_terms())
            .unwrap_or(u64::MAX / 2);
        budget.charge(cost.saturating_add(1))?;
        let spoly = s_polynomial(f, &basis[i], &basis[j]);
        let (reduced, _) = reduce_traced(f, &spoly, &basis, &lms, budget)?;
        if reduced.poly.is_zero() {
            zero_pairs.insert((i, j));
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
            let (again, changed) = reduce_traced(f, &reduced, &basis, &lms, budget)?;
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
        max_terms_seen = max_terms_seen.max(reduced.poly.n_terms());
        lms.push(reduced.poly.lm(DEGREVLEX).unwrap_or_else(Monomial::unit));
        basis.push(reduced);
        let n = basis.len() - 1;
        for k in 0..n {
            if !criterion_applies_lms(&lms, k, n) {
                pairs.push((k, n));
            } else {
                zero_pairs.insert((k, n));
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
/// The leading monomials of a basis slice, computed once (an `lm()` is
/// a full terms-map scan; the pair-selection scan and the reduction
/// scans consult them O(pairs) and O(basis) times respectively —
/// recomputing made the chain 64×96 cascade spend minutes in `lm`
/// alone, ~1000× the per-unit budget charge).
fn lm_cache(basis: &[TracedPoly]) -> Vec<Monomial> {
    basis
        .iter()
        .map(|t| t.poly.lm(DEGREVLEX).unwrap_or_else(Monomial::unit))
        .collect()
}

fn pair_key_lms(lms: &[Monomial], pair: (usize, usize)) -> (u32, Monomial) {
    let l = monomial_lcm(&lms[pair.0], &lms[pair.1]);
    (l.total_degree(), l)
}

/// Gebauer–Möller discard test for the pair (i, j):
/// 1. Buchberger's first criterion — relatively prime leading monomials:
///    the S-polynomial reduces to zero.
/// 2. The third-element criterion — some other leading monomial strictly
///    divides the pair's lcm.
fn criterion_applies_lms(lms: &[Monomial], i: usize, j: usize) -> bool {
    let (lmi, lmj) = (&lms[i], &lms[j]);
    // 1. Relatively prime: no shared variable.
    let coprime = lmi.vars().iter().all(|vp| lmj.degree(vp.var) == 0);
    if coprime {
        return true;
    }
    // 2. Third element: DISABLED (2026-09-18). The simplified second
    //    criterion (`lm_k | lcm(i,j)` for some k) is only sound under
    //    the full Gebauer–Möller installation discipline (pair-lcm
    //    chain conditions on the incremental update order), which this
    //    engine does not implement — measured: whole-ring ideals
    //    returning non-bases with `is_gb = true` (missed refutations:
    //    seeds 0xBEEF_0001 5×6 after the duplicate-lm fix, 0xF00D_CAFE
    //    3×4 through the INITIAL pair set, which used the sibling
    //    `criterion_applies`). Re-enabling requires the proper
    //    Gebauer–Möller pair rules AND the battery in
    //    tests/ff_gb_seed_dedup_regression.rs green.
    false
}

fn criterion_applies(basis: &[TracedPoly], i: usize, j: usize) -> bool {
    let (Some(lmi), Some(lmj)) = (basis[i].poly.lm(DEGREVLEX), basis[j].poly.lm(DEGREVLEX)) else {
        return false;
    };
    // 1. Relatively prime: no shared variable (Buchberger's first
    //    criterion — an unconditional theorem).
    lmi.vars().iter().all(|vp| lmj.degree(vp.var) == 0)
    // 2. Third element: DISABLED here as well — the INITIAL pair
    //    creation went through this sibling while the incremental path
    //    had it disabled, and the 3×4 reproducer's missing pairs were
    //    exactly the initial ones (the dual-computed trace agreed on
    //    every surviving pair; a criterion-1-only replay found the
    //    whole-ring constant in 13 pairs where the engine saw 7). See
    //    criterion_applies_lms for the full story.
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
    lms: &[Monomial],
    budget: &mut GrobnerBudget,
) -> Result<(TracedPoly, bool), GrobnerError> {
    let mut current = p.clone();
    let mut changed = false;
    while !current.poly.is_zero() {
        let Some(lt) = current.poly.lm(DEGREVLEX) else {
            break;
        };
        let mut cancelled = false;
        for (gi, g) in basis.iter().enumerate() {
            let lmg = &lms[gi];
            let Some(q) = monomial_div(&lt, lmg) else {
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
            // The step's true cost: the polynomial subtraction PLUS the
            // cofactor-row maintenance — `TracedPoly::sub` updates every
            // input's cofactor (n_inputs polynomial subtractions), and
            // `mul_monomial`/`scale` rebuilt them on the way in. The
            // first version charged only the poly side: with dozens of
            // inputs and growing elements the cascade did ~n_inputs× the
            // charged work, and a 2^24 budget meant minutes of grinding
            // instead of seconds (the chain-64×96 wall-vs-budget gap,
            // profiled to FieldCtx::add/SmallVec churn in the cofactor
            // rows — T5's charge-what-runs, at the tracer layer).
            // The actual row length (0 when untraced): the charge
            // follows the work really done.
            let n_inputs = current.cofactors.len() as u64;
            let sub_terms = sub.poly.n_terms() as u64;
            let poly_cost =
                u64::try_from(sub.poly.n_terms() + current.poly.n_terms()).unwrap_or(u64::MAX / 2);
            let cost = poly_cost
                .saturating_mul(1)
                .saturating_add(n_inputs.saturating_mul(sub_terms.max(1)));
            current = current.sub(f, &sub);
            budget.charge(cost.saturating_add(1))?;
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
        let others_lms = lm_cache(&others);
        let (reduced, _changed) = reduce_traced(f, &g, &others, &others_lms, budget)?;
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
                let cost = u64::try_from(sub.poly.n_terms() + current.poly.n_terms())
                    .unwrap_or(u64::MAX / 2);
                current = current.sub(f, &sub);
                budget.charge(cost.saturating_add(1))?;
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
            let cost = u64::try_from(sub.n_terms() + current.n_terms()).unwrap_or(u64::MAX / 2);
            current = current.sub(f, &sub);
            budget.charge(cost.saturating_add(1)).ok()?;
            cancelled = true;
            break;
        }
        if !cancelled {
            return Some(current);
        }
    }
    Some(current)
}

/// Reduction with cofactor tracking: computes `p − Σᵢ cof[i]·basis[i]`
/// alongside the normal form, so a reduction to zero yields `p`'s
/// expression over the basis — the branch-exhaustion certificate's
/// membership witness (§8's case trees: the branch polynomial and the
/// leaf refutations must present as combinations of the atoms).
///
/// Returns `None` on budget exhaustion (the caller must not use a
/// partial reduction). Monomial-operation-charged like every reduction
/// (the budget semantics trap).
pub fn normal_form_traced(
    f: &FieldCtx,
    p: &MPoly,
    basis: &GrobnerBasis,
    budget: &mut GrobnerBudget,
) -> Option<(MPoly, Vec<MPoly>)> {
    let mut current = p.clone();
    let mut cofactors: Vec<MPoly> = basis.basis.iter().map(|_| MPoly::zero()).collect();
    while !current.is_zero() {
        let lt = current.lm(DEGREVLEX)?;
        let mut cancelled = false;
        for (i, g) in basis.basis.iter().enumerate() {
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
            let add = mul_by_monomial(f, &MPoly::constant(f, &factor), &q);
            cofactors[i] = cofactors[i].add(f, &add);
            let cost = u64::try_from(sub.n_terms() + current.n_terms()).unwrap_or(u64::MAX / 2);
            current = current.sub(f, &sub);
            budget.charge(cost.saturating_add(1)).ok()?;
            cancelled = true;
            break;
        }
        if !cancelled {
            return Some((current, cofactors));
        }
    }
    Some((current, cofactors))
}

/// The minimal polynomial of `x` modulo a zero-dimensional ideal: find
/// the first linear dependency among `1, x, x², …` in the quotient ring
/// (as vectors over the standard monomials) by Gaussian elimination.
///
/// Each Krylov vector carries its *defining polynomial* alongside the
/// quotient vector, and every row operation updates both — the
/// dependency's polynomial is then the minimal polynomial by
/// construction. (Carrying only each row's top degree — the first
/// version — is wrong whenever back-substitution is needed: it returned
/// non-annihilating polynomials at degree ≥ 2, which the planted
/// fuzzer surfaced as false UNSATs at BN254.)
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

    // A Krylov element: the quotient vector of p(x), plus p's dense
    // coefficient vector (little-endian). The pair moves together through
    // every row operation, so `vector = p(x) in the quotient` is an
    // invariant and a zero vector certifies that p annihilates x.
    #[derive(Clone)]
    struct Krylov {
        vector: Vec<Limbs>,
        poly: Vec<Limbs>,
    }

    // One Krylov step: k ↦ x·k. The vector is the normal form of
    // x·p(x); the polynomial is p SHIFTED one degree up (p_d · x — a
    // shift, not an append: the first version copied p into the low
    // slots and set the new top slot, producing `1 + x` from `1`).
    fn mul_by_x(
        f: &FieldCtx,
        basis: &GrobnerBasis,
        std_monomials: &[Monomial],
        index_of: &rustc_hash::FxHashMap<Monomial, usize>,
        x: Var,
        k: &Krylov,
        budget: &mut GrobnerBudget,
    ) -> Option<Krylov> {
        let mut poly = MPoly::zero();
        for (i, c) in k.poly.iter().enumerate() {
            if f.is_zero(c) {
                continue;
            }
            poly.add_term(f, Monomial::from_var_power(x, (i + 1) as u32), c);
        }
        let reduced = normal_form(f, &poly, basis, budget)?;
        let mut vector = vec![f.zero(); std_monomials.len()];
        for (m, c) in reduced.terms_iter() {
            let pos = index_of.get(m)?;
            vector[*pos] = c.clone();
        }
        let mut next_poly = vec![f.zero(); k.poly.len() + 1];
        for (i, c) in k.poly.iter().enumerate() {
            next_poly[i + 1] = c.clone();
        }
        Some(Krylov {
            vector,
            poly: next_poly,
        })
    }

    let unit_pos = index_of.get(&Monomial::unit()).copied()?;
    let start = {
        let mut vector = vec![f.zero(); n];
        vector[unit_pos] = f.one();
        Krylov {
            vector,
            poly: vec![f.one()],
        }
    };

    let mut rows: Vec<Krylov> = Vec::new();
    let mut current = start;
    for d in 0..=n {
        budget
            .charge(u64::try_from(n).unwrap_or(u64::MAX / 2))
            .ok()?;
        // Reduce `current` against the echelon rows, updating both halves.
        let mut acc = current.clone();
        for row in &rows {
            let pivot = row.vector.iter().position(|c| !f.is_zero(c))?;
            if f.is_zero(&acc.vector[pivot]) {
                continue;
            }
            let Some(row_inv) = f.inv(&row.vector[pivot]) else {
                continue;
            };
            let ratio = f.mul(&acc.vector[pivot], &row_inv);
            for i in 0..n {
                let sub = f.mul(&row.vector[i], &ratio);
                acc.vector[i] = f.sub(&acc.vector[i], &sub);
            }
            // poly -= ratio * row.poly (row.poly has degree ≤ d)
            for i in 0..acc.poly.len().min(row.poly.len()) {
                let sub = f.mul(&row.poly[i], &ratio);
                acc.poly[i] = f.sub(&acc.poly[i], &sub);
            }
        }
        if std::env::var("FFDBG_MP").is_ok() {
            let ps: Vec<String> = acc
                .poly
                .iter()
                .map(|c| f.to_biguint(c).to_string())
                .collect();
            eprintln!("[mp] d={d} poly {ps:?}");
        }
        if acc.vector.iter().all(|c| f.is_zero(c)) {
            // acc.poly annihilates x in the quotient and is monic of
            // degree d: the minimal polynomial.
            return Some(UniPoly::from_coeffs(acc.poly));
        }
        rows.push(acc);
        current = mul_by_x(f, basis, &std_monomials, &index_of, x, &current, budget)?;
        let _ = d;
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
