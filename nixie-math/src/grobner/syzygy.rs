//! Syzygy Computations for Gröbner Bases.
//!
//! Implements:
//! - S-polynomial computation
//! - Syzygy modules
//! - Buchberger's criteria
//! - Resolution of S-polynomials
//! - Critical pair management

use crate::polynomial::{Monomial, MonomialOrder, Polynomial, Term, Var};
#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// Syzygy computer for Gröbner basis algorithms.
pub struct SyzygyComputer {
    /// Critical pairs priority queue
    critical_pairs: BinaryHeap<CriticalPair>,
    /// Syzygy module generators
    syzygies: Vec<Syzygy>,
    /// Buchberger criteria cache (POSITIVE results only — criterion
    /// 2's truth grows monotonically with `zero_pairs`, so a cached
    /// `false` can only be stale)
    criteria_cache: FxHashMap<(usize, usize), BuchbergerCriteria>,
    /// Pairs whose S-polynomial PROVABLY reduces to zero: processed to
    /// zero, coprime leading monomials (criterion 1 is an unconditional
    /// theorem), or recursively chain-verified. The sound form of
    /// Buchberger's second criterion consults this set — a pair (i, j)
    /// is discardable only when some k has `lm_k | lcm(lm_i, lm_j)` AND
    /// both (i,k) and (j,k) are themselves in the set. The simplified
    /// form this replaces (a bare `lm_k | lcm`) is UNSOUND — the
    /// missed-refutation class root-caused in the 𝔽_p engine on
    /// 2026-09-18; tests/grobner_rational_soundness.rs is this
    /// module's gate.
    zero_pairs: std::collections::HashSet<(usize, usize)>,
    /// Statistics
    stats: SyzygyStats,
}

/// A critical pair (S-polynomial pair).
#[derive(Debug, Clone)]
pub struct CriticalPair {
    /// First polynomial index
    pub i: usize,
    /// Second polynomial index
    pub j: usize,
    /// LCM of leading monomials
    pub lcm: Monomial,
    /// Priority (based on monomial order)
    pub priority: i64,
    /// Sugar degree
    pub sugar: usize,
}

/// A syzygy relation: Σ aᵢfᵢ = 0.
#[derive(Debug, Clone)]
pub struct Syzygy {
    /// Coefficients: polynomial index → coefficient polynomial
    pub coefficients: FxHashMap<usize, Polynomial>,
    /// Degree of the syzygy
    pub degree: usize,
}

/// Buchberger's criteria for eliminating critical pairs.
#[derive(Debug, Clone)]
pub struct BuchbergerCriteria {
    /// Criterion 1: Relatively prime leading terms
    pub criterion1: bool,
    /// Criterion 2: LCM equals product (chain criterion)
    pub criterion2: bool,
}

/// Syzygy computation statistics.
#[derive(Debug, Clone, Default)]
pub struct SyzygyStats {
    /// Critical pairs generated
    pub pairs_generated: usize,
    /// Critical pairs eliminated by criteria
    pub pairs_eliminated: usize,
    /// S-polynomials computed
    pub s_polynomials_computed: usize,
    /// S-polynomials reduced to zero
    pub zero_reductions: usize,
    /// Syzygies found
    pub syzygies_found: usize,
    /// Criterion 1 applications
    pub criterion1_apps: usize,
    /// Criterion 2 applications
    pub criterion2_apps: usize,
}

impl SyzygyComputer {
    /// Create a new syzygy computer.
    pub fn new() -> Self {
        Self {
            critical_pairs: BinaryHeap::new(),
            syzygies: Vec::new(),
            criteria_cache: FxHashMap::default(),
            zero_pairs: std::collections::HashSet::new(),
            stats: SyzygyStats::default(),
        }
    }

    /// Record a pair whose S-polynomial provably reduces to zero —
    /// after a processed-to-zero reduction, or a criteria-based
    /// discard. The caller MUST call this for every such event; the
    /// chain criterion's soundness rests on this set containing only
    /// PROVEN facts.
    pub fn record_zero_pair(&mut self, i: usize, j: usize) {
        self.zero_pairs.insert((i.min(j), i.max(j)));
    }

    /// Generate critical pair for two polynomials.
    pub fn generate_critical_pair(
        &mut self,
        i: usize,
        j: usize,
        fi: &Polynomial,
        fj: &Polynomial,
    ) -> Option<CriticalPair> {
        if i >= j {
            return None;
        }

        self.stats.pairs_generated += 1;

        // Get leading monomials
        let lt_i = fi.leading_monomial()?;
        let lt_j = fj.leading_monomial()?;

        // Compute LCM
        let lcm = Self::monomial_lcm(lt_i, lt_j);

        // Compute priority (degree of LCM)
        let priority = -(lcm.total_degree() as i64);

        // Sugar degree
        let sugar_i = fi.sugar_degree() as u32;
        let sugar_j = fj.sugar_degree() as u32;
        let sugar = sugar_i.max(sugar_j) + lcm.total_degree()
            - lt_i.total_degree().max(lt_j.total_degree());

        Some(CriticalPair {
            i,
            j,
            lcm,
            priority,
            sugar: sugar as usize,
        })
    }

    /// Add critical pair to queue.
    pub fn add_critical_pair(&mut self, pair: CriticalPair) {
        self.critical_pairs.push(pair);
    }

    /// Get next critical pair from queue.
    pub fn pop_critical_pair(&mut self) -> Option<CriticalPair> {
        self.critical_pairs.pop()
    }

    /// Apply Buchberger's criteria to eliminate pairs.
    pub fn apply_buchberger_criteria(
        &mut self,
        i: usize,
        j: usize,
        fi: &Polynomial,
        fj: &Polynomial,
        basis: &[Polynomial],
    ) -> bool {
        // Cache lookup: POSITIVE results only (see the struct field's
        // note — a negative-result cache goes stale as zero_pairs
        // grows).
        if let Some(criteria) = self.criteria_cache.get(&(i, j))
            && (criteria.criterion1 || criteria.criterion2)
        {
            self.stats.pairs_eliminated += 1;
            return true;
        }

        // Criterion 1: Relatively prime leading terms
        let criterion1 = self.check_criterion1(fi, fj);

        if criterion1 {
            self.stats.criterion1_apps += 1;
            self.criteria_cache.insert(
                (i, j),
                BuchbergerCriteria {
                    criterion1: true,
                    criterion2: false,
                },
            );
            // Criterion 1 is an unconditional theorem: the pair is
            // provably zero (a chain link may cite it).
            self.zero_pairs.insert((i.min(j), i.max(j)));
            self.stats.pairs_eliminated += 1;
            return true;
        }

        // Criterion 2: Chain criterion
        let criterion2 = self.check_criterion2(i, j, fi, fj, basis);

        if criterion2 {
            self.stats.criterion2_apps += 1;
            self.criteria_cache.insert(
                (i, j),
                BuchbergerCriteria {
                    criterion1: false,
                    criterion2: true,
                },
            );
            // The verified chain proves this pair zero too.
            self.zero_pairs.insert((i.min(j), i.max(j)));
            self.stats.pairs_eliminated += 1;
            return true;
        }

        // No negative-result cache entry (see the lookup note above).
        false
    }

    /// Check Criterion 1: gcd(LM(fi), LM(fj)) = 1.
    fn check_criterion1(&self, fi: &Polynomial, fj: &Polynomial) -> bool {
        if let (Some(lt_i), Some(lt_j)) = (fi.leading_monomial(), fj.leading_monomial()) {
            // Check if leading monomials are relatively prime
            Self::are_relatively_prime(lt_i, lt_j)
        } else {
            false
        }
    }

    /// Check Criterion 2 (chain criterion, SOUND form): (i, j) is
    /// discardable only when some k has `lm_k | lcm(lm_i, lm_j)` AND
    /// both (i,k) and (j,k) are in `zero_pairs` — provably-zero pairs
    /// (a DAG by construction). Two defects fixed relative to the old
    /// form: (a) the bare chain scan was the UNSOUND simplified
    /// criterion — its divisibility side-checks (`lcm_ik | lcm` etc.)
    /// were tautologies whenever the outer divisibility held, so it
    /// reduced to `∃k: lm_k | lcm`, which drops S-polynomials that do
    /// not reduce to zero (the missed-refutation class, 2026-09-18);
    /// (b) the `lcm == product` early return was criterion 1 restated
    /// — and until this change it ran on VACUOUS monomial helpers (see
    /// `monomial_lcm`'s note), making criterion 1 fire on EVERY pair
    /// and the whole engine a decorated no-op that computed zero
    /// S-polynomials.
    fn check_criterion2(
        &self,
        i: usize,
        j: usize,
        fi: &Polynomial,
        fj: &Polynomial,
        basis: &[Polynomial],
    ) -> bool {
        let (Some(lt_i), Some(lt_j)) = (fi.leading_monomial(), fj.leading_monomial()) else {
            return false;
        };
        let lcm = Self::monomial_lcm(lt_i, lt_j);
        for (k, fk) in basis.iter().enumerate() {
            if k == i || k == j {
                continue;
            }
            let Some(lt_k) = fk.leading_monomial() else {
                continue;
            };
            if !Self::monomial_divides(lt_k, &lcm) {
                continue;
            }
            let (a, b) = (k.min(i), k.max(i));
            let (c, d) = (k.min(j), k.max(j));
            if self.zero_pairs.contains(&(a, b)) && self.zero_pairs.contains(&(c, d)) {
                return true;
            }
        }
        false
    }

    /// Compute S-polynomial for a critical pair.
    pub fn compute_s_polynomial(
        &mut self,
        pair: &CriticalPair,
        fi: &Polynomial,
        fj: &Polynomial,
    ) -> Polynomial {
        self.stats.s_polynomials_computed += 1;

        if let (Some(lt_i), Some(lt_j)) = (fi.leading_monomial(), fj.leading_monomial()) {
            // Compute cofactors
            let cofactor_i = Self::monomial_div(&pair.lcm, lt_i);
            let cofactor_j = Self::monomial_div(&pair.lcm, lt_j);

            // Get leading coefficients
            let lc_i = fi.leading_coeff();
            let lc_j = fj.leading_coeff();

            // S(fi, fj) = (lcm/lt_i)/lc_i * fi - (lcm/lt_j)/lc_j * fj
            let term_i = fi
                .mul_monomial(&cofactor_i)
                .mul_scalar(&(BigRational::one() / &lc_i));
            let term_j = fj
                .mul_monomial(&cofactor_j)
                .mul_scalar(&(BigRational::one() / &lc_j));

            &term_i - &term_j
        } else {
            Polynomial::zero()
        }
    }

    /// Record a syzygy.
    pub fn record_syzygy(&mut self, syzygy: Syzygy) {
        self.stats.syzygies_found += 1;
        self.syzygies.push(syzygy);
    }

    /// Create syzygy from S-polynomial reduction to zero.
    pub fn create_syzygy(
        &mut self,
        i: usize,
        j: usize,
        fi: &Polynomial,
        fj: &Polynomial,
    ) -> Syzygy {
        self.stats.zero_reductions += 1;

        let mut coefficients = FxHashMap::default();

        if let (Some(lt_i), Some(lt_j)) = (fi.leading_monomial(), fj.leading_monomial()) {
            let lcm = Self::monomial_lcm(lt_i, lt_j);
            let cofactor_i = Self::monomial_div(&lcm, lt_i);
            let cofactor_j = Self::monomial_div(&lcm, lt_j);

            let lc_i = fi.leading_coeff();
            let lc_j = fj.leading_coeff();

            // Coefficient for fi
            let coeff_i = Polynomial::from_monomial(cofactor_i, BigRational::one() / &lc_i);
            coefficients.insert(i, coeff_i);

            // Coefficient for fj (negative)
            let coeff_j = Polynomial::from_monomial(cofactor_j, -(BigRational::one() / &lc_j));
            coefficients.insert(j, coeff_j);

            Syzygy {
                coefficients,
                degree: lcm.total_degree() as usize,
            }
        } else {
            Syzygy {
                coefficients: FxHashMap::default(),
                degree: 0,
            }
        }
    }

    /// Monomial LCM (per-variable max of exponents). Rewritten 2026-09-18
    /// against the REAL `Monomial::vars()` API — the previous version went
    /// through the `MonomialHelper` stub trait whose `powers()` returned a
    /// **static empty map** ("Simplified"), making this and every other
    /// helper vacuous: `are_relatively_prime` was always-true (so criterion
    /// 1 skipped EVERY pair and the engine computed zero S-polynomials),
    /// and lcm/mul/div returned near-unit monomials. The stub traits are
    /// deleted below; these are the real operations.
    fn monomial_lcm(m1: &Monomial, m2: &Monomial) -> Monomial {
        let mut pairs: Vec<(Var, u32)> = m1.vars().iter().map(|vp| (vp.var, vp.power)).collect();
        for vp2 in m2.vars() {
            match pairs.iter_mut().find(|(v, _)| *v == vp2.var) {
                Some((_, p)) => *p = (*p).max(vp2.power),
                None => pairs.push((vp2.var, vp2.power)),
            }
        }
        Monomial::from_powers(pairs)
    }

    /// Monomial GCD (per-variable min of exponents).
    #[allow(dead_code)]
    fn monomial_gcd(m1: &Monomial, m2: &Monomial) -> Monomial {
        Monomial::from_powers(m1.vars().iter().filter_map(|vp1| {
            m2.vars()
                .iter()
                .find(|vp2| vp2.var == vp1.var)
                .map(|vp2| (vp1.var, vp1.power.min(vp2.power)))
        }))
    }

    /// Monomial multiplication (exponent sums — `from_powers` sums).
    /// Kept real (not stubbed) for any future caller; the criteria no
    /// longer use it since the vacuous `lcm == product` check went.
    #[allow(dead_code)]
    fn monomial_mul(m1: &Monomial, m2: &Monomial) -> Monomial {
        Monomial::from_powers(
            m1.vars()
                .iter()
                .map(|vp| (vp.var, vp.power))
                .chain(m2.vars().iter().map(|vp| (vp.var, vp.power))),
        )
    }

    /// Monomial division (saturating exponent differences).
    fn monomial_div(m1: &Monomial, m2: &Monomial) -> Monomial {
        Monomial::from_powers(m1.vars().iter().filter_map(|vp1| {
            match m2.vars().iter().find(|vp2| vp2.var == vp1.var) {
                Some(vp2) => vp1.power.checked_sub(vp2.power).map(|p| (vp1.var, p)),
                None => Some((vp1.var, vp1.power)),
            }
        }))
    }

    /// Check if m1 divides m2.
    fn monomial_divides(m1: &Monomial, m2: &Monomial) -> bool {
        m1.vars().iter().all(|vp1| {
            m2.vars()
                .iter()
                .any(|vp2| vp2.var == vp1.var && vp2.power >= vp1.power)
        })
    }

    /// Check if two monomials are relatively prime (no shared
    /// variable — `Monomial` never stores zero exponents).
    fn are_relatively_prime(m1: &Monomial, m2: &Monomial) -> bool {
        m1.vars()
            .iter()
            .all(|vp1| !m2.vars().iter().any(|vp2| vp2.var == vp1.var))
    }

    /// Get syzygy module.
    pub fn syzygy_module(&self) -> &[Syzygy] {
        &self.syzygies
    }

    /// Get statistics.
    pub fn stats(&self) -> &SyzygyStats {
        &self.stats
    }

    /// Clear critical pairs.
    pub fn clear(&mut self) {
        self.critical_pairs.clear();
        self.criteria_cache.clear();
    }
}

// Implement Ord for CriticalPair to use in BinaryHeap
impl Ord for CriticalPair {
    fn cmp(&self, other: &Self) -> Ordering {
        // Higher priority pairs come first (max heap)
        self.priority
            .cmp(&other.priority)
            .then_with(|| self.sugar.cmp(&other.sugar))
            .then_with(|| self.i.cmp(&other.i))
            .then_with(|| self.j.cmp(&other.j))
    }
}

impl PartialOrd for CriticalPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for CriticalPair {
    fn eq(&self, other: &Self) -> bool {
        self.i == other.i && self.j == other.j
    }
}

impl Eq for CriticalPair {}

impl Default for SyzygyComputer {
    fn default() -> Self {
        Self::new()
    }
}

// Helper trait extensions for Polynomial: REAL delegations to
// `Polynomial`'s native operations. The previous definitions were
// stubs ("Simplified: return self" for mul_monomial/mul_scalar, zero
// for from_monomial), which made `compute_s_polynomial` compute
// fi - fj with no scaling and `create_syzygy` fabricate coefficients
// — garbage through every path that used them (2026-09-18).
#[allow(dead_code)]
trait PolynomialSyzygy {
    fn sugar_degree(&self) -> usize;
    fn mul_monomial(&self, m: &Monomial) -> Polynomial;
    fn mul_scalar(&self, s: &BigRational) -> Polynomial;
    fn from_monomial(m: Monomial, coeff: BigRational) -> Polynomial;
    fn zero() -> Polynomial;
}

#[allow(dead_code)]
impl PolynomialSyzygy for Polynomial {
    fn sugar_degree(&self) -> usize {
        // The sugar heuristic approximated by total degree (as before —
        // an approximation, not a correctness matter).
        self.total_degree() as usize
    }

    fn mul_monomial(&self, m: &Monomial) -> Polynomial {
        Polynomial::mul_monomial(self, m)
    }

    fn mul_scalar(&self, s: &BigRational) -> Polynomial {
        Polynomial::scale(self, s)
    }

    fn from_monomial(m: Monomial, coeff: BigRational) -> Polynomial {
        Polynomial::from_terms([Term { coeff, monomial: m }], MonomialOrder::default())
    }

    fn zero() -> Polynomial {
        Polynomial::constant(BigRational::zero())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_syzygy_computer() {
        let computer = SyzygyComputer::new();
        assert_eq!(computer.stats.pairs_generated, 0);
    }

    #[test]
    fn test_critical_pair_ordering() {
        let pair1 = CriticalPair {
            i: 0,
            j: 1,
            lcm: Monomial::unit(),
            priority: -5,
            sugar: 3,
        };

        let pair2 = CriticalPair {
            i: 0,
            j: 2,
            lcm: Monomial::unit(),
            priority: -3,
            sugar: 2,
        };

        // Higher priority (less negative) comes first
        assert!(pair2 > pair1);
    }

    #[test]
    fn test_monomial_lcm() {
        let m1 = Monomial::unit();
        let m2 = Monomial::unit();

        let lcm = SyzygyComputer::monomial_lcm(&m1, &m2);
        assert_eq!(lcm.total_degree(), 0);
    }

    #[test]
    fn test_relatively_prime() {
        let m1 = Monomial::unit();
        let m2 = Monomial::unit();

        assert!(SyzygyComputer::are_relatively_prime(&m1, &m2));
    }

    #[test]
    fn test_syzygy_creation() {
        let mut computer = SyzygyComputer::new();

        let f1 = Polynomial::zero();
        let f2 = Polynomial::zero();

        let syzygy = computer.create_syzygy(0, 1, &f1, &f2);
        assert_eq!(syzygy.degree, 0);
    }
}
