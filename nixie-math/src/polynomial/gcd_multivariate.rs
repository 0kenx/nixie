//! Multivariate Polynomial GCD.
//!
//! Computes greatest common divisors of genuinely multivariate polynomials
//! over the rationals using the classical *primitive polynomial remainder
//! sequence* (primitive PRS).
//!
//! ## Algorithm
//!
//! For `f, g` in `Q[x_1, ..., x_n]`:
//!
//! 1. Choose a main variable `v` and view both operands as univariate in
//!    `v` with coefficients in `Q[x_1, ..., x_n] \ {v}`.
//! 2. Split each operand into its content (the GCD of those coefficients,
//!    computed recursively over the *remaining* variables) and its
//!    primitive part (`operand / content`, an exact division).
//! 3. `gcd(f, g) = gcd(content(f), content(g)) * gcd(pp(f), pp(g))`, where
//!    the primitive-part GCD is the last nonzero element of the pseudo
//!    remainder sequence `a, b, prem(a, b, v), ...`, reduced to its
//!    primitive part at every step to keep coefficients small.
//!
//! Step 2's recursion is what bounds the whole computation: coefficients
//! with respect to `v` contain no occurrence of `v`, so every recursive
//! call works over a strictly smaller variable set. The recursion depth is
//! therefore at most the number of distinct variables of the inputs (see
//! [`MultivariateGcdConfig::max_recursion_depth`]). Step 3's loop is bounded
//! by `deg_v(b)`, which strictly decreases per pseudo-division.
//!
//! ## References
//!
//! - Knuth: "TAOCP Vol 2" Section 4.6.1 (primitive PRS)
//! - von zur Gathen & Gerhard: "Modern Computer Algebra" Chapter 6
//! - Reference: Z3's `polynomial.cpp`

use super::{Monomial, Polynomial, Term, Var};
#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::Zero;

/// Configuration for multivariate GCD.
#[derive(Debug, Clone)]
pub struct MultivariateGcdConfig {
    /// Main variable selection strategy.
    pub var_selection: VarSelectionStrategy,
    /// Reduce every intermediate pseudo-remainder to its primitive part.
    ///
    /// This is the difference between a *primitive* PRS and a plain
    /// (Euclidean) pseudo-remainder sequence: it costs one content GCD per
    /// step but keeps the coefficients from growing exponentially. Turning
    /// it off does **not** change the answer -- the content/primitive split
    /// of the *inputs*, and of the final PRS element, is required for
    /// correctness and is always performed.
    pub use_primitive_part: bool,
    /// Maximum recursion depth.
    ///
    /// Each level of recursion eliminates one variable (see the module
    /// documentation), so a value of `n` supports inputs in up to `n`
    /// distinct variables. Beyond that the engine gives up and returns the
    /// trivial common divisor `1`, recording the fact in
    /// [`MultivariateGcdStats::incomplete`].
    pub max_recursion_depth: usize,
}

impl Default for MultivariateGcdConfig {
    fn default() -> Self {
        Self {
            var_selection: VarSelectionStrategy::MaxDegree,
            use_primitive_part: true,
            max_recursion_depth: 100,
        }
    }
}

/// Strategy for selecting main variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarSelectionStrategy {
    /// Choose variable with maximum total degree.
    MaxDegree,
    /// Choose variable with maximum degree in leading term.
    MaxLeadingDegree,
    /// Choose first variable in order.
    FirstVariable,
}

/// Statistics for multivariate GCD.
#[derive(Debug, Clone, Default)]
pub struct MultivariateGcdStats {
    /// Recursion depth reached.
    pub max_depth: usize,
    /// Primitive part decompositions.
    pub primitive_decompositions: u64,
    /// Content GCD computations.
    pub content_gcds: u64,
    /// Pseudo-divisions performed.
    pub pseudo_divisions: u64,
    /// Set when the engine could not compute the *greatest* common divisor
    /// and fell back to the trivial common divisor `1`.
    ///
    /// This happens when the recursion-depth ceiling
    /// ([`MultivariateGcdConfig::max_recursion_depth`]) is reached, i.e. the
    /// inputs have more distinct variables than the budget allows.
    ///
    /// The returned polynomial is still a *sound* common divisor -- `1`
    /// divides everything -- but it is not necessarily the *greatest* one,
    /// so callers lose simplification rather than getting a wrong answer.
    /// The return type of [`MultivariateGcdEngine::gcd`] is `Polynomial`,
    /// which has no channel to say "I gave up"; this flag is that channel,
    /// mirroring `IsolationStats::incomplete` elsewhere in this crate.
    pub incomplete: bool,
}

/// Multivariate GCD engine.
pub struct MultivariateGcdEngine {
    /// Configuration.
    config: MultivariateGcdConfig,
    /// Statistics.
    stats: MultivariateGcdStats,
}

impl MultivariateGcdEngine {
    /// Create a new multivariate GCD engine.
    pub fn new(config: MultivariateGcdConfig) -> Self {
        Self {
            config,
            stats: MultivariateGcdStats::default(),
        }
    }

    /// Create with default configuration.
    pub fn default_config() -> Self {
        Self::new(MultivariateGcdConfig::default())
    }

    /// Compute GCD of two multivariate polynomials.
    ///
    /// The result is normalized to be monic (leading coefficient `1` with
    /// respect to the polynomial's monomial order); GCDs over a field are
    /// only defined up to a unit, and this is the usual convention.
    ///
    /// If [`MultivariateGcdStats::incomplete`] is set afterwards, the result
    /// is a sound but possibly non-greatest common divisor.
    pub fn gcd(&mut self, p: &Polynomial, q: &Polynomial) -> Polynomial {
        let g = self.gcd_recursive(p, q, 0);
        self.normalize_gcd(&g)
    }

    /// Recursive GCD computation.
    ///
    /// `depth` counts eliminated variables, not stack frames of an unbounded
    /// walk: every recursive call below operates on polynomials whose
    /// variable set is strictly smaller than this call's, so the recursion
    /// terminates after at most `|vars(p) union vars(q)|` levels. The
    /// configured ceiling is the hard backstop for pathological variable
    /// counts and is reported honestly through `stats.incomplete`.
    fn gcd_recursive(&mut self, p: &Polynomial, q: &Polynomial, depth: usize) -> Polynomial {
        if depth > self.stats.max_depth {
            self.stats.max_depth = depth;
        }

        if depth >= self.config.max_recursion_depth {
            self.stats.incomplete = true;
            return Polynomial::one();
        }

        // Base cases.
        if p.is_zero() {
            return q.clone();
        }
        if q.is_zero() {
            return p.clone();
        }
        // Over a field every nonzero constant is a unit, so a constant
        // operand forces a unit GCD.
        if p.is_constant() || q.is_constant() {
            return Polynomial::one();
        }

        let mut vars = p.vars();
        vars.extend(q.vars());
        vars.sort_unstable();
        vars.dedup();

        match vars.len() {
            // Unreachable in practice: a variable-free nonzero polynomial is
            // constant and was handled above. Handled explicitly rather than
            // falling through to a main-variable choice that would have no
            // variable to choose.
            0 => return Polynomial::one(),
            // Both operands live in the same single variable.
            1 => return p.gcd_univariate(q),
            _ => {}
        }

        let main_var = self.select_main_variable(p, q);

        let (p_content, p_primitive) = self.extract_content(p, main_var, depth);
        let (q_content, q_primitive) = self.extract_content(q, main_var, depth);
        self.stats.primitive_decompositions += 2;

        // gcd(p, q) = gcd(content(p), content(q)) * gcd(pp(p), pp(q))
        let content_gcd = self.gcd_recursive(&p_content, &q_content, depth + 1);
        self.stats.content_gcds += 1;

        let primitive_gcd = self.primitive_prs(&p_primitive, &q_primitive, main_var, depth);

        content_gcd.mul(&primitive_gcd)
    }

    /// Primitive polynomial remainder sequence in `var`.
    ///
    /// Both operands must already be primitive with respect to `var`. The
    /// last nonzero element of the sequence, made primitive, is
    /// `gcd(f, g)` up to a unit.
    ///
    /// Termination: `deg_var(prem(a, b, var)) < deg_var(b)` by construction,
    /// so the degree in `var` of the trailing element strictly decreases
    /// every iteration.
    fn primitive_prs(
        &mut self,
        f: &Polynomial,
        g: &Polynomial,
        var: Var,
        depth: usize,
    ) -> Polynomial {
        let mut a = f.clone();
        let mut b = g.clone();

        if a.degree(var) < b.degree(var) {
            core::mem::swap(&mut a, &mut b);
        }

        while !b.is_zero() {
            if b.degree(var) == 0 {
                // `b` is primitive with respect to `var` and free of `var`,
                // hence a unit: the primitive parts are coprime.
                return Polynomial::one();
            }

            let r = pseudo_remainder(&a, &b, var);
            self.stats.pseudo_divisions += 1;

            a = b;
            b = if r.is_zero() || !self.config.use_primitive_part {
                r
            } else {
                self.extract_content(&r, var, depth).1
            };
        }

        if a.is_zero() {
            return Polynomial::zero();
        }

        // The trailing element may carry a spurious content picked up from
        // the pseudo-division multipliers; strip it so the result actually
        // divides both inputs.
        self.extract_content(&a, var, depth).1
    }

    /// Select main variable for recursion.
    fn select_main_variable(&self, p: &Polynomial, q: &Polynomial) -> Var {
        match self.config.var_selection {
            VarSelectionStrategy::MaxDegree => self.select_by_max_degree(p, q),
            VarSelectionStrategy::MaxLeadingDegree => self.select_by_leading_degree(p, q),
            VarSelectionStrategy::FirstVariable => {
                // Get first variable from either polynomial
                p.vars()
                    .first()
                    .copied()
                    .or_else(|| q.vars().first().copied())
                    .unwrap_or(0)
            }
        }
    }

    /// Select variable with maximum total degree.
    ///
    /// Ties are broken deterministically in favour of the highest variable
    /// index, matching the "largest variable is the main variable"
    /// convention used elsewhere in this crate.
    fn select_by_max_degree(&self, p: &Polynomial, q: &Polynomial) -> Var {
        let mut vars = p.vars();
        vars.extend(q.vars());
        vars.sort_unstable();
        vars.dedup();

        vars.iter()
            .max_by_key(|var| p.degree(**var).max(q.degree(**var)))
            .copied()
            .unwrap_or(0)
    }

    /// Select variable with maximum degree in leading term.
    fn select_by_leading_degree(&self, p: &Polynomial, q: &Polynomial) -> Var {
        // Get leading monomials
        let p_lead = p.leading_monomial();
        let q_lead = q.leading_monomial();

        // Find variable with max degree in either leading monomial
        let mut max_var = 0;
        let mut max_degree = 0;

        if let Some(p_mono) = p_lead {
            for vp in p_mono.vars() {
                if vp.power > max_degree {
                    max_degree = vp.power;
                    max_var = vp.var;
                }
            }
        }

        if let Some(q_mono) = q_lead {
            for vp in q_mono.vars() {
                if vp.power > max_degree {
                    max_degree = vp.power;
                    max_var = vp.var;
                }
            }
        }

        max_var
    }

    /// Extract content and primitive part with respect to `main_var`.
    ///
    /// Returns `(content, primitive)` with `p = content * primitive`, where
    /// `content` is the GCD of the coefficients of `p` viewed as a
    /// univariate polynomial in `main_var` (and hence free of `main_var`).
    ///
    /// A unit content is normalized to `1`, so the primitive part is only
    /// determined up to a rational factor -- which is all a GCD needs.
    fn extract_content(
        &mut self,
        p: &Polynomial,
        main_var: Var,
        depth: usize,
    ) -> (Polynomial, Polynomial) {
        if p.is_zero() {
            return (Polynomial::one(), p.clone());
        }

        let coefficients = self.extract_coefficients(p, main_var);

        // Content = GCD of the coefficients, computed over the strictly
        // smaller variable set `vars(p) \ {main_var}`.
        let mut content = Polynomial::zero();
        for coeff in &coefficients {
            content = self.gcd_recursive(&content, coeff, depth + 1);
            if content.is_constant() {
                break;
            }
        }

        if content.is_zero() || content.is_constant() {
            return (Polynomial::one(), p.clone());
        }

        match exact_division(p, &content) {
            Some(primitive) => (content, primitive),
            None => {
                // The content divides `p` by construction, so this branch is
                // mathematically unreachable. Report it as a give-up rather
                // than silently returning a quotient that is not one.
                self.stats.incomplete = true;
                (Polynomial::one(), p.clone())
            }
        }
    }

    /// Extract the nonzero coefficients of `p` viewed as univariate in `var`.
    ///
    /// Each returned polynomial is free of `var`.
    fn extract_coefficients(&self, p: &Polynomial, var: Var) -> Vec<Polynomial> {
        let degree = p.degree(var);
        let mut coeffs = Vec::with_capacity(degree as usize + 1);
        for k in 0..=degree {
            let c = p.coeff(var, k);
            if !c.is_zero() {
                coeffs.push(c);
            }
        }
        coeffs
    }

    /// Normalize GCD result.
    fn normalize_gcd(&self, p: &Polynomial) -> Polynomial {
        if p.is_zero() {
            return Polynomial::zero();
        }

        // Make monic (leading coefficient = 1)
        let lead = p.leading_coeff();

        if lead.is_zero() {
            return p.clone();
        }

        p.scale(&lead.recip())
    }

    /// Get statistics.
    pub fn stats(&self) -> &MultivariateGcdStats {
        &self.stats
    }

    /// Reset statistics.
    pub fn reset_stats(&mut self) {
        self.stats = MultivariateGcdStats::default();
    }
}

/// Multivariate pseudo-remainder of `a` by `b` with respect to `var`.
///
/// Treats both operands as univariate in `var` with coefficients in the
/// remaining variables and returns `r` such that
///
/// ```text
/// lc_var(b)^(deg_var(a) - deg_var(b) + 1) * a = quotient * b + r
/// ```
///
/// with `deg_var(r) < deg_var(b)`. The leading-coefficient multiplier is
/// what makes the division exact without introducing denominators, which is
/// exactly why a *pseudo* remainder is used instead of a true one.
///
/// Degenerate divisors are handled without panicking: dividing by the zero
/// polynomial has no defined reduction, so `a` is returned unchanged.
fn pseudo_remainder(a: &Polynomial, b: &Polynomial, var: Var) -> Polynomial {
    if b.is_zero() || a.is_zero() {
        return a.clone();
    }

    let deg_b = b.degree(var);
    let deg_a = a.degree(var);
    if deg_a < deg_b {
        return a.clone();
    }

    let lc_b = b.leading_coeff_wrt(var);
    if lc_b.is_zero() {
        return a.clone();
    }

    // Exactly `deg_a - deg_b + 1` reduction steps suffice: each step cancels
    // the leading `var`-coefficient of `r` exactly, so `deg_var(r)` strictly
    // decreases. Any steps not consumed are folded back in as the remaining
    // `lc_b` power, which keeps the pseudo-division identity exact.
    let steps = deg_a - deg_b + 1;
    let mut used = 0u32;
    let mut r = a.clone();

    while used < steps && !r.is_zero() && r.degree(var) >= deg_b {
        used += 1;
        let deg_r = r.degree(var);
        let lc_r = r.leading_coeff_wrt(var);
        let shift = Monomial::from_var_power(var, deg_r - deg_b);

        // r <- lc_b * r - lc_r * var^(deg_r - deg_b) * b
        let scaled = lc_b.mul(&r);
        let subtractor = lc_r.mul(b).mul_monomial(&shift);
        r = scaled.sub(&subtractor);
    }

    let leftover = steps - used;
    if leftover > 0 && !r.is_zero() {
        r = r.mul(&lc_b.pow(leftover));
    }

    r
}

/// Exact multivariate division `p / q`.
///
/// Returns `Some(quotient)` when `q` divides `p` exactly and `None`
/// otherwise -- never an approximate or truncated quotient. Callers that
/// know divisibility holds (content / primitive-part splits) can treat
/// `None` as an internal inconsistency; callers that do not can use it as a
/// divisibility test.
///
/// Termination: each step removes the leading monomial of the running
/// dividend and only introduces strictly smaller ones under the monomial
/// order, which is a well-order on monomials.
fn exact_division(p: &Polynomial, q: &Polynomial) -> Option<Polynomial> {
    if q.is_zero() {
        return None;
    }
    if p.is_zero() {
        return Some(Polynomial::zero());
    }
    if q.is_one() {
        return Some(p.clone());
    }
    if q.is_constant() {
        // A nonzero constant divides everything over a field.
        return Some(p.scale(&q.constant_value().recip()));
    }

    let order = p.order;
    // Re-express the divisor under the dividend's monomial order: the
    // leading-term cancellation argument below is only valid when both
    // operands are ordered the same way.
    let divisor = Polynomial::from_terms(q.terms().to_vec(), order);
    let lead = divisor.leading_term()?;
    let lead_coeff = lead.coeff.clone();
    let lead_mono = lead.monomial.clone();

    let mut quotient = Polynomial::from_terms(Vec::<Term>::new(), order);
    let mut rest = Polynomial::from_terms(p.terms().to_vec(), order);

    loop {
        let Some(term) = rest.leading_term().cloned() else {
            return Some(quotient);
        };
        // If the divisor's leading monomial does not divide the running
        // dividend's, no exact quotient exists.
        let mono = term.monomial.div(&lead_mono)?;
        let coeff = &term.coeff / &lead_coeff;
        let step = Polynomial::from_terms(vec![Term::new(coeff, mono)], order);
        quotient = quotient.add(&step);
        rest = rest.sub(&divisor.mul(&step));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use num_traits::One;

    /// `x` is variable 0, `y` variable 1, `z` variable 2 throughout.
    const X: Var = 0;
    const Y: Var = 1;
    const Z: Var = 2;

    fn var(v: Var) -> Polynomial {
        Polynomial::from_var(v)
    }

    fn int(n: i64) -> Polynomial {
        Polynomial::constant(BigRational::from_integer(BigInt::from(n)))
    }

    /// Assert that `a` and `b` are associates: each divides the other.
    fn assert_associate(a: &Polynomial, b: &Polynomial) {
        assert!(
            exact_division(a, b).is_some() && exact_division(b, a).is_some(),
            "{a:?} and {b:?} are not associates"
        );
    }

    #[test]
    fn test_engine_creation() {
        let engine = MultivariateGcdEngine::default_config();
        assert_eq!(engine.stats().max_depth, 0);
    }

    #[test]
    fn test_gcd_constants() {
        let mut engine = MultivariateGcdEngine::default_config();

        let gcd = engine.gcd(&int(6), &int(9));

        // Over the rationals every nonzero constant is a unit, so the GCD of
        // two constants is 1.
        assert!(gcd.is_one());
        assert!(!engine.stats().incomplete);
    }

    /// The depth ceiling must be *observable*: when the engine falls back
    /// to the trivial divisor `1`, `stats().incomplete` says so. A `1`
    /// returned as a genuine GCD and a `1` returned as a give-up were
    /// previously indistinguishable.
    #[test]
    fn test_depth_ceiling_is_reported_in_stats() {
        let config = MultivariateGcdConfig {
            max_recursion_depth: 1,
            ..MultivariateGcdConfig::default()
        };
        let mut engine = MultivariateGcdEngine::new(config);

        // Two variables need one level of variable elimination, which the
        // budget of 1 cannot pay for.
        let p = var(X).mul(&var(Y));
        let q = var(X).mul(&var(Y)).mul(&var(X));

        let gcd = engine.gcd(&p, &q);
        assert!(engine.stats().incomplete);
        // The fallback is still a sound common divisor.
        assert!(!gcd.is_zero());
        assert!(engine.stats().max_depth <= 1);
    }

    #[test]
    fn test_gcd_univariate() {
        let mut engine = MultivariateGcdEngine::default_config();

        // x^2 - 1
        let p = Polynomial::from_coeffs_int(&[(1, &[(X, 2)]), (-1, &[])]);
        // x - 1
        let q = Polynomial::from_coeffs_int(&[(1, &[(X, 1)]), (-1, &[])]);

        let gcd = engine.gcd(&p, &q);

        assert_associate(&gcd, &q);
        assert!(!engine.stats().incomplete);
    }

    /// The multivariate engine must agree with the crate's univariate GCD on
    /// univariate input.
    #[test]
    fn test_gcd_agrees_with_univariate_engine() {
        let mut engine = MultivariateGcdEngine::default_config();

        // (x - 1)(x + 1)(x + 2) and (x - 1)(x + 1)(x - 3)
        let x_minus_1 = Polynomial::from_coeffs_int(&[(1, &[(X, 1)]), (-1, &[])]);
        let x_plus_1 = Polynomial::from_coeffs_int(&[(1, &[(X, 1)]), (1, &[])]);
        let x_plus_2 = Polynomial::from_coeffs_int(&[(1, &[(X, 1)]), (2, &[])]);
        let x_minus_3 = Polynomial::from_coeffs_int(&[(1, &[(X, 1)]), (-3, &[])]);

        let p = x_minus_1.mul(&x_plus_1).mul(&x_plus_2);
        let q = x_minus_1.mul(&x_plus_1).mul(&x_minus_3);

        let gcd = engine.gcd(&p, &q);
        let expected = x_minus_1.mul(&x_plus_1);

        assert_associate(&gcd, &expected);
        assert_associate(&gcd, &p.gcd_univariate(&q));
        assert!(!engine.stats().incomplete);
    }

    #[test]
    fn test_gcd_monomials_shares_single_variable() {
        let mut engine = MultivariateGcdEngine::default_config();

        // gcd(x*y, x*z) = x
        let p = var(X).mul(&var(Y));
        let q = var(X).mul(&var(Z));

        let gcd = engine.gcd(&p, &q);

        assert_eq!(gcd, var(X));
        assert!(!engine.stats().incomplete);
    }

    #[test]
    fn test_gcd_shared_multivariate_factor() {
        let mut engine = MultivariateGcdEngine::default_config();

        // gcd((x + y)^2 * (x - z), (x + y) * x^2) = x + y
        let x_plus_y = var(X).add(&var(Y));
        let x_minus_z = var(X).sub(&var(Z));

        let p = x_plus_y.pow(2).mul(&x_minus_z);
        let q = x_plus_y.mul(&var(X).pow(2));

        let gcd = engine.gcd(&p, &q);

        assert_associate(&gcd, &x_plus_y);
        // Monic normalization pins the exact representative.
        assert_eq!(gcd, x_plus_y);
        assert!(!engine.stats().incomplete);
    }

    #[test]
    fn test_gcd_result_divides_both_inputs() {
        let mut engine = MultivariateGcdEngine::default_config();

        // p = (x*y + z) * (x + 2*y), q = (x*y + z) * (y - z)
        let common = var(X).mul(&var(Y)).add(&var(Z));
        let p = common.mul(&var(X).add(&var(Y).mul(&int(2))));
        let q = common.mul(&var(Y).sub(&var(Z)));

        let gcd = engine.gcd(&p, &q);

        assert!(exact_division(&p, &gcd).is_some(), "gcd must divide p");
        assert!(exact_division(&q, &gcd).is_some(), "gcd must divide q");
        assert_associate(&gcd, &common);
        assert!(!engine.stats().incomplete);
    }

    #[test]
    fn test_gcd_coprime_multivariate_is_a_unit() {
        let mut engine = MultivariateGcdEngine::default_config();

        let p = var(X).add(&var(Y));
        let q = var(X).sub(&var(Y)).add(&int(1));

        let gcd = engine.gcd(&p, &q);

        assert!(gcd.is_one(), "expected a unit GCD, got {gcd:?}");
        assert!(!engine.stats().incomplete);
    }

    #[test]
    fn test_gcd_with_zero_operand() {
        let mut engine = MultivariateGcdEngine::default_config();

        let p = var(X).mul(&var(Y));
        let gcd = engine.gcd(&p, &Polynomial::zero());

        assert_associate(&gcd, &p);
        assert!(
            engine
                .gcd(&Polynomial::zero(), &Polynomial::zero())
                .is_zero()
        );
    }

    /// The primitive PRS must not depend on `use_primitive_part`: the flag
    /// only controls intermediate coefficient growth, never the answer.
    #[test]
    fn test_gcd_same_without_intermediate_primitive_parts() {
        let config = MultivariateGcdConfig {
            use_primitive_part: false,
            ..MultivariateGcdConfig::default()
        };
        let mut engine = MultivariateGcdEngine::new(config);

        let x_plus_y = var(X).add(&var(Y));
        let p = x_plus_y.pow(2).mul(&var(X).sub(&var(Z)));
        let q = x_plus_y.mul(&var(X).pow(2));

        let gcd = engine.gcd(&p, &q);

        assert_eq!(gcd, x_plus_y);
        assert!(!engine.stats().incomplete);
    }

    #[test]
    fn test_pseudo_remainder_is_not_a_stub() {
        // prem(x^2 + y, x + y, x): lc = 1, so the pseudo-remainder is the
        // true remainder y^2 + y.
        let p = var(X).pow(2).add(&var(Y));
        let q = var(X).add(&var(Y));

        let r = pseudo_remainder(&p, &q, X);

        assert!(!r.is_zero(), "a stub would wrongly return zero here");
        assert_eq!(r.degree(X), 0);
        assert_eq!(r, var(Y).pow(2).add(&var(Y)));
    }

    #[test]
    fn test_pseudo_remainder_identity_holds() {
        // lc(b)^(deg a - deg b + 1) * a = q*b + r, so
        // (lc^k * a - r) must be exactly divisible by b.
        let a = var(X).pow(3).mul(&var(Y)).add(&var(Z));
        let b = var(Y).mul(&var(X).pow(2)).add(&var(X)).add(&int(1));

        let r = pseudo_remainder(&a, &b, X);
        assert!(r.degree(X) < b.degree(X));

        let lc_b = b.leading_coeff_wrt(X);
        let k = a.degree(X) - b.degree(X) + 1;
        let lhs = lc_b.pow(k).mul(&a).sub(&r);

        assert!(
            exact_division(&lhs, &b).is_some(),
            "pseudo-division identity violated"
        );
    }

    #[test]
    fn test_pseudo_remainder_zero_divisor_no_panic() {
        let a = var(X).add(&int(1));
        assert_eq!(pseudo_remainder(&a, &Polynomial::zero(), X), a);
    }

    #[test]
    fn test_exact_division_reports_non_divisibility() {
        // (x + y) does not divide (x + z).
        let p = var(X).add(&var(Z));
        let q = var(X).add(&var(Y));

        assert!(exact_division(&p, &q).is_none());
        // ... and does not divide by zero either.
        assert!(exact_division(&p, &Polynomial::zero()).is_none());
    }

    #[test]
    fn test_exact_division_recovers_the_factor() {
        let a = var(X).mul(&var(Y)).add(&var(Z)).add(&int(3));
        let b = var(X).pow(2).sub(&var(Y).mul(&var(Z)));
        let product = a.mul(&b);

        assert_eq!(exact_division(&product, &b), Some(a.clone()));
        assert_eq!(exact_division(&product, &a), Some(b));
    }

    #[test]
    fn test_var_selection_max_degree() {
        let engine = MultivariateGcdEngine::default_config();

        // x^3 + y^2
        let p = Polynomial::from_coeffs_int(&[(1, &[(X, 3)]), (1, &[(Y, 2)])]);
        // x + y^3
        let q = Polynomial::from_coeffs_int(&[(1, &[(X, 1)]), (1, &[(Y, 3)])]);

        let main_var = engine.select_by_max_degree(&p, &q);

        // Both variables reach degree 3; ties go to the higher index.
        assert_eq!(main_var, Y);
    }

    #[test]
    fn test_extract_coefficients() {
        let engine = MultivariateGcdEngine::default_config();

        // 2*x^2*y + 3*x*y^2
        let p = Polynomial::from_coeffs_int(&[(2, &[(X, 2), (Y, 1)]), (3, &[(X, 1), (Y, 2)])]);

        let coeffs = engine.extract_coefficients(&p, X);

        // Nonzero coefficients for x^1 and x^2, and none of them mention x.
        assert_eq!(coeffs.len(), 2);
        assert!(coeffs.iter().all(|c| c.degree(X) == 0));
    }

    #[test]
    fn test_extract_content_splits_exactly() {
        let mut engine = MultivariateGcdEngine::default_config();

        // p = y*(x^2 + x) viewed in x: content y, primitive x^2 + x.
        let p = var(Y).mul(&var(X).pow(2).add(&var(X)));

        let (content, primitive) = engine.extract_content(&p, X, 0);

        assert_eq!(content, var(Y));
        assert_eq!(content.mul(&primitive), p);
    }

    #[test]
    fn test_normalize_gcd() {
        let engine = MultivariateGcdEngine::default_config();

        // 6*x^2 + 3*x
        let p = Polynomial::from_coeffs_int(&[(6, &[(X, 2)]), (3, &[(X, 1)])]);

        let normalized = engine.normalize_gcd(&p);

        // 6x^2 + 3x divided by its leading coefficient is x^2 + x/2.
        let half = BigRational::new(BigInt::from(1), BigInt::from(2));
        assert!(normalized.leading_coeff().is_one());
        assert_eq!(normalized, var(X).pow(2).add(&var(X).scale(&half)));
    }

    #[cfg(feature = "std")]
    /// Many-variable input on a small stack: the recursion is bounded by the
    /// variable count, so a 90-variable GCD must *return* (that is the
    /// proof) on a 1 MiB stack without approaching the depth ceiling.
    #[test]
    fn test_many_variables_within_ceiling_returns_on_small_stack() {
        let handle = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let n: Var = 90;
                let mut p = Polynomial::one();
                for v in 0..n {
                    p = p.mul(&Polynomial::from_var(v));
                }

                let mut engine = MultivariateGcdEngine::default_config();
                let gcd = engine.gcd(&p, &p);
                (
                    gcd == p,
                    engine.stats().incomplete,
                    engine.stats().max_depth,
                )
            })
            .expect("failed to spawn worker thread");

        let (matched, incomplete, max_depth) = handle.join().expect("worker thread panicked");
        assert!(matched, "gcd(p, p) must be p");
        assert!(!incomplete);
        assert!(
            max_depth <= 90,
            "depth {max_depth} exceeds the variable count"
        );
    }

    #[cfg(feature = "std")]
    /// Beyond the configured variable budget the engine gives up honestly
    /// instead of overflowing the stack or returning a wrong divisor.
    #[test]
    fn test_more_variables_than_budget_gives_up_honestly() {
        let handle = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let n: Var = 150;
                let mut p = Polynomial::one();
                for v in 0..n {
                    p = p.mul(&Polynomial::from_var(v));
                }

                let mut engine = MultivariateGcdEngine::default_config();
                let gcd = engine.gcd(&p, &p);
                (
                    gcd.is_zero(),
                    engine.stats().incomplete,
                    engine.stats().max_depth,
                )
            })
            .expect("failed to spawn worker thread");

        let (is_zero, incomplete, max_depth) = handle.join().expect("worker thread panicked");
        assert!(!is_zero, "the fallback divisor must still be nonzero");
        assert!(incomplete, "the give-up must be reported");
        assert_eq!(max_depth, 100);
    }
}
