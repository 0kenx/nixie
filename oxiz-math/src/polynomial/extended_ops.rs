//! Extended polynomial operations: calculus, GCD, and evaluation.

use super::helpers::*;
use super::types::*;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::simd::polynomial_simd::{poly_add_coeffs, poly_dot_product, poly_mul_scalar};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

type Polynomial = super::Polynomial;

impl super::Polynomial {
    /// Compute the derivative with respect to a variable.
    pub fn derivative(&self, var: Var) -> Polynomial {
        let terms: Vec<Term> = self
            .terms
            .iter()
            .filter_map(|t| {
                let d = t.monomial.degree(var);
                if d == 0 {
                    return None;
                }
                let new_coeff = &t.coeff * BigRational::from_integer(BigInt::from(d));
                let new_mon = if d == 1 {
                    t.monomial
                        .div(&Monomial::from_var(var))
                        .unwrap_or_else(Monomial::unit)
                } else {
                    let new_powers: Vec<(Var, u32)> = t
                        .monomial
                        .vars()
                        .iter()
                        .map(|vp| {
                            if vp.var == var {
                                (vp.var, vp.power - 1)
                            } else {
                                (vp.var, vp.power)
                            }
                        })
                        .filter(|(_, p)| *p > 0)
                        .collect();
                    Monomial::from_powers(new_powers)
                };
                Some(Term::new(new_coeff, new_mon))
            })
            .collect();
        Polynomial::from_terms(terms, self.order)
    }

    /// Compute the nth derivative of the polynomial with respect to a variable.
    ///
    /// # Arguments
    /// * `var` - The variable to differentiate with respect to
    /// * `n` - The order of the derivative (n = 0 returns the polynomial itself)
    ///
    /// # Examples
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    ///
    /// // f(x) = x^3 = x³
    /// let f = Polynomial::from_coeffs_int(&[(1, &[(0, 3)])]);
    ///
    /// // f'(x) = 3x^2
    /// let f_prime = f.nth_derivative(0, 1);
    /// assert_eq!(f_prime.total_degree(), 2);
    ///
    /// // f''(x) = 6x
    /// let f_double_prime = f.nth_derivative(0, 2);
    /// assert_eq!(f_double_prime.total_degree(), 1);
    ///
    /// // f'''(x) = 6 (constant)
    /// let f_triple_prime = f.nth_derivative(0, 3);
    /// assert_eq!(f_triple_prime.total_degree(), 0);
    /// assert!(!f_triple_prime.is_zero());
    ///
    /// // f''''(x) = 0
    /// let f_fourth = f.nth_derivative(0, 4);
    /// assert!(f_fourth.is_zero());
    /// ```
    pub fn nth_derivative(&self, var: Var, n: u32) -> Polynomial {
        if n == 0 {
            return self.clone();
        }

        let mut result = self.clone();
        for _ in 0..n {
            result = result.derivative(var);
            if result.is_zero() {
                break;
            }
        }
        result
    }

    /// Computes the gradient (vector of partial derivatives) with respect to all variables.
    ///
    /// For a multivariate polynomial f(x₁, x₂, ..., xₙ), returns the vector:
    /// ∇f = [∂f/∂x₁, ∂f/∂x₂, ..., ∂f/∂xₙ]
    ///
    /// # Returns
    /// A vector of polynomials, one for each variable, ordered by variable index.
    ///
    /// # Example
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    /// // f(x,y) = x²y + 2xy + y²
    /// let f = Polynomial::from_coeffs_int(&[
    ///     (1, &[(0, 2), (1, 1)]), // x²y
    ///     (2, &[(0, 1), (1, 1)]), // 2xy
    ///     (1, &[(1, 2)]),          // y²
    /// ]);
    ///
    /// let grad = f.gradient();
    /// // ∂f/∂x = 2xy + 2y
    /// // ∂f/∂y = x² + 2x + 2y
    /// assert_eq!(grad.len(), 2);
    /// ```
    pub fn gradient(&self) -> Vec<Polynomial> {
        let vars = self.vars();
        if vars.is_empty() {
            return vec![];
        }

        // `vars` was just confirmed non-empty above, so `max()` always
        // yields `Some`; `unwrap_or(0)` avoids an `.expect()` panic path
        // without changing behavior (the fallback is unreachable).
        let max_var = *vars.iter().max().unwrap_or(&0);
        let mut grad = Vec::new();

        // Compute partial derivative for each variable from 0 to max_var
        for var in 0..=max_var {
            grad.push(self.derivative(var));
        }

        grad
    }

    /// Computes the Hessian matrix (matrix of second-order partial derivatives).
    ///
    /// For a multivariate polynomial f(x₁, x₂, ..., xₙ), returns the symmetric matrix:
    /// `H[i,j] = ∂²f/(∂xᵢ∂xⱼ)`
    ///
    /// The Hessian is useful for:
    /// - Optimization (finding local minima/maxima)
    /// - Convexity analysis
    /// - Second-order Taylor approximations
    ///
    /// # Returns
    /// A vector of vectors representing the Hessian matrix.
    /// The matrix is symmetric: `H[i][j] = H[j][i]`
    ///
    /// # Example
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    /// // f(x,y) = x² + xy + y²
    /// let f = Polynomial::from_coeffs_int(&[
    ///     (1, &[(0, 2)]),          // x²
    ///     (1, &[(0, 1), (1, 1)]), // xy
    ///     (1, &[(1, 2)]),          // y²
    /// ]);
    ///
    /// let hessian = f.hessian();
    /// // H = [[2, 1],
    /// //      [1, 2]]
    /// assert_eq!(hessian.len(), 2);
    /// assert_eq!(hessian[0].len(), 2);
    /// ```
    pub fn hessian(&self) -> Vec<Vec<Polynomial>> {
        let vars = self.vars();
        if vars.is_empty() {
            return vec![];
        }

        // Same reasoning as `gradient` above: `vars` is confirmed
        // non-empty by the guard above, so `unwrap_or` never triggers.
        let max_var = *vars.iter().max().unwrap_or(&0);
        let n = (max_var + 1) as usize;

        let mut hessian = vec![vec![Polynomial::zero(); n]; n];

        // Compute all second-order partial derivatives
        for i in 0..=max_var {
            for j in 0..=max_var {
                // ∂²f/(∂xᵢ∂xⱼ) = ∂/∂xⱼ(∂f/∂xᵢ)
                let first_deriv = self.derivative(i);
                let second_deriv = first_deriv.derivative(j);
                hessian[i as usize][j as usize] = second_deriv;
            }
        }

        hessian
    }

    /// Computes the Jacobian matrix for a vector of polynomials.
    ///
    /// For a vector of polynomials f = (f₁, f₂, ..., fₘ) each depending on variables
    /// x = (x₁, x₂, ..., xₙ), the Jacobian is the m×n matrix:
    /// `J[i,j] = ∂fᵢ/∂xⱼ`
    ///
    /// # Arguments
    /// * `polys` - Vector of polynomials representing the function components
    ///
    /// # Returns
    /// A matrix where each row i contains the gradient of polynomial i
    ///
    /// # Example
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    /// // f₁(x,y) = x² + y
    /// // f₂(x,y) = x + y²
    /// let f1 = Polynomial::from_coeffs_int(&[(1, &[(0, 2)]), (1, &[(1, 1)])]);
    /// let f2 = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (1, &[(1, 2)])]);
    ///
    /// let jacobian = Polynomial::jacobian(&[f1, f2]);
    /// // J = [[2x, 1 ],
    /// //      [1,  2y]]
    /// assert_eq!(jacobian.len(), 2); // 2 functions
    /// ```
    pub fn jacobian(polys: &[Polynomial]) -> Vec<Vec<Polynomial>> {
        if polys.is_empty() {
            return vec![];
        }

        // Find the maximum variable across all polynomials
        let max_var = polys.iter().flat_map(|p| p.vars()).max().unwrap_or(0);

        let n_vars = (max_var + 1) as usize;
        let mut jacobian = Vec::with_capacity(polys.len());

        for poly in polys {
            let mut row = Vec::with_capacity(n_vars);
            for var in 0..=max_var {
                row.push(poly.derivative(var));
            }
            jacobian.push(row);
        }

        jacobian
    }

    /// Compute the indefinite integral (antiderivative) of the polynomial with respect to a variable.
    ///
    /// For a polynomial p(x), returns ∫p(x)dx. The constant of integration is implicitly zero.
    ///
    /// # Arguments
    /// * `var` - The variable to integrate with respect to
    ///
    /// # Examples
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    /// use num_bigint::BigInt;
    /// use num_rational::BigRational;
    ///
    /// // f(x) = 3x^2
    /// let f = Polynomial::from_coeffs_int(&[(3, &[(0, 2)])]);
    ///
    /// // ∫f(x)dx = x^3
    /// let integral = f.integrate(0);
    ///
    /// // Verify: derivative of integral should be original
    /// let derivative = integral.derivative(0);
    /// assert_eq!(derivative, f);
    /// ```
    pub fn integrate(&self, var: Var) -> Polynomial {
        let terms: Vec<Term> = self
            .terms
            .iter()
            .map(|t| {
                let d = t.monomial.degree(var);
                let new_power = d + 1;

                // Divide coefficient by (power + 1)
                let new_coeff = &t.coeff / BigRational::from_integer(BigInt::from(new_power));

                // Increment the power of var
                let new_powers: Vec<(Var, u32)> = if d == 0 {
                    // Constant term: add var^1
                    let mut powers = t
                        .monomial
                        .vars()
                        .iter()
                        .map(|vp| (vp.var, vp.power))
                        .collect::<Vec<_>>();
                    powers.push((var, 1));
                    powers.sort_by_key(|(v, _)| *v);
                    powers
                } else {
                    // Variable already exists: increment power
                    t.monomial
                        .vars()
                        .iter()
                        .map(|vp| {
                            if vp.var == var {
                                (vp.var, vp.power + 1)
                            } else {
                                (vp.var, vp.power)
                            }
                        })
                        .collect()
                };

                let new_mon = Monomial::from_powers(new_powers);
                Term::new(new_coeff, new_mon)
            })
            .collect();
        Polynomial::from_terms(terms, self.order)
    }

    /// Compute the definite integral of a univariate polynomial over an interval (a, b).
    ///
    /// For a univariate polynomial p(x), returns ∫ₐᵇ p(x)dx = F(b) - F(a)
    /// where F is the antiderivative of p.
    ///
    /// # Arguments
    /// * `var` - The variable to integrate with respect to
    /// * `lower` - Lower bound of integration
    /// * `upper` - Upper bound of integration
    ///
    /// # Returns
    /// The definite integral value, or None if the polynomial is not univariate in the given variable
    ///
    /// # Examples
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    /// use num_bigint::BigInt;
    /// use num_rational::BigRational;
    ///
    /// // ∫[0,2] x^2 dx = [x^3/3] from 0 to 2 = 8/3
    /// let f = Polynomial::from_coeffs_int(&[(1, &[(0, 2)])]);
    /// let result = f.definite_integral(0, &BigRational::from_integer(BigInt::from(0)),
    ///                                     &BigRational::from_integer(BigInt::from(2)));
    /// assert_eq!(result, Some(BigRational::new(BigInt::from(8), BigInt::from(3))));
    /// ```
    pub fn definite_integral(
        &self,
        var: Var,
        lower: &BigRational,
        upper: &BigRational,
    ) -> Option<BigRational> {
        // Get the antiderivative
        let antideriv = self.integrate(var);

        // Evaluate at upper and lower bounds
        let mut upper_assignment = crate::prelude::FxHashMap::default();
        upper_assignment.insert(var, upper.clone());
        let upper_val = antideriv.eval(&upper_assignment);

        let mut lower_assignment = crate::prelude::FxHashMap::default();
        lower_assignment.insert(var, lower.clone());
        let lower_val = antideriv.eval(&lower_assignment);

        // Return F(b) - F(a)
        Some(upper_val - lower_val)
    }

    /// Find critical points of a univariate polynomial by solving f'(x) = 0.
    ///
    /// Critical points are values where the derivative equals zero, which correspond
    /// to local maxima, minima, or saddle points.
    ///
    /// # Arguments
    /// * `var` - The variable to find critical points for
    ///
    /// # Returns
    /// A vector of isolating intervals containing the critical points. Each interval
    /// contains exactly one root of the derivative.
    ///
    /// # Examples
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    ///
    /// // f(x) = x^3 - 3x = x(x^2 - 3)
    /// // f'(x) = 3x^2 - 3 = 3(x^2 - 1) = 3(x-1)(x+1)
    /// // Critical points at x = -1 and x = 1
    /// let f = Polynomial::from_coeffs_int(&[
    ///     (1, &[(0, 3)]),  // x^3
    ///     (-3, &[(0, 1)]), // -3x
    /// ]);
    ///
    /// let critical_points = f.find_critical_points(0);
    /// assert_eq!(critical_points.len(), 2); // Two critical points
    /// ```
    pub fn find_critical_points(&self, var: Var) -> Vec<(BigRational, BigRational)> {
        // Compute the derivative
        let deriv = self.derivative(var);

        // Find roots of the derivative (where f'(x) = 0)
        deriv.isolate_roots(var)
    }

    /// Numerically integrate using the trapezoidal rule.
    ///
    /// Approximates ∫ₐᵇ f(x)dx using the trapezoidal rule with n subintervals.
    /// The trapezoidal rule approximates the integral by summing the areas of trapezoids.
    ///
    /// # Arguments
    /// * `var` - The variable to integrate with respect to
    /// * `lower` - Lower bound of integration
    /// * `upper` - Upper bound of integration
    /// * `n` - Number of subintervals (more subintervals = higher accuracy)
    ///
    /// # Examples
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    /// use num_bigint::BigInt;
    /// use num_rational::BigRational;
    ///
    /// // ∫[0,1] x^2 dx = 1/3
    /// let f = Polynomial::from_coeffs_int(&[(1, &[(0, 2)])]);
    /// let approx = f.trapezoidal_rule(0,
    ///     &BigRational::from_integer(BigInt::from(0)),
    ///     &BigRational::from_integer(BigInt::from(1)),
    ///     100);
    ///
    /// let exact = BigRational::new(BigInt::from(1), BigInt::from(3));
    /// // With 100 intervals, approximation should be very close
    /// ```
    pub fn trapezoidal_rule(
        &self,
        var: Var,
        lower: &BigRational,
        upper: &BigRational,
        n: u32,
    ) -> BigRational {
        if n == 0 {
            return BigRational::zero();
        }

        // Step size h = (b - a) / n
        let h = (upper - lower) / BigRational::from_integer(BigInt::from(n));

        let mut sum = BigRational::zero();

        // First and last terms: f(a)/2 + f(b)/2
        let mut assignment = crate::prelude::FxHashMap::default();
        assignment.insert(var, lower.clone());
        sum += &self.eval(&assignment) / BigRational::from_integer(BigInt::from(2));

        assignment.insert(var, upper.clone());
        sum += &self.eval(&assignment) / BigRational::from_integer(BigInt::from(2));

        // Middle terms: sum of f(x_i) for i = 1 to n-1
        for i in 1..n {
            let x_i = lower + &h * BigRational::from_integer(BigInt::from(i));
            assignment.insert(var, x_i);
            sum += &self.eval(&assignment);
        }

        // Multiply by step size
        sum * h
    }

    /// Numerically integrate using Simpson's rule.
    ///
    /// Approximates ∫ₐᵇ f(x)dx using Simpson's rule with n subintervals (n must be even).
    /// Simpson's rule uses parabolic approximation and is generally more accurate than
    /// the trapezoidal rule for smooth functions.
    ///
    /// # Arguments
    /// * `var` - The variable to integrate with respect to
    /// * `lower` - Lower bound of integration
    /// * `upper` - Upper bound of integration
    /// * `n` - Number of subintervals (must be even for Simpson's rule)
    ///
    /// # Examples
    /// ```
    /// use oxiz_math::polynomial::Polynomial;
    /// use num_bigint::BigInt;
    /// use num_rational::BigRational;
    ///
    /// // ∫[0,1] x^2 dx = 1/3
    /// let f = Polynomial::from_coeffs_int(&[(1, &[(0, 2)])]);
    /// let approx = f.simpsons_rule(0,
    ///     &BigRational::from_integer(BigInt::from(0)),
    ///     &BigRational::from_integer(BigInt::from(1)),
    ///     100);
    ///
    /// let exact = BigRational::new(BigInt::from(1), BigInt::from(3));
    /// // Simpson's rule should give very accurate results for polynomials
    /// ```
    pub fn simpsons_rule(
        &self,
        var: Var,
        lower: &BigRational,
        upper: &BigRational,
        n: u32,
    ) -> BigRational {
        if n == 0 {
            return BigRational::zero();
        }

        // Ensure n is even for Simpson's rule
        let n = if n % 2 == 1 { n + 1 } else { n };

        // Step size h = (b - a) / n
        let h = (upper - lower) / BigRational::from_integer(BigInt::from(n));

        let mut sum = BigRational::zero();
        let mut assignment = crate::prelude::FxHashMap::default();

        // First and last terms: f(a) + f(b)
        assignment.insert(var, lower.clone());
        sum += &self.eval(&assignment);

        assignment.insert(var, upper.clone());
        sum += &self.eval(&assignment);

        // Odd-indexed terms (multiplied by 4): i = 1, 3, 5, ..., n-1
        for i in (1..n).step_by(2) {
            let x_i = lower + &h * BigRational::from_integer(BigInt::from(i));
            assignment.insert(var, x_i);
            sum += BigRational::from_integer(BigInt::from(4)) * &self.eval(&assignment);
        }

        // Even-indexed terms (multiplied by 2): i = 2, 4, 6, ..., n-2
        for i in (2..n).step_by(2) {
            let x_i = lower + &h * BigRational::from_integer(BigInt::from(i));
            assignment.insert(var, x_i);
            sum += BigRational::from_integer(BigInt::from(2)) * &self.eval(&assignment);
        }

        // Multiply by h/3
        sum * h / BigRational::from_integer(BigInt::from(3))
    }

    /// Evaluate the polynomial at a point (substituting a value for a variable).
    pub fn eval_at(&self, var: Var, value: &BigRational) -> Polynomial {
        let terms: Vec<Term> = self
            .terms
            .iter()
            .map(|t| {
                let d = t.monomial.degree(var);
                if d == 0 {
                    t.clone()
                } else {
                    let new_coeff = &t.coeff * value.pow(d as i32);
                    let new_mon = t
                        .monomial
                        .div(&Monomial::from_var_power(var, d))
                        .unwrap_or_else(Monomial::unit);
                    Term::new(new_coeff, new_mon)
                }
            })
            .collect();
        Polynomial::from_terms(terms, self.order)
    }

    /// Evaluate the polynomial completely (all variables assigned).
    ///
    /// (Numeric substitution of `assignment` into the polynomial's terms —
    /// no code/expression execution of any kind is involved.)
    ///
    /// # Panics
    ///
    /// Panics if `assignment` does not cover every variable occurring in
    /// `self`. Callers that cannot guarantee a complete assignment ahead of
    /// time (e.g. because it was built incrementally, or comes from
    /// untrusted/partial input) should use [`Self::try_eval`] instead, which
    /// reports the same condition as `None` rather than aborting.
    pub fn eval(&self, assignment: &FxHashMap<Var, BigRational>) -> BigRational {
        match self.try_eval(assignment) {
            Some(v) => v,
            None => panic!(
                "Polynomial::eval: assignment does not cover every variable in the polynomial \
                 (use try_eval for a non-panicking partial-assignment check)"
            ),
        }
    }

    /// Evaluate the polynomial completely (all variables assigned),
    /// returning `None` instead of panicking if `assignment` is missing a
    /// variable that occurs in `self`.
    pub fn try_eval(&self, assignment: &FxHashMap<Var, BigRational>) -> Option<BigRational> {
        let mut result = BigRational::zero();

        for term in &self.terms {
            let mut val = term.coeff.clone();
            for vp in term.monomial.vars() {
                let v = assignment.get(&vp.var)?;
                val *= v.pow(vp.power as i32);
            }
            result += val;
        }

        Some(result)
    }

    /// Evaluate a univariate polynomial using Horner's method.
    ///
    /// Horner's method evaluates a polynomial p(x) = a_n x^n + ... + a_1 x + a_0
    /// as (((...((a_n) x + a_{n-1}) x + ...) x + a_1) x + a_0), which requires
    /// only n multiplications instead of n(n+1)/2 for the naive method.
    ///
    /// This method is more efficient than eval() for univariate polynomials.
    ///
    /// # Arguments
    /// * `var` - The variable to evaluate
    /// * `value` - The value to substitute for the variable
    ///
    /// # Returns
    /// The evaluated value
    ///
    /// # Panics
    ///
    /// Panics if the polynomial is genuinely multivariate in `var` — i.e. it
    /// still contains a variable other than `var` after substituting `value`
    /// for `var`, so it cannot be reduced to a scalar. Callers that cannot
    /// guarantee univariate-in-`var` input (e.g. because it comes from
    /// untrusted or incrementally built terms) should use
    /// [`Self::try_eval_horner`] instead, which reports the same condition as
    /// `None` rather than aborting.
    pub fn eval_horner(&self, var: Var, value: &BigRational) -> BigRational {
        match self.try_eval_horner(var, value) {
            Some(v) => v,
            None => panic!(
                "Polynomial::eval_horner: polynomial is not univariate in variable x{var} \
                 (use try_eval_horner for a non-panicking check)"
            ),
        }
    }

    /// Evaluate a univariate polynomial using Horner's method, returning `None`
    /// instead of panicking when the polynomial is genuinely multivariate in
    /// `var` (i.e. it still contains another variable after substituting
    /// `value` for `var`, so no scalar result exists).
    ///
    /// This is the non-panicking counterpart of [`Self::eval_horner`]; see its
    /// documentation for the numeric contract.
    pub fn try_eval_horner(&self, var: Var, value: &BigRational) -> Option<BigRational> {
        if self.is_zero() {
            return Some(BigRational::zero());
        }

        // For polynomials that are not univariate *in `var`*, fall back to
        // full substitution: this succeeds only when the substitution leaves a
        // constant (every other variable, if any, cancelled out).
        if !self.is_univariate() || self.max_var() != var {
            let result = self.eval_at(var, value);
            if result.is_constant() {
                return Some(result.constant_value());
            }
            return None;
        }

        let deg = self.degree(var);
        if deg == 0 {
            return Some(self.constant_value());
        }

        // Collect coefficients in descending order of degree
        let mut coeffs = vec![BigRational::zero(); (deg + 1) as usize];
        for k in 0..=deg {
            coeffs[k as usize] = self.univ_coeff(var, k);
        }

        // Apply Horner's method: start from highest degree
        let mut result = coeffs[deg as usize].clone();
        for k in (0..deg).rev() {
            result = &result * value + &coeffs[k as usize];
        }

        Some(result)
    }

    /// Substitute a polynomial for a variable.
    pub fn substitute(&self, var: Var, replacement: &Polynomial) -> Polynomial {
        let mut result = Polynomial::zero();

        for term in &self.terms {
            let d = term.monomial.degree(var);
            if d == 0 {
                result = Polynomial::add(
                    &result,
                    &Polynomial::from_terms(vec![term.clone()], self.order),
                );
            } else {
                let remainder = term
                    .monomial
                    .div(&Monomial::from_var_power(var, d))
                    .unwrap_or_else(Monomial::unit);
                let coeff_poly = Polynomial::from_terms(
                    vec![Term::new(term.coeff.clone(), remainder)],
                    self.order,
                );
                let rep_pow = replacement.pow(d);
                result = Polynomial::add(&result, &Polynomial::mul(&coeff_poly, &rep_pow));
            }
        }

        result
    }

    /// Integer content: GCD of all coefficients (as integers).
    /// Assumes all coefficients are integers.
    pub fn integer_content(&self) -> BigInt {
        if self.terms.is_empty() {
            return BigInt::one();
        }

        let mut gcd: Option<BigInt> = None;
        for term in &self.terms {
            let num = term.coeff.numer().clone();
            gcd = Some(match gcd {
                None => num.abs(),
                Some(g) => gcd_bigint(g, num.abs()),
            });
        }
        gcd.unwrap_or_else(BigInt::one)
    }

    /// Make the polynomial primitive (divide by integer content).
    pub fn primitive(&self) -> Polynomial {
        let content = self.integer_content();
        if content.is_one() {
            return self.clone();
        }
        let c = BigRational::from_integer(content);
        self.scale(&(BigRational::one() / c))
    }

    /// GCD of two polynomials (univariate, using Euclidean algorithm).
    pub fn gcd_univariate(&self, other: &Polynomial) -> Polynomial {
        if self.is_zero() {
            return other.primitive();
        }
        if other.is_zero() {
            return self.primitive();
        }

        let var = self.max_var().max(other.max_var());
        if var == NULL_VAR {
            // Both are constants, GCD is 1
            return Polynomial::one();
        }

        let mut a = self.primitive();
        let mut b = other.primitive();

        // Ensure deg(a) >= deg(b)
        if a.degree(var) < b.degree(var) {
            core::mem::swap(&mut a, &mut b);
        }

        // Limit iterations for safety
        let mut iter_count = 0;
        let max_iters = a.degree(var) as usize + b.degree(var) as usize + 10;

        while !b.is_zero() && iter_count < max_iters {
            iter_count += 1;
            let r = a.pseudo_remainder(&b, var);
            a = b;
            b = if r.is_zero() { r } else { r.primitive() };
        }

        a.primitive()
    }

    /// Pseudo-remainder for univariate polynomials.
    /// Returns r such that lc(b)^d * a = q * b + r for some q,
    /// where d = max(deg(a) - deg(b) + 1, 0).
    ///
    /// Division by the zero polynomial is mathematically undefined; rather
    /// than panicking on a crafted degenerate `divisor` (a soundness/DoS
    /// concern for any caller reachable from untrusted input), this treats
    /// it as "no reduction possible" and returns `self` unchanged, mirroring
    /// `Self::exact_remainder_univariate`'s convention for the same case.
    pub fn pseudo_remainder(&self, divisor: &Polynomial, var: Var) -> Polynomial {
        if divisor.is_zero() {
            return self.clone();
        }

        if self.is_zero() {
            return Polynomial::zero();
        }

        let deg_a = self.degree(var);
        let deg_b = divisor.degree(var);

        if deg_a < deg_b {
            return self.clone();
        }

        let lc_b = divisor.univ_coeff(var, deg_b);
        let mut r = self.clone();

        // Limit iterations
        let max_iters = (deg_a - deg_b + 2) as usize;
        let mut iters = 0;

        while !r.is_zero() && r.degree(var) >= deg_b && iters < max_iters {
            iters += 1;
            let deg_r = r.degree(var);
            let lc_r = r.univ_coeff(var, deg_r);
            let shift = deg_r - deg_b;

            // r = lc_b * r - lc_r * x^shift * divisor
            r = r.scale(&lc_b);
            let subtractor = divisor
                .scale(&lc_r)
                .mul_monomial(&Monomial::from_var_power(var, shift));
            r = Polynomial::sub(&r, &subtractor);
        }

        r
    }

    /// Pseudo-division for univariate polynomials.
    /// Returns (quotient, remainder) such that lc(b)^d * a = q * b + r
    /// where d = deg(a) - deg(b) + 1.
    ///
    /// Division by the zero polynomial is mathematically undefined; rather
    /// than panicking on a crafted degenerate `divisor`, this returns
    /// `(0, self)` -- "no division performed" -- matching the convention
    /// used for the `deg(a) < deg(b)` case below.
    pub fn pseudo_div_univariate(&self, divisor: &Polynomial) -> (Polynomial, Polynomial) {
        if divisor.is_zero() {
            return (Polynomial::zero(), self.clone());
        }

        if self.is_zero() {
            return (Polynomial::zero(), Polynomial::zero());
        }

        let var = self.max_var().max(divisor.max_var());
        if var == NULL_VAR {
            // Both are constants
            return (Polynomial::zero(), self.clone());
        }

        let deg_a = self.degree(var);
        let deg_b = divisor.degree(var);

        if deg_a < deg_b {
            return (Polynomial::zero(), self.clone());
        }

        let lc_b = divisor.univ_coeff(var, deg_b);
        let mut q = Polynomial::zero();
        let mut r = self.clone();

        // Limit iterations
        let max_iters = (deg_a - deg_b + 2) as usize;
        let mut iters = 0;

        while !r.is_zero() && r.degree(var) >= deg_b && iters < max_iters {
            iters += 1;
            let deg_r = r.degree(var);
            let lc_r = r.univ_coeff(var, deg_r);
            let shift = deg_r - deg_b;

            let term = Polynomial::from_terms(
                vec![Term::new(
                    lc_r.clone(),
                    Monomial::from_var_power(var, shift),
                )],
                self.order,
            );

            q = q.scale(&lc_b);
            q = Polynomial::add(&q, &term);

            r = r.scale(&lc_b);
            let subtractor = Polynomial::mul(divisor, &term);
            r = Polynomial::sub(&r, &subtractor);
        }

        (q, r)
    }

    /// Compute the subresultant polynomial remainder sequence (PRS).
    ///
    /// The subresultant PRS is a more efficient variant of the pseudo-remainder sequence
    /// that avoids coefficient explosion through careful normalization. It's useful for
    /// GCD computation and other polynomial algorithms.
    ///
    /// Returns a sequence of polynomials [p0, p1, ..., pk] where:
    /// - p0 = self
    /// - p1 = other
    /// - Each subsequent polynomial is derived using the subresultant algorithm
    ///
    /// Reference: "Algorithms for Computer Algebra" by Geddes, Czapor, Labahn
    pub fn subresultant_prs(&self, other: &Polynomial, var: Var) -> Vec<Polynomial> {
        if self.is_zero() || other.is_zero() {
            return vec![];
        }

        let mut prs = Vec::new();
        let mut a = self.clone();
        let mut b = other.clone();

        // Ensure deg(a) >= deg(b)
        if a.degree(var) < b.degree(var) {
            core::mem::swap(&mut a, &mut b);
        }

        prs.push(a.clone());
        prs.push(b.clone());

        let mut g = Polynomial::one();
        let mut h = Polynomial::one();

        let max_iters = a.degree(var) as usize + b.degree(var) as usize + 10;
        let mut iter_count = 0;

        while !b.is_zero() && iter_count < max_iters {
            iter_count += 1;

            let delta = a.degree(var) as i32 - b.degree(var) as i32;
            if delta < 0 {
                break;
            }

            // Compute pseudo-remainder
            let prem = a.pseudo_remainder(&b, var);

            if prem.is_zero() {
                break;
            }

            // Subresultant normalization to prevent coefficient explosion
            let normalized = if delta == 0 {
                // No adjustment needed for delta = 0
                prem.scale(&(BigRational::one() / &h.constant_value()))
            } else {
                // For delta > 0, divide by g^delta * h
                let g_pow = g.constant_value().pow(delta);
                let divisor = &g_pow * &h.constant_value();
                prem.scale(&(BigRational::one() / divisor))
            };

            // Update g and h for next iteration
            let lc_b = b.leading_coeff_wrt(var);
            g = lc_b;

            h = if delta == 0 {
                Polynomial::one()
            } else {
                let g_val = g.constant_value();
                let h_val = h.constant_value();
                let new_h = g_val.pow(delta) / h_val.pow(delta - 1);
                Polynomial::constant(new_h)
            };

            // Move to next iteration
            a = b;
            b = normalized.primitive(); // Make primitive to keep coefficients manageable
            prs.push(b.clone());
        }

        prs
    }

    /// Resultant of two polynomials with respect to a variable.
    ///
    /// The resultant `Res_var(p, q)` eliminates `var` from `{p = 0, q = 0}`,
    /// returning a polynomial in the remaining variables that vanishes exactly
    /// when `p` and `q` share a common root (over an algebraic closure) or
    /// their leading coefficients in `var` both vanish.
    ///
    /// * **Univariate inputs** (both operands contain only `var`): computed via
    ///   the exact subresultant PRS with rational scalar normalization.
    /// * **Multivariate inputs** (either operand contains another variable):
    ///   computed *exactly* as the determinant of the `(deg_p + deg_q)`-square
    ///   Sylvester matrix over the polynomial coefficient ring, evaluated
    ///   division-free via the Samuelson–Berkowitz algorithm (see
    ///   `sylvester_resultant`). This replaces the former `primitive()`-based
    ///   approximation, which could return a mathematically wrong (non-zero)
    ///   value for genuinely multivariate operands.
    ///
    /// The sign/value convention is the classical
    /// `Res(p, q) = lc(p)^{deg q} · Π_{p(α)=0} q(α)`; in particular
    /// `Res(x - a, x - b) = a - b`.
    pub fn resultant(&self, other: &Polynomial, var: Var) -> Polynomial {
        if self.is_zero() || other.is_zero() {
            return Polynomial::zero();
        }

        let deg_p = self.degree(var);
        let deg_q = other.degree(var);

        if deg_p == 0 {
            return self.pow(deg_q);
        }
        if deg_q == 0 {
            return other.pow(deg_p);
        }

        // Both operands have positive degree in `var`. Compute the resultant
        // exactly as the Sylvester matrix determinant over the coefficient
        // ring, evaluated division-free (Berkowitz). This is exact for both
        // univariate and genuinely multivariate inputs; it replaces the former
        // subresultant-PRS loop, whose leading-coefficient normalization was
        // only correct for constant coefficients (a wrong `primitive()`
        // approximation for multivariate operands) and could return a
        // non-canonical scalar multiple even in the univariate case.
        sylvester_resultant(self, other, var, deg_p as usize, deg_q as usize)
    }

    /// Discriminant of a polynomial with respect to a variable.
    /// discriminant(p) = resultant(p, dp/dx) / lc(p)
    pub fn discriminant(&self, var: Var) -> Polynomial {
        let deriv = self.derivative(var);
        self.resultant(&deriv, var)
    }

    /// Check if the polynomial has a positive sign for all variable assignments.
    /// This is an incomplete check that only handles obvious cases.
    pub fn is_definitely_positive(&self) -> bool {
        // All terms with even total degree and positive coefficients
        if self.terms.is_empty() {
            return false;
        }

        // Check if all monomials are even powers and coefficients are positive
        self.terms
            .iter()
            .all(|t| t.coeff.is_positive() && t.monomial.vars().iter().all(|vp| vp.power % 2 == 0))
    }

    /// Check if the polynomial has a negative sign for all variable assignments.
    /// This is an incomplete check.
    pub fn is_definitely_negative(&self) -> bool {
        self.neg().is_definitely_positive()
    }

    /// Make the polynomial monic (leading coefficient = 1).
    pub fn make_monic(&self) -> Polynomial {
        if self.is_zero() {
            return self.clone();
        }
        let lc = self.leading_coeff();
        if lc.is_one() {
            return self.clone();
        }
        self.scale(&(BigRational::one() / lc))
    }

    /// Compute the square-free part of a polynomial (removes repeated factors).
    pub fn square_free(&self) -> Polynomial {
        if self.is_zero() || self.is_constant() {
            return self.clone();
        }

        let var = self.max_var();
        if var == NULL_VAR {
            return self.clone();
        }

        // Square-free: p / gcd(p, p')
        let deriv = self.derivative(var);
        if deriv.is_zero() {
            return self.clone();
        }

        let g = self.gcd_univariate(&deriv);
        if g.is_constant() {
            self.primitive()
        } else {
            let (q, r) = self.pseudo_div_univariate(&g);
            if r.is_zero() {
                q.primitive().square_free()
            } else {
                self.primitive()
            }
        }
    }

    /// Exact univariate polynomial division over the rationals.
    ///
    /// Returns `(q, r)` with `deg(r) < deg(divisor)` such that
    /// `self = q * divisor + r`, using exact rational coefficient division
    /// (no leading-coefficient scaling factor, unlike
    /// [`pseudo_div_univariate`](Self::pseudo_div_univariate)).
    ///
    /// This is exact and correct for polynomials that are univariate in
    /// `var` (or constant in the other variables); it is used by both
    /// `Self::exact_remainder_univariate` (Sturm sequences) and by
    /// [`super::gcd::PolynomialGcd`]'s Euclidean-algorithm GCD/LCM.
    ///
    /// # Multivariate limitation
    ///
    /// [`Self::univ_coeff`] only recognizes terms with at most one variable,
    /// so if `self` or `divisor` contains a term mixing `var` with another
    /// variable, that term is treated as contributing `0` to the relevant
    /// coefficient rather than being folded into a coefficient polynomial.
    /// Callers that need an exact result for genuinely multivariate
    /// polynomials should use [`super::gcd_multivariate`] /
    /// [`super::gcd_multivariate_advanced`] instead.
    pub(crate) fn exact_div_rem_univariate(
        &self,
        divisor: &Polynomial,
        var: Var,
    ) -> (Polynomial, Polynomial) {
        if divisor.is_zero() {
            // Degenerate divisor: nothing to reduce by, remainder is self.
            return (Polynomial::zero(), self.clone());
        }
        if self.is_zero() {
            return (Polynomial::zero(), Polynomial::zero());
        }

        let deg_b = divisor.degree(var);
        let lc_b = divisor.univ_coeff(var, deg_b);
        if lc_b.is_zero() {
            return (Polynomial::zero(), self.clone());
        }

        let mut q = Polynomial::zero();
        let mut r = self.clone();
        // Each iteration strictly lowers deg(r) by at least one; bound the loop
        // by the initial degree gap plus slack for safety.
        let deg_a = self.degree(var);
        let max_iters = deg_a.saturating_sub(deg_b) as usize + 2;
        let mut iters = 0;

        while !r.is_zero() && r.degree(var) >= deg_b && iters < max_iters {
            iters += 1;
            let deg_r = r.degree(var);
            let lc_r = r.univ_coeff(var, deg_r);
            let shift = deg_r - deg_b;

            // factor = lc_r / lc_b (exact rational)
            let factor = lc_r / &lc_b;
            let term = Polynomial::constant(factor.clone())
                .mul_monomial(&Monomial::from_var_power(var, shift));
            q = Polynomial::add(&q, &term);

            let subtractor = divisor
                .scale(&factor)
                .mul_monomial(&Monomial::from_var_power(var, shift));
            r = Polynomial::sub(&r, &subtractor);
        }

        (q, r)
    }

    /// Exact univariate polynomial remainder over the rationals.
    ///
    /// Returns `r` with `deg(r) < deg(divisor)` such that
    /// `self = q * divisor + r` for some quotient `q`, using exact rational
    /// coefficient division (no leading-coefficient scaling factor).
    ///
    /// Unlike [`pseudo_remainder`](Self::pseudo_remainder), this introduces no
    /// `lc(divisor)^k` multiplier, so the sign of the result is exactly the
    /// sign of the true remainder. This sign fidelity is essential for Sturm
    /// sequences: a spurious negative scale factor (which arises whenever
    /// `lc(divisor)` is negative and `k` is odd) would corrupt sign-variation
    /// counts and hence real-root counts.
    fn exact_remainder_univariate(&self, divisor: &Polynomial, var: Var) -> Polynomial {
        self.exact_div_rem_univariate(divisor, var).1
    }

    /// Compute the Sturm sequence for a univariate polynomial.
    /// The Sturm sequence is used for counting real roots in an interval.
    ///
    /// The chain is built as `p_{i+1} = -rem(p_{i-1}, p_i)` using the *exact*
    /// rational remainder. The pseudo-remainder must not be used here: it
    /// scales by `lc(p_i)^k`, whose sign flips when the leading coefficient is
    /// negative, which would break the Sturm sign invariant and yield wrong
    /// root counts (e.g. `-x^2 + 1` on `(-2, 2)` would report 0 roots instead
    /// of 2).
    pub fn sturm_sequence(&self, var: Var) -> Vec<Polynomial> {
        if self.is_zero() || self.degree(var) == 0 {
            return vec![self.clone()];
        }

        let mut seq = Vec::new();
        seq.push(self.clone());
        seq.push(self.derivative(var));

        // Build Sturm sequence: p_i+1 = -rem(p_i-1, p_i)
        let max_iterations = self.degree(var) as usize + 5;
        let mut iterations = 0;

        // `seq` always has >= 2 elements by construction (two pushes above,
        // never popped), so `last()` is never `None`; `unwrap_or(false)`
        // documents that invariant without an `.expect()` panic path, and
        // degrades gracefully (stops the loop) instead of aborting even if
        // that invariant were ever violated by a future edit.
        while seq.last().map(|p| !p.is_zero()).unwrap_or(false) && iterations < max_iterations {
            iterations += 1;
            let n = seq.len();
            let rem = seq[n - 2].exact_remainder_univariate(&seq[n - 1], var);
            if rem.is_zero() {
                break;
            }
            seq.push(rem.neg());
        }

        seq
    }

    /// Count the number of real roots in an interval using Sturm's theorem.
    /// Returns the number of distinct real roots in (a, b).
    pub fn count_roots_in_interval(&self, var: Var, a: &BigRational, b: &BigRational) -> usize {
        if self.is_zero() {
            return 0;
        }

        let sturm_seq = self.sturm_sequence(var);
        if sturm_seq.is_empty() {
            return 0;
        }

        // Count sign variations at a and b
        let var_a = count_sign_variations(&sturm_seq, var, a);
        let var_b = count_sign_variations(&sturm_seq, var, b);

        // Number of roots = var_a - var_b
        var_a.saturating_sub(var_b)
    }

    /// Compute Cauchy's root bound for a univariate polynomial.
    /// Returns B such that all roots have absolute value <= B.
    ///
    /// Cauchy bound: 1 + max(|a_i| / |a_n|) for i < n
    ///
    /// This is a simple, conservative bound that's fast to compute.
    pub fn cauchy_bound(&self, var: Var) -> BigRational {
        cauchy_root_bound(self, var)
    }

    /// Compute Fujiwara's root bound for a univariate polynomial.
    /// Returns B such that all roots have absolute value <= B.
    ///
    /// Fujiwara bound: 2 * max(|a_i/a_n|^(1/(n-i))) for i < n
    ///
    /// This bound is generally tighter than Cauchy's bound but more expensive to compute.
    ///
    /// Reference: Fujiwara, "Über die obere Schranke des absoluten Betrages
    /// der Wurzeln einer algebraischen Gleichung" (1916)
    pub fn fujiwara_bound(&self, var: Var) -> BigRational {
        fujiwara_root_bound(self, var)
    }

    /// Compute Lagrange's bound for positive roots of a univariate polynomial.
    /// Returns B such that all positive roots are <= B.
    ///
    /// This can provide a tighter bound than general root bounds when analyzing
    /// only positive roots, useful for root isolation optimization.
    pub fn lagrange_positive_bound(&self, var: Var) -> BigRational {
        lagrange_positive_root_bound(self, var)
    }

    /// Isolate real roots of a univariate polynomial.
    /// Returns a list of intervals, each containing exactly one root.
    /// Uses Descartes' rule of signs to optimize the search.
    pub fn isolate_roots(&self, var: Var) -> Vec<(BigRational, BigRational)> {
        if self.is_zero() || self.is_constant() {
            return vec![];
        }

        // Make square-free first
        let p = self.square_free();
        if p.is_constant() {
            return vec![];
        }

        // Find a bound for all real roots using Cauchy's bound
        let bound = cauchy_root_bound(&p, var);

        // Use Descartes' rule to check if there are any roots at all
        let (_pos_lower, pos_upper) = descartes_positive_roots(&p, var);
        let (_neg_lower, neg_upper) = descartes_negative_roots(&p, var);

        // Use interval bisection with Sturm's theorem
        let mut intervals = Vec::new();
        let mut queue = Vec::new();

        // `count_roots_in_interval` counts roots in the *open* interval
        // (a, b) (standard Sturm's theorem convention). The search below
        // seeds (0, bound) for positive roots and (-bound, 0) for negative
        // roots, so a root at exactly x=0 — the shared boundary of both
        // ranges — falls outside both open intervals and would otherwise be
        // silently dropped. Check for it explicitly up front, the same way
        // an exact root found at a bisection midpoint is recorded below.
        if p.eval_at(var, &BigRational::zero())
            .constant_term()
            .is_zero()
        {
            intervals.push((BigRational::zero(), BigRational::zero()));
        }

        // Only search in positive interval if there might be positive roots
        if pos_upper > 0 {
            queue.push((BigRational::zero(), bound.clone()));
        }

        // Only search in negative interval if there might be negative roots
        if neg_upper > 0 {
            queue.push((-bound, BigRational::zero()));
        }

        let max_iterations = 1000;
        let mut iterations = 0;

        while let Some((a, b)) = queue.pop() {
            iterations += 1;
            if iterations > max_iterations {
                break;
            }

            let num_roots = p.count_roots_in_interval(var, &a, &b);

            if num_roots == 0 {
                // No roots in this interval
                continue;
            } else if num_roots == 1 {
                // Exactly one root
                intervals.push((a, b));
            } else {
                // Multiple roots, bisect
                let mid = (&a + &b) / BigRational::from_integer(BigInt::from(2));

                // Check if mid is a root
                let val_mid = p.eval_at(var, &mid);
                if val_mid.constant_term().is_zero() {
                    // Found an exact root
                    intervals.push((mid.clone(), mid.clone()));
                    // Don't add intervals that would contain this root again
                    let left_roots = p.count_roots_in_interval(var, &a, &mid);
                    let right_roots = p.count_roots_in_interval(var, &mid, &b);
                    if left_roots > 0 {
                        queue.push((a, mid.clone()));
                    }
                    if right_roots > 0 {
                        queue.push((mid, b));
                    }
                } else {
                    queue.push((a, mid.clone()));
                    queue.push((mid, b));
                }
            }
        }

        intervals
    }

    /// Refine a root approximation using Newton-Raphson iteration.
    ///
    /// Given an initial approximation and bounds, refines the root using the formula:
    /// x_{n+1} = x_n - f(x_n) / f'(x_n)
    ///
    /// # Arguments
    ///
    /// * `var` - The variable to solve for
    /// * `initial` - Initial approximation of the root
    /// * `lower` - Lower bound for the root (for verification)
    /// * `upper` - Upper bound for the root (for verification)
    /// * `max_iterations` - Maximum number of iterations
    /// * `tolerance` - Convergence tolerance (stop when |f(x)| < tolerance)
    ///
    /// # Returns
    ///
    /// The refined root approximation, or None if the method fails to converge
    /// or if the derivative is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigInt;
    /// use num_rational::BigRational;
    /// use oxiz_math::polynomial::Polynomial;
    ///
    /// // Solve x^2 - 2 = 0 (find sqrt(2) ≈ 1.414...)
    /// let p = Polynomial::from_coeffs_int(&[
    ///     (1, &[(0, 2)]),  // x^2
    ///     (-2, &[]),       // -2
    /// ]);
    ///
    /// let initial = BigRational::new(BigInt::from(3), BigInt::from(2)); // 1.5
    /// let lower = BigRational::from_integer(BigInt::from(1));
    /// let upper = BigRational::from_integer(BigInt::from(2));
    ///
    /// let root = p.newton_raphson(0, initial, lower, upper, 10, &BigRational::new(BigInt::from(1), BigInt::from(1000000)));
    /// assert!(root.is_some());
    /// ```
    pub fn newton_raphson(
        &self,
        var: Var,
        initial: BigRational,
        lower: BigRational,
        upper: BigRational,
        max_iterations: usize,
        tolerance: &BigRational,
    ) -> Option<BigRational> {
        use num_traits::{Signed, Zero};

        let derivative = self.derivative(var);

        let mut x = initial;

        for _ in 0..max_iterations {
            // Evaluate f(x)
            let mut assignment = FxHashMap::default();
            assignment.insert(var, x.clone());
            let fx = self.eval(&assignment);

            // Check if we're close enough
            if fx.abs() < *tolerance {
                return Some(x);
            }

            // Evaluate f'(x)
            let fpx = derivative.eval(&assignment);

            // Check for zero derivative
            if fpx.is_zero() {
                return None;
            }

            // Newton-Raphson update: x_new = x - f(x)/f'(x)
            let x_new = x - (fx / fpx);

            // Verify the new point is within bounds
            if x_new < lower || x_new > upper {
                // If out of bounds, use bisection fallback
                return None;
            }

            x = x_new;
        }

        // Return the result even if not fully converged
        Some(x)
    }

    // ── Dense i64 coefficient fast paths (SIMD-accelerated) ─────────────────

    /// Extract the dense integer coefficient vector for a univariate polynomial.
    ///
    /// Returns `Some(coeffs)` where `coeffs[k]` is the coefficient of `var^k`,
    /// if and only if every coefficient is an integer that fits in `i64`.
    /// Returns `None` for multivariate, non-integer, or out-of-range coefficients.
    pub fn as_dense_i64(&self, var: Var) -> Option<Vec<i64>> {
        if self.is_zero() {
            return Some(vec![0i64]);
        }
        // Require the polynomial to be univariate *in `var`* specifically:
        // at most one variable overall (`is_univariate()`), and that
        // variable — if any (a nonzero constant has none, `max_var() ==
        // NULL_VAR`) — must be `var` itself. The previous `&&` accepted any
        // multivariate polynomial whose *highest-indexed* variable happened
        // to equal `var`, silently dropping every other variable's
        // contribution when the coefficients below are extracted purely by
        // `var`-degree.
        if !self.is_univariate() || (self.max_var() != var && self.max_var() != NULL_VAR) {
            return None;
        }

        let deg = self.degree(var) as usize;
        let mut coeffs = vec![0i64; deg + 1];

        for term in &self.terms {
            let d = term.monomial.degree(var) as usize;
            if !term.coeff.is_integer() {
                return None;
            }
            let numer = term.coeff.numer();
            match i64::try_from(numer.clone()) {
                Ok(v) => coeffs[d] = v,
                Err(_) => return None,
            }
        }

        Some(coeffs)
    }

    /// Add two univariate polynomials using the SIMD-accelerated i64 fast path.
    ///
    /// Falls back to the generic [`Polynomial::add`] when coefficients do not fit
    /// in `i64` or the polynomials are not univariate in the same variable.
    pub fn add_fast_i64(&self, other: &Polynomial, var: Var) -> Polynomial {
        let a_opt = self.as_dense_i64(var);
        let b_opt = other.as_dense_i64(var);

        match (a_opt, b_opt) {
            (Some(a), Some(b)) => {
                // poly_add_coeffs pads the shorter slice to max(a.len(), b.len())
                let out = poly_add_coeffs(&a, &b);
                Polynomial::from_dense_i64(&out, var, self.order)
            }
            _ => Polynomial::add(self, other),
        }
    }

    /// Scale a univariate polynomial by an integer scalar using the SIMD fast path.
    ///
    /// Falls back to generic scalar-multiply when coefficients do not fit in `i64`.
    pub fn scale_fast_i64(&self, scalar: i64, var: Var) -> Polynomial {
        match self.as_dense_i64(var) {
            Some(coeffs) => {
                let scaled = poly_mul_scalar(&coeffs, scalar);
                Polynomial::from_dense_i64(&scaled, var, self.order)
            }
            None => {
                let s = BigRational::from_integer(BigInt::from(scalar));
                let scaled_terms: Vec<Term> = self
                    .terms
                    .iter()
                    .map(|t| Term::new(&t.coeff * &s, t.monomial.clone()))
                    .collect();
                Polynomial::from_terms(scaled_terms, self.order)
            }
        }
    }

    /// Compute the i64 dot product between two same-degree dense coefficient arrays.
    ///
    /// Returns `Some(value)` when both polynomials are expressible as dense univariate
    /// `i64` coefficient arrays of equal length, `None` otherwise.
    pub fn dot_product_i64(&self, other: &Polynomial, var: Var) -> Option<i64> {
        let a = self.as_dense_i64(var)?;
        let b = other.as_dense_i64(var)?;
        if a.len() != b.len() {
            return None;
        }
        poly_dot_product(&a, &b).ok()
    }

    /// Reconstruct a [`Polynomial`] from a dense `i64` coefficient array.
    ///
    /// `coeffs[k]` is the coefficient of `var^k`.  Zero coefficients are omitted.
    fn from_dense_i64(coeffs: &[i64], var: Var, order: super::types::MonomialOrder) -> Polynomial {
        let terms: Vec<Term> = coeffs
            .iter()
            .enumerate()
            .filter(|(_, c)| **c != 0)
            .map(|(k, c)| {
                let coeff = BigRational::from_integer(BigInt::from(*c));
                let mon = if k == 0 {
                    Monomial::unit()
                } else {
                    Monomial::from_var_power(var, k as u32)
                };
                Term::new(coeff, mon)
            })
            .collect();
        Polynomial::from_terms(terms, order)
    }
}

// ── Multivariate resultant via Sylvester matrix + Berkowitz determinant ─────

/// Exact resultant `Res_var(p, q)` for polynomials whose coefficients with
/// respect to `var` may themselves be polynomials in other variables.
///
/// Builds the `(deg_p + deg_q)`-square Sylvester matrix in the classical
/// high-to-low coefficient layout (so the value/sign matches the standard
/// resultant `Res(p, q) = lc(p)^{deg q} · Π q(αᵢ)`), then evaluates its
/// determinant over the polynomial coefficient ring **division-free** via the
/// Samuelson–Berkowitz algorithm. Because Berkowitz uses only ring `+`, `-`,
/// `*` (never division), the result is exact for genuinely multivariate
/// inputs, where exact polynomial division is not generally available.
///
/// `deg_p` / `deg_q` are the degrees of `p` / `q` in `var` and must both be
/// `>= 1` (the constant-in-`var` cases are handled by the caller).
///
/// Reference: Z3's `math/polynomial/polynomial.cpp` resultant, computed here
/// division-free rather than via pseudo-remainder chains.
fn sylvester_resultant(
    p: &Polynomial,
    q: &Polynomial,
    var: Var,
    deg_p: usize,
    deg_q: usize,
) -> Polynomial {
    let size = deg_p + deg_q;

    // High-to-low coefficient rows: `p_coeff[i]` is the coefficient of
    // `var^(deg_p - i)` in `p` (index 0 = leading coefficient).
    let p_coeff: Vec<Polynomial> = (0..=deg_p)
        .map(|i| p.coeff(var, (deg_p - i) as u32))
        .collect();
    let q_coeff: Vec<Polynomial> = (0..=deg_q)
        .map(|i| q.coeff(var, (deg_q - i) as u32))
        .collect();

    let mut mat: Vec<Vec<Polynomial>> = (0..size)
        .map(|_| (0..size).map(|_| Polynomial::zero()).collect())
        .collect();

    // First `deg_q` rows: shifted copies of `p`'s coefficients.
    for (r, row) in mat.iter_mut().take(deg_q).enumerate() {
        for (i, c) in p_coeff.iter().enumerate() {
            row[r + i] = c.clone();
        }
    }
    // Last `deg_p` rows: shifted copies of `q`'s coefficients.
    for (r, row) in mat.iter_mut().skip(deg_q).take(deg_p).enumerate() {
        for (i, c) in q_coeff.iter().enumerate() {
            row[r + i] = c.clone();
        }
    }

    berkowitz_determinant(&mat)
}

/// Determinant of a square matrix over the (commutative) polynomial ring,
/// computed division-free via the Samuelson–Berkowitz algorithm.
///
/// Returns the exact determinant using only ring `+`, `-`, `*`; it never
/// divides, so it is well-defined over the multivariate polynomial ring (an
/// integral domain but not a field). Singular matrices yield the zero
/// polynomial. `mat` is read but not mutated.
///
/// The algorithm accumulates the characteristic polynomial of each leading
/// principal submatrix as a product of lower-triangular Toeplitz matrices; the
/// determinant of the full `n × n` matrix is `(-1)^n` times the constant
/// coefficient of `det(λI - mat)`.
///
/// Reference: Berkowitz, S. J. (1984), "On computing the determinant in small
/// parallel time using a small number of processors", *Inf. Process. Lett.*
/// 18(3).
fn berkowitz_determinant(mat: &[Vec<Polynomial>]) -> Polynomial {
    let n = mat.len();
    if n == 0 {
        return Polynomial::one();
    }

    // `char_vec` holds coefficients [c_0, c_1, …, c_k] of the characteristic
    // polynomial of the `k × k` leading principal submatrix:
    // `det(λI - M_k) = c_0 λ^k + c_1 λ^{k-1} + … + c_k`, with `c_0 = 1`.
    // Base case `k = 0`: the empty matrix's characteristic polynomial is `1`.
    let mut char_vec: Vec<Polynomial> = vec![Polynomial::one()];

    for r in 1..=n {
        let a = mat[r - 1][r - 1].clone();

        // Toeplitz first-column vector `t` (length `r + 1`):
        //   t[0] = 1
        //   t[1] = -a
        //   t[k] = -(row · M_{r-1}^{k-2} · col)   for k = 2..=r
        // where the leading `(r-1)`-square submatrix `M_{r-1}` is `mat[0..r-1]
        // [0..r-1]`, `col` its column `r-1`, and `row` its row `r-1`.
        let mut t: Vec<Polynomial> = Vec::with_capacity(r + 1);
        t.push(Polynomial::one());
        t.push(a.neg());

        if r >= 2 {
            let dim = r - 1;
            let col: Vec<Polynomial> = (0..dim).map(|i| mat[i][r - 1].clone()).collect();
            let row: Vec<Polynomial> = (0..dim).map(|j| mat[r - 1][j].clone()).collect();

            // `w` starts as `M^0 · col = col`, then `w ← M_{r-1} · w`.
            let mut w = col;
            for k in 0..dim {
                let mut dot = Polynomial::zero();
                for (rj, wj) in row.iter().zip(w.iter()) {
                    dot = Polynomial::add(&dot, &Polynomial::mul(rj, wj));
                }
                t.push(dot.neg());

                if k + 1 < dim {
                    let mut w_next: Vec<Polynomial> = Vec::with_capacity(dim);
                    for mat_row in mat.iter().take(dim) {
                        let mut acc = Polynomial::zero();
                        for (j, wj) in w.iter().enumerate() {
                            acc = Polynomial::add(&acc, &Polynomial::mul(&mat_row[j], wj));
                        }
                        w_next.push(acc);
                    }
                    w = w_next;
                }
            }
        }

        // `new_char = C · char_vec`, where `C` is the `(r+1) × r` lower-
        // triangular Toeplitz matrix with first column `t`:
        // `C[i][j] = t[i-j]` for `i >= j`, else `0`.
        let mut new_char: Vec<Polynomial> = Vec::with_capacity(r + 1);
        for i in 0..=r {
            let mut acc = Polynomial::zero();
            for (j, cv) in char_vec.iter().enumerate() {
                if i >= j && (i - j) < t.len() {
                    acc = Polynomial::add(&acc, &Polynomial::mul(&t[i - j], cv));
                }
            }
            new_char.push(acc);
        }
        char_vec = new_char;
    }

    // det(M) = (-1)^n · c_n, where c_n is the trailing coefficient of
    // `det(λI - M)`.
    let c_n = char_vec[n].clone();
    if n.is_multiple_of(2) { c_n } else { c_n.neg() }
}
