//! Cardinality constraint encoding
//!
//! This module implements efficient encoding of cardinality constraints into CNF.
//! Cardinality constraints express conditions like:
//! - At-most-k: at most k of the given literals can be true
//! - At-least-k: at least k of the given literals must be true
//! - Exactly-k: exactly k of the given literals must be true
//!
//! We use the Totalizer encoding which provides:
//! - Efficient incremental strengthening
//! - Good propagation
//! - Reasonable clause count

use crate::literal::Lit;
#[cfg(test)]
use crate::literal::Var;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::Solver;
use smallvec::SmallVec;

/// Cardinality constraint encoder
pub struct CardinalityEncoder;

impl CardinalityEncoder {
    /// Encode an at-most-k constraint: sum(lits) <= k
    ///
    /// # Arguments
    ///
    /// * `solver` - The SAT solver
    /// * `lits` - The literals in the constraint
    /// * `k` - The upper bound
    ///
    /// Returns true if the constraint was successfully encoded
    pub fn encode_at_most_k(solver: &mut Solver, lits: &[Lit], k: usize) -> bool {
        if k >= lits.len() {
            return true; // Constraint is trivially satisfied
        }

        if k == 0 {
            // None of the literals can be true
            for &lit in lits {
                solver.add_clause([lit.negate()]);
            }
            return true;
        }

        if lits.len() <= 4 {
            // For small constraints, use direct encoding
            Self::encode_at_most_k_direct(solver, lits, k)
        } else {
            // For larger constraints, use totalizer encoding
            Self::encode_at_most_k_totalizer(solver, lits, k)
        }
    }

    /// Encode an at-least-k constraint: sum(lits) >= k
    ///
    /// Equivalent to: at-most-(n-k) of the negations
    pub fn encode_at_least_k(solver: &mut Solver, lits: &[Lit], k: usize) -> bool {
        if k == 0 {
            return true; // Trivially satisfied
        }

        if k > lits.len() {
            return false; // Unsatisfiable
        }

        if k == 1 {
            // At least one must be true - simple clause
            solver.add_clause(lits.iter().copied());
            return true;
        }

        // Transform to at-most constraint on negations
        let negated: Vec<Lit> = lits.iter().map(|&l| l.negate()).collect();
        Self::encode_at_most_k(solver, &negated, lits.len() - k)
    }

    /// Encode an exactly-k constraint: sum(lits) == k
    pub fn encode_exactly_k(solver: &mut Solver, lits: &[Lit], k: usize) -> bool {
        if k > lits.len() {
            return false;
        }

        // Combine at-most-k and at-least-k
        Self::encode_at_most_k(solver, lits, k) && Self::encode_at_least_k(solver, lits, k)
    }

    /// Direct encoding for small at-most-k constraints
    fn encode_at_most_k_direct(solver: &mut Solver, lits: &[Lit], k: usize) -> bool {
        // Generate all subsets of size k+1 and forbid them
        let n = lits.len();
        if k >= n {
            return true;
        }

        // Generate all combinations of k+1 literals
        Self::generate_combinations(lits, k + 1, &mut |combo| {
            // Add clause: at least one of these must be false
            let negated: SmallVec<[Lit; 8]> = combo.iter().map(|&&l| l.negate()).collect();
            solver.add_clause(negated.iter().copied());
        });

        true
    }

    /// Helper function to generate all k-combinations
    fn generate_combinations<F>(lits: &[Lit], k: usize, callback: &mut F)
    where
        F: FnMut(&[&Lit]),
    {
        let mut indices = vec![0; k];
        let n = lits.len();

        if k > n {
            return;
        }

        // Initialize first combination
        for (i, item) in indices.iter_mut().enumerate().take(k) {
            *item = i;
        }

        loop {
            // Call callback with current combination
            let combo: Vec<&Lit> = indices.iter().map(|&i| &lits[i]).collect();
            callback(&combo);

            // Find the rightmost index that can be incremented
            let mut i = k;
            loop {
                if i == 0 {
                    return; // No more combinations
                }
                i -= 1;
                if indices[i] < n - k + i {
                    break;
                }
            }

            // Increment this index and reset all following indices
            indices[i] += 1;
            for j in (i + 1)..k {
                indices[j] = indices[j - 1] + 1;
            }
        }
    }

    /// Totalizer encoding for at-most-k constraints
    ///
    /// The totalizer builds a tree of adder circuits that count the number
    /// of true literals. It introduces auxiliary variables representing
    /// "at least i literals are true" for various i.
    fn encode_at_most_k_totalizer(solver: &mut Solver, lits: &[Lit], k: usize) -> bool {
        if lits.is_empty() || k >= lits.len() {
            return true;
        }

        // Build totalizer tree
        let root = Self::build_totalizer_tree(solver, lits, k);
        let Some(&overflow) = root.get(k) else {
            return false;
        };
        solver.add_clause([overflow.negate()]);
        true
    }

    /// Bounded addition of unary counts, following Z3's pb2bv bounded_addition.
    /// Leaves are LITERALS, including their polarity and repeated occurrences.
    /// Only the forward implication is needed: the root overflow is forbidden.
    /// Output bits need not be reified counts for arbitrary other consumers.
    fn build_totalizer_tree(solver: &mut Solver, lits: &[Lit], bound: usize) -> Vec<Lit> {
        let mut layer: Vec<Vec<Lit>> = lits.iter().map(|&lit| vec![lit]).collect();
        while layer.len() > 1 {
            let mut next = Vec::with_capacity(layer.len().div_ceil(2));
            let mut pairs = layer.into_iter();
            while let Some(left) = pairs.next() {
                let Some(right) = pairs.next() else {
                    next.push(left);
                    break;
                };
                let size = (left.len() + right.len()).min(bound + 1);
                let output: Vec<_> = (0..size).map(|_| Lit::pos(solver.new_var())).collect();
                for i in 0..=left.len() {
                    for j in 0..=right.len() {
                        if i + j == 0 || i + j > size {
                            continue;
                        }
                        let mut clause = SmallVec::<[Lit; 3]>::new();
                        if i > 0 {
                            clause.push(left[i - 1].negate());
                        }
                        if j > 0 {
                            clause.push(right[j - 1].negate());
                        }
                        clause.push(output[i + j - 1]);
                        solver.add_clause(clause);
                    }
                }
                next.push(output);
            }
            layer = next;
        }
        layer.pop().unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::SolverResult;

    #[test]
    fn signed_and_repeated_literals_match_exhaustive_counts() {
        for polarity in 0u32..32 {
            for assignment in 0u32..32 {
                for k in 0..=6 {
                    for lower in [false, true] {
                        let mut solver = Solver::new();
                        let vars: Vec<_> = (0..5).map(|_| solver.new_var()).collect();
                        let mut lits: Vec<_> = vars
                            .iter()
                            .enumerate()
                            .map(|(i, &v)| {
                                if polarity & (1 << i) != 0 {
                                    Lit::neg(v)
                                } else {
                                    Lit::pos(v)
                                }
                            })
                            .collect();
                        // A repeated occurrence counts twice, even when negated.
                        lits.push(lits[0]);
                        let count = (0..6)
                            .filter(|&i| {
                                let i = if i == 5 { 0 } else { i };
                                (assignment & (1 << i) != 0) ^ (polarity & (1 << i) != 0)
                            })
                            .count();
                        for (i, &v) in vars.iter().enumerate() {
                            solver.add_clause([if assignment & (1 << i) != 0 {
                                Lit::pos(v)
                            } else {
                                Lit::neg(v)
                            }]);
                        }
                        let encoded = if lower {
                            CardinalityEncoder::encode_at_least_k(&mut solver, &lits, k)
                        } else {
                            CardinalityEncoder::encode_at_most_k(&mut solver, &lits, k)
                        };
                        let expected = if lower { count >= k } else { count <= k };
                        assert!(encoded);
                        assert_eq!(
                            solver.solve(),
                            if expected {
                                SolverResult::Sat
                            } else {
                                SolverResult::Unsat
                            },
                            "polarity={polarity} assignment={assignment} k={k} lower={lower}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_at_most_0() {
        let mut solver = Solver::new();
        let vars: Vec<Var> = (0..3).map(|_| solver.new_var()).collect();
        let lits: Vec<Lit> = vars.iter().map(|&v| Lit::pos(v)).collect();

        CardinalityEncoder::encode_at_most_k(&mut solver, &lits, 0);

        let result = solver.solve();
        // At most 0 means all must be false, which is satisfiable
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_at_most_1() {
        let mut solver = Solver::new();
        let vars: Vec<Var> = (0..3).map(|_| solver.new_var()).collect();
        let lits: Vec<Lit> = vars.iter().map(|&v| Lit::pos(v)).collect();

        CardinalityEncoder::encode_at_most_k(&mut solver, &lits, 1);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_at_least_1() {
        let mut solver = Solver::new();
        let vars: Vec<Var> = (0..3).map(|_| solver.new_var()).collect();
        let lits: Vec<Lit> = vars.iter().map(|&v| Lit::pos(v)).collect();

        CardinalityEncoder::encode_at_least_k(&mut solver, &lits, 1);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_exactly_2() {
        let mut solver = Solver::new();
        let vars: Vec<Var> = (0..3).map(|_| solver.new_var()).collect();
        let lits: Vec<Lit> = vars.iter().map(|&v| Lit::pos(v)).collect();

        CardinalityEncoder::encode_exactly_k(&mut solver, &lits, 2);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_at_most_exceeds_length() {
        let mut solver = Solver::new();
        let vars: Vec<Var> = (0..3).map(|_| solver.new_var()).collect();
        let lits: Vec<Lit> = vars.iter().map(|&v| Lit::pos(v)).collect();

        let success = CardinalityEncoder::encode_at_most_k(&mut solver, &lits, 5);
        assert!(success);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Sat);
    }
}
