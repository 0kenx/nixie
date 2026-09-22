//! Exhaustive interface case splitting, with scoped assumptions and witnesses.
//! For each shared arithmetic pair, (=), (<), (>) partition all possibilities.
//! EUF receives equality or disequality; arithmetic receives the exact order.
use super::*;

impl TheoryCombiner {
    /// Value of a shared term in the last accepted combined model. Component
    /// solvers are restored after search; their private candidates may differ.
    #[must_use]
    pub fn shared_value(&self, term: TermId) -> Option<&num_rational::BigRational> {
        self.current_arrangement.as_ref()?;
        self.arrangement_values.get(&term)
    }

    pub(super) fn search_arrangements(&mut self) -> Result<TheoryResult> {
        let mut terms: Vec<_> = self.shared_vars.iter().copied().collect();
        terms.sort_unstable();
        if terms.len() > 64 {
            return Ok(TheoryResult::Unknown);
        }
        let nodes: Vec<_> = terms.iter().map(|&t| self.euf.intern(t)).collect();
        let pairs: Vec<_> = (0..terms.len())
            .flat_map(|i| (0..i).map(move |j| (j, i)))
            .collect();
        let mut reasons = self.arith.arrangement_reasons();
        reasons.extend(self.euf.arrangement_reasons());
        reasons.sort_unstable();
        reasons.dedup();
        let mut next_choice = vec![0u8];
        let mut choices = Vec::new();
        let mut incomplete = false;
        let mut steps = 0usize;
        let outcome = (|| {
            while let Some(next) = next_choice.last_mut() {
                let depth = choices.len();
                if depth == pairs.len() {
                    let arrangement = self.extract_arrangement_from_arith();
                    if !arrangement.is_complete(&terms) {
                        return Ok(TheoryResult::Unknown);
                    }
                    self.arrangement_values = terms
                        .iter()
                        .filter_map(|&v| self.arith.value_exact(v).map(|value| (v, value)))
                        .collect();
                    if self.arrangement_values.len() != terms.len() {
                        return Ok(TheoryResult::Unknown);
                    }
                    self.current_arrangement = Some(arrangement);
                    return Ok(TheoryResult::Sat);
                }
                if *next == 3 {
                    next_choice.pop();
                    if choices.pop().is_some() {
                        self.arith.pop();
                        self.euf.pop();
                    }
                    continue;
                }
                let choice = *next;
                *next += 1;
                steps += 1;
                if steps > 16_384 {
                    return Ok(TheoryResult::Unknown);
                }
                let (a, b) = pairs[depth];
                let lhs = [
                    (terms[a], Rational64::from_integer(1)),
                    (terms[b], Rational64::from_integer(-1)),
                ];
                self.arith.push();
                self.euf.push();
                // Include the open scope in cleanup even if an inner call fails.
                choices.push(choice);
                let zero = Rational64::from_integer(0);
                let reason = TermId::new(0);
                match choice {
                    0 => {
                        self.arith.assert_eq(&lhs, zero, reason);
                        self.euf.merge(nodes[a], nodes[b], reason)?;
                    }
                    1 => {
                        self.arith.assert_lt(&lhs, zero, reason);
                        self.euf.assert_diseq(nodes[a], nodes[b], reason);
                    }
                    2 => {
                        self.arith.assert_gt(&lhs, zero, reason);
                        self.euf.assert_diseq(nodes[a], nodes[b], reason);
                    }
                    _ => return Ok(TheoryResult::Unknown),
                }
                let euf = self.euf.check()?;
                let arithmetic = if matches!(euf, TheoryResult::Unsat(_)) {
                    TheoryResult::Sat
                } else {
                    self.arith.check()?
                };
                match (euf, arithmetic) {
                    (TheoryResult::Sat, TheoryResult::Sat) => {
                        next_choice.push(0);
                        continue;
                    }
                    (TheoryResult::Unsat(_), _) | (_, TheoryResult::Unsat(_)) => {}
                    _ => incomplete = true,
                }
                choices.pop();
                self.arith.pop();
                self.euf.pop();
            }
            if incomplete {
                Ok(TheoryResult::Unknown)
            } else {
                Ok(TheoryResult::Unsat(reasons))
            }
        })();
        // Neither a successful witness nor an error commits any search choice.
        for _ in choices {
            self.arith.pop();
            self.euf.pop();
        }
        outcome
    }
}
