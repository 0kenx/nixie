//! Debug-only theory-model violation scanning (env-gated, debug builds).
//!
//! At a `Sat` verdict, walk every assigned theory atom and report the first
//! one the final theory model violates — the diagnostic used to hunt the
//! negated-atom enforcement holes (see
//! `docs/studies/2026-08-arithmetic-negated-atoms-false-sat.md`). Split into
//! its own module to keep the parent under the workspace line limit.
//!
//! Semantics note (the first version of this scanner got this wrong, which
//! cost a misdiagnosis): `var_to_parsed_arith` carries a **`Le` placeholder**
//! for `Eq` atoms (encode.rs stores it so the positive polarity can assert
//! both bounds). A scanner that evaluates every parsed form as a comparison
//! therefore misreads every negated `=` atom as a violated `≤`. The
//! comparison branch below only fires when the atom's `Constraint` is
//! genuinely `Lt/Le/Gt/Ge`; `Eq`/`Diseq` atoms are checked as (dis)equalities.

use super::TheoryManager;
use crate::solver::Constraint;
use crate::solver::types::ArithConstraintType::{Ge, Gt, Le, Lt};
use num_rational::Rational64;
use oxiz_core::ast::TermId;

impl TheoryManager<'_> {
    /// Scan every assigned theory atom against the final theory model and
    /// print the first violation. `OXIZ_SCAN_VIOL=1` (debug builds) to enable.
    pub fn debug_scan_theory_model_violations(&self, tag: &str) {
        let Some(report) = self.debug_first_model_violation() else {
            return;
        };
        eprintln!("[viol] {tag}: {report}");
    }

    pub(super) fn debug_first_model_violation(&self) -> Option<String> {
        for (var, constraint) in self.var_to_constraint.iter() {
            let Some(is_pos) = self.assigned_pol_of(*var) else {
                continue;
            };

            match constraint {
                // Genuine comparisons (NOT `Eq` atoms, whose parsed form is a
                // `Le` placeholder — see the module doc).
                Constraint::Lt(..)
                | Constraint::Le(..)
                | Constraint::Gt(..)
                | Constraint::Ge(..) => {
                    let Some(parsed) = self.var_to_parsed_arith.get(var) else {
                        continue;
                    };
                    let mut val = Rational64::from_integer(0);
                    let mut known = true;
                    for (t, c) in &parsed.terms {
                        match self.arith.value(*t) {
                            Some(v) => val += v * *c,
                            None => {
                                known = false;
                                break;
                            }
                        }
                    }
                    if !known {
                        continue;
                    }
                    let holds = match parsed.constraint_type {
                        Lt => val < parsed.constant,
                        Le => val <= parsed.constant,
                        Gt => val > parsed.constant,
                        Ge => val >= parsed.constant,
                    };
                    if is_pos != holds {
                        return Some(format!(
                            "cmp atom var={var:?} {:?} lhs-eval={val:?} rhs={:?} \
                             assigned={is_pos} in_guard={} [{}]",
                            parsed.constraint_type,
                            parsed.constant,
                            self.processed_lits.contains(&(*var, is_pos)),
                            self.debug_describe_terms(
                                &parsed.terms.iter().map(|(t, _)| *t).collect::<Vec<_>>()
                            ),
                        ));
                    }
                }
                Constraint::Eq(l, r) => {
                    let (l, r) = (*l, *r);
                    match (self.arith.value(l), self.arith.value(r)) {
                        (Some(a), Some(b)) => {
                            if is_pos != (a == b) {
                                return Some(format!(
                                    "eq atom var={var:?} arith {l:?}={a:?} vs {r:?}={b:?} \
                                     assigned={is_pos} in_guard={}",
                                    self.processed_lits.contains(&(*var, is_pos)),
                                ));
                            }
                        }
                        _ => {
                            let (Some(nl), Some(nr)) =
                                (self.euf.term_to_node(l), self.euf.term_to_node(r))
                            else {
                                continue;
                            };
                            let model_eq = self.euf.are_equal_immutable(nl, nr);
                            if is_pos != model_eq {
                                return Some(format!(
                                    "eq atom var={var:?} euf-equal={model_eq} assigned={is_pos} \
                                     in_guard={}",
                                    self.processed_lits.contains(&(*var, is_pos)),
                                ));
                            }
                        }
                    }
                }
                Constraint::Diseq(l, r) => {
                    let (l, r) = (*l, *r);
                    match (self.arith.value(l), self.arith.value(r)) {
                        (Some(a), Some(b)) => {
                            if is_pos != (a != b) {
                                return Some(format!(
                                    "diseq atom var={var:?} arith {l:?}={a:?} vs {r:?}={b:?} \
                                     assigned={is_pos} in_guard={}",
                                    self.processed_lits.contains(&(*var, is_pos)),
                                ));
                            }
                        }
                        _ => {
                            let (Some(nl), Some(nr)) =
                                (self.euf.term_to_node(l), self.euf.term_to_node(r))
                            else {
                                continue;
                            };
                            let model_ne = self.euf.are_proven_disequal(nl, nr);
                            if is_pos != model_ne {
                                return Some(format!(
                                    "diseq atom var={var:?} euf-disequal={model_ne} \
                                     assigned={is_pos} in_guard={}",
                                    self.processed_lits.contains(&(*var, is_pos)),
                                ));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn debug_describe_terms(&self, terms: &[TermId]) -> String {
        terms
            .iter()
            .map(|t| {
                self.arith
                    .debug_describe_term(*t)
                    .unwrap_or_else(|| format!("{t:?}:n/a"))
            })
            .collect::<Vec<_>>()
            .join(" | ")
    }
}
