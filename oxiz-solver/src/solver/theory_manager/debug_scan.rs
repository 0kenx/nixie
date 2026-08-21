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

    /// Congruence-gap probe: find same-function application pairs whose
    /// results are in different EUF classes and report why congruence did not
    /// merge them —
    /// * args pairwise EUF-**equal** ⇒ a congruence-closure miss (EUF bug);
    /// * args EUF-distinct but pairwise **arith-model-equal** ⇒ the
    ///   arith→EUF equality propagation never merged the args (the
    ///   combination gap behind the pete false-SATs).
    ///
    /// Prints at most `cap` findings; `OXIZ_SCAN_VIOL=1` gates the caller.
    pub fn debug_scan_congruence_gaps(&self, cap: usize) {
        let apps = self.euf.debug_app_nodes();
        let mut found = 0usize;
        for i in 0..apps.len() {
            for j in i + 1..apps.len() {
                if found >= cap {
                    return;
                }
                let (a, b) = (apps[i], apps[j]);
                if self.euf.node_func(a) != self.euf.node_func(b) {
                    continue;
                }
                if self.euf.are_equal_immutable(a, b) {
                    continue;
                }
                let (Some(ka), Some(kb)) = (self.euf.node_args(a), self.euf.node_args(b)) else {
                    continue;
                };
                if ka.len() != kb.len() || ka.is_empty() {
                    continue;
                }
                let ta = self.euf.node_term(a);
                let tb = self.euf.node_term(b);
                let args_eq: Vec<bool> = ka
                    .iter()
                    .zip(kb.iter())
                    .map(|(x, y)| self.euf.are_equal_immutable(*x, *y))
                    .collect();
                if args_eq.iter().all(|&e| e) {
                    eprintln!(
                        "[cgap] CONGRUENCE MISS: apps {ta:?}({a}) vs {tb:?}({b}) — args \
                         EUF-equal, results distinct"
                    );
                    found += 1;
                    continue;
                }
                // Args EUF-distinct: are they arith-model-equal?
                let mut all_arith_eq = true;
                let mut any_value = false;
                for (&x, &y) in ka.iter().zip(kb.iter()) {
                    let (Some(tx), Some(ty)) = (self.euf.node_term(x), self.euf.node_term(y))
                    else {
                        all_arith_eq = false;
                        break;
                    };
                    match (self.arith.value(tx), self.arith.value(ty)) {
                        (Some(vx), Some(vy)) => {
                            any_value = true;
                            if vx != vy {
                                all_arith_eq = false;
                                break;
                            }
                        }
                        _ => {
                            all_arith_eq = false;
                            break;
                        }
                    }
                }
                if all_arith_eq && any_value {
                    eprintln!(
                        "[cgap] PROPAGATION GAP: apps {ta:?}({a}) vs {tb:?}({b}) — args \
                         arith-equal in the model, EUF-distinct (merge never propagated)"
                    );
                    found += 1;
                }
            }
        }
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
