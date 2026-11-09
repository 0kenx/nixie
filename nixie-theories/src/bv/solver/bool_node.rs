//! Boolean definitions shared by scoped bit-vector checks.

use super::*;
use nixie_core::ast::{TermKind, TermManager};

impl BvSolver {
    /// Encode a Boolean circuit with an explicit postorder worklist.
    /// Memoized definitions survive every assertion scope; unsupported nodes
    /// return `None` instead of receiving unconstrained truth variables.
    pub fn encode_bool_node(&mut self, term: TermId, manager: &TermManager) -> Option<Var> {
        let mut stack = vec![(term, false)];
        while let Some((current, ready)) = stack.pop() {
            let data = manager.get(current)?;
            if data.sort != manager.sorts.bool_sort {
                return None;
            }
            if self.bool_node.contains_key(&current) {
                continue;
            }
            if ready {
                self.encode_bool_node_ready(current, manager)?;
                continue;
            }
            stack.push((current, true));
            match &data.kind {
                TermKind::Not(a) => stack.push((*a, false)),
                TermKind::And(args) | TermKind::Or(args) => {
                    stack.extend(args.iter().rev().map(|&arg| (arg, false)));
                }
                TermKind::Xor(a, b) | TermKind::Implies(a, b) => {
                    stack.push((*b, false));
                    stack.push((*a, false));
                }
                TermKind::Eq(a, b) => {
                    if manager.get(*a)?.sort != manager.get(*b)?.sort {
                        return None;
                    }
                    if manager.get(*a)?.sort == manager.sorts.bool_sort {
                        stack.push((*b, false));
                        stack.push((*a, false));
                    }
                }
                TermKind::Distinct(args) => {
                    if args.iter().all(|&arg| {
                        manager
                            .get(arg)
                            .is_some_and(|t| t.sort == manager.sorts.bool_sort)
                    }) {
                        stack.extend(args.iter().rev().map(|&arg| (arg, false)));
                    }
                }
                TermKind::Ite(c, t, e) => {
                    stack.push((*e, false));
                    stack.push((*t, false));
                    stack.push((*c, false));
                }
                TermKind::Var(_)
                | TermKind::True
                | TermKind::False
                | TermKind::BvUlt(_, _)
                | TermKind::BvUle(_, _)
                | TermKind::BvSlt(_, _)
                | TermKind::BvSle(_, _) => {}
                _ => return None,
            }
        }
        self.bool_node.get(&term).copied()
    }

    fn encode_bool_node_ready(
        &mut self,
        term: TermId,
        manager: &nixie_core::ast::TermManager,
    ) -> Option<Var> {
        use nixie_core::ast::TermKind;
        if let Some(&v) = self.bool_node.get(&term) {
            return Some(v);
        }
        let kind = manager.get(term)?.kind.clone();
        let out = match kind {
            TermKind::Var(_) => {
                // Free boolean variable: a single fresh SAT var stands for it.
                self.sat.new_var()
            }
            TermKind::True => {
                let v = self.sat.new_var();
                self.define([Lit::pos(v)]);
                v
            }
            TermKind::False => {
                let v = self.sat.new_var();
                self.define([Lit::neg(v)]);
                v
            }
            TermKind::Not(inner) => {
                let iv = self.bool_node.get(&inner).copied()?;
                let v = self.sat.new_var();
                self.encode_not(v, iv);
                v
            }
            TermKind::And(ref args) => {
                // Conjunction of all operands.
                let mut acc: Option<Var> = None;
                for &arg in args {
                    let av = self.bool_node.get(&arg).copied()?;
                    acc = Some(match acc {
                        None => av,
                        Some(prev) => {
                            let v = self.sat.new_var();
                            self.encode_and(v, prev, av);
                            v
                        }
                    });
                }
                match acc {
                    Some(v) => v,
                    None => {
                        // Empty conjunction is `true`.
                        let v = self.sat.new_var();
                        self.define([Lit::pos(v)]);
                        v
                    }
                }
            }
            TermKind::Or(ref args) => {
                let mut acc: Option<Var> = None;
                for &arg in args {
                    let av = self.bool_node.get(&arg).copied()?;
                    acc = Some(match acc {
                        None => av,
                        Some(prev) => {
                            let v = self.sat.new_var();
                            self.encode_or(v, prev, av);
                            v
                        }
                    });
                }
                match acc {
                    Some(v) => v,
                    None => {
                        // Empty disjunction is `false`.
                        let v = self.sat.new_var();
                        self.define([Lit::neg(v)]);
                        v
                    }
                }
            }
            TermKind::Eq(lhs, rhs) => {
                // Bool-sorted operands compare truth values (not bit-blasted
                // vectors); BV-sorted operands are pre-bit-blasted by the
                // caller and take the flat per-bit encoder below.
                let lhs_bool = manager
                    .get(lhs)
                    .is_some_and(|t| t.sort == manager.sorts.bool_sort);
                if lhs_bool {
                    let lv = self.bool_node.get(&lhs).copied()?;
                    let rv = self.bool_node.get(&rhs).copied()?;
                    let out = self.sat.new_var();
                    // v <=> (l ↔ r) = ¬(l ⊕ r), folded on constants.
                    let xored = self.gate_xor(self.sig(lv), self.sig(rv));
                    let folded = self.gate_not(xored);
                    self.wire(out, folded);
                    out
                } else {
                    self.encode_eq_node(lhs, rhs)?
                }
            }
            TermKind::BvUlt(lhs, rhs) => self.bool_ult(lhs, rhs, manager, false)?,
            TermKind::BvUle(lhs, rhs) => self.bool_ule(lhs, rhs, manager, false)?,
            TermKind::BvSlt(lhs, rhs) => self.bool_ult(lhs, rhs, manager, true)?,
            TermKind::BvSle(lhs, rhs) => self.bool_ule(lhs, rhs, manager, true)?,
            TermKind::Xor(a, b) => {
                // Boolean XOR through the folding gate: `v <=> a ⊕ b`.
                let av = self.bool_node.get(&a).copied()?;
                let bv = self.bool_node.get(&b).copied()?;
                let out = self.sat.new_var();
                let folded = self.gate_xor(self.sig(av), self.sig(bv));
                self.wire(out, folded);
                out
            }
            TermKind::Implies(a, b) => {
                // `v <=> (¬a ∨ b)`, through the folding gates so constant
                // operands collapse instead of emitting dead clauses.
                let av = self.bool_node.get(&a).copied()?;
                let bv = self.bool_node.get(&b).copied()?;
                let out = self.sat.new_var();
                let negated = self.gate_not(self.sig(av));
                let folded = self.gate_or(negated, self.sig(bv));
                self.wire(out, folded);
                out
            }
            TermKind::Ite(cond, t, e) => {
                // Bool-sorted `ite`: a mux over the two branch truth values.
                let cv = self.bool_node.get(&cond).copied()?;
                let tv = self.bool_node.get(&t).copied()?;
                let ev = self.bool_node.get(&e).copied()?;
                let out = self.sat.new_var();
                let folded = self.gate_mux(self.sig(cv), self.sig(tv), self.sig(ev));
                self.wire(out, folded);
                out
            }
            TermKind::Distinct(ref args)
                if args.iter().all(|&arg| {
                    manager
                        .get(arg)
                        .is_some_and(|t| t.sort == manager.sorts.bool_sort)
                }) =>
            {
                match args.as_slice() {
                    [] | [_] => self.const_true,
                    &[a, b] => {
                        let av = self.bool_node.get(&a).copied()?;
                        let bv = self.bool_node.get(&b).copied()?;
                        let value = self.gate_xor(self.sig(av), self.sig(bv));
                        self.sig_var(value)
                    }
                    _ => self.const_false,
                }
            }
            TermKind::Distinct(ref args) => {
                // `distinct(a_1..a_n)` over bit-vector or Bool operands:
                // the conjunction of pairwise disequalities, each obtained by
                // negating the flat equality encoder (Z3's `blast_distinct`).
                // The n² pairs stay finite: `distinct` arity is bounded by the
                // input's own breadth.
                if args.len() < 2 {
                    // Degenerate `distinct` is vacuously true (and of one
                    // argument, true by definition).
                    let v = self.sat.new_var();
                    self.define([Lit::pos(v)]);
                    v
                } else {
                    let mut pair_lits: SmallVec<[Var; 8]> = SmallVec::new();
                    for i in 0..args.len() {
                        for j in (i + 1)..args.len() {
                            let eq_var = self.encode_eq_node(args[i], args[j])?;
                            let ne_var = self.sat.new_var();
                            self.encode_not(ne_var, eq_var);
                            pair_lits.push(ne_var);
                        }
                    }
                    let mut acc: Option<Var> = None;
                    for pv in pair_lits {
                        acc = Some(match acc {
                            None => pv,
                            Some(prev) => {
                                let v = self.sat.new_var();
                                self.encode_and(v, prev, pv);
                                v
                            }
                        });
                    }
                    acc.unwrap_or_else(|| {
                        let v = self.sat.new_var();
                        self.define([Lit::pos(v)]);
                        v
                    })
                }
            }
            _ => return None,
        };
        self.bool_node.insert(term, out);
        Some(out)
    }
}
