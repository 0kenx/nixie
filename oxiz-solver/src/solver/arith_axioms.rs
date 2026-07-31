//! Defining axioms for integer `div` / `mod` and for arithmetic `ite` terms.
//!
//! The linear arithmetic solver only understands sums of scaled *atoms*.  Three
//! term shapes look like atoms but carry a meaning the simplex tableau cannot
//! see on its own:
//!
//!   * `(div m n)` and `(mod m n)` — SMT-LIB *Euclidean* integer division;
//!   * `(ite c a b)` at Int/Real sort — the desugaring of `abs`, `min`, `max`
//!     and of every hand-written conditional value.
//!
//! Handing those to the tableau as free variables is an over-approximation: it
//! keeps `unsat` sound but lets a spurious model through, which is exactly how
//! `(= (abs (- 9)) (abs (mod i0 7)))` used to be reported `sat` even though
//! `(mod i0 7)` can never leave `[0, 7)`.
//!
//! This module restores the missing meaning by asserting the *defining axioms*
//! of each such term to the SAT core as ground unit lemmas, the moment the term
//! has been internalised into [`Solver::arith_terms`]:
//!
//! | term | axioms |
//! |---|---|
//! | `(mod m n)`, `(div m n)`, `n` a non-zero integer constant | `m = n·(div m n) + (mod m n)`, `0 <= (mod m n)`, `(mod m n) <= abs(n) - 1` |
//! | `(mod m 0)`, `(div m 0)` | none — uninterpreted per SMT-LIB; only congruence `m1 = m2 => (mod m1 0) = (mod m2 0)` |
//! | `(div m n)`, `(mod m n)`, `n` symbolic | none — the identity `m = n·q + r` is nonlinear; the atom stays gated |
//! | `(ite c a b)` at Int/Real sort | `c => ite = a`, `¬c => ite = b` |
//!
//! Every axiom is a theorem of the theory, so adding it never changes
//! satisfiability — it only removes the models that violate the term's
//! definition.  A term whose axioms have been asserted is recorded in
//! [`Solver::arith_defined_terms`]; the honesty gate in
//! [`super::encode_guards`] answers `Unknown` for any arithmetic atom that
//! still mentions an *undefined* one, so the incomplete cases above stay honest
//! instead of trusting a free Boolean.
//!
//! Reference: Z3's `smt/theory_lra.cpp::mk_idiv_mod_axioms`, which asserts the
//! same three facts as unit clauses for a numeral divisor and guards them with
//! `q = 0` otherwise.

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};

use super::Solver;
use super::trail::TrailOp;

/// Safety valve on the number of distinct terms that may receive defining
/// axioms in a single solver run.  Each definition costs a bounded handful of
/// clauses, so this only guards against pathological inputs (a formula built
/// from hundreds of thousands of distinct `div`/`mod` sub-terms); realistic
/// benchmarks define a few dozen.  Terms past the cap stay *undefined*, which
/// the honesty gate turns into `Unknown` rather than a guess.
const MAX_ARITH_DEFINED_TERMS: usize = 50_000;

/// How an arithmetic term that the linear solver treats as an opaque atom gets
/// its meaning back.
#[derive(Debug, Clone, Copy)]
enum ArithDef {
    /// `(div m n)` / `(mod m n)` with `n` a non-zero integer constant.
    Euclidean {
        dividend: TermId,
        divisor_term: TermId,
        divisor: i64,
    },
    /// `(div m 0)` / `(mod m 0)`: uninterpreted per SMT-LIB, so the only fact
    /// that holds is congruence in the dividend.  `is_mod` separates the two
    /// operators, which are distinct uninterpreted functions.
    ZeroDivisor { dividend: TermId, is_mod: bool },
    /// Int/Real-sorted `(ite c a b)`.
    Ite {
        cond: TermId,
        then_br: TermId,
        else_br: TermId,
    },
}

/// Classify `term`, or `None` when it needs no defining axiom (an ordinary
/// variable, an uninterpreted application, …) or when no linear axiomatisation
/// exists (a symbolic or out-of-`i64` divisor — those stay gated).
fn classify(term: TermId, manager: &TermManager) -> Option<ArithDef> {
    let node = manager.get(term)?;
    let is_int = node.sort == manager.sorts.int_sort;
    let is_numeric = is_int || node.sort == manager.sorts.real_sort;

    match &node.kind {
        // `div`/`mod` are only Euclidean at Int sort; a Real-sorted `Div` node
        // is exact rational division and is deliberately left undefined here.
        TermKind::Div(m, n) | TermKind::Mod(m, n) if is_int => {
            let is_mod = matches!(node.kind, TermKind::Mod(_, _));
            let divisor = int_constant(*n, manager)?;
            if divisor == 0 {
                Some(ArithDef::ZeroDivisor {
                    dividend: *m,
                    is_mod,
                })
            } else {
                Some(ArithDef::Euclidean {
                    dividend: *m,
                    divisor_term: *n,
                    divisor,
                })
            }
        }
        TermKind::Ite(c, a, b) if is_numeric => Some(ArithDef::Ite {
            cond: *c,
            then_br: *a,
            else_br: *b,
        }),
        _ => None,
    }
}

/// Maximum nesting depth explored by [`int_constant`].  A divisor is a tiny
/// expression in practice; the bound only keeps the evaluator from recursing on
/// an adversarially deep term.
const MAX_CONST_EVAL_DEPTH: u32 = 32;

/// The `i64` value of a *constant* integer expression, or `None` when the term
/// is not constant, does not fit in `i64`, or overflows while folding — in all
/// of which cases the enclosing `div`/`mod` stays gated rather than gaining a
/// wrong axiom.
///
/// This has to look past a bare `IntConst`: the solver's Boolean simplifier does
/// not run the arithmetic rewriter, so `(mod i0 (- 7))` still reaches the
/// encoder with a `Neg(IntConst(7))` divisor.  The kinds folded here are exactly
/// those [`Solver::extract_linear_terms`] also treats as constants, so the
/// value used to build the axiom always agrees with the value the linear parse
/// derives from the very same term.
fn int_constant(term: TermId, manager: &TermManager) -> Option<i64> {
    int_constant_at(term, manager, 0)
}

fn int_constant_at(term: TermId, manager: &TermManager, depth: u32) -> Option<i64> {
    if depth >= MAX_CONST_EVAL_DEPTH {
        return None;
    }
    match &manager.get(term)?.kind {
        TermKind::IntConst(n) => n.to_i64(),
        TermKind::Neg(a) => int_constant_at(*a, manager, depth + 1)?.checked_neg(),
        TermKind::Sub(a, b) => {
            let lhs = int_constant_at(*a, manager, depth + 1)?;
            let rhs = int_constant_at(*b, manager, depth + 1)?;
            lhs.checked_sub(rhs)
        }
        TermKind::Add(args) => {
            let mut sum: i64 = 0;
            for &a in args {
                sum = sum.checked_add(int_constant_at(a, manager, depth + 1)?)?;
            }
            Some(sum)
        }
        TermKind::Mul(args) => {
            let mut product: i64 = 1;
            for &a in args {
                product = product.checked_mul(int_constant_at(a, manager, depth + 1)?)?;
            }
            Some(product)
        }
        _ => None,
    }
}

impl Solver {
    /// Assert the defining axioms of every internalised `div` / `mod` / numeric
    /// `ite` term that does not have them yet.
    ///
    /// Driven from [`Solver::arith_terms`] — the set of terms the encoder
    /// actually handed to the arithmetic solver — so a `div`/`mod` sub-term
    /// that the simplifier folded away, or that only occurs inside a quantifier
    /// body, never costs a clause.
    ///
    /// Scope: the lemmas are added to the SAT core at the *current* assertion
    /// level, and [`Solver::arith_defined_terms`] is journalled on the trail, so
    /// a `pop` retracts the clauses and the "already defined" marks together.
    /// A later scope that needs the same term re-derives its axioms.
    pub(super) fn instantiate_arith_axioms(&mut self, manager: &mut TermManager) {
        if self.arith_terms.is_empty() {
            return;
        }

        // Deterministic order: `arith_terms` is a hash set, and the order in
        // which lemmas enter the SAT core perturbs the search.
        let mut candidates: Vec<TermId> = self.arith_terms.iter().copied().collect();
        candidates.sort_unstable();

        // Euclidean semantics rest on the quotient being an *integer*; in real
        // mode the tableau would satisfy `m = n·q + r` with a fractional `q` and
        // the definition would carry no information.  Leave those terms
        // undefined so the honesty gate reports `Unknown`.
        let integer_mode = self.arith.is_integer();

        // Zero-divisor terms already visited in this pass, for pairwise
        // congruence.  `(mod _ 0)` is an uninterpreted unary function, so two
        // occurrences must agree whenever their dividends do.
        let mut zero_divisor_seen: Vec<ZeroDivisorTerm> = Vec::new();

        for term in candidates {
            let Some(def) = classify(term, manager) else {
                continue;
            };
            let already_defined = self.arith_defined_terms.contains(&term);

            match def {
                ArithDef::Euclidean {
                    dividend,
                    divisor_term,
                    divisor,
                } => {
                    if already_defined || !integer_mode {
                        continue;
                    }
                    if self.arith_defined_terms.len() >= MAX_ARITH_DEFINED_TERMS {
                        break;
                    }
                    self.assert_euclidean_axioms(dividend, divisor_term, divisor, manager);
                }
                ArithDef::ZeroDivisor { dividend, is_mod } => {
                    if !integer_mode {
                        continue;
                    }
                    let fresh = !already_defined;
                    for other in &zero_divisor_seen {
                        // Emit each unordered pair once: only when at least one
                        // side is new in this pass.
                        if (fresh || other.fresh) && other.is_mod == is_mod {
                            let (t1, m1, t2, m2) = (other.term, other.dividend, term, dividend);
                            self.assert_zero_divisor_congruence(t1, m1, t2, m2, manager);
                        }
                    }
                    zero_divisor_seen.push(ZeroDivisorTerm {
                        term,
                        dividend,
                        is_mod,
                        fresh,
                    });
                    if fresh {
                        if self.arith_defined_terms.len() >= MAX_ARITH_DEFINED_TERMS {
                            break;
                        }
                        self.mark_arith_defined(term);
                    }
                }
                ArithDef::Ite {
                    cond,
                    then_br,
                    else_br,
                } => {
                    if already_defined {
                        continue;
                    }
                    if self.arith_defined_terms.len() >= MAX_ARITH_DEFINED_TERMS {
                        break;
                    }
                    self.assert_ite_axioms(term, cond, then_br, else_br, manager);
                }
            }
        }
    }

    /// `m = n·(div m n) + (mod m n)` together with `0 <= (mod m n) < abs(n)`,
    /// for a non-zero constant `n`.  The two facts pin `(mod m n)` to the unique
    /// Euclidean remainder, and therefore `(div m n)` to the unique quotient.
    ///
    /// The partner term is materialised on demand: seeing only `(mod m n)` in
    /// the input is enough to introduce `(div m n)`, which is what makes the
    /// divisibility half of the definition available to the tableau.
    fn assert_euclidean_axioms(
        &mut self,
        dividend: TermId,
        divisor_term: TermId,
        divisor: i64,
        manager: &mut TermManager,
    ) {
        // `i64::MIN` has no representable magnitude; leave such a divisor
        // undefined (gated) rather than emit a wrong bound.
        let Some(upper) = divisor.checked_abs().and_then(|d| d.checked_sub(1)) else {
            return;
        };

        let quotient = manager.mk_div(dividend, divisor_term);
        let remainder = manager.mk_mod(dividend, divisor_term);
        let zero = manager.mk_int(0);
        let upper_bound = manager.mk_int(upper);

        let scaled_quotient = manager.mk_mul([divisor_term, quotient]);
        let reconstructed = manager.mk_add([scaled_quotient, remainder]);
        let identity = manager.mk_eq(dividend, reconstructed);
        let lower = manager.mk_ge(remainder, zero);
        let upper_axiom = manager.mk_le(remainder, upper_bound);

        for lemma in [identity, lower, upper_axiom] {
            self.assert_ground_lemma(lemma, manager);
        }

        // Both halves of the pair are now fully determined.
        self.mark_arith_defined(quotient);
        self.mark_arith_defined(remainder);
    }

    /// `c => ite = a` and `¬c => ite = b` for an Int/Real-sorted `(ite c a b)`.
    ///
    /// This is what gives `(abs t)` — parsed as `(ite (>= t 0) t (- t))` — its
    /// arithmetic meaning, including `(abs t) >= 0` (both branches are `>= 0`
    /// under their guard) and `(abs t) = t` / `= -t` under a known sign.
    fn assert_ite_axioms(
        &mut self,
        ite: TermId,
        cond: TermId,
        then_br: TermId,
        else_br: TermId,
        manager: &mut TermManager,
    ) {
        let then_eq = manager.mk_eq(ite, then_br);
        let else_eq = manager.mk_eq(ite, else_br);
        let negated_cond = manager.mk_not(cond);
        let then_axiom = manager.mk_implies(cond, then_eq);
        let else_axiom = manager.mk_implies(negated_cond, else_eq);

        for lemma in [then_axiom, else_axiom] {
            self.assert_ground_lemma(lemma, manager);
        }
        self.mark_arith_defined(ite);
    }

    /// `m1 = m2 => (op m1 0) = (op m2 0)`.
    ///
    /// Division and modulo by zero are *uninterpreted* in SMT-LIB — any value is
    /// allowed — so the linear solver may treat each occurrence as a free
    /// variable.  The one property it must not lose is that they denote a
    /// *function* of the dividend: `(mod i 0)` and `(mod j 0)` cannot differ
    /// once `i = j`.  Ackermann-style congruence over the finitely many
    /// zero-divisor terms in the formula restores exactly that.
    fn assert_zero_divisor_congruence(
        &mut self,
        left: TermId,
        left_dividend: TermId,
        right: TermId,
        right_dividend: TermId,
        manager: &mut TermManager,
    ) {
        let antecedent = manager.mk_eq(left_dividend, right_dividend);
        let consequent = manager.mk_eq(left, right);
        let lemma = manager.mk_implies(antecedent, consequent);
        self.assert_ground_lemma(lemma, manager);
    }

    /// Encode `lemma` and force it true with a unit clause at the current
    /// assertion level.
    fn assert_ground_lemma(&mut self, lemma: TermId, manager: &mut TermManager) {
        let lit = self.encode(lemma, manager);
        let _ = self.sat.add_clause([lit]);
    }

    /// Record that `term` now carries its defining axioms, journalling the mark
    /// so a `pop` drops it alongside the lemma clauses it stands for.
    fn mark_arith_defined(&mut self, term: TermId) {
        if self.arith_defined_terms.insert(term) {
            self.trail.push(TrailOp::ArithDefinedTermAdded { term });
        }
    }
}

/// A `(div m 0)` / `(mod m 0)` occurrence collected during one instantiation
/// pass, used to generate congruence lemmas pairwise.
struct ZeroDivisorTerm {
    term: TermId,
    dividend: TermId,
    is_mod: bool,
    /// `true` when this occurrence was first seen in the current pass; a pair of
    /// two old occurrences already has its congruence lemma.
    fresh: bool,
}
