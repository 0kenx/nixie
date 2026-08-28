//! NLSAT Theory Wrapper
//!
//! This module wraps the NLSAT solver (from oxiz-nlsat) to provide Theory trait
//! implementation for nonlinear arithmetic (QF_NIA and QF_NRA).
//!
//! ## Architecture
//!
//! - `NlsatTheory`: Main wrapper implementing `Theory` trait
//! - Handles both Real (QF_NRA) and Integer (QF_NIA) nonlinear arithmetic
//! - Delegates to `NlsatSolver` (real) or `NiaSolver` (integer)
//! - `TermPolyTranslator`: Converts `TermId` AST nodes to `Polynomial` representations
//! - `dispatch_nia_constraints`: Runs `NiaSolver` over a set of NIA assertions
//! - `dispatch_nra_constraints`: Runs `NlsatSolver` over a set of NRA assertions
//!
//! ## Reference
//!
//! - Z3's NLSAT integration in nlsat/nlsat_explain.cpp
//! - NLSAT solver: oxiz-nlsat::solver::NlsatSolver
//! - Integer solver: oxiz-nlsat::nia::NiaSolver

#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{Theory, TheoryId, TheoryResult};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::error::Result;
use oxiz_core::sort::SortId;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::nia::{NiaConfig, NiaSolver, VarType};
use oxiz_nlsat::solver::{NlsatSolver, SolverResult};
use oxiz_nlsat::types::{AtomKind, BoolVar, Literal};
use std::collections::HashMap;

// ========  ========
// Public result type for dispatch functions
// ========  ========

// The dispatch vocabulary lives in the ungated `nl_dispatch` module (see its
// doc) so the ground searches stay compiled in the no-`nlsat` build.
pub use crate::nl_dispatch::{NlDispatchResult, NlSatModel};

// ========  ========
// Term→Polynomial translator
// ========  ========

/// Translates `TermId` AST nodes to `Polynomial` values for use with
/// the NLSAT / NIA solver.
///
/// Maintains a cache of `TermId → polynomial variable index` so that each
/// unique variable term receives a stable index.
///
/// Integer `div`/`mod` are encoded with fresh quotient/remainder variables and
/// the Euclidean identities `a = q·b + r`, `0 ≤ r < |b|` (constant positive
/// divisors only for the strict upper bound; otherwise extraction is marked
/// incomplete). Side-constraint atoms are buffered in `pending_atoms`.
pub struct TermPolyTranslator<'a> {
    manager: &'a TermManager,
    nlsat: &'a mut NiaSolver,
    var_cache: HashMap<TermId, u32>,
    integer_mode: bool,
    /// Fresh poly var for each `(div a b)` / `(mod a b)` term pair key.
    divmod_cache: HashMap<(TermId, TermId), (u32, u32)>,
    /// Side constraints emitted while translating div/mod.
    pending_atoms: Vec<PolyAtom>,
    /// Set when a div/mod could not be fully encoded (non-constant divisor, …).
    divmod_incomplete: bool,
}

impl<'a> TermPolyTranslator<'a> {
    /// Create a new translator.
    pub fn new(manager: &'a TermManager, nlsat: &'a mut NiaSolver, integer_mode: bool) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
            integer_mode,
            divmod_cache: HashMap::new(),
            pending_atoms: Vec::new(),
            divmod_incomplete: false,
        }
    }

    /// Translate a term into a `Polynomial`.
    ///
    /// Returns `None` for sub-expressions that cannot be expressed as a
    /// polynomial (e.g. uninterpreted functions, non-constant real division).
    pub fn translate(&mut self, term_id: TermId) -> Option<Polynomial> {
        // `div`/`mod` are encoded via Euclidean auxiliary variables (see
        // [`Self::ensure_divmod`]) rather than by the generic polynomial
        // builder; the wiring lives in [`PolyVarSource::divmod_leaf`], reached
        // through `translate_poly` / `open_poly` so nested occurrences are
        // handled too.
        let manager = self.manager;
        translate_poly(manager, self, term_id)
    }

    /// Ensure Euclidean `div`/`mod` witnesses for `(lhs, rhs)`.
    ///
    /// Emits `lhs = q·rhs + r` and, when `rhs` is a positive integer constant
    /// `b`, `0 ≤ r < b`. Returns `(q_var, r_var)`.
    fn ensure_divmod(&mut self, lhs: TermId, rhs: TermId) -> Option<(u32, u32)> {
        if let Some(&pair) = self.divmod_cache.get(&(lhs, rhs)) {
            return Some(pair);
        }
        let a = self.translate(lhs)?;
        let b_poly = self.translate(rhs)?;

        let q = self.nlsat.nlsat_mut().new_arith_var();
        let r = self.nlsat.nlsat_mut().new_arith_var();
        if self.integer_mode {
            self.nlsat.set_var_type(q, VarType::Integer);
            self.nlsat.set_var_type(r, VarType::Integer);
        } else {
            // Sort-based: div/mod are integer ops in SMT-LIB.
            self.nlsat.set_var_type(q, VarType::Integer);
            self.nlsat.set_var_type(r, VarType::Integer);
        }

        let q_poly = Polynomial::from_var(q);
        let r_poly = Polynomial::from_var(r);
        // a - (q*b + r) = 0
        let qb = Polynomial::mul(&q_poly, &b_poly);
        let qb_r = Polynomial::add(&qb, &r_poly);
        self.pending_atoms.push(PolyAtom {
            poly: Polynomial::sub(&a, &qb_r),
            kind: AtomKind::Eq,
            positive: true,
        });
        // r >= 0  ⇔  NOT(r < 0)
        self.pending_atoms.push(PolyAtom {
            poly: r_poly.clone(),
            kind: AtomKind::Lt,
            positive: false,
        });

        // 0 ≤ r < |b|. For constant b use a linear bound; for variable b use
        // the polynomial encoding r² < b² (equivalent under r ≥ 0, b ≠ 0).
        if b_poly.is_constant() {
            let b_const = b_poly.constant_value();
            if b_const.is_zero() {
                self.divmod_incomplete = true;
                return None;
            }
            let abs_b = if b_const < BigRational::zero() {
                -b_const
            } else {
                b_const
            };
            // r - |b| < 0  ⇔  r < |b|
            self.pending_atoms.push(PolyAtom {
                poly: Polynomial::sub(&r_poly, &Polynomial::constant(abs_b)),
                kind: AtomKind::Lt,
                positive: true,
            });
        } else {
            // r*r - b*b < 0
            let r2 = Polynomial::mul(&r_poly, &r_poly);
            let b2 = Polynomial::mul(&b_poly, &b_poly);
            self.pending_atoms.push(PolyAtom {
                poly: Polynomial::sub(&r2, &b2),
                kind: AtomKind::Lt,
                positive: true,
            });
        }

        self.divmod_cache.insert((lhs, rhs), (q, r));
        Some((q, r))
    }

    fn get_or_create_var(&mut self, term_id: TermId) -> u32 {
        if let Some(&v) = self.var_cache.get(&term_id) {
            return v;
        }
        let v = self.nlsat.nlsat_mut().new_arith_var();
        // Assign integrality from the variable's *actual* sort, not the global
        // `integer_mode` flag. In mixed QF_NIRA problems only genuinely
        // Int-sorted variables may carry the integrality constraint; Real
        // variables must stay real (the NiaSolver default), otherwise a
        // satisfiable non-integral real assignment is spuriously rejected and
        // the solver reports a false UNSAT.
        // Reference: Z3's mixed Int/Real handling in nlsat/nlsat_solver.cpp.
        let is_int_var = self
            .manager
            .get(term_id)
            .map(|t| t.sort == self.manager.sorts.int_sort)
            .unwrap_or(self.integer_mode);
        if is_int_var {
            self.nlsat.set_var_type(v, VarType::Integer);
        }
        self.var_cache.insert(term_id, v);
        v
    }

    /// Return the variable mapping (for model extraction).
    pub fn var_cache(&self) -> &HashMap<TermId, u32> {
        &self.var_cache
    }
}

impl PolyVarSource for TermPolyTranslator<'_> {
    fn var_for(&mut self, term_id: TermId) -> u32 {
        self.get_or_create_var(term_id)
    }

    fn divmod_leaf(
        &mut self,
        _manager: &TermManager,
        lhs: TermId,
        rhs: TermId,
        is_div: bool,
    ) -> Option<Polynomial> {
        let (q, r) = self.ensure_divmod(lhs, rhs)?;
        if is_div {
            Some(Polynomial::from_var(q))
        } else {
            Some(Polynomial::from_var(r))
        }
    }
}

// ========  ========
// Shared iterative term→polynomial translation
// ========  ========

/// The one thing the two translators do differently: mint (or look up) the
/// polynomial variable index for a term.
trait PolyVarSource {
    /// The polynomial variable index standing for `term_id`.
    fn var_for(&mut self, term_id: TermId) -> u32;

    /// Encode a `(div lhs rhs)` (`is_div`) or `(mod lhs rhs)` term as a
    /// polynomial leaf, typically via fresh auxiliary variables and side
    /// constraints. `None` means the source does not support the operator; the
    /// default keeps the real translator's "not a polynomial" behaviour.
    fn divmod_leaf(
        &mut self,
        _manager: &TermManager,
        _lhs: TermId,
        _rhs: TermId,
        _is_div: bool,
    ) -> Option<Polynomial> {
        None
    }
}

/// How a node's polynomial is assembled from its operands'.
#[derive(Debug, Clone, Copy)]
enum PolyCombine {
    /// Unary `-`, over the sum of the (single) operand.
    Neg,
    /// n-ary `+`, folded left to right from zero.
    Add,
    /// n-ary `*`, folded left to right from one.
    Mul,
    /// Binary `-`: the first operand minus the rest.
    Sub,
}

/// One pending arithmetic node of the iterative translation.
struct PolyFrame {
    /// How to combine the operands.
    combine: PolyCombine,
    /// Operand terms still to translate, reversed so `pop` yields them in the
    /// same left-to-right order the recursive version used (which matters:
    /// `var_for` mints variable indices as a side effect).
    pending: Vec<TermId>,
    /// Operands translated so far, in operand order.
    done: Vec<Polynomial>,
}

impl PolyFrame {
    /// Fold this node's operands into its polynomial.
    fn finish(self) -> Polynomial {
        match self.combine {
            PolyCombine::Neg => Polynomial::neg(&fold_add(self.done)),
            PolyCombine::Add => fold_add(self.done),
            PolyCombine::Mul => {
                let mut acc = Polynomial::one();
                for p in &self.done {
                    acc = Polynomial::mul(&acc, p);
                }
                acc
            }
            PolyCombine::Sub => {
                let mut operands = self.done.into_iter();
                let mut acc = operands.next().unwrap_or_else(Polynomial::zero);
                for p in operands {
                    acc = Polynomial::sub(&acc, &p);
                }
                acc
            }
        }
    }
}

/// Sum a list of polynomials left to right, starting from zero – which is also
/// exactly what a one-element list needs, so unary nodes can reuse it instead
/// of asserting their operand is present.
fn fold_add(parts: Vec<Polynomial>) -> Polynomial {
    let mut acc = Polynomial::zero();
    for p in &parts {
        acc = Polynomial::add(&acc, p);
    }
    acc
}

/// What translating one term needs: a polynomial already, or its operands.
enum PolyOpened {
    /// A constant or a variable.
    Leaf(Polynomial),
    /// An arithmetic operator whose operands must be translated first.
    Frame(PolyFrame),
}

/// Classify one term for [`translate_poly`]. `None` means "not expressible as
/// a polynomial", exactly as the recursive version's `_ => None` did.
fn open_poly<S: PolyVarSource>(
    manager: &TermManager,
    src: &mut S,
    term_id: TermId,
) -> Option<PolyOpened> {
    // The operand list is copied out before `src` is touched, so the borrow of
    // `manager` never overlaps the `&mut` borrow `var_for` needs.
    enum Shape {
        Const(Polynomial),
        Var,
        Op(PolyCombine, Vec<TermId>),
        /// `(div lhs rhs)` (`is_div`) or `(mod lhs rhs)`: encoded by the source
        /// via auxiliary variables rather than by the generic builder.
        DivMod {
            lhs: TermId,
            rhs: TermId,
            is_div: bool,
        },
    }
    let shape = {
        let term = manager.get(term_id)?;
        match &term.kind {
            TermKind::IntConst(n) => {
                Shape::Const(Polynomial::constant(BigRational::from_integer(n.clone())))
            }
            TermKind::RealConst(r) => Shape::Const(Polynomial::constant(BigRational::new(
                BigInt::from(r.numer().to_i64().unwrap_or(0)),
                BigInt::from(r.denom().to_i64().unwrap_or(1)),
            ))),
            TermKind::Var(_) => Shape::Var,
            TermKind::Neg(inner) => Shape::Op(PolyCombine::Neg, vec![*inner]),
            TermKind::Add(args) => {
                Shape::Op(PolyCombine::Add, args.iter().rev().copied().collect())
            }
            TermKind::Sub(lhs, rhs) => Shape::Op(PolyCombine::Sub, vec![*rhs, *lhs]),
            TermKind::Mul(args) => {
                Shape::Op(PolyCombine::Mul, args.iter().rev().copied().collect())
            }
            TermKind::Div(lhs, rhs) => Shape::DivMod {
                lhs: *lhs,
                rhs: *rhs,
                is_div: true,
            },
            TermKind::Mod(lhs, rhs) => Shape::DivMod {
                lhs: *lhs,
                rhs: *rhs,
                is_div: false,
            },
            _ => return None,
        }
    };
    Some(match shape {
        Shape::Const(p) => PolyOpened::Leaf(p),
        Shape::Var => PolyOpened::Leaf(Polynomial::from_var(src.var_for(term_id))),
        Shape::Op(combine, pending) => PolyOpened::Frame(PolyFrame {
            combine,
            pending,
            done: Vec::new(),
        }),
        Shape::DivMod { lhs, rhs, is_div } => {
            PolyOpened::Leaf(src.divmod_leaf(manager, lhs, rhs, is_div)?)
        }
    })
}

/// Translate an arithmetic term into a polynomial with an explicit stack.
///
/// The recursive version descended once per nesting level of an entirely
/// input-controlled term (and cloned the whole `TermKind`, `Vec<TermId>` and
/// `BigInt` included, into every frame). Shared subterms are translated once
/// and reused, so a `let`-shared doubling term cannot re-expand exponentially.
fn translate_poly<S: PolyVarSource>(
    manager: &TermManager,
    src: &mut S,
    root: TermId,
) -> Option<Polynomial> {
    let mut memo: HashMap<TermId, Polynomial> = HashMap::new();
    let mut frames: Vec<PolyFrame> = match open_poly(manager, src, root)? {
        PolyOpened::Leaf(p) => return Some(p),
        PolyOpened::Frame(f) => vec![f],
    };
    // A finished operand polynomial travelling back to the frame that asked
    // for it, paired with the term it came from so it can be memoised.
    let mut carry: Option<Polynomial> = None;
    // The term each frame is translating, parallel to `frames`.
    let mut frame_terms: Vec<TermId> = vec![root];

    while !frames.is_empty() {
        let next = match frames.last_mut() {
            Some(top) => {
                if let Some(p) = carry.take() {
                    top.done.push(p);
                }
                top.pending.pop()
            }
            // Unreachable: the loop condition just checked non-emptiness.
            None => break,
        };
        match next {
            Some(child) => {
                if let Some(hit) = memo.get(&child) {
                    carry = Some(hit.clone());
                    continue;
                }
                match open_poly(manager, src, child)? {
                    PolyOpened::Leaf(p) => {
                        memo.insert(child, p.clone());
                        carry = Some(p);
                    }
                    PolyOpened::Frame(f) => {
                        frames.push(f);
                        frame_terms.push(child);
                    }
                }
            }
            None => match (frames.pop(), frame_terms.pop()) {
                (Some(frame), Some(term)) => {
                    let built = frame.finish();
                    memo.insert(term, built.clone());
                    carry = Some(built);
                }
                // Unreachable: the two stacks are pushed and popped together.
                _ => break,
            },
        }
    }

    carry
}

// ========  ========
// Helper: nonlinearity detection
// ========  ========

/// Returns `true` if `term_id` (recursively) contains a `Mul` node where at
/// least two non-constant operands are multiplied together.
pub fn term_is_nonlinear(term_id: TermId, manager: &TermManager) -> bool {
    // Explicit stack plus a visited set. This is the first thing the NIA/NRA
    // dispatcher does for every assertion, so its depth is the assertion's
    // nesting depth (input-controlled) and its breadth is the assertion DAG
    // (which a `let`-shared term makes exponential to re-walk). It returns
    // `bool`, so a depth cap could only answer "linear" for a nonlinear
    // problem and hand the whole logic to the wrong solver.
    let mut stack: Vec<TermId> = vec![term_id];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        let Some(term) = manager.get(current) else {
            continue;
        };
        match &term.kind {
            TermKind::Mul(args) => {
                let non_const_count = args.iter().filter(|&&a| !is_const_term(a, manager)).count();
                if non_const_count >= 2 {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermKind::Add(args)
            | TermKind::And(args)
            | TermKind::Or(args)
            | TermKind::Distinct(args) => stack.extend(args.iter().copied()),
            TermKind::Sub(lhs, rhs)
            | TermKind::Eq(lhs, rhs)
            | TermKind::Gt(lhs, rhs)
            | TermKind::Ge(lhs, rhs)
            | TermKind::Lt(lhs, rhs)
            | TermKind::Le(lhs, rhs) => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            TermKind::Neg(inner) | TermKind::Not(inner) => stack.push(*inner),
            // Walk into ite/let so nonlinear products nested under them are
            // detected (industrial QF_NIA VCs are let/ite-heavy; without this
            // NL dispatch never engaged and CDCL returned spurious sat).
            TermKind::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            _ => {}
        }
    }
    false
}

fn is_const_term(term_id: TermId, manager: &TermManager) -> bool {
    manager
        .get(term_id)
        .map(|t| matches!(&t.kind, TermKind::IntConst(_) | TermKind::RealConst(_)))
        .unwrap_or(false)
}

fn term_contains_divmod(term_id: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(term_id) else {
        return false;
    };
    match &term.kind {
        TermKind::Div(_, _) | TermKind::Mod(_, _) => true,
        TermKind::Neg(inner) | TermKind::Not(inner) => term_contains_divmod(*inner, manager),
        TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Distinct(args) => args.iter().any(|&a| term_contains_divmod(a, manager)),
        TermKind::Ite(c, t, e) => {
            term_contains_divmod(*c, manager)
                || term_contains_divmod(*t, manager)
                || term_contains_divmod(*e, manager)
        }
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b) => {
            term_contains_divmod(*a, manager) || term_contains_divmod(*b, manager)
        }
        _ => false,
    }
}

/// Whether the term mentions an operator the polynomial translation cannot
/// express. Same shape (and same reasons for being iterative + memoised) as
/// [`term_is_nonlinear`]: `bool` return, `check_sat` path, input-controlled
/// depth and sharing.
pub(crate) fn contains_non_polynomial_ops(term_id: TermId, manager: &TermManager) -> bool {
    let mut stack: Vec<TermId> = vec![term_id];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        let Some(term) = manager.get(current) else {
            continue;
        };
        match &term.kind {
            // Div/Mod are encoded via Euclidean auxiliaries in the NIA
            // translator when the divisor is a nonzero constant; still walk
            // children so a div/mod of something genuinely non-polynomial is
            // still detected.
            TermKind::Div(lhs, rhs) | TermKind::Mod(lhs, rhs) => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            TermKind::Apply { args, .. } => {
                // A numeric-sorted application is an opaque poly var after
                // purification; only a non-numeric application is foreign.
                if !is_numeric_sort(manager, term.sort) {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermKind::Select(arr, idx) => {
                if !is_numeric_sort(manager, term.sort) {
                    return true;
                }
                stack.push(*arr);
                stack.push(*idx);
            }
            // `store` is an array op, not arithmetic; walk children so a store
            // of something genuinely non-polynomial is still detected.
            TermKind::Store(a, i, v) => {
                stack.push(*a);
                stack.push(*i);
                stack.push(*v);
            }
            TermKind::Forall { .. } | TermKind::Exists { .. } | TermKind::Match { .. } => {
                return true;
            }
            // `let` is a transparent local binding – walk into it so a
            // nonlinear product bound by a let is still detected.
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            TermKind::Neg(inner) | TermKind::Not(inner) => stack.push(*inner),
            TermKind::Add(args)
            | TermKind::Mul(args)
            | TermKind::And(args)
            | TermKind::Or(args)
            | TermKind::Distinct(args) => stack.extend(args.iter().copied()),
            TermKind::Ite(cond, then_term, else_term) => {
                stack.push(*cond);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermKind::Xor(lhs, rhs) | TermKind::Implies(lhs, rhs) => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            TermKind::Sub(lhs, rhs)
            | TermKind::Eq(lhs, rhs)
            | TermKind::Gt(lhs, rhs)
            | TermKind::Ge(lhs, rhs)
            | TermKind::Lt(lhs, rhs)
            | TermKind::Le(lhs, rhs) => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            _ => {}
        }
    }
    false
}

// ========  ========
// Polynomial atom (internal representation)
// ========  ========

#[derive(Debug, Clone)]
struct PolyAtom {
    poly: Polynomial,
    kind: AtomKind,
    /// `true` → atom appears positively; `false` → negated literal.
    positive: bool,
}

// ========  ========
// Assertion-level translation (integer mode)
// ========  ========

/// Whether `sort` is Int or Real.
fn is_numeric_sort(manager: &TermManager, sort: oxiz_core::sort::SortId) -> bool {
    sort == manager.sorts.int_sort || sort == manager.sorts.real_sort
}

fn is_array_sort_id(manager: &TermManager, sort: oxiz_core::sort::SortId) -> bool {
    manager
        .sorts
        .get(sort)
        .is_some_and(|s| matches!(s.kind, oxiz_core::sort::SortKind::Array { .. }))
}

/// A top-level equality whose operands are array-sorted (or one is) is an
/// array-theory structural fact, not an arithmetic constraint – skip it.
fn is_array_structural_eq(manager: &TermManager, lhs: TermId, rhs: TermId) -> bool {
    let ls = manager.get(lhs).map(|t| t.sort);
    let rs = manager.get(rhs).map(|t| t.sort);
    ls.is_some_and(|s| is_array_sort_id(manager, s))
        || rs.is_some_and(|s| is_array_sort_id(manager, s))
}

/// A purification interface naming: `c = select(...)` / `c = f(...)` where one
/// side is a fresh Var and the other a foreign numeric term. Encoding the
/// foreign side as a second poly var would leave it unbounded, so the pure
/// arith fragment must skip these (purification already bound `c`).
fn is_arith_interface_eq(manager: &TermManager, lhs: TermId, rhs: TermId) -> bool {
    fn is_var(manager: &TermManager, t: TermId) -> bool {
        manager
            .get(t)
            .is_some_and(|n| matches!(n.kind, TermKind::Var(_)))
    }
    fn is_foreign_numeric(manager: &TermManager, t: TermId) -> bool {
        let Some(n) = manager.get(t) else {
            return false;
        };
        if !is_numeric_sort(manager, n.sort) {
            return false;
        }
        matches!(
            n.kind,
            TermKind::Select(_, _)
                | TermKind::Apply { .. }
                | TermKind::Store(_, _, _)
                | TermKind::Ite(_, _, _)
        )
    }
    (is_var(manager, lhs) && is_foreign_numeric(manager, rhs))
        || (is_var(manager, rhs) && is_foreign_numeric(manager, lhs))
}

/// `incomplete` is set to `true` whenever some part of the assertion could
/// **not** be captured as a pure conjunction of polynomial atoms – an
/// unrecognized top-level connective (`Or`/`Not`/`Distinct`/`Ite`/…) or a
/// comparison whose operand does not translate to a polynomial (e.g. it
/// contains `Div`/`Mod`/an uninterpreted apply). The dispatcher must treat a
/// `Sat` verdict as untrustworthy once `incomplete` is set, because the solver
/// then only sees a strictly weaker (relaxed) subproblem. Reference: Z3's
/// nlsat/nlsat_solver.cpp only trusts a model for the full atom set.
fn extract_poly_atoms(
    term_id: TermId,
    manager: &TermManager,
    translator: &mut TermPolyTranslator<'_>,
    out: &mut Vec<PolyAtom>,
    incomplete: &mut bool,
) {
    // Iterative conjunction descent: an assertion is an implicit conjunction
    // and `(and A (and B …))` nests as deep as the input makes it. Conjuncts
    // are pushed in reverse so they pop left to right, the order the recursive
    // descent used (and the order atoms land in `out`).
    let mut worklist = vec![term_id];
    while let Some(current) = worklist.pop() {
        let Some(term) = manager.get(current) else {
            *incomplete = true;
            continue;
        };
        let kind = term.kind.clone();
        match &kind {
            TermKind::Eq(lhs, rhs) => {
                // Array structural equalities and purification interface namings
                // (`c = select(...)`) are not arithmetic constraints: skip them
                // so the pure-arith fragment does not encode an unbounded second
                // var for the foreign side.
                if is_array_structural_eq(manager, *lhs, *rhs)
                    || is_arith_interface_eq(manager, *lhs, *rhs)
                {
                    continue;
                }
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&lp, &rp),
                        kind: AtomKind::Eq,
                        positive: true,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Lt(lhs, rhs) => {
                // lhs < rhs → rhs - lhs > 0
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&rp, &lp),
                        kind: AtomKind::Gt,
                        positive: true,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Le(lhs, rhs) => {
                // lhs <= rhs → rhs - lhs >= 0 → NOT(rhs - lhs < 0)
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&rp, &lp),
                        kind: AtomKind::Lt,
                        positive: false,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Gt(lhs, rhs) => {
                // lhs > rhs → lhs - rhs > 0
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&lp, &rp),
                        kind: AtomKind::Gt,
                        positive: true,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Ge(lhs, rhs) => {
                // lhs >= rhs → NOT(lhs - rhs < 0)
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&lp, &rp),
                        kind: AtomKind::Lt,
                        positive: false,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::And(args) => worklist.extend(args.iter().rev().copied()),
            // Negated comparisons are still single algebraic atoms: the NLSAT
            // solver evaluates both polarities of Eq/Lt/Gt natively, so
            // `¬(a OP b)` maps to the same atom with `positive = false`
            // instead of poisoning the extraction. (DPLL case-splitting
            // produces exactly these leaves from `(not (and …))` guards.)
            TermKind::Not(x) => {
                let Some(node) = manager.get(*x) else {
                    *incomplete = true;
                    continue;
                };
                match &node.kind {
                    // ¬(a < b) ≡ a ≥ b ≡ ¬(a − b < 0)
                    TermKind::Lt(a, b) => push_cmp(
                        manager,
                        translator,
                        out,
                        incomplete,
                        *a,
                        *b,
                        AtomKind::Lt,
                        false,
                    ),
                    // ¬(a ≤ b) ≡ a > b ≡ (a − b) > 0
                    TermKind::Le(a, b) => push_cmp(
                        manager,
                        translator,
                        out,
                        incomplete,
                        *a,
                        *b,
                        AtomKind::Gt,
                        true,
                    ),
                    // ¬(a > b) ≡ a ≤ b ≡ ¬(a − b > 0)
                    TermKind::Gt(a, b) => push_cmp(
                        manager,
                        translator,
                        out,
                        incomplete,
                        *a,
                        *b,
                        AtomKind::Gt,
                        false,
                    ),
                    // ¬(a ≥ b) ≡ a < b ≡ (a − b) < 0
                    TermKind::Ge(a, b) => push_cmp(
                        manager,
                        translator,
                        out,
                        incomplete,
                        *a,
                        *b,
                        AtomKind::Lt,
                        true,
                    ),
                    TermKind::Eq(a, b)
                        if !is_array_structural_eq(manager, *a, *b)
                            && !is_arith_interface_eq(manager, *a, *b) =>
                    {
                        push_cmp(
                            manager,
                            translator,
                            out,
                            incomplete,
                            *a,
                            *b,
                            AtomKind::Eq,
                            false,
                        )
                    }
                    // ¬true / ¬false fold; anything else (nested Boolean
                    // structure) is out of scope for the conjunction path.
                    TermKind::True | TermKind::False => {}
                    _ => *incomplete = true,
                }
            }
            // `distinct a b` over arithmetic is exactly the negated Eq atom.
            TermKind::Distinct(args)
                if args.len() == 2 && {
                    let s = manager.sorts.bool_sort;
                    let b = |t: TermId| manager.get(t).is_some_and(|n| n.sort != s);
                    b(args[0]) && b(args[1])
                } =>
            {
                push_cmp(
                    manager,
                    translator,
                    out,
                    incomplete,
                    args[0],
                    args[1],
                    AtomKind::Eq,
                    false,
                );
            }
            _ => {
                // Any other top-level shape (Or/Not/Distinct/Ite/…) belongs to the
                // boolean abstraction layer, not to this pure-conjunction fast
                // path. Dropping it silently would let the solver "prove" Sat on a
                // relaxed problem, so flag the extraction as incomplete instead.
                *incomplete = true;
            }
        }
    }
}

/// Push the algebraic atom for `lhs OP rhs` over `poly = lhs − rhs` with the
/// given literal polarity. Shared by the negated-comparison and pairwise-
/// distinct leaves of `extract_poly_atoms`.
#[allow(clippy::too_many_arguments)]
fn push_cmp(
    _manager: &TermManager,
    translator: &mut TermPolyTranslator<'_>,
    out: &mut Vec<PolyAtom>,
    incomplete: &mut bool,
    lhs: TermId,
    rhs: TermId,
    kind: AtomKind,
    positive: bool,
) {
    if let (Some(lp), Some(rp)) = (translator.translate(lhs), translator.translate(rhs)) {
        out.push(PolyAtom {
            poly: Polynomial::sub(&lp, &rp),
            kind,
            positive,
        });
    } else {
        *incomplete = true;
    }
}

// ========  ========
// Tseitin-CNF encoding of Boolean-structured nonlinear goals
// ========  ========
//
// `extract_poly_atoms` above only descends conjunctions: any disjunctive or
// negated Boolean structure is dropped and flagged `incomplete`, so the CAD
// core solves a *weaker* goal whose model the concrete verifier then refutes
// (the dominant QF_NIA `unknown` shape on VeryMax/AProVE ITS benchmarks,
// whose transition relations are `(or template₁ template₂ …)`).
//
// This encoder is the Z3-faithful alternative (`qfnra_nlsat_tactic` runs
// `mk_tseitin_cnf_core_tactic` before `mk_nlsat_tactic`): the *entire*
// Boolean structure of every assertion is Tseitin-encoded into clauses over
// the NLSAT solver's own algebraic-atom literals, with fresh gate variables
// for compound connectives. The solver's CDCL loop then case-splits the
// disjunctions itself, using its incremental cell-based theory engine, and
// `NiaSolver`'s branch-and-bound supplies integrality on top.
//
// Soundness contract (mirrors the conjunction path):
// * every arithmetic comparison becomes exactly one algebraic atom literal;
//   its polynomial semantics is the theory's, not an abstraction;
// * gate variables are pure Booleans with definitional clauses, so the CNF
//   is *equisatisfiable* with the assertions;
// * anything the encoder cannot express faithfully sets `incomplete`, and
//   the dispatcher then refuses both `Unsat` and unverified `Sat`;
// * `Sat` is only ever reported after concrete verification against the raw
//   assertions (`verify_nl_model`), with free Booleans substituted from the
//   solver's own satisfying assignment.

/// Result of encoding one Boolean subterm.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CnfEncoded {
    /// The subterm is the constant `true` (no literal needed).
    True,
    /// The subterm is the constant `false`.
    False,
    /// A literal over an algebraic atom, gate, or free Boolean variable.
    Lit(Literal),
}

impl CnfEncoded {
    /// Boolean negation of the encoding (constants swap, literal flips).
    fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Lit(l) => Self::Lit(l.negate()),
        }
    }
}

/// Hard ceiling on emitted gate clauses. A pathological input (deep
/// alternation) must fall through to `unknown`, not exhaust memory.
const CNF_MAX_CLAUSES: usize = 500_000;

/// Pending unit of the encoding worklist.
enum CnfJob {
    /// Encode `term` in polarity `positive`; memoize the result.
    Enc(TermId, bool),
    /// All children of `term` are encoded (in the polarities this connective
    /// requested); read them from the memo and build the gate.
    Combine(TermId, bool),
}

/// Tseitin encoder from assertion terms to NLSAT clauses.
///
/// The walk is iterative (explicit worklist, per the project stack-safety
/// rule) and memoized per `TermId` polarity, so hash-consed shared
/// subformulas are encoded exactly once – the VeryMax goal shape repeats the
/// same ranking-function conjunctions across disjuncts.
struct NlCnfEncoder<'t, 'a> {
    translator: &'t mut TermPolyTranslator<'a>,
    /// Positive-polarity memo: term → encoding of `term`.
    pos: HashMap<TermId, CnfEncoded>,
    /// Negative-polarity memo: term → encoding of `¬term`.
    neg: HashMap<TermId, CnfEncoded>,
    /// Free user Boolean variables: term → solver BoolVar (model extraction).
    free_bools: Vec<(TermId, BoolVar)>,
    /// Buffered clauses: gate definitions and top-level units.
    clauses: Vec<Vec<Literal>>,
    /// Set when any subterm could not be faithfully encoded.
    incomplete: bool,
    /// Encoding budget guard (clause count).
    budget: usize,
}

impl<'t, 'a> NlCnfEncoder<'t, 'a> {
    fn new(translator: &'t mut TermPolyTranslator<'a>) -> Self {
        Self {
            translator,
            pos: HashMap::new(),
            neg: HashMap::new(),
            free_bools: Vec::new(),
            clauses: Vec::new(),
            incomplete: false,
            budget: CNF_MAX_CLAUSES,
        }
    }

    fn manager(&self) -> &TermManager {
        self.translator.manager
    }

    fn bool_sort(&self) -> SortId {
        self.manager().sorts.bool_sort
    }

    fn is_bool(&self, t: TermId) -> bool {
        self.manager()
            .get(t)
            .is_some_and(|n| n.sort == self.bool_sort())
    }

    fn memo_get(&self, term: TermId, positive: bool) -> Option<CnfEncoded> {
        if positive {
            self.pos.get(&term).copied()
        } else {
            self.neg.get(&term).copied()
        }
    }

    fn memo_put(&mut self, term: TermId, enc: CnfEncoded) {
        self.pos.insert(term, enc);
        self.neg.insert(term, enc.negate());
    }

    fn fresh_gate(&mut self) -> Literal {
        let v = self.translator.nlsat.nlsat_mut().new_bool_var();
        Literal::positive(v)
    }

    fn push_clause(&mut self, clause: Vec<Literal>) {
        if self.budget == 0 {
            self.incomplete = true;
            return;
        }
        self.budget -= 1;
        self.clauses.push(clause);
    }

    /// Encode a fresh free Boolean variable (a user-declared Bool leaf).
    fn encode_free_bool(&mut self, term: TermId) -> CnfEncoded {
        let v = self.translator.nlsat.nlsat_mut().new_bool_var();
        self.free_bools.push((term, v));
        let lit = Literal::positive(v);
        self.memo_put(term, CnfEncoded::Lit(lit));
        CnfEncoded::Lit(lit)
    }

    /// Create (or reuse) the algebraic atom for `lhs OP rhs` and return its
    /// positive literal. `poly`/`kind` follow the conventions of
    /// `extract_poly_atoms` (see the per-kind comments).
    ///
    /// Constant polynomials (the Gaussian preamble routinely rewrites
    /// comparisons over eliminated variables into `0 < 0`-shaped atoms) are
    /// folded to `True`/`False` on the spot: the algebraic engine has no
    /// variables to sample for them and its conflict explainer cannot
    /// certify a variable-free contradiction, so leaving them as atoms
    /// turns a level-0 refutation into an honest-but-useless `Unknown`.
    fn cmp_atom(&mut self, poly: Polynomial, kind: AtomKind, positive: bool) -> Option<CnfEncoded> {
        // Note `is_constant` alone misses the *zero* polynomial (it has an
        // empty term list, not a single constant term), so fold on both.
        if poly.is_constant() || poly.is_zero() {
            let c = poly.constant_value();
            let zero = BigRational::zero();
            let raw = match kind {
                AtomKind::Eq => c == zero,
                AtomKind::Lt => c < zero,
                AtomKind::Gt => c > zero,
                _ => false,
            };
            let v = if positive { raw } else { !raw };
            return Some(if v {
                CnfEncoded::True
            } else {
                CnfEncoded::False
            });
        }
        let id = self.translator.nlsat.nlsat_mut().new_ineq_atom(poly, kind);
        let lit = self.translator.nlsat.nlsat().atom_literal(id, positive);
        Some(CnfEncoded::Lit(lit))
    }

    /// Encode an arithmetic comparison leaf via the polynomial translator.
    fn encode_comparison(&mut self, lhs: TermId, rhs: TermId, kind: CmpKind) -> Option<CnfEncoded> {
        let lp = self.translator.translate(lhs)?;
        let rp = self.translator.translate(rhs)?;
        match kind {
            // lhs < rhs ⇔ lhs − rhs < 0
            CmpKind::Lt => self.cmp_atom(Polynomial::sub(&lp, &rp), AtomKind::Lt, true),
            // lhs ≤ rhs ⇔ ¬(lhs − rhs > 0)
            CmpKind::Le => self.cmp_atom(Polynomial::sub(&lp, &rp), AtomKind::Gt, false),
            // lhs > rhs ⇔ lhs − rhs > 0
            CmpKind::Gt => self.cmp_atom(Polynomial::sub(&lp, &rp), AtomKind::Gt, true),
            // lhs ≥ rhs ⇔ ¬(lhs − rhs < 0)
            CmpKind::Ge => self.cmp_atom(Polynomial::sub(&lp, &rp), AtomKind::Lt, false),
            // lhs = rhs ⇔ lhs − rhs = 0
            CmpKind::Eq => self.cmp_atom(Polynomial::sub(&lp, &rp), AtomKind::Eq, true),
        }
    }

    /// g ↔ ∧lits (n ≥ 2 assumed; shorter inputs collapse).
    fn and_gate(&mut self, lits: &[Literal]) -> CnfEncoded {
        if lits.len() == 1 {
            return CnfEncoded::Lit(lits[0]);
        }
        let g = self.fresh_gate();
        for &l in lits {
            self.push_clause(vec![g.negate(), l]);
        }
        let mut cls = vec![g];
        cls.extend(lits.iter().map(|l| l.negate()));
        self.push_clause(cls);
        CnfEncoded::Lit(g)
    }

    /// g ↔ ∨lits (n ≥ 2 assumed; shorter inputs collapse).
    fn or_gate(&mut self, lits: &[Literal]) -> CnfEncoded {
        if lits.len() == 1 {
            return CnfEncoded::Lit(lits[0]);
        }
        let g = self.fresh_gate();
        for &l in lits {
            self.push_clause(vec![g, l.negate()]);
        }
        let mut cls = vec![g.negate()];
        cls.extend(lits.iter().copied());
        self.push_clause(cls);
        CnfEncoded::Lit(g)
    }

    /// g ↔ (a ↔ b).
    fn iff_gate(&mut self, a: Literal, b: Literal) -> CnfEncoded {
        let g = self.fresh_gate();
        // g → (a→b) and g → (b→a)
        self.push_clause(vec![g.negate(), a.negate(), b]);
        self.push_clause(vec![g.negate(), a, b.negate()]);
        // (a↔b) → g:  (a∨b∨g) ∧ (¬a∨¬b∨g)
        self.push_clause(vec![a, b, g]);
        self.push_clause(vec![a.negate(), b.negate(), g]);
        CnfEncoded::Lit(g)
    }

    /// g ↔ a ⊕ b.
    fn xor_gate(&mut self, a: Literal, b: Literal) -> CnfEncoded {
        let g = self.fresh_gate();
        self.push_clause(vec![g.negate(), a.negate(), b.negate()]);
        self.push_clause(vec![g.negate(), a, b]);
        self.push_clause(vec![a, b, g]);
        self.push_clause(vec![a.negate(), b.negate(), g]);
        CnfEncoded::Lit(g)
    }

    /// Encode every assertion into clauses. Returns `false` when the goal is
    /// trivially `false` at the top level (some assertion encodes to the
    /// constant `false`), in which case the caller answers `Unsat` directly.
    fn encode_assertions(&mut self, assertions: &[TermId]) -> bool {
        // Top-level `And` nodes are asserted conjunct-by-conjunct (no gate):
        // this keeps pure-conjunction goals gate-free, exactly like the
        // `extract_poly_atoms` path, and peels the common
        // `(and bound… constraint…)` VeryMax wrapper.
        let mut tops: Vec<TermId> = Vec::new();
        for &a in assertions {
            let mut stack = vec![a];
            while let Some(t) = stack.pop() {
                if let Some(n) = self.manager().get(t)
                    && let TermKind::And(args) = &n.kind
                {
                    stack.extend(args.iter().rev().copied());
                } else {
                    tops.push(t);
                }
            }
        }
        for t in tops {
            match self.encode(t, true) {
                CnfEncoded::True => {}
                CnfEncoded::False => return false,
                CnfEncoded::Lit(l) => self.push_clause(vec![l]),
            }
        }
        !self.incomplete
    }

    /// Drive the worklist until `term` is encoded in the given polarity.
    fn encode(&mut self, root: TermId, positive: bool) -> CnfEncoded {
        let mut work: Vec<CnfJob> = vec![CnfJob::Enc(root, positive)];
        while let Some(job) = work.pop() {
            match job {
                CnfJob::Enc(term, pol) => {
                    if self.incomplete {
                        return CnfEncoded::False; // abandoned; result unused
                    }
                    if let Some(found) = self.memo_get(term, pol) {
                        let _ = found;
                        continue;
                    }
                    self.enc_one(term, pol, &mut work);
                }
                CnfJob::Combine(term, pol) => {
                    if self.incomplete {
                        return CnfEncoded::False;
                    }
                    self.combine(term, pol);
                }
            }
        }
        self.memo_get(root, positive).unwrap_or(CnfEncoded::False)
    }

    /// Encode one node: leaves are encoded in place; connectives push their
    /// children (in the polarities they need) and a `Combine` continuation.
    fn enc_one(&mut self, term: TermId, pol: bool, work: &mut Vec<CnfJob>) {
        let Some(node) = self.manager().get(term) else {
            // Unknown node: cannot encode faithfully.
            self.incomplete = true;
            return;
        };
        let kind = node.kind.clone();
        match &kind {
            TermKind::True => {
                self.memo_put(term, CnfEncoded::True);
            }
            TermKind::False => {
                self.memo_put(term, CnfEncoded::False);
            }
            TermKind::Var(_) if node.sort == self.bool_sort() => {
                self.encode_free_bool(term);
            }
            TermKind::Not(x) => {
                work.push(CnfJob::Combine(term, pol));
                work.push(CnfJob::Enc(*x, !pol));
            }
            TermKind::And(args) | TermKind::Or(args) => {
                work.push(CnfJob::Combine(term, true));
                for &a in args.iter().rev() {
                    work.push(CnfJob::Enc(a, true));
                }
            }
            TermKind::Implies(a, b) => {
                // a → b  ≡  ¬a ∨ b: encode antecedent negatively so the
                // or-combine reads the already-negated literal.
                work.push(CnfJob::Combine(term, true));
                work.push(CnfJob::Enc(*b, true));
                work.push(CnfJob::Enc(*a, false));
            }
            TermKind::Xor(a, b) => {
                work.push(CnfJob::Combine(term, true));
                work.push(CnfJob::Enc(*b, true));
                work.push(CnfJob::Enc(*a, true));
            }
            TermKind::Ite(c, t, e) if node.sort == self.bool_sort() => {
                // ite(c,t,e) ≡ (c ∧ t) ∨ (¬c ∧ e), all Boolean.
                work.push(CnfJob::Combine(term, true));
                work.push(CnfJob::Enc(*e, true));
                work.push(CnfJob::Enc(*t, true));
                work.push(CnfJob::Enc(*c, true));
            }
            TermKind::Distinct(args) => {
                // distinct(xs) ≡ ∧_{i<j} xi ≠ xj. Boolean children are
                // formulas (encode normally); arithmetic children are *terms*
                // that the pair construction in `combine` translates directly
                // (an `Enc` job on an arithmetic leaf would hit the
                // not-a-formula catch-all below and spuriously flag the
                // encoding incomplete).
                work.push(CnfJob::Combine(term, true));
                for &a in args.iter().rev() {
                    if self.is_bool(a) {
                        work.push(CnfJob::Enc(a, true));
                    }
                }
            }
            TermKind::Eq(a, b) => {
                if *a == *b {
                    self.memo_put(term, CnfEncoded::True);
                } else if self.is_bool(*a) || self.is_bool(*b) {
                    work.push(CnfJob::Combine(term, true));
                    work.push(CnfJob::Enc(*b, true));
                    work.push(CnfJob::Enc(*a, true));
                } else {
                    // Arithmetic equality. Array structural equalities and
                    // purification interface namings are not arithmetic
                    // constraints (see `extract_poly_atoms`); skipping them
                    // weakens the CNF, which is sound for `Unsat` and covered
                    // by concrete verification for `Sat`.
                    if is_array_structural_eq(self.manager(), *a, *b)
                        || is_arith_interface_eq(self.manager(), *a, *b)
                    {
                        self.memo_put(term, CnfEncoded::True);
                    } else if let Some(e) = self.encode_comparison(*a, *b, CmpKind::Eq) {
                        self.memo_put(term, e);
                    } else {
                        self.incomplete = true;
                    }
                }
            }
            TermKind::Lt(a, b) | TermKind::Le(a, b) | TermKind::Gt(a, b) | TermKind::Ge(a, b) => {
                let k = match &kind {
                    TermKind::Lt(_, _) => CmpKind::Lt,
                    TermKind::Le(_, _) => CmpKind::Le,
                    TermKind::Gt(_, _) => CmpKind::Gt,
                    _ => CmpKind::Ge,
                };
                if let Some(e) = self.encode_comparison(*a, *b, k) {
                    self.memo_put(term, e);
                } else {
                    self.incomplete = true;
                }
            }
            // Everything else – arithmetic leaves in Boolean position, other
            // theories' operators, quantifiers, applications – is outside the
            // polynomial-fragment contract. Flag incomplete: the dispatcher
            // must not trust a verdict over a dropped subformula.
            _ => {
                self.incomplete = true;
            }
        }
    }

    /// Build the gate for a connective whose children are all memoized.
    fn combine(&mut self, term: TermId, pol: bool) {
        let take = |enc: &Self, child: TermId, positive: bool| -> Option<CnfEncoded> {
            enc.memo_get(child, positive)
        };
        let Some(node) = self.manager().get(term) else {
            self.incomplete = true;
            return;
        };
        let kind = node.kind.clone();
        let lit_of = |enc: &Self, child: TermId, positive: bool| -> Option<Literal> {
            match enc.memo_get(child, positive) {
                Some(CnfEncoded::Lit(l)) => Some(l),
                Some(CnfEncoded::True) | Some(CnfEncoded::False) | None => None,
            }
        };
        let result: Option<CnfEncoded> = match &kind {
            // The child was encoded at polarity `!pol`, i.e. with meaning
            // (!pol ? x : ¬x) = (pol ? term : ¬term) – *already* the wanted
            // polarity. Negating it here would invert every `not` under the
            // goal (the exact wrong-`unsat` bug caught by VeryMax
            // `ex36.t2_fixed p23678`, where `(not (<= …))` guards flipped).
            TermKind::Not(x) => take(self, *x, !pol).map(|e| if pol { e } else { e.negate() }),
            TermKind::And(args) => {
                let mut lits = Vec::with_capacity(args.len());
                let mut consts: Vec<bool> = Vec::with_capacity(args.len());
                for &a in args {
                    match self.memo_get(a, true) {
                        Some(CnfEncoded::True) => consts.push(true),
                        Some(CnfEncoded::False) => consts.push(false),
                        Some(CnfEncoded::Lit(l)) => lits.push(l),
                        None => return self.combine_missing(term),
                    }
                }
                Some(if consts.contains(&false) {
                    CnfEncoded::False
                } else if lits.is_empty() {
                    CnfEncoded::True
                } else {
                    self.and_gate(&lits)
                })
            }
            TermKind::Or(args) => {
                let mut lits = Vec::with_capacity(args.len());
                let mut has_true = false;
                for &a in args {
                    match self.memo_get(a, true) {
                        Some(CnfEncoded::True) => has_true = true,
                        Some(CnfEncoded::False) => {}
                        Some(CnfEncoded::Lit(l)) => lits.push(l),
                        None => return self.combine_missing(term),
                    }
                }
                Some(if has_true {
                    CnfEncoded::True
                } else if lits.is_empty() {
                    CnfEncoded::False
                } else {
                    self.or_gate(&lits)
                })
            }
            TermKind::Implies(a, b) => {
                // antecedent was encoded negatively.
                let (Some(la), Some(lb)) = (lit_of(self, *a, false), lit_of(self, *b, true)) else {
                    return self.combine_missing(term);
                };
                Some(self.or_gate(&[la, lb]))
            }
            TermKind::Xor(a, b) => {
                let (Some(la), Some(lb)) = (lit_of(self, *a, true), lit_of(self, *b, true)) else {
                    return self.combine_missing(term);
                };
                Some(self.xor_gate(la, lb))
            }
            TermKind::Ite(c, t, e) if node.sort == self.bool_sort() => {
                let (Some(lc), Some(lt), Some(le)) = (
                    lit_of(self, *c, true),
                    lit_of(self, *t, true),
                    lit_of(self, *e, true),
                ) else {
                    return self.combine_missing(term);
                };
                let ga = self.and_gate(&[lc, lt]);
                let CnfEncoded::Lit(la) = ga else {
                    // and_gate with ≥2 inputs always yields a gate literal;
                    // a constant here means a degenerate child slipped
                    // through – flag rather than guess.
                    self.incomplete = true;
                    return;
                };
                let gb = self.and_gate(&[lc.negate(), le]);
                let CnfEncoded::Lit(lb) = gb else {
                    self.incomplete = true;
                    return;
                };
                Some(self.or_gate(&[la, lb]))
            }
            TermKind::Distinct(args) => {
                // Pairwise distinctness. Arith pairs become ¬Eq atoms
                // (translated here, with constant polynomials folded to
                // their truth value); Boolean pairs become xor gates over
                // their encoded literals.
                let mut pair_lits: Vec<Literal> = Vec::new();
                for i in 0..args.len() {
                    for j in 0..i {
                        let is_bool_i = self.is_bool(args[i]);
                        let is_bool_j = self.is_bool(args[j]);
                        let pair = if !is_bool_i && !is_bool_j {
                            let Some(lp) = self.translator.translate(args[i]) else {
                                self.incomplete = true;
                                return;
                            };
                            let Some(rp) = self.translator.translate(args[j]) else {
                                self.incomplete = true;
                                return;
                            };
                            self.cmp_atom(Polynomial::sub(&lp, &rp), AtomKind::Eq, false)
                        } else if is_bool_i && is_bool_j {
                            let (Some(CnfEncoded::Lit(la)), Some(CnfEncoded::Lit(lb))) =
                                (self.memo_get(args[i], true), self.memo_get(args[j], true))
                            else {
                                return self.combine_missing(term);
                            };
                            Some(self.xor_gate(la, lb))
                        } else {
                            // Mixed bool/arith pair: ill-sorted input; refuse.
                            self.incomplete = true;
                            return;
                        };
                        match pair {
                            // A false pair falsifies the whole conjunction.
                            Some(CnfEncoded::False) => {
                                self.memo_put(term, CnfEncoded::False);
                                return;
                            }
                            Some(CnfEncoded::True) => {}
                            Some(CnfEncoded::Lit(l)) => pair_lits.push(l),
                            None => {
                                self.incomplete = true;
                                return;
                            }
                        }
                    }
                }
                Some(if pair_lits.is_empty() {
                    CnfEncoded::True
                } else {
                    self.and_gate(&pair_lits)
                })
            }
            TermKind::Eq(a, b) => {
                // Boolean equality: iff gate over the two child literals.
                let (Some(la), Some(lb)) = (lit_of(self, *a, true), lit_of(self, *b, true)) else {
                    return self.combine_missing(term);
                };
                Some(self.iff_gate(la, lb))
            }
            _ => {
                self.incomplete = true;
                return;
            }
        };
        match result {
            Some(e) => self.memo_put(term, e),
            None => self.incomplete = true,
        }
    }

    /// A child was never encoded (worklist inconsistency): flag rather than
    /// guess.
    fn combine_missing(&mut self, term: TermId) {
        let _ = term;
        self.incomplete = true;
    }
}

/// Comparison kinds for the CNF encoder (mirrors the `TermKind` relations).
#[derive(Clone, Copy)]
enum CmpKind {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

/// Does the goal contain Boolean structure the conjunction core cannot
/// handle natively?  That is: `or` / `=>` / `xor` / Boolean `ite` /
/// Boolean `=` / Boolean variables / Boolean-ish `distinct` anywhere under
/// the assertions, *or* a `not` whose operand is not one of the negated
/// comparison leaves `extract_poly_atoms` translates directly (a bare
/// `¬(a OP b)` is a single algebraic atom in negative polarity and must
/// not be reported as structure, or the DPLL splitter would re-discover it
/// forever – each split round would hand back the identical term).
pub(crate) fn has_boolean_structure(assertions: &[TermId], manager: &TermManager) -> bool {
    let bool_sort = manager.sorts.bool_sort;
    let is_bool = |t: TermId| manager.get(t).is_some_and(|n| n.sort == bool_sort);
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Or(_) | TermKind::Implies(_, _) | TermKind::Xor(_, _) => return true,
            TermKind::Not(x) => {
                // Descend: only a `not` over another Boolean connective or
                // over a Boolean variable counts as structure here; `not`
                // over an arithmetic comparison (or over `distinct` of two
                // arithmetic terms, which is the negated Eq atom) is a
                // native leaf.
                match manager.get(*x).map(|c| c.kind.clone()) {
                    Some(TermKind::And(_))
                    | Some(TermKind::Or(_))
                    | Some(TermKind::Implies(_, _))
                    | Some(TermKind::Xor(_, _))
                    | Some(TermKind::Ite(_, _, _))
                    | Some(TermKind::Eq(_, _))
                    | Some(TermKind::Distinct(_))
                    | Some(TermKind::Not(_)) => return true,
                    Some(TermKind::Var(_)) if is_bool(*x) => return true,
                    _ => {}
                }
            }
            TermKind::Ite(_, _, _) => return true,
            TermKind::Var(_) if n.sort == bool_sort => return true,
            TermKind::Distinct(args) => {
                // Pairwise arithmetic distinctness is the negated-Eq leaf;
                // anything with Boolean arguments (or a Boolean-sized set)
                // needs splitting.
                if args.iter().any(|&a| is_bool(a)) || args.len() != 2 {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermKind::Eq(a, b) => {
                if is_bool(*a) || is_bool(*b) {
                    return true;
                }
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::And(args) => stack.extend(args.iter().copied()),
            _ => {
                // Atoms and other leaves: no Boolean structure to descend.
            }
        }
    }
    false
}

// ========  ========
// NIA dispatch: public entry point
// ========  ========

/// Env-gated dispatch tracing (`OXIZ_NIA_TRACE=1`): prints the stage that
/// decided (or gave up on) each nonlinear goal to stderr. Zero cost when the
/// variable is unset; invaluable for exactly the kind of stage-attribution
/// triage that found the disjunction-dropping gap.
macro_rules! nl_trace {
    ($($arg:tt)*) => {
        if cfg!(feature = "std") && std::env::var("OXIZ_NIA_TRACE").is_ok() {
            eprintln!("[nia] {}", format!($($arg)*));
        }
    };
}

/// Dispatch nonlinear integer arithmetic assertions to the `NiaSolver`.
///
/// Returns:
/// - `Some(NlDispatchResult::Unsat)` if the system is provably UNSAT,
/// - `Some(NlDispatchResult::Sat(_))` if NiaSolver finds an integer model,
/// - `None` if translation yields no atoms or the solver returns Unknown.
///
/// Both linear and nonlinear assertions are passed so the solver has full context.
pub fn dispatch_nia_constraints(
    assertions: &[TermId],
    manager: &mut TermManager,
    integer_mode: bool,
    model_search: bool,
) -> Option<NlDispatchResult> {
    let has_nl = assertions.iter().any(|&a| term_is_nonlinear(a, manager));
    let has_divmod = assertions.iter().any(|&a| term_contains_divmod(a, manager));
    // Engage for nonlinear products *or* integer div/mod (encoded via
    // Euclidean auxiliaries below). Pure linear problems stay with LIA.
    if !has_nl && !has_divmod {
        nl_trace!("bail: no nonlinear, no divmod");
        return None;
    }

    // ---- Z3 qfnia-preamble analogue: Gaussian elimination of defining
    // linear equalities (see `nl_preprocess`).  Industrial QF_NIA asserts
    // hundreds of defining equalities that pin most variables to a small
    // core; eliminating them is what keeps every later stage tractable.
    let gauss = crate::nl_preprocess::gaussian_eliminate(assertions, manager);
    let false_id = manager.mk_false();
    if gauss.conjuncts.contains(&false_id) {
        nl_trace!("gauss: level-0 false -> Unsat");
        return Some(NlDispatchResult::Unsat);
    }
    let working: Vec<TermId> = if gauss.changed {
        gauss.conjuncts.clone()
    } else {
        assertions.to_vec()
    };
    if working.is_empty() {
        // Everything simplified away: the goal is trivially satisfiable.
        return Some(NlDispatchResult::sat_empty());
    }

    // CDCL(T) search (z3-style theory_arith_nl port): Tseitin CNF over
    // arithmetic atoms + 1-UIP lemma learning + Simplex theory with monomial
    // abstraction.  Opt-in via `OXIZ_NIA_CDCL`: with learning enabled the
    // integer-split branching can spiral (hundreds of split atoms on
    // three-variable goals) and its coarse all-atoms theory nogood is not
    // yet strong enough to keep the learnt-clause stream sound on every
    // goal shape, so the default path stays on the verified-safe stages.
    // Sat answers are concretely verified; Unsat comes only from level-0
    // conflicts, but a spiralling search can still mis-assign level-0 units
    // through learnt clauses (observed on VeryMax SAT goals), hence opt-in.
    #[cfg(feature = "std")]
    if std::env::var("OXIZ_NIA_CDCL").is_ok()
        && std::env::var("OXIZ_NIA_CDCL")
            .map(|v| v != "0")
            .unwrap_or(false)
        && let Some(r) = crate::nia_cdcl::cdcl_nia_search(&working, assertions, manager)
    {
        match r {
            NlDispatchResult::Sat(model) => {
                // `cdcl_nia_search` already concretely verified against
                // `assertions`; re-verify the extended model anyway so the
                // dispatch's single exit guarantees it.
                if let ModelCheck::Verified(verified) =
                    verify_nl_model(&model.assignments, &gauss.eliminations, assertions, manager)
                {
                    return Some(verified);
                }
            }
            NlDispatchResult::Unsat => return Some(NlDispatchResult::Unsat),
        }
    }

    // A `div`/`mod` with a symbolic (non-constant) divisor has no polynomial
    // encoding in the ground enumerators below (the defining identity is
    // itself nonlinear in the divisor).  Those stages must not treat the
    // application as an opaque free variable, so skip them; the CDCL stage
    // above is the one that handles such divisors soundly.
    let symbolic_divmod =
        crate::nl_model_search::assertions_have_symbolic_divmod(&working, manager);

    // Ground store-chains + finite index boxes: decide by evaluating selects
    // (sound for QF_ANIA).  Runs before the pure-arith relaxation so we never
    // report Sat from free select-vars when stores constrain them.
    //
    // These box/model stages run on the *original* assertions, not the
    // Gaussian-rewritten goal: their concrete enumeration keys off unit
    // bounds (`v ≥ c` conjuncts), which the rewrite substitutes into
    // compound comparisons (`e ≥ 0`) – feeding them `working` silently
    // starved their domains (regression: VeryMax 489/510 sat→unknown).
    if !symbolic_divmod
        && crate::ania_ground::assertions_contain_store(assertions, manager)
        && let Some(r) = crate::ania_ground::try_decide_ground_ania(assertions, manager)
    {
        nl_trace!("ania_ground stores: decided {:?}", r);
        return Some(r);
    }
    // Finite-domain enumeration for pure nonlinear-integer formulas whose
    // free integer vars lie in small boxes (e.g. lookup-table products over
    // bounded indices). The relaxation-based NIA core routinely returns
    // Unknown on these; exhaustive substitution decides them.
    if !symbolic_divmod
        && let Some(r) = crate::ania_ground::try_decide_finite_domain_nia(assertions, manager)
    {
        nl_trace!("finite-domain: decided {:?}", r);
        return Some(r);
    }
    // Model-based nonlinear search (z3-style): linearise monomials into fresh
    // Simplex vars, solve the relaxation (sound Unsat on infeasibility), then
    // bounded concrete enumeration that verifies the full formula before Sat.
    // Gated by the caller's `model_search` config (a budget decision, never a
    // soundness one – the search can only turn `unknown` into `sat`).
    if model_search && !symbolic_divmod {
        // The stage is its own certificate producer: internally it grounds
        // Boolean interface equalities, case-splits the remaining free Bool
        // variables (≤ 2^MAX_FREE_BOOL_CASESPLIT), and accepts a witness
        // only when every assertion concretely evaluates to `true` under it
        // (`None` counts as `false` – conservative).  Re-verifying its
        // result here against the *raw* assertions cannot work: the free
        // Booleans are existentials the split already chose, so raw
        // evaluation is undecidable by construction (this exact gate
        // regressed VeryMax 489/510 sat→unknown).  The dispatch-level
        // `verify_nl_model` backstop stays on the CAD path, whose models
        // carry no such split.
        if let Some(r) = crate::nl_model_search::try_model_based_nia_search(assertions, manager) {
            nl_trace!("model-based search: decided {:?}", r);
            return Some(r);
        }
        nl_trace!("model-based search: no decision");
    }

    // ---- DPLL case-split over the Boolean structure.  Disjunctive goals
    // (`(or template₁ template₂ …)` ITS relations) are split into
    // conjunction cases decided by the CAD/B&B core below, mirroring Z3's
    // per-case nlsat runs.  Runs *before* the global symbol gate: each case
    // is re-simplified and typically far smaller than the whole goal.
    // Size gate first: on very large goals the per-frame re-simplification
    // dominates the budget even when every leaf is skipped by its own gate
    // (observed: 1 200-conjunct goals burning seconds per frame).  Real
    // disjunctive ITS goals collapse far below this ceiling after the
    // Gaussian preamble.
    if has_boolean_structure(&working, manager)
        && count_arith_symbols(&working, manager) <= DPLL_MAX_GOAL_SYMBOLS
        && let Some(r) = crate::nl_dpll::try_dpll_nia_case_split(
            &working,
            assertions,
            &gauss.eliminations,
            manager,
            integer_mode,
        )
    {
        nl_trace!("dpll case-split: decided {r:?}");
        return Some(r);
    }

    // ---- Exact CAD/B&B core.  Prohibitively expensive above a small core:
    // gate on the number of distinct arithmetic symbols remaining after the
    // Gaussian preamble (Z3 never enters nlsat with hundreds of variables –
    // its `qfnia-nlsat` arm runs only after solve-eqs has collapsed the
    // goal, under `try_for` budgets).
    let n_symbols = count_arith_symbols(&working, manager);
    if n_symbols > CAD_MAX_SYMBOLS {
        nl_trace!("bail: {n_symbols} arith symbols > CAD_MAX_SYMBOLS");
        return None;
    }

    let has_unsupported_ops = working
        .iter()
        .any(|&a| contains_non_polynomial_ops(a, manager));
    // Store-definitions further constrain purified select constants, so a Sat
    // from the pure-arith relaxation can over-approximate when stores are
    // present (free select-vars).  Tracked separately: with the concrete
    // verification below, only the *Unsat* direction needs this gate.
    let has_array_stores = crate::ania_ground::assertions_contain_store(&working, manager);

    let has_real_symbols = working
        .iter()
        .any(|&a| assertions_have_real_symbols(a, manager));

    // Goals whose Boolean structure goes beyond conjunctions
    // (`(or template₁ template₂ …)` transition relations, negated guards,
    // Boolean `ite`/`=`/`distinct`) cannot be served by the conjunction-only
    // extraction below without dropping disjuncts: the CAD core would then
    // decide a strictly weaker relaxation. Route them through the full
    // Tseitin-CNF encoding over the NLSAT solver's own algebraic-atom
    // literals (Z3's `qfnra_nlsat_tactic`: tseitin-cnf → nlsat), so the
    // solver's CDCL loop case-splits the disjunctions itself.
    // The Tseitin-CNF route hands the whole Boolean structure to the NLSAT
    // CDCL engine.  Today that engine concludes on small coupled cores (a
    // few dozen atoms) but burns its resample budget on large industrial
    // goals, so it runs by default only under a size ceiling; `OXIZ_NIA_CNF`
    // forces it on for any size.
    let cnf_enabled = n_symbols <= CNF_MAX_DEFAULT_SYMBOLS
        || (cfg!(feature = "std") && std::env::var("OXIZ_NIA_CNF").is_ok());
    if has_boolean_structure(&working, manager) && cnf_enabled {
        nl_trace!("cnf dispatch: boolean-structured goal ({n_symbols} symbols)");
        return cnf_nia_dispatch(
            &working,
            assertions,
            &gauss.eliminations,
            manager,
            integer_mode,
            has_unsupported_ops,
            has_array_stores,
            has_real_symbols,
        );
    }

    solve_conjunction_nia(
        &working,
        assertions,
        &gauss.eliminations,
        manager,
        integer_mode,
        has_unsupported_ops,
        has_array_stores,
        has_real_symbols,
        10_000,
    )
}

/// The conjunction-only CAD/B&B core, shared by the flat dispatch tail and
/// the DPLL case-split driver's leaves.
///
/// `case` is the (already case-split) assertion list; `raw_assertions` the
/// *original* assertions for concrete model verification; `eliminations`
/// the accumulated Gaussian eliminations for the raw set.
#[allow(clippy::too_many_arguments)]
pub(crate) fn solve_conjunction_nia(
    case: &[TermId],
    raw_assertions: &[TermId],
    eliminations: &[(TermId, TermId)],
    manager: &mut TermManager,
    integer_mode: bool,
    has_unsupported_ops: bool,
    has_array_stores: bool,
    has_real_symbols: bool,
    arith_resample_budget: u32,
) -> Option<NlDispatchResult> {
    let config = NiaConfig {
        enable_cutting_planes: true,
        arith_resample_budget,
        ..NiaConfig::default()
    };
    let mut nia = NiaSolver::with_config(config);
    let mut translator = TermPolyTranslator::new(manager, &mut nia, integer_mode);

    let mut poly_atoms: Vec<PolyAtom> = Vec::new();
    let mut incomplete = false;
    for &assertion in case {
        extract_poly_atoms(
            assertion,
            manager,
            &mut translator,
            &mut poly_atoms,
            &mut incomplete,
        );
    }
    // Euclidean div/mod side constraints collected during translation.
    poly_atoms.extend(translator.pending_atoms.iter().cloned());
    if translator.divmod_incomplete {
        incomplete = true;
    }

    // Constant-polynomial atoms (the Gaussian preamble rewrites comparisons
    // over eliminated variables into `0 < 0`-shaped atoms) are folded to
    // their truth value here: a provably-false comparison refutes the whole
    // conjunction outright, and a provably-true one constrains nothing.
    // Leaving them as atoms turns a level-0 refutation into an honest but
    // useless `Unknown` (the conflict explainer has no variables to blame
    // for a constant polynomial).
    let mut conjunction_refuted = false;
    poly_atoms.retain(|atom| {
        if atom.poly.is_constant() || atom.poly.is_zero() {
            // Only the three inequality kinds ever appear here (extraction
            // and the div/mod encoder produce Eq/Lt/Gt exclusively); any
            // other kind is left untouched rather than guessed at.
            let c = atom.poly.constant_value();
            let zero = BigRational::zero();
            let raw = match atom.kind {
                AtomKind::Eq => Some(c == zero),
                AtomKind::Lt => Some(c < zero),
                AtomKind::Gt => Some(c > zero),
                _ => None,
            };
            match raw {
                Some(raw) => {
                    let holds = if atom.positive { raw } else { !raw };
                    if !holds {
                        conjunction_refuted = true;
                    }
                    // Drop constants either way: a true one constrains
                    // nothing, a false one is recorded in the flag.
                    false
                }
                None => true,
            }
        } else {
            true
        }
    });
    if conjunction_refuted {
        return Some(NlDispatchResult::Unsat);
    }

    if poly_atoms.is_empty() {
        return None;
    }

    // Unsat from NiaSolver is sound whenever extraction saw the full case
    // as polynomial atoms (no dropped disjunctions / incomplete div-mod)
    // and the Gaussian preamble made `working` equivalent to `assertions`.
    // Multivariate CAD/B&B unsat is trustworthy under that completeness
    // condition: a false unsat from greedy cell failure was fixed by arithmetic
    // re-sampling in `oxiz-nlsat` (bare `x*y=c` no longer collapses to Unsat).
    // An `Unsat` from the integer B&B is only meaningful for a goal whose
    // arithmetic symbols are all Int-sorted: with `integer_mode` the
    // translator types *every* variable Integer, so a Real-sorted symbol
    // (NIRA goals dispatched here) makes branch-and-bound "prove" integer
    // facts about a real variable – a wrong `Unsat` on a satisfiable goal.
    let unsat_is_trustworthy = !has_unsupported_ops && !incomplete && !has_real_symbols;
    // A `Sat` verdict no longer relies on trust flags at all: every Sat is
    // re-verified against the original assertions by `verify_model` below.
    // (Array stores still require the ground-ANIA pre-check for Unsat; Sat
    // is verified concretely either way.)
    let _ = has_array_stores;

    for atom in &poly_atoms {
        let atom_id = translator
            .nlsat
            .nlsat_mut()
            .new_ineq_atom(atom.poly.clone(), atom.kind);
        let lit = translator
            .nlsat
            .nlsat()
            .atom_literal(atom_id, atom.positive);
        translator.nlsat.nlsat_mut().add_clause(vec![lit]);
    }

    match translator.nlsat.solve() {
        SolverResult::Sat => {
            let model = extract_nia_model(&translator);
            // The relaxation may have abstracted structure the CAD core
            // cannot see (stores, dropped disjunctions, …).  A model that
            // survives concrete verification is a certified `Sat`; a refuted
            // one is discarded; an undecidable one falls back to the
            // pre-existing trust gate (extraction completeness).
            match verify_nl_model(&model, eliminations, raw_assertions, manager) {
                ModelCheck::Verified(verified) => Some(verified),
                ModelCheck::Refuted => None,
                ModelCheck::Undecidable => {
                    if !incomplete && !has_array_stores {
                        let mut env: HashMap<TermId, BigInt> = HashMap::new();
                        for (t, v) in &model {
                            if v.is_integer() {
                                env.insert(*t, v.to_integer());
                            }
                        }
                        augment_select_values(&mut env, raw_assertions, manager);
                        Some(NlDispatchResult::sat_with(
                            env.into_iter()
                                .map(|(t, v)| (t, BigRational::from(v)))
                                .collect(),
                        ))
                    } else {
                        None
                    }
                }
            }
        }
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

/// Tseitin-CNF dispatch for Boolean-structured nonlinear-integer goals.
///
/// Encodes the *entire* Boolean structure of `working` as clauses over the
/// NLSAT solver's algebraic-atom literals (gates for compound connectives,
/// free Boolean variables for user-declared Bool leaves), then solves with
/// the `NiaSolver` (real CDCL relaxation + integer branch-and-bound).
///
/// Verdict discipline (identical to the conjunction path):
/// * `Unsat` is trusted only when the encoding was complete (nothing
///   dropped), the goal carries no array stores and no Real-sorted symbols,
///   and no non-polynomial operator was seen; otherwise fall through.
/// * `Sat` is *always* concretely verified against the raw `assertions`
///   (with the Gaussian eliminations extended and free Booleans substituted
///   from the solver's satisfying assignment) before it is reported.
#[allow(clippy::too_many_arguments)]
fn cnf_nia_dispatch(
    working: &[TermId],
    assertions: &[TermId],
    eliminations: &[(TermId, TermId)],
    manager: &mut TermManager,
    integer_mode: bool,
    has_unsupported_ops: bool,
    has_array_stores: bool,
    has_real_symbols: bool,
) -> Option<NlDispatchResult> {
    let config = NiaConfig {
        enable_cutting_planes: true,
        ..NiaConfig::default()
    };
    let mut nia = NiaSolver::with_config(config);

    // Phase 1 – encode. The translator (and with it the manager) is immutably
    // borrowed until the encoder is done; clauses are buffered so the solver
    // is only mutated through the atom/gate constructors, exactly like the
    // conjunction path.
    let free_bools: Vec<(TermId, BoolVar)>;
    let clauses: Vec<Vec<Literal>>;
    let mut pending_atoms: Vec<PolyAtom> = Vec::new();
    let mut var_cache: HashMap<TermId, u32> = HashMap::new();
    let mut incomplete;
    {
        let mut translator = TermPolyTranslator::new(manager, &mut nia, integer_mode);
        let mut enc = NlCnfEncoder::new(&mut translator);
        let top_false = !enc.encode_assertions(working);
        incomplete = enc.incomplete;
        clauses = enc.clauses;
        free_bools = enc.free_bools;
        pending_atoms.extend(translator.pending_atoms.iter().cloned());
        var_cache.extend(translator.var_cache().iter().map(|(&t, &v)| (t, v)));
        if translator.divmod_incomplete {
            incomplete = true;
        }
        // Guard the trivial-verdict case before touching the solver: the
        // encoding already proved some top-level conjunct is `false`. Only
        // trustworthy when nothing else failed to encode (an `incomplete`
        // flag means we did not see the whole goal).
        if top_false && !incomplete {
            return Some(NlDispatchResult::Unsat);
        }
    }
    if incomplete {
        // Something in the goal is outside the polynomial-Boolean fragment
        // (other theories, quantifiers, untranslatable operands). Solving a
        // partial encoding could mis-decide both directions; fall through.
        nl_trace!("cnf dispatch: incomplete encoding -> fall through");
        return None;
    }
    nl_trace!(
        "cnf dispatch: {} clauses, {} atoms",
        clauses.len(),
        nia.nlsat().num_atoms()
    );

    // Phase 2 – load the solver: gate/unit clauses, then the Euclidean
    // div/mod side constraints collected during translation.
    for clause in clauses {
        nia.nlsat_mut().add_clause(clause);
    }
    for atom in &pending_atoms {
        let atom_id = nia.nlsat_mut().new_ineq_atom(atom.poly.clone(), atom.kind);
        let lit = nia.nlsat().atom_literal(atom_id, atom.positive);
        nia.nlsat_mut().add_clause(vec![lit]);
    }

    let unsat_is_trustworthy = !has_unsupported_ops && !has_real_symbols && !has_array_stores;
    let verdict = nia.solve();
    if cfg!(feature = "std") && std::env::var("OXIZ_NIA_TRACE").is_ok() {
        let s = nia.nlsat().stats();
        let ns = nia.stats();
        eprintln!(
            "[nia] cnf dispatch: solve -> {verdict:?} (decisions={} conflicts={} theory_conflicts={} | bb nodes={} depth={})",
            s.decisions, s.conflicts, s.theory_conflicts, ns.nodes_explored, ns.max_depth_reached
        );
    }
    match verdict {
        SolverResult::Sat => {
            let nlsat_model = nia.nlsat().get_model()?;
            // Arithmetic part: map the solver's poly-var values back onto the
            // original terms through the translator cache.
            let mut model: HashMap<TermId, BigRational> = HashMap::new();
            for (&term, &poly_var) in &var_cache {
                if let Some(val) = nlsat_model.arith_value(poly_var) {
                    model.insert(term, val.clone());
                }
            }
            // Boolean part: substitute the free user Booleans by the values
            // the solver assigned them, so the concrete verifier can
            // evaluate the raw assertions without free Boolean leaves.
            let mut sub: rustc_hash::FxHashMap<TermId, TermId> = rustc_hash::FxHashMap::default();
            for (term, var) in &free_bools {
                let v = nlsat_model.bool_value(*var);
                sub.insert(
                    *term,
                    if v == Some(true) {
                        manager.mk_true()
                    } else {
                        manager.mk_false()
                    },
                );
            }
            let to_verify: Vec<TermId> = if sub.is_empty() {
                assertions.to_vec()
            } else {
                assertions
                    .iter()
                    .map(|&a| manager.substitute(a, &sub))
                    .collect()
            };
            // Concrete verification against the raw assertions (Gaussian
            // eliminations extended first) is the sole gate for `Sat`.
            match verify_nl_model(&model, eliminations, &to_verify, manager) {
                ModelCheck::Verified(verified) => Some(verified),
                // A refuted or undecidable witness is discarded: the CNF may
                // have been weakened by skipped interface equalities, and an
                // undecidable evaluation is not a certificate.
                ModelCheck::Refuted | ModelCheck::Undecidable => None,
            }
        }
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

// pub(crate) aliases for the DPLL case-split driver (nl_dpll.rs).
pub(crate) use assertions_have_real_symbols as assertions_have_real_symbols_pub;
pub(crate) use contains_non_polynomial_ops as contains_non_polynomial_ops_pub;
pub(crate) use count_arith_symbols as count_arith_symbols_pub;
pub(crate) use has_boolean_structure as has_boolean_structure_pub;
pub(crate) use solve_conjunction_nia as solve_conjunction_nia_pub;

/// Count the distinct arithmetic symbols (variables, monomials, opaque
/// numeric leaves) appearing in the goal's arithmetic atoms.
pub(crate) fn count_arith_symbols(assertions: &[TermId], manager: &TermManager) -> usize {
    let mut symbols: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(id) = stack.pop() {
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Var(_) => {
                if n.sort == manager.sorts.int_sort || n.sort == manager.sorts.real_sort {
                    symbols.insert(id);
                }
            }
            TermKind::IntConst(_) | TermKind::RealConst(_) => {}
            TermKind::Div(_, _) | TermKind::Mod(_, _) | TermKind::Select(_, _) => {
                if n.sort == manager.sorts.int_sort || n.sort == manager.sorts.real_sort {
                    symbols.insert(id);
                }
                // Divisors/operands may themselves contain symbols.
                let children = oxiz_core::ast::traversal::get_children(&n.kind);
                stack.extend(children.iter().copied());
            }
            _ => {
                let children = oxiz_core::ast::traversal::get_children(&n.kind);
                stack.extend(children.iter().copied());
            }
        }
    }
    symbols.len()
}

/// `true` when any Real-sorted variable appears in the term.
pub(crate) fn assertions_have_real_symbols(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        if let TermKind::Var(_) = &n.kind
            && n.sort == manager.sorts.real_sort
        {
            return true;
        }
        let children = oxiz_core::ast::traversal::get_children(&n.kind);
        stack.extend(children.iter().copied());
    }
    false
}

/// Maximum number of distinct arithmetic symbols for which the exact
/// CAD/branch-and-bound core is entered at all.
///
/// Measured against the parity corpus: beyond ~150 symbols the per-node cost
/// of the branch-and-bound (a fresh relaxation solve per node) makes the
/// core hopeless, and Z3's own qfnia portfolio never enters nlsat on such
/// goals without first collapsing them via solve-eqs.
const CAD_MAX_SYMBOLS: usize = 150;

/// Default symbol ceiling for the Tseitin-CNF dispatch: above it the NLSAT
/// engine's coupled-cell search usually concedes, so the stage is skipped
/// (still reachable with `OXIZ_NIA_CNF`).
const CNF_MAX_DEFAULT_SYMBOLS: usize = 40;

/// Whole-goal symbol ceiling for the DPLL case-split driver (see the gate
/// comment in `dispatch_nia_constraints`).
const DPLL_MAX_GOAL_SYMBOLS: usize = 200;

/// Outcome of concretely verifying a candidate model against the original
/// assertions.
enum ModelCheck {
    /// Every assertion evaluates to `true` under the extended model – a
    /// certified `Sat` witness.
    Verified(NlDispatchResult),
    /// Some assertion evaluates to `false` – the candidate model is refuted;
    /// the caller must not report it.
    Refuted,
    /// The evaluator cannot decide some assertion (an operator outside the
    /// ground evaluator's fragment).  Neither a certificate nor a refutation;
    /// the caller falls back to its trust gate.
    Undecidable,
}

/// Verify a candidate model of the *reduced* goal against the *original*
/// assertions: extend it over the Gaussian-eliminated symbols, then
/// concretely evaluate every original assertion.  A non-integral value for
/// an Int-sorted term or an extension failure is a refutation; an assertion
/// the evaluator cannot decide makes the whole check `Undecidable` (never a
/// silent `false` – treating "cannot evaluate" as "violated" here used to
/// discard legitimate CAD models whose only exotic op was, e.g., a `mod`
/// with a negative constant divisor).
fn verify_nl_model(
    model: &HashMap<TermId, BigRational>,
    eliminations: &[(TermId, TermId)],
    assertions: &[TermId],
    manager: &mut TermManager,
) -> ModelCheck {
    // Rational environment: a value is only required to be integral when
    // its term is Int-sorted (a Real-sorted variable may legitimately hold
    // a fraction – demanding integrality of it used to refute every mixed
    // NIRA model).
    let mut renv: HashMap<TermId, BigRational> = HashMap::new();
    let int_sort = manager.sorts.int_sort;
    for (&term, value) in model {
        let term_is_int = manager.get(term).is_none_or(|t| t.sort == int_sort);
        if term_is_int && !value.is_integer() {
            return ModelCheck::Refuted;
        }
        renv.insert(term, value.clone());
    }
    // Extend over the Gaussian-eliminated symbols (integer-valued by
    // construction: every elimination is exact over ℤ).
    let mut bigint_env: HashMap<TermId, BigInt> = HashMap::new();
    for (&term, value) in &renv {
        if value.is_integer() {
            bigint_env.insert(term, value.to_integer());
        }
    }
    if !crate::nl_preprocess::extend_model(eliminations, &mut bigint_env, manager) {
        return ModelCheck::Refuted;
    }
    for (&t, v) in &bigint_env {
        renv.entry(t).or_insert(BigRational::from(v.clone()));
    }
    // Ground exactly like the model-search stage does (Boolean interface
    // equalities `(= spur φ)` substituted away, resolvable array reads
    // folded): the raw VeryMax shape carries free Bool spurs that no
    // evaluator can read, and treating them as "cannot decide" rejected
    // witnesses the stage itself had already certified (regression:
    // 489/510 sat→unknown).
    let grounded = crate::nl_model_search::ground_bool_interface_eqs(assertions, manager);
    let grounded = crate::nl_model_search::fold_array_reads(grounded, manager);
    let all_integral = renv.values().all(num_rational::BigRational::is_integer);
    for &a in &grounded {
        let v = if all_integral {
            let arrays: HashMap<TermId, crate::ania_ground::ArrayInterp> = HashMap::new();
            crate::ania_ground::eval_bool(a, manager, &arrays, &bigint_env)
        } else {
            crate::nl_preprocess::eval_bool_rational(a, &renv, manager)
        };
        match v {
            Some(true) => {}
            Some(false) => return ModelCheck::Refuted,
            None => return ModelCheck::Undecidable,
        }
    }
    let mut env: HashMap<TermId, BigInt> = bigint_env;
    augment_select_values(&mut env, assertions, manager);
    for (&t, v) in &renv {
        if v.is_integer() {
            env.entry(t).or_insert_with(|| v.to_integer());
        }
    }
    ModelCheck::Verified(NlDispatchResult::sat_with(
        env.into_iter()
            .map(|(t, v)| (t, BigRational::from(v)))
            .collect(),
    ))
}

/// Augment a model environment with *select-term* values read through the
/// purification interface (`c = select(A, i)` equalities): the relaxation
/// pins the spur variable `c`, not the `select` term, so without this a
/// caller's `(get-value ((select A i) …))` cannot resolve the read.
fn augment_select_values(
    env: &mut HashMap<TermId, BigInt>,
    assertions: &[TermId],
    manager: &TermManager,
) {
    for &a in assertions {
        for st in oxiz_core::ast::collect_subterms(a, manager) {
            let Some(n) = manager.get(st) else { continue };
            if let TermKind::Select(_, _) = &n.kind
                && let Some(v) = select_value_via_interface(st, assertions, env, manager)
            {
                env.entry(st).or_insert(v);
            }
        }
    }
}

/// Value of a `select` term under `env`, read through its purification
/// interface definition (`c = select(A, i)`): the spur `c`'s value if
/// present, else the select term's own entry, else `None`.
fn select_value_via_interface(
    select_term: TermId,
    assertions: &[TermId],
    env: &HashMap<TermId, BigInt>,
    manager: &TermManager,
) -> Option<BigInt> {
    if let Some(v) = env.get(&select_term) {
        return Some(v.clone());
    }
    for &a in assertions {
        for st in oxiz_core::ast::collect_subterms(a, manager) {
            let Some(n) = manager.get(st) else { continue };
            if let TermKind::Eq(l, r) = &n.kind {
                for (v, sel) in [(*l, *r), (*r, *l)] {
                    if sel == select_term
                        && manager
                            .get(v)
                            .is_some_and(|vn| matches!(vn.kind, TermKind::Var(_)))
                        && let Some(val) = env.get(&v)
                    {
                        return Some(val.clone());
                    }
                }
            }
        }
    }
    None
}

/// Map NIA poly-var indices back to TermIds via the translator cache.
fn extract_nia_model(translator: &TermPolyTranslator<'_>) -> HashMap<TermId, BigRational> {
    let mut out = HashMap::new();
    let Some(nlsat_model) = translator.nlsat.nlsat().get_model() else {
        return out;
    };
    for (&term, &poly_var) in translator.var_cache() {
        if let Some(val) = nlsat_model.arith_value(poly_var) {
            out.insert(term, val.clone());
        }
    }
    out
}

// ========  ========
// NRA dispatch (real arithmetic)
// ========  ========

struct RealPolyTranslator<'a> {
    manager: &'a TermManager,
    nlsat: &'a mut NlsatSolver,
    var_cache: HashMap<TermId, u32>,
}

impl<'a> RealPolyTranslator<'a> {
    fn new(manager: &'a TermManager, nlsat: &'a mut NlsatSolver) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
        }
    }

    fn translate(&mut self, term_id: TermId) -> Option<Polynomial> {
        let manager = self.manager;
        translate_poly(manager, self, term_id)
    }

    fn get_or_create_var(&mut self, term_id: TermId) -> u32 {
        if let Some(&v) = self.var_cache.get(&term_id) {
            return v;
        }
        let v = self.nlsat.new_arith_var();
        self.var_cache.insert(term_id, v);
        v
    }

    fn var_cache(&self) -> &HashMap<TermId, u32> {
        &self.var_cache
    }
}

/// Map NRA poly-var indices back to TermIds via the translator cache.
fn extract_nra_model(translator: &RealPolyTranslator<'_>) -> HashMap<TermId, BigRational> {
    // All-or-nothing (upstream v0.3.3): a variable holding an algebraic point
    // answers None from `arith_value`, and a partial rational map would be
    // completed with sort defaults by whatever renders the model — an
    // assignment that satisfies nothing. Refusing wholesale keeps the
    // modelless-but-correct `sat` of old, always safe; the algebraic channel
    // carries the case this declines.
    let mut out = HashMap::new();
    let Some(nlsat_model) = translator.nlsat.get_model() else {
        return out;
    };
    for (&term, &poly_var) in translator.var_cache() {
        let Some(val) = nlsat_model.arith_value(poly_var) else {
            return HashMap::new();
        };
        out.insert(term, val.clone());
    }
    out
}

/// The exact-value witness, for the real models [`extract_nra_model`] has to
/// decline. Empty map = "channel does not apply, use the rational one";
/// otherwise it covers **every** variable, rationals included. (Ported from
/// upstream v0.3.3.)
fn algebraic_witness_from_real_translator(
    translator: &RealPolyTranslator<'_>,
) -> rustc_hash::FxHashMap<TermId, crate::nl_witness::NlWitnessValue> {
    use crate::nl_witness::{AlgebraicValue, NlWitnessValue};
    use oxiz_nlsat::cad::CadPoint;

    let empty = rustc_hash::FxHashMap::default;
    let Some(model) = translator.nlsat.get_model() else {
        return empty();
    };
    let mut values = rustc_hash::FxHashMap::default();
    let mut saw_algebraic = false;
    for (&term, &poly_var) in translator.var_cache() {
        let Some(point) = model.arith_point(poly_var) else {
            return empty();
        };
        let value = match point {
            CadPoint::Rational(value) => NlWitnessValue::Rational(value.clone()),
            CadPoint::Algebraic {
                lo,
                hi,
                poly,
                index,
            } => {
                let Some(coefficients) = root_obj_coefficients(poly) else {
                    return empty();
                };
                saw_algebraic = true;
                NlWitnessValue::Algebraic(AlgebraicValue {
                    coefficients,
                    root_index: *index,
                    lower: lo.clone(),
                    upper: hi.clone(),
                })
            }
        };
        values.insert(term, value);
    }
    if saw_algebraic { values } else { empty() }
}

/// Put a `CadPoint::Algebraic` defining polynomial into `root-obj` normal
/// form: integer coefficients indexed by degree, primitive, positive leading
/// coefficient. `None` when not a univariate polynomial of degree >= 1.
/// (Ported from upstream v0.3.3; the normalisation-is-sound argument lives
/// there — clearing denominators / dividing content / sign flipping reorder
/// no root.)
fn root_obj_coefficients(
    poly: &oxiz_math::polynomial::Polynomial,
) -> Option<Vec<num_bigint::BigInt>> {
    use num_bigint::BigInt;
    use num_traits::{Signed, Zero};

    // num-integer's lcm/gcd over BigInt, inlined (the crate is not a
    // dependency here): gcd by Euclid on absolute values, lcm = |a*b|/gcd.
    fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
        let (mut a, mut b) = (a.abs(), b.abs());
        while !b.is_zero() {
            let r = &a % &b;
            a = b;
            b = r;
        }
        a
    }

    let vars = poly.vars();
    let &[var] = vars.as_slice() else {
        return None;
    };
    let degree = poly.degree(var) as usize;
    if degree == 0 {
        return None;
    }

    let mut rational = vec![BigRational::zero(); degree + 1];
    for term in poly.terms() {
        let power = match term.monomial.vars() {
            [] => 0usize,
            [vp] if vp.var == var => vp.power as usize,
            _ => return None,
        };
        let slot = rational.get_mut(power)?;
        *slot = &*slot + &term.coeff;
    }

    let mut denominator_lcm = BigInt::from(1);
    for coefficient in &rational {
        denominator_lcm =
            &denominator_lcm * coefficient.denom() / gcd(&denominator_lcm, coefficient.denom());
    }
    let mut integral: Vec<BigInt> = rational
        .iter()
        .map(|coefficient| coefficient.numer() * (&denominator_lcm / coefficient.denom()))
        .collect();

    let mut content = BigInt::from(0);
    for coefficient in &integral {
        content = gcd(&content, coefficient);
    }
    if content.is_zero() {
        return None;
    }
    for coefficient in &mut integral {
        *coefficient /= &content;
    }

    let leading = integral.last()?;
    if leading.is_zero() {
        return None;
    }
    if leading < &BigInt::from(0) {
        for coefficient in &mut integral {
            *coefficient = -&*coefficient;
        }
    }
    Some(integral)
}

impl PolyVarSource for RealPolyTranslator<'_> {
    fn var_for(&mut self, term_id: TermId) -> u32 {
        self.get_or_create_var(term_id)
    }
}

/// Real-arithmetic analogue of [`extract_poly_atoms`]. See its documentation
/// for the meaning of `incomplete`.
fn extract_real_poly_atoms(
    term_id: TermId,
    manager: &TermManager,
    translator: &mut RealPolyTranslator<'_>,
    out: &mut Vec<PolyAtom>,
    incomplete: &mut bool,
) {
    // Iterative conjunction descent: an assertion is an implicit conjunction
    // and `(and A (and B …))` nests as deep as the input makes it. Conjuncts
    // are pushed in reverse so they pop left to right, the order the recursive
    // descent used (and the order atoms land in `out`).
    let mut worklist = vec![term_id];
    while let Some(current) = worklist.pop() {
        let Some(term) = manager.get(current) else {
            *incomplete = true;
            continue;
        };
        let kind = term.kind.clone();
        match &kind {
            TermKind::Eq(lhs, rhs) => {
                // Array structural equalities and purification interface namings
                // (`c = select(...)`) are not arithmetic constraints: skip them
                // so the pure-arith fragment does not encode an unbounded second
                // var for the foreign side.
                if is_array_structural_eq(manager, *lhs, *rhs)
                    || is_arith_interface_eq(manager, *lhs, *rhs)
                {
                    continue;
                }
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&lp, &rp),
                        kind: AtomKind::Eq,
                        positive: true,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Lt(lhs, rhs) => {
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&rp, &lp),
                        kind: AtomKind::Gt,
                        positive: true,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Le(lhs, rhs) => {
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&rp, &lp),
                        kind: AtomKind::Lt,
                        positive: false,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Gt(lhs, rhs) => {
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&lp, &rp),
                        kind: AtomKind::Gt,
                        positive: true,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::Ge(lhs, rhs) => {
                if let (Some(lp), Some(rp)) =
                    (translator.translate(*lhs), translator.translate(*rhs))
                {
                    out.push(PolyAtom {
                        poly: Polynomial::sub(&lp, &rp),
                        kind: AtomKind::Lt,
                        positive: false,
                    });
                } else {
                    *incomplete = true;
                }
            }
            TermKind::And(args) => worklist.extend(args.iter().rev().copied()),
            _ => {
                *incomplete = true;
            }
        }
    }
}

/// Dispatch nonlinear real arithmetic assertions to `NlsatSolver`.
pub fn dispatch_nra_constraints(
    assertions: &[TermId],
    manager: &mut TermManager,
) -> Option<NlDispatchResult> {
    let has_nl = assertions.iter().any(|&a| term_is_nonlinear(a, manager));
    if !has_nl {
        return None;
    }

    let mut nlsat = NlsatSolver::new();
    let mut translator = RealPolyTranslator::new(manager, &mut nlsat);

    let mut poly_atoms: Vec<PolyAtom> = Vec::new();
    let mut incomplete = false;
    for &assertion in assertions {
        extract_real_poly_atoms(
            assertion,
            manager,
            &mut translator,
            &mut poly_atoms,
            &mut incomplete,
        );
    }

    if poly_atoms.is_empty() {
        return None;
    }

    let unsat_is_trustworthy = poly_atoms.iter().all(|atom| atom.kind != AtomKind::Eq);
    // See `dispatch_nia_constraints`: trusting Sat under a dropped (relaxed)
    // constraint is unsound, so only accept Sat when extraction was complete.
    let sat_is_trustworthy = !incomplete;

    for atom in &poly_atoms {
        let atom_id = translator.nlsat.new_ineq_atom(atom.poly.clone(), atom.kind);
        let lit = translator.nlsat.atom_literal(atom_id, atom.positive);
        translator.nlsat.add_clause(vec![lit]);
    }

    match translator.nlsat.solve() {
        SolverResult::Sat if sat_is_trustworthy => {
            // Exactly one of the two witness channels, never both (upstream
            // v0.3.3): the algebraic one applies only when some variable's
            // value is irrational, and then it carries the whole model.
            let algebraic = algebraic_witness_from_real_translator(&translator);
            Some(if algebraic.is_empty() {
                NlDispatchResult::sat_with(extract_nra_model(&translator))
            } else {
                NlDispatchResult::sat_algebraic(algebraic)
            })
        }
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Sat | SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

// ========  ========
// NlsatTheory – Theory trait wrapper
// ========  ========

#[derive(Debug, Clone)]
struct NlsatContextState {
    level: usize,
}

enum NlsatSolverWrapper {
    Real(NlsatSolver),
    Integer(NiaSolver),
}

impl core::fmt::Debug for NlsatSolverWrapper {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Real(_) => write!(f, "NlsatSolverWrapper::Real(..)"),
            Self::Integer(_) => write!(f, "NlsatSolverWrapper::Integer(..)"),
        }
    }
}

impl NlsatSolverWrapper {
    fn new(integer: bool) -> Self {
        if integer {
            Self::Integer(NiaSolver::new())
        } else {
            Self::Real(NlsatSolver::new())
        }
    }

    fn solve(&mut self) -> SolverResult {
        match self {
            Self::Real(s) => s.solve(),
            Self::Integer(s) => s.solve(),
        }
    }
}

/// NLSAT Theory Solver for nonlinear arithmetic.
///
/// Supports both real (QF_NRA) and integer (QF_NIA) nonlinear arithmetic.
/// Full constraint translation happens in `dispatch_nia_constraints` /
/// `dispatch_nra_constraints`; this wrapper integrates with the `Theory` trait.
#[derive(Debug)]
pub struct NlsatTheory {
    solver: NlsatSolverWrapper,
    context_stack: Vec<NlsatContextState>,
    is_integer: bool,
    last_result: Option<SolverResult>,
    asserted_terms: Vec<TermId>,
}

impl NlsatTheory {
    /// Create a new NLSAT theory solver.
    ///
    /// * `integer` – true for QF_NIA, false for QF_NRA.
    pub fn new(integer: bool) -> Self {
        Self {
            solver: NlsatSolverWrapper::new(integer),
            context_stack: Vec::new(),
            is_integer: integer,
            last_result: None,
            asserted_terms: Vec::new(),
        }
    }
}

impl Theory for NlsatTheory {
    fn id(&self) -> TheoryId {
        if self.is_integer {
            TheoryId::NIA
        } else {
            TheoryId::NRA
        }
    }

    fn name(&self) -> &str {
        if self.is_integer { "NIA" } else { "NRA" }
    }

    fn can_handle(&self, _term: TermId) -> bool {
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        self.asserted_terms.push(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        self.asserted_terms.push(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        let result = self.solver.solve();
        self.last_result = Some(result);
        match result {
            SolverResult::Sat => Ok(TheoryResult::Sat),
            SolverResult::Unsat => {
                let conflict = self.asserted_terms.clone();
                Ok(TheoryResult::Unsat(conflict))
            }
            SolverResult::Unknown => Ok(TheoryResult::Unknown),
        }
    }

    fn push(&mut self) {
        self.context_stack.push(NlsatContextState {
            level: self.asserted_terms.len(),
        });
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            self.asserted_terms.truncate(state.level);
        }
    }

    fn reset(&mut self) {
        *self = Self::new(self.is_integer);
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        Vec::new()
    }
}

// ========  ========
// Unit tests
// ========  ========

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::ast::TermManager;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    // ======== Theory trait tests ========

    #[test]
    fn test_nlsat_theory_new() {
        let theory_nia = NlsatTheory::new(true);
        assert_eq!(theory_nia.id(), TheoryId::NIA);
        assert_eq!(theory_nia.name(), "NIA");
        assert!(theory_nia.is_integer);

        let theory_nra = NlsatTheory::new(false);
        assert_eq!(theory_nra.id(), TheoryId::NRA);
        assert_eq!(theory_nra.name(), "NRA");
        assert!(!theory_nra.is_integer);
    }

    #[test]
    fn test_nlsat_theory_push_pop() {
        let mut theory = NlsatTheory::new(false);
        assert_eq!(theory.context_stack.len(), 0);
        theory.push();
        assert_eq!(theory.context_stack.len(), 1);
        theory.push();
        assert_eq!(theory.context_stack.len(), 2);
        theory.pop();
        assert_eq!(theory.context_stack.len(), 1);
        theory.pop();
        assert_eq!(theory.context_stack.len(), 0);
    }

    #[test]
    fn test_nlsat_theory_reset() {
        let mut theory = NlsatTheory::new(false);
        let term = TermId::new(1);
        let _ = theory.assert_true(term);
        assert!(!theory.asserted_terms.is_empty());
        theory.reset();
        assert!(theory.asserted_terms.is_empty());
        assert!(theory.context_stack.is_empty());
    }

    #[test]
    fn test_nlsat_theory_can_handle() {
        let theory = NlsatTheory::new(false);
        assert!(theory.can_handle(TermId::new(1)));
    }

    #[test]
    fn test_nlsat_theory_check_placeholder() {
        let mut theory = NlsatTheory::new(false);
        let result = theory.check().expect("check should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    // ======== Translator unit tests ========

    #[test]
    fn test_translator_constant() {
        let mut manager = TermManager::new();
        let five = manager.mk_int(5);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(five).expect("constant should translate");
        assert!(poly.is_constant());
        assert_eq!(poly.constant_value(), rat(5));
    }

    #[test]
    fn test_translator_variable() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(x).expect("variable should translate");
        assert!(poly.is_linear());
        assert_eq!(poly.num_terms(), 1);
    }

    #[test]
    fn test_translator_add() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let sum = manager.mk_add(vec![x, y]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(sum).expect("add should translate");
        assert_eq!(poly.num_terms(), 2);
    }

    #[test]
    fn test_translator_mul_vars() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let product = manager.mk_mul(vec![x, y]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(product).expect("mul should translate");
        // x * y is a single monomial of degree 2
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 2);
    }

    #[test]
    fn test_translator_square() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(square).expect("x*x should translate");
        // x^2 – single term, degree 2
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 2);
    }

    #[test]
    fn test_translator_neg() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let neg_x = manager.mk_neg(x);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(neg_x).expect("neg should translate");
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.leading_coeff(), rat(-1));
    }

    #[test]
    fn test_translator_sub() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let two = manager.mk_int(2);
        let x_minus_2 = manager.mk_sub(x, two);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(x_minus_2).expect("sub should translate");
        // x - 2 → two terms: x and -2
        assert_eq!(poly.num_terms(), 2);
    }

    #[test]
    fn test_translator_triple_product() {
        // (* x y z) – degree-3 monomial
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let z = manager.mk_var("z", int_sort);
        let triple = manager.mk_mul(vec![x, y, z]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t
            .translate(triple)
            .expect("triple product should translate");
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 3);
    }

    #[test]
    fn test_translator_factored_product() {
        // (* (+ x 1) (- y 2)) → xy - 2x + y - 2
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let xp1 = manager.mk_add(vec![x, one]);
        let ym2 = manager.mk_sub(y, two);
        let product = manager.mk_mul(vec![xp1, ym2]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t
            .translate(product)
            .expect("factored product should translate");
        // (x+1)(y-2) = xy - 2x + y - 2  → 4 terms
        assert_eq!(poly.num_terms(), 4);
        assert_eq!(poly.total_degree(), 2);
    }

    // ======== term_is_nonlinear tests ========

    #[test]
    fn test_term_is_nonlinear_square() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        assert!(term_is_nonlinear(square, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_product_xy() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let xy = manager.mk_mul(vec![x, y]);
        assert!(term_is_nonlinear(xy, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_linear_is_false() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let three = manager.mk_int(3);
        let three_x = manager.mk_mul(vec![three, x]);
        assert!(!term_is_nonlinear(three_x, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_constant() {
        let mut manager = TermManager::new();
        let c = manager.mk_int(42);
        assert!(!term_is_nonlinear(c, &manager));
    }

    // ======== dispatch integration tests ========

    #[test]
    fn test_dispatch_nia_x_squared_eq_4_sat() {
        // x * x = 4 → SAT (x=2 or x=-2)
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let four = manager.mk_int(4);
        let eq = manager.mk_eq(square, four);
        let result = dispatch_nia_constraints(&[eq], &mut manager, true, true);
        // SAT or Unknown (unknown means solver fell through)
        assert!(
            matches!(result, Some(NlDispatchResult::Sat(_)) | None),
            "x*x=4 should be SAT or unknown, got {:?}",
            result
        );
    }

    #[test]
    fn test_dispatch_nia_x_squared_neg_unsat() {
        // x * x = -1 → UNSAT (no integer square is negative)
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let neg_one = manager.mk_int(-1);
        let eq = manager.mk_eq(square, neg_one);
        let result = dispatch_nia_constraints(&[eq], &mut manager, true, true);
        assert!(
            matches!(result, Some(NlDispatchResult::Unsat) | None),
            "x*x=-1 should be UNSAT or unknown, got {:?}",
            result
        );
    }

    #[test]
    fn test_dispatch_nra_x_squared_neg_unsat() {
        // x * x < 0 → UNSAT (no real square is negative)
        let mut manager = TermManager::new();
        let real_sort = manager.sorts.real_sort;
        let x = manager.mk_var("x", real_sort);
        let square = manager.mk_mul(vec![x, x]);
        let zero = manager.mk_int(0);
        let lt = manager.mk_lt(square, zero);
        let result = dispatch_nra_constraints(&[lt], &mut manager);
        assert!(
            matches!(result, Some(NlDispatchResult::Unsat) | None),
            "x*x<0 should be UNSAT or unknown, got {:?}",
            result
        );
    }

    // ======== Tseitin-CNF dispatch (Boolean-structured goals) ========

    #[test]
    fn cnf_dispatch_disjunction_sat() {
        // x >= 1, y >= 1, and (x <= 0 or y <= 0 or x*y < 1) → UNSAT: every
        // disjunct is refuted (integers: x*y >= 1), each through the or-gate.
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let one = manager.mk_int(1);
        let xy = manager.mk_mul(vec![x, y]);
        let ge_x1 = manager.mk_ge(x, one);
        let ge_y1 = manager.mk_ge(y, one);
        let not_x1 = manager.mk_not(ge_x1);
        let not_y1 = manager.mk_not(ge_y1);
        let lt1 = manager.mk_lt(xy, one);
        let disj = manager.mk_or(vec![not_x1, not_y1, lt1]);
        let assertions = vec![ge_x1, ge_y1, disj];
        let result = dispatch_nia_constraints(&assertions, &mut manager, true, true);
        assert_eq!(
            result,
            Some(NlDispatchResult::Unsat),
            "x,y>=1 with x<=0 or y<=0 or x*y<1 is UNSAT"
        );
    }

    #[test]
    fn cnf_dispatch_disjunction_witness_side_sat() {
        // Same shape but satisfiable: allow x >= 1, and keep the or.
        // (x*y >= 4) and (x >= 1 or y >= 1) → SAT (x=4,y=1).
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let one = manager.mk_int(1);
        let four = manager.mk_int(4);
        let xy = manager.mk_mul(vec![x, y]);
        let ge4 = manager.mk_ge(xy, four);
        let ge_x1 = manager.mk_ge(x, one);
        let ge_y1 = manager.mk_ge(y, one);
        let disj = manager.mk_or(vec![ge_x1, ge_y1]);
        let assertions = vec![ge4, disj];
        let result = dispatch_nia_constraints(&assertions, &mut manager, true, true);
        assert!(
            matches!(result, Some(NlDispatchResult::Sat(_))),
            "x*y>=4 with x>=1 or y>=1 is SAT, got {result:?}"
        );
    }

    #[test]
    fn cnf_dispatch_negation_polarity_regression() {
        // Regression for the `Not`-polarity inversion: `(not (<= (x*x) 0))`
        // under a conjunction used to flip and produce a wrong UNSAT on
        // VeryMax `ex36.t2_fixed__p23678`. Satisfiable side: x = 5.
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let zero = manager.mk_int(0);
        let five = manager.mk_int(5);
        let sq = manager.mk_mul(vec![x, x]);
        let le0 = manager.mk_le(sq, zero);
        let not_le = manager.mk_not(le0);
        let eq5 = manager.mk_eq(x, five);
        let assertions = vec![not_le, eq5];
        let result = dispatch_nia_constraints(&assertions, &mut manager, true, true);
        assert!(
            matches!(result, Some(NlDispatchResult::Sat(_))),
            "x*x>0 with x=5 is SAT, got {result:?}"
        );
    }

    #[test]
    fn cnf_dispatch_negation_polarity_unsat_side() {
        // The dual of the polarity regression: the negated bound contradicts
        // (on the nonlinear monomial x*y, so the NIA dispatch engages).
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let zero = manager.mk_int(0);
        let xy = manager.mk_mul(vec![x, y]);
        let le = manager.mk_le(xy, zero);
        let not_le = manager.mk_not(le);
        let assertions = vec![not_le, le];
        let result = dispatch_nia_constraints(&assertions, &mut manager, true, true);
        assert_eq!(
            result,
            Some(NlDispatchResult::Unsat),
            "x*y>0 and x*y<=0 is UNSAT"
        );
    }

    #[test]
    fn cnf_dispatch_free_bool_sat_and_unsat() {
        // A free Boolean b equated to an arithmetic atom: b ↔ (x*x >= 4).
        // With x*x < 4 and b → UNSAT; without b → SAT.
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;
        let x = manager.mk_var("x", int_sort);
        let b = manager.mk_var("b", bool_sort);
        let four = manager.mk_int(4);
        let sq = manager.mk_mul(vec![x, x]);
        let ge = manager.mk_ge(sq, four);
        let iff = manager.mk_eq(b, ge);
        let lt = manager.mk_lt(sq, four);
        let assertions = vec![iff, lt, b];
        let result = dispatch_nia_constraints(&assertions, &mut manager, true, true);
        assert_eq!(
            result,
            Some(NlDispatchResult::Unsat),
            "b ↔ x²≥4 with x²<4 and b is UNSAT"
        );
    }

    #[test]
    fn cnf_dispatch_distinct_pair() {
        // (distinct x y) with x = y = 3 and x*x = 9 (nonlinear, engages NIA)
        // → UNSAT.
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let three = manager.mk_int(3);
        let nine = manager.mk_int(9);
        let xy = manager.mk_mul(vec![x, y]);
        let assertions = vec![
            manager.mk_distinct(vec![x, y]),
            manager.mk_eq(x, three),
            manager.mk_eq(y, three),
            manager.mk_eq(xy, nine),
        ];
        let result = dispatch_nia_constraints(&assertions, &mut manager, true, true);
        assert_eq!(
            result,
            Some(NlDispatchResult::Unsat),
            "distinct x y with x=y=3 is UNSAT"
        );
    }
}
