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
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::error::Result;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::nia::{NiaConfig, NiaSolver, VarType};
use oxiz_nlsat::solver::{NlsatSolver, SolverResult};
use oxiz_nlsat::types::AtomKind;
use std::collections::HashMap;

// ─────────────────────────────────────────────────────────────────────────────
// Public result type for dispatch functions
// ─────────────────────────────────────────────────────────────────────────────

/// The definitive result from a nonlinear dispatch call.
///
/// `Unknown` is not included: `dispatch_*` functions return `None` to signal
/// "fall through to CDCL(T)" instead of wrapping Unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NlDispatchResult {
    /// The constraint set is satisfiable.
    Sat,
    /// The constraint set is unsatisfiable.
    Unsat,
}

// ─────────────────────────────────────────────────────────────────────────────
// Term→Polynomial translator
// ─────────────────────────────────────────────────────────────────────────────

/// Translates `TermId` AST nodes to `Polynomial` values for use with
/// the NLSAT / NIA solver.
///
/// Maintains a cache of `TermId → polynomial variable index` so that each
/// unique variable term receives a stable index.
pub struct TermPolyTranslator<'a> {
    manager: &'a TermManager,
    nlsat: &'a mut NiaSolver,
    var_cache: HashMap<TermId, u32>,
    integer_mode: bool,
}

impl<'a> TermPolyTranslator<'a> {
    /// Create a new translator.
    pub fn new(manager: &'a TermManager, nlsat: &'a mut NiaSolver, integer_mode: bool) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
            integer_mode,
        }
    }

    /// Translate a term into a `Polynomial`.
    ///
    /// Returns `None` for sub-expressions that cannot be expressed as a
    /// polynomial (e.g. division, modulo, uninterpreted functions).
    pub fn translate(&mut self, term_id: TermId) -> Option<Polynomial> {
        let manager = self.manager;
        translate_poly(manager, self, term_id)
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
}

// ─────────────────────────────────────────────────────────────────────────────
// Shared iterative term→polynomial translation
// ─────────────────────────────────────────────────────────────────────────────

/// The one thing the two translators do differently: mint (or look up) the
/// polynomial variable index for a term.
trait PolyVarSource {
    /// The polynomial variable index standing for `term_id`.
    fn var_for(&mut self, term_id: TermId) -> u32;
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

/// Sum a list of polynomials left to right, starting from zero — which is also
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

// ─────────────────────────────────────────────────────────────────────────────
// Helper: nonlinearity detection
// ─────────────────────────────────────────────────────────────────────────────

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
            TermKind::Add(args) | TermKind::And(args) => stack.extend(args.iter().copied()),
            TermKind::Sub(lhs, rhs)
            | TermKind::Eq(lhs, rhs)
            | TermKind::Gt(lhs, rhs)
            | TermKind::Ge(lhs, rhs)
            | TermKind::Lt(lhs, rhs)
            | TermKind::Le(lhs, rhs) => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            TermKind::Neg(inner) => stack.push(*inner),
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

/// Whether the term mentions an operator the polynomial translation cannot
/// express. Same shape (and same reasons for being iterative + memoised) as
/// [`term_is_nonlinear`]: `bool` return, `check_sat` path, input-controlled
/// depth and sharing.
fn contains_non_polynomial_ops(term_id: TermId, manager: &TermManager) -> bool {
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
            TermKind::Div(_, _) | TermKind::Mod(_, _) => return true,
            TermKind::Apply { .. }
            | TermKind::Forall { .. }
            | TermKind::Exists { .. }
            | TermKind::Let { .. }
            | TermKind::Match { .. } => return true,
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

// ─────────────────────────────────────────────────────────────────────────────
// Polynomial atom (internal representation)
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
struct PolyAtom {
    poly: Polynomial,
    kind: AtomKind,
    /// `true` → atom appears positively; `false` → negated literal.
    positive: bool,
}

// ─────────────────────────────────────────────────────────────────────────────
// Assertion-level translation (integer mode)
// ─────────────────────────────────────────────────────────────────────────────

/// Extract polynomial atoms from a top-level assertion.
///
/// `incomplete` is set to `true` whenever some part of the assertion could
/// **not** be captured as a pure conjunction of polynomial atoms — an
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

// ─────────────────────────────────────────────────────────────────────────────
// NIA dispatch: public entry point
// ─────────────────────────────────────────────────────────────────────────────

/// Dispatch nonlinear integer arithmetic assertions to the `NiaSolver`.
///
/// Returns:
/// - `Some(NlDispatchResult::Unsat)` if the system is provably UNSAT,
/// - `Some(NlDispatchResult::Sat)` if NiaSolver finds an integer model,
/// - `None` if translation yields no atoms or the solver returns Unknown.
///
/// Both linear and nonlinear assertions are passed so the solver has full context.
pub fn dispatch_nia_constraints(
    assertions: &[TermId],
    manager: &TermManager,
    integer_mode: bool,
) -> Option<NlDispatchResult> {
    let has_nl = assertions.iter().any(|&a| term_is_nonlinear(a, manager));
    if !has_nl {
        return None;
    }
    let has_unsupported_ops = assertions
        .iter()
        .any(|&a| contains_non_polynomial_ops(a, manager));

    let config = NiaConfig {
        enable_cutting_planes: true,
        ..NiaConfig::default()
    };
    let mut nia = NiaSolver::with_config(config);
    let mut translator = TermPolyTranslator::new(manager, &mut nia, integer_mode);

    let mut poly_atoms: Vec<PolyAtom> = Vec::new();
    let mut incomplete = false;
    for &assertion in assertions {
        extract_poly_atoms(
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

    let unsat_is_trustworthy =
        !has_unsupported_ops && poly_atoms.iter().all(|atom| atom.poly.is_univariate());
    // A `Sat` verdict is only sound when the solver saw the *entire* assertion
    // set as a conjunction of translatable atoms. If any top-level term was
    // dropped (a disjunction, an untranslatable operand, …) the solver worked
    // on a strictly weaker problem, so its model may violate the dropped
    // constraint — fall through to CDCL(T) instead of trusting Sat.
    let sat_is_trustworthy = !incomplete;

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
        SolverResult::Sat if sat_is_trustworthy => Some(NlDispatchResult::Sat),
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Sat | SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NRA dispatch (real arithmetic)
// ─────────────────────────────────────────────────────────────────────────────

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
    manager: &TermManager,
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
        SolverResult::Sat if sat_is_trustworthy => Some(NlDispatchResult::Sat),
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Sat | SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NlsatTheory – Theory trait wrapper
// ─────────────────────────────────────────────────────────────────────────────

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

// ─────────────────────────────────────────────────────────────────────────────
// Unit tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::ast::TermManager;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    // ── Theory trait tests ────────────────────────────────────────────────────

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

    // ── Translator unit tests ──────────────────────────────────────────────────

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
        // x^2 — single term, degree 2
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
        // (* x y z) — degree-3 monomial
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

    // ── term_is_nonlinear tests ────────────────────────────────────────────────

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

    // ── dispatch integration tests ─────────────────────────────────────────────

    #[test]
    fn test_dispatch_nia_x_squared_eq_4_sat() {
        // x * x = 4 → SAT (x=2 or x=-2)
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let four = manager.mk_int(4);
        let eq = manager.mk_eq(square, four);
        let result = dispatch_nia_constraints(&[eq], &manager, true);
        // SAT or Unknown (unknown means solver fell through)
        assert!(
            matches!(result, Some(NlDispatchResult::Sat) | None),
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
        let result = dispatch_nia_constraints(&[eq], &manager, true);
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
        let result = dispatch_nra_constraints(&[lt], &manager);
        assert!(
            matches!(result, Some(NlDispatchResult::Unsat) | None),
            "x*x<0 should be UNSAT or unknown, got {:?}",
            result
        );
    }
}
