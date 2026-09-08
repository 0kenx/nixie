//! FP class/order propagation followed by monotone refinement of symbolic
//! arithmetic into exact BV circuits. See docs/FP_HYBRID.md for the contract.

mod circuit;
mod domain;
#[cfg(test)]
mod tests;

use super::{Solver, SolverResult, types::Model};
use circuit::{Circuit, Expr};
use nixie_core::ast::{RoundingMode, TermId, TermKind, TermManager};
use nixie_sat::{Solver as SatSolver, SolverResult as SatResult};
use nixie_theories::{FpFormat, FpValue, bv::BvSolver};
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sort {
    Bool,
    Rm,
    Fp(FpFormat),
}
#[derive(Clone, Copy, Debug)]
enum Value {
    Bool(bool),
    Rm(u8),
    Fp(FpValue),
}
impl Value {
    fn boolean(self) -> Option<bool> {
        if let Self::Bool(v) = self {
            Some(v)
        } else {
            None
        }
    }
    fn fp(self) -> Option<FpValue> {
        if let Self::Fp(v) = self {
            Some(v)
        } else {
            None
        }
    }
    fn same(self, other: Self) -> bool {
        match (self, other) {
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Rm(a), Self::Rm(b)) => a == b,
            (Self::Fp(a), Self::Fp(b)) => {
                a.format == b.format && ((a.is_nan() && b.is_nan()) || a == b)
            }
            _ => false,
        }
    }
}
#[derive(Clone, Copy, Debug)]
enum Predicate {
    Nan,
    Infinite,
    Zero,
    Normal,
    Subnormal,
    Positive,
    Negative,
}
impl Predicate {
    fn eval(self, v: FpValue) -> bool {
        match self {
            Self::Nan => v.is_nan(),
            Self::Infinite => v.is_infinite(),
            Self::Zero => v.is_zero(),
            Self::Normal => v.is_normal(),
            Self::Subnormal => v.is_subnormal(),
            Self::Positive => v.is_positive(),
            Self::Negative => v.is_negative(),
        }
    }
}
#[derive(Clone, Copy, Debug)]
enum Arithmetic {
    Add,
    Sub,
    Mul,
}
#[derive(Debug)]
enum Op {
    Const(Value),
    Var,
    Not(usize),
    And(Vec<usize>),
    Or(Vec<usize>),
    Eq(usize, usize),
    Ite(usize, usize, usize),
    Lt(usize, usize, bool),
    IeeeEq(usize, usize),
    Pred(Predicate, usize),
    Neg(usize),
    Abs(usize),
    Arithmetic(Arithmetic, RoundingMode, usize, usize),
}
struct Node {
    original: TermId,
    sort: Sort,
    op: Op,
}
struct Goal {
    nodes: Vec<Node>,
    roots: Vec<usize>,
}

fn sort_of(t: TermId, m: &TermManager) -> Option<Sort> {
    let sort = m.sorts.get(m.get(t)?.sort)?;
    if sort.is_bool() {
        return Some(Sort::Bool);
    }
    if m.get(t)?.sort == m.sorts.rounding_mode_sort {
        return Some(Sort::Rm);
    }
    let (e, p) = sort.float_format()?;
    // Exact concrete validation currently uses FpValue's u64 fields. Refuse
    // wider formats explicitly; no field is truncated. The exponent bound
    // also bounds exact rational witnesses and circuit construction.
    if !(2..=15).contains(&e) || !(2..=64).contains(&p) {
        return None;
    }
    Some(Sort::Fp(FpFormat::new(e, p)))
}

impl Goal {
    fn parse(assertions: &[TermId], m: &TermManager) -> Option<Self> {
        let mut nodes: Vec<Node> = Vec::new();
        let mut ids = FxHashMap::default();
        let mut stack: Vec<_> = assertions.iter().rev().map(|&t| (t, false)).collect();
        let mut active = FxHashSet::default();
        let mut has_fp = false;
        while let Some((t, combine)) = stack.pop() {
            if ids.contains_key(&t) {
                continue;
            }
            let sort = sort_of(t, m)?;
            has_fp |= matches!(sort, Sort::Fp(_));
            let kind = &m.get(t)?.kind;
            match kind {
                TermKind::FpLit { eb, sb, .. }
                | TermKind::FpPlusZero { eb, sb }
                | TermKind::FpMinusZero { eb, sb }
                | TermKind::FpPlusInfinity { eb, sb }
                | TermKind::FpMinusInfinity { eb, sb }
                | TermKind::FpNaN { eb, sb }
                | TermKind::RealToFp { eb, sb, .. }
                    if sort != Sort::Fp(FpFormat::new(*eb, *sb)) =>
                {
                    return None;
                }
                _ => {}
            }
            let constant = match kind {
                TermKind::Var(name) if sort == Sort::Rm => RoundingMode::ALL
                    .iter()
                    .position(|&rm| TermManager::rounding_mode_name(rm) == m.resolve_str(*name))
                    .map(|i| Value::Rm(i as u8)),
                TermKind::True => Some(Value::Bool(true)),
                TermKind::False => Some(Value::Bool(false)),
                TermKind::FpLit {
                    exp, sig, eb, sb, ..
                } => {
                    if *exp < BigInt::ZERO
                        || *sig < BigInt::ZERO
                        || exp.bits() > u64::from(*eb)
                        || sig.bits() > u64::from(*sb - 1)
                    {
                        return None;
                    }
                    Some(Value::Fp(super::fp_fold::fp_const_value(t, m)?))
                }
                TermKind::FpPlusZero { .. }
                | TermKind::FpMinusZero { .. }
                | TermKind::FpPlusInfinity { .. }
                | TermKind::FpMinusInfinity { .. }
                | TermKind::FpNaN { .. } => Some(Value::Fp(super::fp_fold::fp_const_value(t, m)?)),
                TermKind::RealToFp { rm, arg, eb, sb } => {
                    let r = super::fp_fold::eval_rational(*arg, m)?;
                    Some(Value::Fp(super::fp_fold::rational_to_fp(
                        &r, *eb, *sb, *rm,
                    )?))
                }
                _ => None,
            };
            let children = if constant.is_some() {
                Vec::new()
            } else {
                match kind {
                    TermKind::Var(_) => Vec::new(),
                    TermKind::Not(a)
                    | TermKind::FpNeg(a)
                    | TermKind::FpAbs(a)
                    | TermKind::FpIsNormal(a)
                    | TermKind::FpIsSubnormal(a)
                    | TermKind::FpIsZero(a)
                    | TermKind::FpIsInfinite(a)
                    | TermKind::FpIsNaN(a)
                    | TermKind::FpIsNegative(a)
                    | TermKind::FpIsPositive(a) => vec![*a],
                    TermKind::And(xs) | TermKind::Or(xs) | TermKind::Distinct(xs) => xs.to_vec(),
                    TermKind::Eq(a, b)
                    | TermKind::Implies(a, b)
                    | TermKind::Xor(a, b)
                    | TermKind::FpEq(a, b)
                    | TermKind::FpLt(a, b)
                    | TermKind::FpLeq(a, b)
                    | TermKind::FpGt(a, b)
                    | TermKind::FpGeq(a, b)
                    | TermKind::FpAdd(_, a, b)
                    | TermKind::FpSub(_, a, b)
                    | TermKind::FpMul(_, a, b) => vec![*a, *b],
                    TermKind::Ite(a, b, c) => vec![*a, *b, *c],
                    _ => return None,
                }
            };
            if !combine {
                if !active.insert(t) {
                    return None;
                }
                stack.push((t, true));
                for &child in children.iter().rev() {
                    if !ids.contains_key(&child) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            active.remove(&t);
            let cs: Vec<usize> = children
                .iter()
                .map(|t| ids.get(t).copied())
                .collect::<Option<_>>()?;
            let boolean = |i: usize| nodes.get(i).is_some_and(|n| n.sort == Sort::Bool);
            let same_fp = |a: usize, b: usize| {
                nodes
                    .get(a)
                    .zip(nodes.get(b))
                    .is_some_and(|(a, b)| matches!(a.sort, Sort::Fp(_)) && a.sort == b.sort)
            };
            let op = if let Some(v) = constant {
                let actual = match v {
                    Value::Bool(_) => Sort::Bool,
                    Value::Rm(_) => Sort::Rm,
                    Value::Fp(v) => Sort::Fp(v.format),
                };
                if sort != actual {
                    return None;
                }
                Op::Const(v)
            } else {
                match kind {
                    TermKind::Var(_) => Op::Var,
                    TermKind::Not(_) if sort == Sort::Bool && boolean(cs[0]) => Op::Not(cs[0]),
                    TermKind::And(_) | TermKind::Or(_)
                        if sort == Sort::Bool && cs.iter().all(|&i| boolean(i)) =>
                    {
                        if matches!(kind, TermKind::And(_)) {
                            Op::And(cs)
                        } else {
                            Op::Or(cs)
                        }
                    }
                    TermKind::Eq(_, _)
                        if sort == Sort::Bool && nodes[cs[0]].sort == nodes[cs[1]].sort =>
                    {
                        Op::Eq(cs[0], cs[1])
                    }
                    TermKind::Ite(_, _, _)
                        if boolean(cs[0])
                            && nodes[cs[1]].sort == sort
                            && nodes[cs[2]].sort == sort =>
                    {
                        Op::Ite(cs[0], cs[1], cs[2])
                    }
                    TermKind::FpLt(_, _)
                    | TermKind::FpLeq(_, _)
                    | TermKind::FpGt(_, _)
                    | TermKind::FpGeq(_, _)
                        if sort == Sort::Bool && same_fp(cs[0], cs[1]) =>
                    {
                        let (a, b) = if matches!(kind, TermKind::FpGt(_, _) | TermKind::FpGeq(_, _))
                        {
                            (cs[1], cs[0])
                        } else {
                            (cs[0], cs[1])
                        };
                        Op::Lt(
                            a,
                            b,
                            matches!(kind, TermKind::FpLeq(_, _) | TermKind::FpGeq(_, _)),
                        )
                    }
                    TermKind::FpEq(_, _) if sort == Sort::Bool && same_fp(cs[0], cs[1]) => {
                        Op::IeeeEq(cs[0], cs[1])
                    }
                    TermKind::FpNeg(_) | TermKind::FpAbs(_)
                        if matches!(sort, Sort::Fp(_)) && nodes[cs[0]].sort == sort =>
                    {
                        if matches!(kind, TermKind::FpNeg(_)) {
                            Op::Neg(cs[0])
                        } else {
                            Op::Abs(cs[0])
                        }
                    }
                    TermKind::FpAdd(rm, _, _)
                    | TermKind::FpSub(rm, _, _)
                    | TermKind::FpMul(rm, _, _)
                        if same_fp(cs[0], cs[1]) && nodes[cs[0]].sort == sort =>
                    {
                        let a = match kind {
                            TermKind::FpAdd(..) => Arithmetic::Add,
                            TermKind::FpSub(..) => Arithmetic::Sub,
                            TermKind::FpMul(..) => Arithmetic::Mul,
                            _ => return None,
                        };
                        Op::Arithmetic(a, *rm, cs[0], cs[1])
                    }
                    TermKind::FpIsNaN(_)
                    | TermKind::FpIsInfinite(_)
                    | TermKind::FpIsZero(_)
                    | TermKind::FpIsNormal(_)
                    | TermKind::FpIsSubnormal(_)
                    | TermKind::FpIsPositive(_)
                    | TermKind::FpIsNegative(_)
                        if sort == Sort::Bool && matches!(nodes[cs[0]].sort, Sort::Fp(_)) =>
                    {
                        let p = match kind {
                            TermKind::FpIsNaN(_) => Predicate::Nan,
                            TermKind::FpIsInfinite(_) => Predicate::Infinite,
                            TermKind::FpIsZero(_) => Predicate::Zero,
                            TermKind::FpIsNormal(_) => Predicate::Normal,
                            TermKind::FpIsSubnormal(_) => Predicate::Subnormal,
                            TermKind::FpIsPositive(_) => Predicate::Positive,
                            TermKind::FpIsNegative(_) => Predicate::Negative,
                            _ => return None,
                        };
                        Op::Pred(p, cs[0])
                    }
                    // Normalize Boolean sugar into already-typed internal nodes.
                    TermKind::Implies(_, _) | TermKind::Xor(_, _)
                        if sort == Sort::Bool && boolean(cs[0]) && boolean(cs[1]) =>
                    {
                        let index = nodes.len();
                        let inner = if matches!(kind, TermKind::Implies(_, _)) {
                            Op::Not(cs[0])
                        } else {
                            Op::Eq(cs[0], cs[1])
                        };
                        nodes.push(Node {
                            original: t,
                            sort: Sort::Bool,
                            op: inner,
                        });
                        if matches!(kind, TermKind::Implies(_, _)) {
                            Op::Or(vec![index, cs[1]])
                        } else {
                            Op::Not(index)
                        }
                    }
                    TermKind::Distinct(_)
                        if sort == Sort::Bool
                            && cs.windows(2).all(|w| nodes[w[0]].sort == nodes[w[1]].sort) =>
                    {
                        let mut pairs = Vec::new();
                        for (pos, &a) in cs.iter().enumerate() {
                            for &b in &cs[pos + 1..] {
                                let eq = nodes.len();
                                nodes.push(Node {
                                    original: t,
                                    sort: Sort::Bool,
                                    op: Op::Eq(a, b),
                                });
                                let ne = nodes.len();
                                nodes.push(Node {
                                    original: t,
                                    sort: Sort::Bool,
                                    op: Op::Not(eq),
                                });
                                pairs.push(ne);
                            }
                        }
                        Op::And(pairs)
                    }
                    _ => return None,
                }
            };
            ids.insert(t, nodes.len());
            nodes.push(Node {
                original: t,
                sort,
                op,
            });
        }
        if !has_fp {
            return None;
        }
        let roots: Vec<usize> = assertions
            .iter()
            .map(|t| ids.get(t).copied())
            .collect::<Option<_>>()?;
        if roots.iter().any(|&i| nodes[i].sort != Sort::Bool) {
            return None;
        }
        Some(Self { nodes, roots })
    }
    fn format(&self, i: usize) -> Option<FpFormat> {
        if let Sort::Fp(f) = self.nodes.get(i)?.sort {
            Some(f)
        } else {
            None
        }
    }
}

/// Independent arithmetic evaluator: exact rational operation followed by the
/// existing BigRational rounding procedure, with IEEE special/zero cases.
fn arithmetic(op: Arithmetic, rm: RoundingMode, a: FpValue, mut b: FpValue) -> Option<FpValue> {
    let f = a.format;
    if f != b.format {
        return None;
    }
    if matches!(op, Arithmetic::Sub) {
        b.sign = !b.sign;
    }
    if a.is_nan() || b.is_nan() {
        return Some(FpValue::nan(f));
    }
    let sign = a.sign ^ b.sign;
    if matches!(op, Arithmetic::Mul) {
        if (a.is_infinite() && b.is_zero()) || (b.is_infinite() && a.is_zero()) {
            return Some(FpValue::nan(f));
        }
        if a.is_infinite() || b.is_infinite() {
            let mut v = FpValue::pos_infinity(f);
            v.sign = sign;
            return Some(v);
        }
        if a.is_zero() || b.is_zero() {
            let mut v = FpValue::pos_zero(f);
            v.sign = sign;
            return Some(v);
        }
    } else {
        if a.is_infinite() && b.is_infinite() && a.sign != b.sign {
            return Some(FpValue::nan(f));
        }
        if a.is_infinite() {
            return Some(a);
        }
        if b.is_infinite() {
            return Some(b);
        }
    }
    let x = super::fp_fold::fp_value_rational(&a)?;
    let y = super::fp_fold::fp_value_rational(&b)?;
    let r = if matches!(op, Arithmetic::Mul) {
        x * y
    } else {
        x + y
    };
    if r.is_zero() {
        let mut v = FpValue::pos_zero(f);
        v.sign = if a.is_zero() && b.is_zero() && a.sign == b.sign {
            a.sign
        } else {
            rm == RoundingMode::RTN
        };
        return Some(v);
    }
    super::fp_fold::rational_to_fp(&r, f.exponent_bits, f.significand_bits, rm)
}

fn less(a: FpValue, b: FpValue) -> bool {
    if a.is_nan() || b.is_nan() || (a.is_zero() && b.is_zero()) {
        return false;
    }
    if a.sign != b.sign {
        return a.sign;
    }
    let ord = (a.exponent, a.significand).cmp(&(b.exponent, b.significand));
    if a.sign { ord.is_gt() } else { ord.is_lt() }
}
fn ieee_eq(a: FpValue, b: FpValue) -> bool {
    !a.is_nan() && !b.is_nan() && (a == b || (a.is_zero() && b.is_zero()))
}

impl Goal {
    fn lower(&self, c: &Circuit) -> Option<Vec<Expr>> {
        let mut wires: Vec<Expr> = Vec::new();
        for n in &self.nodes {
            let w = match &n.op {
                Op::Const(Value::Bool(v)) => c.boolean(*v),
                Op::Const(Value::Rm(v)) => c.n(*v, 3),
                Op::Const(Value::Fp(v)) => c.constant(*v),
                Op::Var | Op::Arithmetic(..) => c.fresh(match n.sort {
                    Sort::Bool => 0,
                    Sort::Rm => 3,
                    Sort::Fp(f) => f.width(),
                }),
                Op::Not(a) => c.not(wires[*a]),
                Op::And(xs) => c.and(&xs.iter().map(|&i| wires[i]).collect::<Vec<_>>()),
                Op::Or(xs) => c.or(&xs.iter().map(|&i| wires[i]).collect::<Vec<_>>()),
                Op::Eq(a, b) => {
                    if let Some(f) = self.format(*a) {
                        c.datum_eq(wires[*a], wires[*b], f)
                    } else {
                        c.eq(wires[*a], wires[*b])
                    }
                }
                Op::Ite(a, b, d) => c.ite(wires[*a], wires[*b], wires[*d]),
                Op::Lt(a, b, equal) => {
                    let f = self.format(*a)?;
                    let lt = c.lt(wires[*a], wires[*b], f);
                    if *equal {
                        c.or(&[lt, c.ieee_eq(wires[*a], wires[*b], f)])
                    } else {
                        lt
                    }
                }
                Op::IeeeEq(a, b) => c.ieee_eq(wires[*a], wires[*b], self.format(*a)?),
                Op::Neg(a) => c.fp_neg(wires[*a]),
                Op::Abs(a) => c.fp_abs(wires[*a]),
                Op::Pred(p, a) => {
                    let x = wires[*a];
                    let f = self.format(*a)?;
                    match p {
                        Predicate::Nan => c.is_nan(x, f),
                        Predicate::Infinite => c.is_inf(x, f),
                        Predicate::Zero => c.is_zero(x),
                        Predicate::Normal => c.is_normal(x, f),
                        Predicate::Subnormal => c.is_subnormal(x, f),
                        Predicate::Negative => {
                            c.and(&[c.not(c.is_nan(x, f)), c.nonzero(c.sign(x))])
                        }
                        Predicate::Positive => {
                            c.and(&[c.not(c.is_nan(x, f)), c.not(c.nonzero(c.sign(x)))])
                        }
                    }
                }
            };
            wires.push(w);
        }
        Some(wires)
    }
    fn expected(&self, i: usize, values: &[Value]) -> Option<Value> {
        let b = |i: usize| values.get(i).copied()?.boolean();
        let f = |i: usize| values.get(i).copied()?.fp();
        Some(match &self.nodes.get(i)?.op {
            Op::Const(v) => *v,
            Op::Var => *values.get(i)?,
            Op::Not(a) => Value::Bool(!b(*a)?),
            Op::And(xs) => Value::Bool(
                xs.iter()
                    .map(|&i| b(i))
                    .collect::<Option<Vec<_>>>()?
                    .iter()
                    .all(|v| *v),
            ),
            Op::Or(xs) => Value::Bool(
                xs.iter()
                    .map(|&i| b(i))
                    .collect::<Option<Vec<_>>>()?
                    .iter()
                    .any(|v| *v),
            ),
            Op::Eq(a, d) => Value::Bool(values[*a].same(values[*d])),
            Op::Ite(a, d, e) => {
                if b(*a)? {
                    values[*d]
                } else {
                    values[*e]
                }
            }
            Op::Lt(a, d, equal) => {
                Value::Bool(less(f(*a)?, f(*d)?) || (*equal && ieee_eq(f(*a)?, f(*d)?)))
            }
            Op::IeeeEq(a, d) => Value::Bool(ieee_eq(f(*a)?, f(*d)?)),
            Op::Pred(p, a) => Value::Bool(p.eval(f(*a)?)),
            Op::Neg(a) => {
                let mut v = f(*a)?;
                v.sign = !v.sign;
                Value::Fp(v)
            }
            Op::Abs(a) => {
                let mut v = f(*a)?;
                v.sign = false;
                Value::Fp(v)
            }
            Op::Arithmetic(op, rm, a, d) => Value::Fp(arithmetic(*op, *rm, f(*a)?, f(*d)?)?),
        })
    }
}

fn decode(raw: BigUint, f: FpFormat) -> Option<FpValue> {
    let mask = (BigUint::from(1u8) << (f.significand_bits - 1)) - BigUint::from(1u8);
    Some(FpValue {
        sign: raw.bit(u64::from(f.width() - 1)),
        exponent: ((&raw >> (f.significand_bits - 1)) & BigUint::from(f.max_exponent()))
            .to_u64()?,
        significand: (&raw & mask).to_u64()?,
        format: f,
    })
}

#[derive(Default, Debug)]
struct Stats {
    domain_reductions: usize,
    exact_operations: usize,
    checks: usize,
}

fn solve(goal: &Goal, conflict_limit: u64) -> Option<(SolverResult, Vec<Value>, Stats)> {
    let mut stats = Stats::default();
    let domains = match domain::propagate(goal, &mut stats) {
        Ok(d) => d,
        Err(domain::Failure::Conflict) => return Some((SolverResult::Unsat, Vec::new(), stats)),
        Err(domain::Failure::InvalidNode) => return None,
    };
    let c = Circuit::new();
    let wires = goal.lower(&c)?;
    let mut bv = BvSolver::new();
    bv.enter_unified();
    let mut sat = SatSolver::new();
    if conflict_limit != 0 {
        sat.set_max_conflicts(Some(conflict_limit));
    }
    let mut constraints: Vec<Expr> = goal.roots.iter().map(|&i| wires[i]).collect();
    for (i, &domain) in domains.iter().enumerate() {
        if let Some(f) = goal.format(i) {
            constraints.push(domain::encode(&c, wires[i], f, domain));
        }
        if goal.nodes[i].sort == Sort::Rm {
            constraints.push(c.ult(wires[i], c.n(5, 3)));
        }
    }
    let mut exact = FxHashSet::default();
    let mut encoded_count = 0usize;
    let mut encoded_bv = FxHashSet::default();
    loop {
        let ok = bv.build_with(&mut sat, |bv| {
            encode_remaining(bv, &c, &constraints, &mut encoded_count, &mut encoded_bv)
        });
        if !ok {
            return None;
        }
        constraints.clear();
        stats.checks += 1;
        sat.freeze_theory_vars((0..sat.num_vars()).map(|i| nixie_sat::Var::new(i as u32)));
        match sat.solve() {
            SatResult::Unknown => return Some((SolverResult::Unknown, Vec::new(), stats)),
            SatResult::Unsat => return Some((SolverResult::Unsat, Vec::new(), stats)),
            SatResult::Sat => {}
        }
        bv.adopt_model_snapshot(sat.model());
        let mut values = Vec::new();
        for (i, w) in wires.iter().enumerate() {
            values.push(match goal.nodes[i].sort {
                Sort::Bool => Value::Bool(bv.bool_value(w.id)?),
                Sort::Rm => Value::Rm(bv.get_value_big(w.id)?.to_u8().filter(|v| *v < 5)?),
                Sort::Fp(f) => Value::Fp(decode(bv.get_value_big(w.id)?, f)?),
            });
        }
        let mut violations = Vec::new();
        for i in 0..goal.nodes.len() {
            if !goal.expected(i, &values)?.same(values[i]) {
                if matches!(goal.nodes[i].op, Op::Arithmetic(..)) && !exact.contains(&i) {
                    violations.push(i);
                } else {
                    return Some((SolverResult::Unknown, Vec::new(), stats));
                }
            }
        }
        if violations.is_empty() {
            if goal
                .roots
                .iter()
                .any(|&i| values[i].boolean() != Some(true))
            {
                return None;
            }
            return Some((SolverResult::Sat, values, stats));
        }
        sat.backtrack_to_root();
        for i in violations {
            let Op::Arithmetic(op, rm, a, b) = goal.nodes[i].op else {
                return None;
            };
            let f = goal.format(i)?;
            let result = match op {
                Arithmetic::Add => c.fp_add(wires[a], wires[b], f, rm),
                Arithmetic::Sub => c.fp_add(wires[a], c.fp_neg(wires[b]), f, rm),
                Arithmetic::Mul => c.fp_mul(wires[a], wires[b], f, rm),
            };
            constraints.push(c.datum_eq(wires[i], result, f));
            exact.insert(i);
            stats.exact_operations += 1;
        }
    }
}

fn encode_remaining(
    bv: &mut BvSolver,
    c: &Circuit,
    constraints: &[Expr],
    encoded_count: &mut usize,
    encoded_bv: &mut FxHashSet<TermId>,
) -> bool {
    let m = c.manager.borrow();
    // Circuit nodes are interned after their children. Encode in that order:
    // the BV encoder requires pre-blasted equality operands, and the Boolean
    // encoder's recursive calls then find memoized children immediately.
    for i in *encoded_count..m.len() {
        let id = TermId(i as u32);
        let Some(node) = m.get(id) else {
            return false;
        };
        let Some(sort) = m.sorts.get(node.sort) else {
            return false;
        };
        if sort.is_bool() {
            if bv.encode_bool_node(id, &m).is_none() {
                return false;
            }
        } else if sort.bitvec_width().is_some() {
            if !super::theory_bv_encode::encode_bv_term_recursive(bv, id, &m, encoded_bv) {
                return false;
            }
        } else {
            return false;
        }
    }
    *encoded_count = m.len();
    for a in constraints {
        // All definitions are encoded already; pin their truth variables.
        // Check the memo first because pin_bool_term is intentionally a no-op
        // for absent terms in other callers.
        if bv.encode_bool_node(a.id, &m).is_none() {
            return false;
        }
        bv.pin_bool_term(a.id, true);
    }
    true
}

impl Solver {
    pub(super) fn dispatch_fp_hybrid(&mut self, m: &mut TermManager) -> Option<SolverResult> {
        // This dispatch has no proof translation yet. Limits not supported by
        // its SAT API retain the existing path rather than being ignored.
        if self.proof.is_some()
            || self.config.certification_mode == super::CertificationMode::Certified
            || self.config.timeout_ms != 0
            || self.config.max_decisions != 0
        {
            return None;
        }
        let goal = Goal::parse(&self.assertions, m)?;
        let (result, values, _stats) = solve(&goal, self.config.max_conflicts)?;
        match result {
            SolverResult::Sat => {
                let mut model = Model::new();
                for (node, value) in goal.nodes.iter().zip(values) {
                    let term = match value {
                        Value::Bool(v) => m.mk_bool(v),
                        Value::Rm(v) => m.mk_rounding_mode(*RoundingMode::ALL.get(v as usize)?),
                        Value::Fp(v) => m.mk_fp_lit(
                            v.sign,
                            BigInt::from(v.exponent),
                            BigInt::from(v.significand),
                            v.format.exponent_bits,
                            v.format.significand_bits,
                        ),
                    };
                    model.set(node.original, term);
                }
                self.model = Some(model);
            }
            SolverResult::Unsat => self.build_unsat_core(),
            SolverResult::Unknown => {}
        }
        Some(result)
    }
}
