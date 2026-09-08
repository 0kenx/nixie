//! Finite FP class domains, bidirectional class propagation and strict-order
//! cycle detection. Every narrowing is a consequence of unconditional facts
//! and operation semantics. No host floating-point bounds are used.

use super::*;

const NAN: u16 = 1;
const PZERO: u16 = 1 << 1;
const NZERO: u16 = 1 << 2;
const PSUB: u16 = 1 << 3;
const NSUB: u16 = 1 << 4;
const PNORMAL: u16 = 1 << 5;
const NNORMAL: u16 = 1 << 6;
const PINF: u16 = 1 << 7;
const NINF: u16 = 1 << 8;
const ZERO: u16 = PZERO | NZERO;
const SUB: u16 = PSUB | NSUB;
const NORMAL: u16 = PNORMAL | NNORMAL;
const INF: u16 = PINF | NINF;
const POS: u16 = PZERO | PSUB | PNORMAL | PINF;
const NEG: u16 = NZERO | NSUB | NNORMAL | NINF;
const ALL: u16 = (1 << 9) - 1;

#[derive(Clone, Copy, Debug)]
#[repr(u16)]
enum Class {
    Nan = NAN,
    PositiveZero = PZERO,
    NegativeZero = NZERO,
    PositiveSubnormal = PSUB,
    NegativeSubnormal = NSUB,
    PositiveNormal = PNORMAL,
    NegativeNormal = NNORMAL,
    PositiveInfinity = PINF,
    NegativeInfinity = NINF,
}
impl Class {
    const ALL: [Self; 9] = [
        Self::Nan,
        Self::PositiveZero,
        Self::NegativeZero,
        Self::PositiveSubnormal,
        Self::NegativeSubnormal,
        Self::PositiveNormal,
        Self::NegativeNormal,
        Self::PositiveInfinity,
        Self::NegativeInfinity,
    ];
    fn mask(self) -> u16 {
        self as u16
    }
}
fn classes(mask: u16) -> impl Iterator<Item = Class> {
    Class::ALL.into_iter().filter(move |c| mask & c.mask() != 0)
}
fn negate(c: Class) -> Class {
    match c {
        Class::Nan => Class::Nan,
        Class::PositiveZero => Class::NegativeZero,
        Class::NegativeZero => Class::PositiveZero,
        Class::PositiveSubnormal => Class::NegativeSubnormal,
        Class::NegativeSubnormal => Class::PositiveSubnormal,
        Class::PositiveNormal => Class::NegativeNormal,
        Class::NegativeNormal => Class::PositiveNormal,
        Class::PositiveInfinity => Class::NegativeInfinity,
        Class::NegativeInfinity => Class::PositiveInfinity,
    }
}
fn class(v: FpValue) -> u16 {
    if v.is_nan() {
        NAN
    } else if v.is_zero() {
        if v.sign { NZERO } else { PZERO }
    } else if v.is_infinite() {
        if v.sign { NINF } else { PINF }
    } else if v.is_subnormal() {
        if v.sign { NSUB } else { PSUB }
    } else if v.sign {
        NNORMAL
    } else {
        PNORMAL
    }
}
fn predicate(p: Predicate) -> u16 {
    match p {
        Predicate::Nan => NAN,
        Predicate::Infinite => INF,
        Predicate::Zero => ZERO,
        Predicate::Normal => NORMAL,
        Predicate::Subnormal => SUB,
        Predicate::Positive => POS,
        Predicate::Negative => NEG,
    }
}

/// Overapproximation of all results for two *single* classes. Finite/finite
/// rows deliberately retain every possible magnitude class of the right
/// sign; precision-specific boundary reasoning belongs in a later domain.
fn transfer(op: Arithmetic, rm: RoundingMode, a: Class, mut b: Class) -> u16 {
    if matches!(op, Arithmetic::Sub) {
        b = negate(b);
    }
    let (a, b) = (a.mask(), b.mask());
    if a == NAN || b == NAN {
        return NAN;
    }
    let negative = (a & NEG != 0) ^ (b & NEG != 0);
    let zero = if negative { NZERO } else { PZERO };
    let inf = if negative { NINF } else { PINF };
    if matches!(op, Arithmetic::Mul) {
        if (a & ZERO != 0 && b & INF != 0) || (b & ZERO != 0 && a & INF != 0) {
            return NAN;
        }
        if a & INF != 0 || b & INF != 0 {
            return inf;
        }
        if a & ZERO != 0 || b & ZERO != 0 {
            return zero;
        }
        return if negative { NEG } else { POS };
    }
    if a & INF != 0 && b & INF != 0 {
        return if a == b { a } else { NAN };
    }
    if a & INF != 0 {
        return a;
    }
    if b & INF != 0 {
        return b;
    }
    if a & ZERO != 0 && b & ZERO != 0 {
        return if a == b {
            a
        } else if rm == RoundingMode::RTN {
            NZERO
        } else {
            PZERO
        };
    }
    if a & ZERO != 0 {
        return b;
    }
    if b & ZERO != 0 {
        return a;
    }
    if !negative {
        if a & NEG != 0 { NEG } else { POS }
    } else {
        ZERO | SUB | NORMAL
    }
}

fn rank(c: Class) -> Option<u8> {
    match c {
        Class::Nan => None,
        Class::NegativeInfinity => Some(0),
        Class::NegativeNormal => Some(1),
        Class::NegativeSubnormal => Some(2),
        Class::NegativeZero | Class::PositiveZero => Some(3),
        Class::PositiveSubnormal => Some(4),
        Class::PositiveNormal => Some(5),
        Class::PositiveInfinity => Some(6),
    }
}
fn order_possible(a: Class, b: Class, equal: bool) -> bool {
    let (Some(a_rank), Some(b_rank)) = (rank(a), rank(b)) else {
        return false;
    };
    a_rank < b_rank || (a_rank == b_rank && (equal || a.mask() & (SUB | NORMAL) != 0))
}
pub(super) enum Failure {
    Conflict,
    InvalidNode,
}

/// Preserve datum congruence before introducing arithmetic abstractions.
/// IEEE fp.eq is deliberately excluded: it equates the two zero signs, which
/// are observably different operands to sign-sensitive FP operations.
fn congruence(g: &Goal, facts: &[(usize, bool)]) -> Result<Vec<usize>, Failure> {
    let mut euf = nixie_theories::euf::EufSolver::new();
    let mut ids = Vec::new();
    let mut symbols = FxHashMap::default();
    for (i, n) in g.nodes.iter().enumerate() {
        let term = TermId(u32::try_from(i).map_err(|_| Failure::InvalidNode)?);
        let app = match n.op {
            Op::Neg(a) => Some((0, vec![a])),
            Op::Abs(a) => Some((1, vec![a])),
            Op::Ite(c, a, b) if g.format(i).is_some() => Some((2, vec![c, a, b])),
            Op::Arithmetic(op, rm, a, b) => {
                let mode = RoundingMode::ALL
                    .iter()
                    .position(|m| *m == rm)
                    .ok_or(Failure::InvalidNode)?;
                let op = match op {
                    Arithmetic::Add => 0,
                    Arithmetic::Sub => 1,
                    Arithmetic::Mul => 2,
                };
                Some((3 + 3 * mode + op, vec![a, b]))
            }
            _ => None,
        };
        let id = if let Some((tag, children)) = app {
            let f = g.format(i).ok_or(Failure::InvalidNode)?;
            let next = u32::try_from(symbols.len()).map_err(|_| Failure::InvalidNode)?;
            let symbol = *symbols
                .entry((f.exponent_bits, f.significand_bits, tag))
                .or_insert(next);
            let args = children
                .into_iter()
                .map(|a| ids.get(a).copied().ok_or(Failure::InvalidNode))
                .collect::<Result<Vec<_>, _>>()?;
            euf.intern_app(term, symbol, args)
        } else {
            euf.intern(term)
        };
        ids.push(id);
    }
    for &(i, positive) in facts {
        if positive && let Op::Eq(a, b) = g.nodes[i].op {
            euf.merge(ids[a], ids[b], g.nodes[i].original)
                .map_err(|_| Failure::InvalidNode)?;
        }
    }
    let mut first = FxHashMap::default();
    Ok(ids
        .into_iter()
        .enumerate()
        .map(|(i, id)| *first.entry(euf.find(id)).or_insert(i))
        .collect())
}

fn narrow(ds: &mut [u16], i: usize, allowed: u16, stats: &mut Stats) -> Result<bool, Failure> {
    let previous = *ds.get(i).ok_or(Failure::InvalidNode)?;
    let next = previous & allowed;
    if next == 0 {
        return Err(Failure::Conflict);
    }
    ds[i] = next;
    if next != previous {
        stats.domain_reductions += 1;
    }
    Ok(next != previous)
}

pub(super) fn propagate(g: &Goal, stats: &mut Stats) -> Result<Vec<u16>, Failure> {
    let mut ds = vec![ALL; g.nodes.len()];
    for (i, n) in g.nodes.iter().enumerate() {
        if let Op::Const(Value::Fp(v)) = n.op {
            ds[i] = class(v);
        }
    }
    let mut facts = Vec::new();
    let mut stack: Vec<_> = g.roots.iter().map(|&i| (i, true)).collect();
    let mut seen = FxHashSet::default();
    while let Some((i, positive)) = stack.pop() {
        if !seen.insert((i, positive)) {
            continue;
        }
        match &g.nodes[i].op {
            Op::Not(a) => stack.push((*a, !positive)),
            Op::And(xs) if positive => stack.extend(xs.iter().map(|&i| (i, true))),
            Op::Or(xs) if !positive => stack.extend(xs.iter().map(|&i| (i, false))),
            Op::Const(Value::Bool(v)) if *v != positive => return Err(Failure::Conflict),
            _ => facts.push((i, positive)),
        }
    }
    let representatives = congruence(g, &facts)?;
    for &(i, positive) in &facts {
        match g.nodes[i].op {
            Op::Eq(a, b) if !positive && representatives[a] == representatives[b] => {
                return Err(Failure::Conflict);
            }
            Op::Lt(a, b, false) if positive && representatives[a] == representatives[b] => {
                return Err(Failure::Conflict);
            }
            _ => {}
        }
    }
    loop {
        let mut changed = false;
        for (i, &r) in representatives.iter().enumerate() {
            if g.format(i).is_some() {
                let common = ds[i] & ds[r];
                changed |= narrow(&mut ds, i, common, stats)?;
                changed |= narrow(&mut ds, r, common, stats)?;
            }
        }
        for &(i, positive) in &facts {
            match g.nodes[i].op {
                Op::Pred(p, a) => {
                    let allowed = if positive {
                        predicate(p)
                    } else {
                        ALL ^ predicate(p)
                    };
                    changed |= narrow(&mut ds, a, allowed, stats)?;
                }
                Op::Eq(a, b) if positive && g.format(a).is_some() => {
                    let common = ds[a] & ds[b];
                    changed |= narrow(&mut ds, a, common, stats)?;
                    changed |= narrow(&mut ds, b, common, stats)?;
                }
                Op::IeeeEq(a, b) if positive => {
                    let zeros = ds[a] & ZERO != 0 && ds[b] & ZERO != 0;
                    let common = (ds[a] & ds[b] & !NAN) | if zeros { ZERO } else { 0 };
                    changed |= narrow(&mut ds, a, common, stats)?;
                    changed |= narrow(&mut ds, b, common, stats)?;
                }
                Op::Lt(a, b, equal) if positive => {
                    let mut aa = 0;
                    let mut bb = 0;
                    for ca in classes(ds[a]) {
                        for cb in classes(ds[b]) {
                            if order_possible(ca, cb, equal) {
                                aa |= ca.mask();
                                bb |= cb.mask();
                            }
                        }
                    }
                    changed |= narrow(&mut ds, a, aa, stats)?;
                    changed |= narrow(&mut ds, b, bb, stats)?;
                }
                _ => {}
            }
        }
        for (i, n) in g.nodes.iter().enumerate() {
            match n.op {
                Op::Arithmetic(op, rm, a, b) => {
                    let mut aa = 0;
                    let mut bb = 0;
                    let mut rr = 0;
                    for ca in classes(ds[a]) {
                        for cb in classes(ds[b]) {
                            let out = transfer(op, rm, ca, cb) & ds[i];
                            if out != 0 {
                                aa |= ca.mask();
                                bb |= cb.mask();
                                rr |= out;
                            }
                        }
                    }
                    changed |= narrow(&mut ds, a, aa, stats)?;
                    changed |= narrow(&mut ds, b, bb, stats)?;
                    changed |= narrow(&mut ds, i, rr, stats)?;
                }
                Op::Neg(a) | Op::Abs(a) => {
                    let mut aa = 0;
                    let mut rr = 0;
                    for ca in classes(ds[a]) {
                        let out = if matches!(n.op, Op::Neg(_)) || ca.mask() & NEG != 0 {
                            negate(ca)
                        } else {
                            ca
                        };
                        if out.mask() & ds[i] != 0 {
                            aa |= ca.mask();
                            rr |= out.mask();
                        }
                    }
                    changed |= narrow(&mut ds, a, aa, stats)?;
                    changed |= narrow(&mut ds, i, rr, stats)?;
                }
                Op::Ite(_, a, b) if g.format(i).is_some() => {
                    let union = ds[a] | ds[b];
                    changed |= narrow(&mut ds, i, union, stats)?;
                }
                _ => {}
            }
        }
        if !changed {
            break;
        }
    }
    // Equality edges denote identity (including NaN), comparison edges denote
    // numerical order. Any cycle containing a strict comparison is impossible:
    // every comparison excludes NaN and identity cannot change that value.
    let mut edges = vec![Vec::new(); g.nodes.len()];
    for (i, &r) in representatives.iter().enumerate() {
        if i != r && g.format(i).is_some() {
            edges[i].push(r);
            edges[r].push(i);
        }
    }
    let mut strict = Vec::new();
    for (i, positive) in facts {
        if !positive {
            continue;
        }
        match g.nodes[i].op {
            Op::Lt(a, b, equal) => {
                edges[a].push(b);
                if !equal {
                    strict.push((a, b));
                }
            }
            Op::Eq(a, b) | Op::IeeeEq(a, b) if g.format(a).is_some() => {
                edges[a].push(b);
                edges[b].push(a);
            }
            _ => {}
        }
    }
    // Iterative reachability. No recursion over a user-controlled graph.
    let mut visited = vec![0usize; g.nodes.len()];
    for (generation, (a, b)) in strict.into_iter().enumerate() {
        let marker = generation + 1;
        let mut stack = vec![b];
        while let Some(i) = stack.pop() {
            if i == a {
                return Err(Failure::Conflict);
            }
            if visited[i] == marker {
                continue;
            }
            visited[i] = marker;
            stack.extend(edges[i].iter().copied());
        }
    }
    Ok(ds)
}

pub(super) fn encode(c: &Circuit, x: Expr, f: FpFormat, mask: u16) -> Expr {
    if mask == ALL {
        return c.boolean(true);
    }
    let sign = c.nonzero(c.sign(x));
    let mut cases = Vec::new();
    for cls in classes(mask) {
        let magnitude = match cls {
            Class::Nan => c.is_nan(x, f),
            Class::PositiveZero | Class::NegativeZero => c.is_zero(x),
            Class::PositiveSubnormal | Class::NegativeSubnormal => c.is_subnormal(x, f),
            Class::PositiveNormal | Class::NegativeNormal => c.is_normal(x, f),
            Class::PositiveInfinity | Class::NegativeInfinity => c.is_inf(x, f),
        };
        cases.push(if matches!(cls, Class::Nan) {
            magnitude
        } else {
            c.and(&[
                magnitude,
                if cls.mask() & NEG != 0 {
                    sign
                } else {
                    c.not(sign)
                },
            ])
        });
    }
    c.or(&cases)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn class_transfer_contains_every_tiny_arithmetic_result() {
        let f = FpFormat::new(2, 3);
        let bound = 1u64 << f.width();
        for a in 0..bound {
            for b in 0..bound {
                let av = decode(BigUint::from(a), f).expect("a");
                let bv = decode(BigUint::from(b), f).expect("b");
                let ca = classes(class(av)).next().expect("class a");
                let cb = classes(class(bv)).next().expect("class b");
                for rm in RoundingMode::ALL {
                    for op in [Arithmetic::Add, Arithmetic::Sub, Arithmetic::Mul] {
                        let result = arithmetic(op, rm, av, bv).expect("oracle");
                        assert_ne!(
                            transfer(op, rm, ca, cb) & class(result),
                            0,
                            "{op:?} {rm:?} {av:?} {bv:?} -> {result:?}"
                        );
                    }
                }
            }
        }
    }
}
