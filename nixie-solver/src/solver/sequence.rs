//! Exact finite-shape reduction for native sequences. No guessed length bounds.
//! All state belongs to one check and is derived from the active assertion stack.
use super::types::{CertificationMode, Model};
use super::{Solver, SolverResult};
use crate::prelude::*;
use nixie_core::ast::{sequence::SeqOp, traversal::get_children};
use nixie_core::{SortId, SortKind, TermId, TermKind, TermManager};
use num_traits::ToPrimitive;

const MAX_ELEMENTS: usize = 4096;

fn element(tm: &TermManager, sort: SortId) -> Option<SortId> {
    match tm.sorts.get(sort)?.kind {
        SortKind::Seq(e) => Some(e),
        _ => None,
    }
}

/// Includes sequences inside containers, which this slice must decline.
pub(super) fn contains(roots: &[TermId], tm: &TermManager) -> bool {
    if !tm.sorts.has_sequences() {
        return false;
    }
    let mut stack = roots.to_vec();
    let mut seen = FxHashSet::default();
    let mut sorts = Vec::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let Some(t) = tm.get(t) else {
            continue;
        };
        if matches!(t.kind, TermKind::Sequence(..)) {
            return true;
        }
        sorts.push(t.sort);
        stack.extend(get_children(&t.kind));
    }
    let mut seen = FxHashSet::default();
    while let Some(s) = sorts.pop() {
        if !seen.insert(s) {
            continue;
        }
        match tm.sorts.get(s).map(|s| &s.kind) {
            Some(SortKind::Seq(_)) => return true,
            Some(SortKind::Array { domain, range }) => {
                sorts.push(*domain);
                sorts.push(*range);
            }
            Some(SortKind::Set(e) | SortKind::Bag(e)) => sorts.push(*e),
            Some(SortKind::Parametric { args, .. }) => sorts.extend(args.iter().copied()),
            Some(SortKind::Datatype(_)) => {
                if let Some(name) = tm.sorts.datatype_name(s)
                    && let Some(d) = tm.sorts.get_datatype(name)
                {
                    for c in &d.constructors {
                        sorts.extend(c.selectors.iter().map(|(_, s)| *s));
                    }
                }
            }
            _ => {}
        }
    }
    false
}

fn value(tm: &mut TermManager, sort: SortId, xs: &[TermId]) -> Option<TermId> {
    if xs.is_empty() {
        return tm.mk_sequence(SeqOp::Empty(sort), &[]).ok();
    }
    let units: Option<Vec<_>> = xs
        .iter()
        .map(|&x| tm.mk_sequence(SeqOp::Unit, &[x]).ok())
        .collect();
    tm.mk_sequence(SeqOp::Concat, &units?).ok()
}

/// Flatten a constructor value without descending into its elements.
fn list(tm: &TermManager, t: TermId) -> Option<Vec<TermId>> {
    let mut stack = vec![t];
    let mut out = Vec::new();
    while let Some(t) = stack.pop() {
        match &tm.get(t)?.kind {
            TermKind::Sequence(SeqOp::Empty(_), a) if a.is_empty() => {}
            TermKind::Sequence(SeqOp::Unit, a) if a.len() == 1 => out.push(a[0]),
            TermKind::Sequence(SeqOp::Concat, a) => stack.extend(a.iter().rev().copied()),
            _ => return None,
        }
        if out.len() + stack.len() > MAX_ELEMENTS {
            return None;
        }
    }
    Some(out)
}

/// Extensional equality, including nested sequence elements, on a heap stack.
fn equal(tm: &mut TermManager, a: TermId, b: TermId) -> Option<TermId> {
    let mut pending = vec![(a, b)];
    let mut conjuncts = Vec::new();
    let mut seen = FxHashSet::default();
    while let Some((a, b)) = pending.pop() {
        if !seen.insert((a, b)) {
            continue;
        }
        if tm.get(a)?.sort != tm.get(b)?.sort {
            return None;
        }
        if element(tm, tm.get(a)?.sort).is_some() {
            let (a, b) = (list(tm, a)?, list(tm, b)?);
            if a.len() != b.len() {
                return Some(tm.mk_false());
            }
            pending.extend(a.into_iter().zip(b));
        } else {
            conjuncts.push(tm.mk_eq(a, b));
        }
        if pending.len() + conjuncts.len() > MAX_ELEMENTS {
            return None;
        }
    }
    Some(tm.mk_and(conjuncts))
}

fn integer(tm: &TermManager, t: TermId) -> Option<num_bigint::BigInt> {
    match &tm.get(t)?.kind {
        TermKind::IntConst(n) => Some(n.clone()),
        _ => None,
    }
}

#[derive(Default)]
struct Reduction {
    definitions: FxHashMap<TermId, TermId>,
    lengths: FxHashMap<TermId, usize>,
    mapped: FxHashMap<TermId, TermId>,
    vars: Vec<TermId>,
}
impl Reduction {
    fn new(roots: &[TermId], tm: &TermManager) -> Self {
        let mut this = Self::default();
        // Only positive top-level conjuncts justify definitions or fixed shapes.
        let mut stack = roots.to_vec();
        let mut seen = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match tm.get(t).map(|t| &t.kind) {
                Some(TermKind::And(a)) => stack.extend(a.iter().copied()),
                Some(TermKind::Eq(a, b)) => {
                    for (a, b) in [(*a, *b), (*b, *a)] {
                        if let Some(t) = tm.get(a) {
                            if matches!(t.kind, TermKind::Var(_))
                                && element(tm, t.sort).is_some()
                                && a != b
                            {
                                this.definitions.entry(a).or_insert(b);
                            }
                            if let TermKind::Sequence(SeqOp::Len, args) = &t.kind
                                && let [s] = args.as_slice()
                                && tm
                                    .get(*s)
                                    .is_some_and(|s| matches!(s.kind, TermKind::Var(_)))
                                && let Some(n) = integer(tm, b).and_then(|n| n.to_usize())
                                && n <= MAX_ELEMENTS
                            {
                                this.lengths.entry(*s).or_insert(n);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        this
    }

    fn lower(&mut self, root: TermId, tm: &mut TermManager) -> Option<TermId> {
        let mut stack = vec![(root, false)];
        let mut active = FxHashSet::default();
        while let Some((id, finish)) = stack.pop() {
            if self.mapped.contains_key(&id) {
                continue;
            }
            let t = tm.get(id)?.clone();
            if let TermKind::Sequence(op, args) = &t.kind {
                let checked = tm.mk_sequence(*op, args).ok()?;
                if tm.get(checked)?.sort != t.sort {
                    return None;
                }
            }
            if !finish {
                if !active.insert(id) {
                    return None;
                } // cyclic sequence definitions
                if matches!(
                    t.kind,
                    TermKind::Forall { .. }
                        | TermKind::Exists { .. }
                        | TermKind::Let { .. }
                        | TermKind::Match { .. }
                ) {
                    return None;
                }
                stack.push((id, true));
                if let Some(&d) = self.definitions.get(&id) {
                    stack.push((d, false));
                } else {
                    stack.extend(get_children(&t.kind).into_iter().rev().map(|c| (c, false)));
                }
                continue;
            }
            active.remove(&id);
            let result = if let Some(&d) = self.definitions.get(&id) {
                self.vars.push(id);
                *self.mapped.get(&d)?
            } else if matches!(t.kind, TermKind::Var(_)) && element(tm, t.sort).is_some() {
                let n = *self.lengths.get(&id)?;
                let e = element(tm, t.sort)?;
                if element(tm, e).is_some() {
                    return None;
                }
                let mut xs = Vec::new();
                for _ in 0..n {
                    // Collision-free even if a client deliberately used our prefix.
                    let mut serial = tm.len();
                    let x = loop {
                        let name = tm.intern_str(&format!("@native.seq.element.{serial}"));
                        let kind = TermKind::Var(name);
                        if tm.find_interned(&kind, e).is_none() {
                            break tm.intern_term(kind, e);
                        }
                        serial = serial.checked_add(1)?;
                    };
                    self.vars.push(x);
                    xs.push(x);
                }
                self.vars.push(id);
                value(tm, t.sort, &xs)?
            } else {
                let rebuilt = tm.rebuild_children_with(t.kind.clone(), t.sort, &|c| {
                    self.mapped.get(&c).copied().unwrap_or(c)
                });
                let node = tm.get(rebuilt)?.clone();
                match node.kind {
                    TermKind::Sequence(op, a) => match (op, a.as_slice()) {
                        (SeqOp::Empty(_), []) => rebuilt,
                        (SeqOp::Unit, [_]) => rebuilt,
                        (SeqOp::Concat, _) => {
                            let xs = list(tm, rebuilt)?;
                            value(tm, t.sort, &xs)?
                        }
                        (SeqOp::Len, [s]) => {
                            tm.mk_int(num_bigint::BigInt::from(list(tm, *s)?.len()))
                        }
                        (SeqOp::Nth, [s, i]) => {
                            let xs = list(tm, *s)?;
                            let i = integer(tm, *i)?.to_usize()?;
                            *xs.get(i)?
                        }
                        (SeqOp::Extract, [s, i, n]) => {
                            let xs = list(tm, *s)?;
                            let start = integer(tm, *i)?;
                            let n = integer(tm, *n)?;
                            let xs = match start.to_usize() {
                                Some(i) if i < xs.len() && n > 0.into() => {
                                    &xs[i..i + n.to_usize().unwrap_or(usize::MAX).min(xs.len() - i)]
                                }
                                _ => &[],
                            };
                            value(tm, t.sort, xs)?
                        }
                        (SeqOp::Update, [s, i, r]) => {
                            let mut xs = list(tm, *s)?;
                            let ys = list(tm, *r)?;
                            if let Some(i) = integer(tm, *i)?.to_usize().filter(|i| *i < xs.len()) {
                                for (x, y) in xs[i..].iter_mut().zip(ys) {
                                    *x = y;
                                }
                            }
                            value(tm, t.sort, &xs)?
                        }
                        _ => return None,
                    },
                    TermKind::Eq(a, b) if element(tm, tm.get(a)?.sort).is_some() => {
                        equal(tm, a, b)?
                    }
                    TermKind::Distinct(a)
                        if a.first()
                            .and_then(|a| tm.get(*a))
                            .and_then(|t| element(tm, t.sort))
                            .is_some() =>
                    {
                        if a.len().saturating_mul(a.len().saturating_sub(1)) / 2 > MAX_ELEMENTS {
                            return None;
                        }
                        let mut cs = Vec::new();
                        for (i, &x) in a.iter().enumerate() {
                            for &b in &a[i + 1..] {
                                let eq = equal(tm, x, b)?;
                                cs.push(tm.mk_not(eq));
                            }
                        }
                        tm.mk_and(cs)
                    }
                    TermKind::Var(_) => {
                        self.vars.push(id);
                        rebuilt
                    }
                    _ => {
                        // No native sequence may leak into the underlying solver,
                        // including arrays/UFs with a sequence in their signature.
                        if contains(&[rebuilt], tm) {
                            return None;
                        }
                        rebuilt
                    }
                }
            };
            if tm.get(result)?.sort != t.sort {
                return None;
            }
            self.mapped.insert(id, result);
        }
        self.mapped.get(&root).copied()
    }
}

impl Solver {
    pub(super) fn check_sequences(&mut self, tm: &mut TermManager) -> Option<SolverResult> {
        if !contains(&self.certificate_assertions, tm) {
            return None;
        }
        self.invalidate_results();
        // No proof-producing sequence rewrite rule has been implemented yet.
        if self.config.proof
            || self.config.certification_mode == CertificationMode::Certified
            || self.user_state.active()
            || self.logic.as_deref().is_some_and(|logic| logic != "ALL")
        {
            return Some(SolverResult::Unknown);
        }
        let roots: Vec<_> = self
            .certificate_assertions
            .clone()
            .into_iter()
            .map(|t| self.expand_lets(t, tm))
            .collect();
        let mut reduction = Reduction::new(&roots, tm);
        let lowered: Option<Vec<_>> = roots.iter().map(|&t| reduction.lower(t, tm)).collect();
        let Some(lowered) = lowered else {
            return Some(SolverResult::Unknown);
        };
        if contains(&lowered, tm) {
            return Some(SolverResult::Unknown);
        }
        let mut solver = Solver::with_config(self.config.clone());
        for t in lowered {
            solver.assert(t, tm);
        }
        let result = solver.check(tm);
        if result != SolverResult::Sat {
            return Some(result);
        }
        let Some(mut model) = solver.model().cloned() else {
            return Some(SolverResult::Unknown);
        };
        // Complete only variables, never native compound expressions.
        for &v in &reduction.vars {
            let Some(t) = tm.get(v) else {
                return Some(SolverResult::Unknown);
            };
            if element(tm, t.sort).is_none() && model.get(v).is_none() {
                if let Some(d) = super::model_builder::ground_default_term(tm, t.sort) {
                    model.set(v, d);
                } else {
                    return Some(SolverResult::Unknown);
                }
            }
        }
        for &v in &reduction.vars {
            if let Some(&s) = reduction.mapped.get(&v)
                && tm.get(v).and_then(|t| element(tm, t.sort)).is_some()
            {
                let Some(val) = evaluate(&model, s, tm) else {
                    return Some(SolverResult::Unknown);
                };
                model.set(v, val);
            }
        }
        // Independently execute every ORIGINAL assertion, not the reduced copy.
        for &root in &roots {
            let Some(v) = evaluate(&model, root, tm) else {
                return Some(SolverResult::Unknown);
            };
            if !tm.get(v).is_some_and(|t| matches!(t.kind, TermKind::True)) {
                return Some(SolverResult::Unknown);
            }
        }
        self.model = Some(model);
        self.last_check = Some((self.goal_fingerprint(), SolverResult::Sat));
        Some(SolverResult::Sat)
    }
}

/// Independent interpreter used for model publication and public model queries.
/// It reads model assignments only for variables and ordinary scalar terms;
/// native operators are always executed from their operands.
pub(super) fn evaluate(model: &Model, root: TermId, tm: &mut TermManager) -> Option<TermId> {
    let mut values = FxHashMap::default();
    let mut sequences: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
    let mut active = FxHashSet::default();
    let mut stack = vec![(root, false)];
    while let Some((id, done)) = stack.pop() {
        if values.contains_key(&id) {
            continue;
        }
        let t = tm.get(id)?.clone();
        let assignment = if matches!(t.kind, TermKind::Var(_)) {
            model.get(id).filter(|v| *v != id)
        } else {
            None
        };
        if !done {
            if !active.insert(id) {
                return None;
            }
            stack.push((id, true));
            if let Some(v) = assignment {
                stack.push((v, false));
            } else {
                stack.extend(get_children(&t.kind).into_iter().rev().map(|c| (c, false)));
            }
            continue;
        }
        active.remove(&id);
        if let Some(v) = assignment {
            if tm.get(v)?.sort != t.sort {
                return None;
            }
            values.insert(id, *values.get(&v)?);
            if let Some(xs) = sequences.get(&v).cloned() {
                sequences.insert(id, xs);
            }
            continue;
        }
        let v = match &t.kind {
            TermKind::Sequence(op, args) => {
                let checked = tm.mk_sequence(*op, args).ok()?;
                if tm.get(checked)?.sort != t.sort {
                    return None;
                }
                let xs = match (*op, args.as_slice()) {
                    (SeqOp::Empty(_), []) => Vec::new(),
                    (SeqOp::Unit, [a]) => vec![*values.get(a)?],
                    (SeqOp::Concat, _) => {
                        let mut all = Vec::new();
                        for a in args {
                            all.extend_from_slice(sequences.get(a)?);
                            if all.len() > MAX_ELEMENTS {
                                return None;
                            }
                        }
                        all
                    }
                    (SeqOp::Len, [a]) => {
                        values.insert(
                            id,
                            tm.mk_int(num_bigint::BigInt::from(sequences.get(a)?.len())),
                        );
                        continue;
                    }
                    (SeqOp::Nth, [a, i]) => {
                        let index = integer(tm, *values.get(i)?)?.to_usize()?;
                        let v = *sequences.get(a)?.get(index)?;
                        // A sequence-valued nth is a constructor value already
                        // evaluated as an element; recover its concrete spine.
                        if element(tm, t.sort).is_some() {
                            sequences.insert(id, list(tm, v)?);
                        }
                        values.insert(id, v);
                        continue;
                    }
                    (SeqOp::Extract, [a, i, n]) => {
                        let a = sequences.get(a)?;
                        let start = integer(tm, *values.get(i)?)?;
                        let count = integer(tm, *values.get(n)?)?;
                        // Filter by exact integer inequalities. Unlike the
                        // reducer this never converts the requested endpoints.
                        a.iter()
                            .enumerate()
                            .filter(|(k, _)| {
                                let k = num_bigint::BigInt::from(*k);
                                start >= 0.into() && k >= start && k < &start + &count
                            })
                            .map(|(_, v)| *v)
                            .collect()
                    }
                    (SeqOp::Update, [a, i, b]) => {
                        let a = sequences.get(a)?;
                        let b = sequences.get(b)?;
                        let start = integer(tm, *values.get(i)?)?;
                        let mut out = Vec::with_capacity(a.len());
                        for (k, &old) in a.iter().enumerate() {
                            let offset = num_bigint::BigInt::from(k) - &start;
                            let replacement = if start >= 0.into() {
                                offset.to_usize().and_then(|j| b.get(j)).copied()
                            } else {
                                None
                            };
                            out.push(replacement.unwrap_or(old));
                        }
                        out
                    }
                    _ => return None,
                };
                let v = value(tm, t.sort, &xs)?;
                sequences.insert(id, xs);
                v
            }
            TermKind::Eq(a, b) if sequences.contains_key(a) || sequences.contains_key(b) => {
                let a = *values.get(a)?;
                let b = *values.get(b)?;
                // Canonical concrete sequence values have constructor equality.
                // For elements whose equality still needs theory evaluation,
                // compare them individually, including nested sequences.
                concrete_equal(model, tm, a, b)?
            }
            TermKind::Distinct(args) => {
                if args.len().saturating_mul(args.len().saturating_sub(1)) / 2 > MAX_ELEMENTS {
                    return None;
                }
                let mut all = true;
                for (i, a) in args.iter().enumerate() {
                    for b in &args[i + 1..] {
                        let eq = concrete_equal(model, tm, *values.get(a)?, *values.get(b)?)?;
                        match tm.get(eq)?.kind {
                            TermKind::True => all = false,
                            TermKind::False => {}
                            _ => return None,
                        }
                    }
                }
                if all { tm.mk_true() } else { tm.mk_false() }
            }
            TermKind::Forall { .. }
            | TermKind::Exists { .. }
            | TermKind::Let { .. }
            | TermKind::Match { .. } => return None,
            _ => {
                let rebuilt = tm.rebuild_children_with(t.kind.clone(), t.sort, &|c| {
                    values.get(&c).copied().unwrap_or(c)
                });
                if contains(&[rebuilt], tm) {
                    return None;
                }
                model.eval_scalar(rebuilt, tm)
            }
        };
        values.insert(id, v);
    }
    values.get(&root).copied()
}

fn concrete_equal(model: &Model, tm: &mut TermManager, a: TermId, b: TermId) -> Option<TermId> {
    let mut stack = vec![(a, b)];
    let mut seen = FxHashSet::default();
    while let Some((a, b)) = stack.pop() {
        if !seen.insert((a, b)) {
            continue;
        }
        if tm.get(a)?.sort != tm.get(b)?.sort {
            return None;
        }
        if element(tm, tm.get(a)?.sort).is_some() {
            let (a, b) = (list(tm, a)?, list(tm, b)?);
            if a.len() != b.len() {
                return Some(tm.mk_false());
            }
            stack.extend(a.into_iter().zip(b));
        } else {
            let eq = tm.mk_eq(a, b);
            let eq = model.eval_scalar(eq, tm);
            match tm.get(eq)?.kind {
                TermKind::True => {}
                TermKind::False => return Some(tm.mk_false()),
                _ => return None,
            }
        }
    }
    Some(tm.mk_true())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn interpreter_ignores_fabricated_sequence_operator_assignments() {
        let mut tm = TermManager::new();
        let one = tm.mk_int(1);
        let unit = tm.mk_sequence(SeqOp::Unit, &[one]).expect("unit");
        let len = tm.mk_sequence(SeqOp::Len, &[unit]).expect("length");
        let zero = tm.mk_int(0);
        let mut model = Model::new();
        model.set(len, zero);
        assert_eq!(evaluate(&model, len, &mut tm), Some(one));
        let eq = tm.mk_eq(len, zero);
        assert_eq!(evaluate(&model, eq, &mut tm), Some(tm.mk_false()));
    }
    #[test]
    fn reduction_never_uses_bounds_from_a_disjunction() {
        let mut tm = TermManager::new();
        let s = tm.sorts.seq(tm.sorts.int_sort);
        let q = tm.mk_var("q", s);
        let len = tm.mk_sequence(SeqOp::Len, &[q]).expect("length");
        let zero = tm.mk_int(0);
        let one = tm.mk_int(1);
        let a = tm.mk_eq(len, zero);
        let b = tm.mk_eq(len, one);
        let root = tm.mk_or([a, b]);
        let mut reduction = Reduction::new(&[root], &tm);
        assert!(reduction.lengths.is_empty());
        assert!(reduction.lower(root, &mut tm).is_none());
    }
    #[test]
    fn sequence_constructor_spines_use_heap_stacks() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut tm = TermManager::new();
                let int = tm.sorts.int_sort;
                let sort = tm.sorts.seq(int);
                let empty = tm.mk_sequence(SeqOp::Empty(sort), &[]).expect("empty");
                let mut seq = empty;
                for _ in 0..5000 {
                    seq = tm
                        .mk_sequence(SeqOp::Concat, &[empty, seq])
                        .expect("concat");
                }
                let len = tm.mk_sequence(SeqOp::Len, &[seq]).expect("len");
                let zero = tm.mk_int(0);
                assert_eq!(evaluate(&Model::new(), len, &mut tm), Some(zero));
                let eq = tm.mk_eq(len, zero);
                let mut solver = Solver::new();
                solver.assert(eq, &mut tm);
                assert_eq!(solver.check(&mut tm), SolverResult::Sat);
            })
            .expect("thread")
            .join()
            .expect("no stack overflow");
    }
}
