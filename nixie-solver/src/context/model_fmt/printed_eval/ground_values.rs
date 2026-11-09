//! A closed quantifier-free assertion over datatype, enumeration and
//! uninterpreted-sort VALUES, decided by value — without interning a term
//! (re-fix pass 17, decision (79)(a)).
//!
//! # Why the quantifier-free net needs it
//!
//! The exact evaluator the printed-model checks run on
//! (`solver::array_completion_certify::evaluate_closed`, the model gate's
//! evaluator) has no value for a datatype- or uninterpreted-sorted term, so
//! an equality, a `distinct`, an `ite` or an array read of such a sort stays
//! open there.  The quantifier-free datatype net (decision (72)(a),
//! `Context::withhold_a_falsifying_datatype_model`) therefore only ever saw
//! the comparisons the term builder had already folded while the printed
//! model was substituted in — two literal constructor applications, which
//! `mk_eq` decides at construction (`#P2b-76`).  Whether a check's model was
//! caught depended on how its printed tables happened to read: `gen_dt.py`
//! seed 30093154 `d00239`'s first model prints `h` as an `ite` chain over its
//! argument, so `(= (cons (k (v nil)) l3) (h (+ 1 (- 1))))` closed to an
//! equality between an `ite` whose conditions compare `(+ 1 (- 1))` with
//! numerals and the list `(cons 5 (cons 2 nil))` — open, published, and
//! false; its second and third checks closed the same assertion to two
//! literal constructor applications, which folded to `false` and were
//! withheld.  A `distinct` of two constructor values was never decided at
//! all, and an array whose element sort is a datatype, an enumeration or an
//! uninterpreted sort (`#P2b-89`) was never read.
//!
//! # What is read
//!
//! A closed term is evaluated to a VALUE: a scalar (the model gate's own
//! exact evaluator reads every sub-term with no datatype- or
//! uninterpreted-sorted part, so every scalar operator means here what it
//! means there), a constructor applied to values, or an uninterpreted-sort
//! witness (`@uc_S_n`, read back as a constant of its own).  On top of the
//! scalars: a constructor application, a selector or tester of a constructor
//! value, the Boolean connectives (three-valued: an open operand decides
//! nothing it could change), an `ite` by its condition, a read of a printed
//! store chain by comparing its keys with the index, and `+`, `-`, `*`, the
//! order comparisons over numbers whose operands are values.  Two values
//! compare constructor by constructor and then field by field, numbers by
//! their exact value, witnesses by identity: two distinct witnesses are two
//! distinct elements, which is what the printed model says and the
//! hypothesis every certificate of it takes.  Anything else is open.  Sound
//! for the reason every evaluation of the printed model is: each step reads
//! the model as printed.
//!
//! # Why nothing is interned
//!
//! The reading runs at every quantifier-free `sat` over such a sort, and the
//! search of a LATER check is sensitive to what the term arena holds (the
//! note on `(get-value)`'s printed reading says the same): a first version
//! that rewrote the assertion through the term builder moved later checks'
//! trajectories — `gen_dt.py` seed 30093154 `d00261`'s third check printed
//! a model pass 16 printed and z3 confirms, and that version found another.
//! So the reading borrows the term manager shared and builds nothing.

use super::*;
use crate::prelude::{FxHashMap, FxHashSet};
use crate::solver::EvalVal;
use nixie_core::interner::Spur;

/// Nesting depth of a closed term the reading follows (a deeper term is
/// open; the round's assertions are a few dozen levels deep).
const MAX_GROUND_DEPTH: u32 = 100_000;

/// Constructor fields one value comparison may visit.
const MAX_VALUE_PAIRS: usize = 4_096;

/// Entries one array value may hold (a longer printed store chain is open).
const MAX_ARRAY_ENTRIES: usize = 4_096;

/// The value of a closed term.
#[derive(Clone, Debug, PartialEq)]
enum GroundValue {
    /// A Boolean, number or bit-vector.
    Scalar(EvalVal),
    /// A constructor applied to values.
    Constructor(Spur, Vec<usize>),
    /// An uninterpreted-sort witness: an element of its own.
    Witness(TermId),
    /// An array (re-fix pass 18, decision (85)): its default, its stored
    /// entries (the latest first), and whether its index sort is infinite
    /// (`Int` / `Real`: two arrays whose defaults differ then differ at an
    /// index neither names).  An array of arrays reads by value at every
    /// level (recheck 17's `b05`, `#P2b-89` one level down).
    Array {
        default: usize,
        entries: Vec<(usize, usize)>,
        infinite_index: bool,
    },
}

impl Context {
    pub(in crate::context) fn ground_witness(
        &self,
        term: TermId,
        witnesses: &FxHashSet<TermId>,
    ) -> Option<TermId> {
        let mut reader = GroundReader {
            ctx: self,
            witnesses,
            memo: FxHashMap::default(),
            valued_sorts: FxHashMap::default(),
            values: Vec::new(),
        };
        match reader.evaluate(term)? {
            GroundValue::Witness(value) => Some(value),
            _ => None,
        }
    }

    /// The truth value of `term` — a closed Boolean term, with no free
    /// symbol but the uninterpreted-sort witnesses in `witnesses` — read by
    /// value (see the module docs); `None` where the reading is open.
    pub(in crate::context) fn ground_truth(
        &self,
        term: TermId,
        witnesses: &FxHashSet<TermId>,
    ) -> Option<bool> {
        let mut reader = GroundReader {
            ctx: self,
            witnesses,
            memo: FxHashMap::default(),
            valued_sorts: FxHashMap::default(),
            values: Vec::new(),
        };
        match reader.evaluate(term)? {
            GroundValue::Scalar(EvalVal::Bool(holds)) => Some(holds),
            _ => None,
        }
    }
}

/// One reading of closed terms: memoised per term, so a shared sub-term is
/// read once.
struct GroundReader<'a> {
    ctx: &'a Context,
    witnesses: &'a FxHashSet<TermId>,
    memo: FxHashMap<TermId, Option<GroundValue>>,
    values: Vec<GroundValue>,
    /// Whether a term has a datatype- or uninterpreted-sorted part (or a
    /// witness), by term.
    valued_sorts: FxHashMap<TermId, bool>,
}

impl GroundReader<'_> {
    fn evaluate(&mut self, term: TermId) -> Option<GroundValue> {
        let mut stack = vec![(term, false)];
        let mut seen = FxHashSet::default();
        while let Some((term, expanded)) = stack.pop() {
            if expanded {
                let valued = self.witnesses.contains(&term)
                    || self.ctx.terms.get(term).is_none_or(|node| {
                        matches!(
                            self.ctx.terms.sorts.get(node.sort).map(|s| &s.kind),
                            Some(SortKind::Datatype(_) | SortKind::Uninterpreted(_))
                        ) || nixie_core::ast::traversal::get_children(&node.kind)
                            .iter()
                            .any(|child| self.valued_sorts.get(child).copied().unwrap_or(true))
                    });
                self.valued_sorts.insert(term, valued);
                let value = self.compute(term, 0);
                self.memo.insert(term, value);
            } else if seen.insert(term) {
                if seen.len() > MAX_GROUND_DEPTH as usize {
                    return None;
                }
                stack.push((term, true));
                if let Some(node) = self.ctx.terms.get(term) {
                    for child in nixie_core::ast::traversal::get_children(&node.kind) {
                        stack.push((child, false));
                    }
                }
            }
        }
        self.value(term, 0)
    }

    fn value(&self, term: TermId, _depth: u32) -> Option<GroundValue> {
        self.memo.get(&term).cloned().flatten()
    }

    fn store_value(&mut self, value: GroundValue) -> usize {
        let id = self.values.len();
        self.values.push(value);
        id
    }

    fn compute(&mut self, term: TermId, depth: u32) -> Option<GroundValue> {
        if self.witnesses.contains(&term) {
            return Some(GroundValue::Witness(term));
        }
        let data = self.ctx.terms.get(term)?;
        let sort = data.sort;
        let kind = data.kind.clone();
        // A scalar sub-term with no datatype or uninterpreted part is the
        // model gate's to read: every operator means what it means there.
        if self.is_scalar_sort(sort)
            && !self.has_valued_sort(term, depth)
            && let Some(value) = crate::solver::array_completion_certify::evaluate_closed_value_pure(
                &self.ctx.solver,
                term,
                &self.ctx.terms,
            )
        {
            return Some(GroundValue::Scalar(value));
        }
        let next = depth + 1;
        match kind {
            TermKind::True => Some(boolean(true)),
            TermKind::False => Some(boolean(false)),
            TermKind::DtConstructor { constructor, args } => {
                let mut fields = Vec::with_capacity(args.len());
                for arg in args {
                    let value = self.value(arg, next)?;
                    fields.push(self.store_value(value));
                }
                Some(GroundValue::Constructor(constructor, fields))
            }
            TermKind::DtSelector { selector, arg } => {
                let GroundValue::Constructor(built, fields) = self.value(arg, next)? else {
                    return None;
                };
                let arg_sort = self.ctx.terms.get(arg)?.sort;
                let position = self.field_position(arg_sort, built, selector)?;
                self.values.get(*fields.get(position)?).cloned()
            }
            TermKind::DtTester { constructor, arg } => {
                let GroundValue::Constructor(built, _) = self.value(arg, next)? else {
                    return None;
                };
                let arg_sort = self.ctx.terms.get(arg)?.sort;
                self.has_constructor(arg_sort, constructor)
                    .then(|| boolean(built == constructor))
            }
            TermKind::Not(inner) => Some(boolean(!self.truth(inner, next)?)),
            TermKind::And(args) => {
                let mut open = false;
                for arg in args {
                    match self.truth(arg, next) {
                        Some(false) => return Some(boolean(false)),
                        Some(true) => {}
                        None => open = true,
                    }
                }
                (!open).then(|| boolean(true))
            }
            TermKind::Or(args) => {
                let mut open = false;
                for arg in args {
                    match self.truth(arg, next) {
                        Some(true) => return Some(boolean(true)),
                        Some(false) => {}
                        None => open = true,
                    }
                }
                (!open).then(|| boolean(false))
            }
            TermKind::Implies(premise, conclusion) => {
                match (self.truth(premise, next), self.truth(conclusion, next)) {
                    (Some(false), _) | (_, Some(true)) => Some(boolean(true)),
                    (Some(true), Some(false)) => Some(boolean(false)),
                    _ => None,
                }
            }
            TermKind::Xor(left, right) => {
                let (a, b) = (self.truth(left, next)?, self.truth(right, next)?);
                Some(boolean(a != b))
            }
            TermKind::Ite(condition, then_branch, else_branch) => {
                match self.truth(condition, next) {
                    Some(true) => self.value(then_branch, next),
                    Some(false) => self.value(else_branch, next),
                    None => {
                        let a = self.value(then_branch, next)?;
                        let b = self.value(else_branch, next)?;
                        (self.equal(&a, &b) == Some(true)).then_some(a)
                    }
                }
            }
            TermKind::Eq(left, right) => {
                let a = self.value(left, next)?;
                let b = self.value(right, next)?;
                Some(boolean(self.equal(&a, &b)?))
            }
            TermKind::Distinct(args) => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.value(arg, next)?);
                }
                for (position, a) in values.iter().enumerate() {
                    for b in values.iter().skip(position + 1) {
                        if self.equal(a, b)? {
                            return Some(boolean(false));
                        }
                    }
                }
                Some(boolean(true))
            }
            TermKind::Select(array, index) => {
                let index = self.value(index, next)?;
                self.read(array, &index, next)
            }
            TermKind::Store(inner, key, stored) => {
                let GroundValue::Array {
                    default,
                    mut entries,
                    infinite_index,
                } = self.value(inner, next)?
                else {
                    return None;
                };
                if entries.len() >= MAX_ARRAY_ENTRIES {
                    return None;
                }
                let key = self.value(key, next)?;
                let stored = self.value(stored, next)?;
                let key = self.store_value(key);
                let stored = self.store_value(stored);
                entries.insert(0, (key, stored));
                Some(GroundValue::Array {
                    default,
                    entries,
                    infinite_index,
                })
            }
            TermKind::Apply { func, args }
                if args.len() == 1
                    && self.ctx.terms.resolve_str(func) == nixie_core::smtlib::CONST_ARRAY_FUNC =>
            {
                let default = self.value(*args.first()?, next)?;
                Some(GroundValue::Array {
                    default: self.store_value(default),
                    entries: Vec::new(),
                    infinite_index: self.infinite_index(sort),
                })
            }
            TermKind::Neg(inner) => {
                let number = self.number(inner, next)?;
                Some(number_value(-number))
            }
            TermKind::Add(args) => {
                let mut sum = num_rational::BigRational::from_integer(0.into());
                for arg in args {
                    let term = self.number(arg, next)?;
                    sum += term;
                }
                Some(number_value(sum))
            }
            TermKind::Mul(args) => {
                let mut product = num_rational::BigRational::from_integer(1.into());
                for arg in args {
                    let factor = self.number(arg, next)?;
                    product *= factor;
                }
                Some(number_value(product))
            }
            TermKind::Sub(left, right) => {
                let (a, b) = (self.number(left, next)?, self.number(right, next)?);
                Some(number_value(a - b))
            }
            TermKind::Lt(left, right) => self.compare(left, right, next, |a, b| a < b),
            TermKind::Le(left, right) => self.compare(left, right, next, |a, b| a <= b),
            TermKind::Gt(left, right) => self.compare(left, right, next, |a, b| a > b),
            TermKind::Ge(left, right) => self.compare(left, right, next, |a, b| a >= b),
            _ => None,
        }
    }

    /// The Boolean value of `term`, where it is read.
    fn truth(&mut self, term: TermId, depth: u32) -> Option<bool> {
        match self.value(term, depth)? {
            GroundValue::Scalar(EvalVal::Bool(holds)) => Some(holds),
            _ => None,
        }
    }

    /// The number `term` reads, where it is read.
    fn number(&mut self, term: TermId, depth: u32) -> Option<num_rational::BigRational> {
        match self.value(term, depth)? {
            GroundValue::Scalar(value) => value.to_big(),
            _ => None,
        }
    }

    /// An order comparison of two numbers.
    fn compare(
        &mut self,
        left: TermId,
        right: TermId,
        depth: u32,
        holds: impl Fn(&num_rational::BigRational, &num_rational::BigRational) -> bool,
    ) -> Option<GroundValue> {
        let (a, b) = (self.number(left, depth)?, self.number(right, depth)?);
        Some(boolean(holds(&a, &b)))
    }

    /// The value `(select array index)` reads where `array` is a printed
    /// store chain (or an `ite` over such chains): the entry whose key equals
    /// `index`, passing every key that differs, then the constant array's
    /// default.
    fn read(&mut self, array: TermId, index: &GroundValue, depth: u32) -> Option<GroundValue> {
        let mut level = array;
        let mut steps = depth;
        loop {
            steps += 1;
            if steps > MAX_GROUND_DEPTH {
                return None;
            }
            match self.ctx.terms.get(level)?.kind.clone() {
                TermKind::Store(inner, key, value) => {
                    let key = self.value(key, steps)?;
                    if self.equal(&key, index)? {
                        return self.value(value, steps);
                    }
                    level = inner;
                }
                TermKind::Ite(condition, then_branch, else_branch) => {
                    level = if self.truth(condition, steps)? {
                        then_branch
                    } else {
                        else_branch
                    };
                }
                TermKind::Apply { func, args }
                    if args.len() == 1
                        && self.ctx.terms.resolve_str(func)
                            == nixie_core::smtlib::CONST_ARRAY_FUNC =>
                {
                    return self.value(*args.first()?, steps);
                }
                // Any other array term — a read of an array of arrays —
                // is read by value.
                _ => {
                    let array = self.value(level, steps)?;
                    return self.read_value(&array, index);
                }
            }
        }
    }

    /// The value the array value `array` reads at `index`: the latest entry
    /// whose key equals it, passing every key that differs, then the
    /// default; open where a key comparison is.
    fn read_value(&mut self, array: &GroundValue, index: &GroundValue) -> Option<GroundValue> {
        let GroundValue::Array {
            default, entries, ..
        } = array
        else {
            return None;
        };
        for (key, stored) in entries {
            let key = self.values.get(*key)?.clone();
            if self.equal(&key, index)? {
                return self.values.get(*stored).cloned();
            }
        }
        self.values.get(*default).cloned()
    }

    /// Whether the index sort of the array sort `sort` is infinite.
    fn infinite_index(&self, sort: SortId) -> bool {
        let sorts = &self.ctx.terms.sorts;
        let Some(SortKind::Array { domain, .. }) = sorts.get(sort).map(|s| &s.kind) else {
            return false;
        };
        matches!(
            sorts.get(*domain).map(|s| &s.kind),
            Some(SortKind::Int | SortKind::Real)
        )
    }

    /// Whether two values are one: `Some(true)` / `Some(false)` where they
    /// decide it, `None` otherwise (see the module docs).
    fn equal(&mut self, left: &GroundValue, right: &GroundValue) -> Option<bool> {
        let root = (
            self.store_value(left.clone()),
            self.store_value(right.clone()),
        );
        let mut stack = vec![root];
        let mut ready: FxHashMap<(usize, usize), Option<bool>> = FxHashMap::default();
        let mut work = 0usize;
        while let Some(pair) = stack.pop() {
            work += 1;
            if work > MAX_VALUE_PAIRS {
                return None;
            }
            if ready.contains_key(&pair) {
                continue;
            }
            let answer =
                self.equal_ready(pair, &mut |a, b| ready.get(&(a, b)).copied().ok_or((a, b)));
            match answer {
                Ok(value) => {
                    ready.insert(pair, value);
                }
                Err(child) => {
                    stack.push(pair);
                    stack.push(child);
                }
            }
        }
        ready.remove(&root).flatten()
    }

    fn equal_ready(
        &self,
        pair: (usize, usize),
        lookup: &mut dyn FnMut(usize, usize) -> Result<Option<bool>, (usize, usize)>,
    ) -> Result<Option<bool>, (usize, usize)> {
        let (Some(a), Some(b)) = (self.values.get(pair.0), self.values.get(pair.1)) else {
            return Ok(None);
        };
        Ok(match (a, b) {
            (GroundValue::Scalar(a), GroundValue::Scalar(b)) => match (a.to_big(), b.to_big()) {
                (Some(a), Some(b)) => Some(a == b),
                _ => Some(a == b),
            },
            (GroundValue::Witness(a), GroundValue::Witness(b)) => Some(a == b),
            (GroundValue::Constructor(a, fa), GroundValue::Constructor(b, fb)) => {
                if a != b {
                    return Ok(Some(false));
                }
                if fa.len() != fb.len() {
                    return Ok(None);
                }
                let mut open = false;
                for (&a, &b) in fa.iter().zip(fb) {
                    match lookup(a, b)? {
                        Some(false) => return Ok(Some(false)),
                        Some(true) => {}
                        None => open = true,
                    }
                }
                (!open).then_some(true)
            }
            (
                GroundValue::Array {
                    default: da,
                    entries: ea,
                    infinite_index,
                },
                GroundValue::Array {
                    default: db,
                    entries: eb,
                    ..
                },
            ) => {
                let mut open = false;
                for &(key, _) in ea.iter().chain(eb) {
                    let a = self.read_ready(*da, ea, key, lookup)?;
                    let b = self.read_ready(*db, eb, key, lookup)?;
                    match (a, b) {
                        (Some(a), Some(b)) => match lookup(a, b)? {
                            Some(false) => return Ok(Some(false)),
                            Some(true) => {}
                            None => open = true,
                        },
                        _ => open = true,
                    }
                }
                match lookup(*da, *db)? {
                    Some(true) => (!open).then_some(true),
                    Some(false) if *infinite_index => Some(false),
                    _ => None,
                }
            }
            _ => None,
        })
    }

    fn read_ready(
        &self,
        default: usize,
        entries: &[(usize, usize)],
        index: usize,
        lookup: &mut dyn FnMut(usize, usize) -> Result<Option<bool>, (usize, usize)>,
    ) -> Result<Option<usize>, (usize, usize)> {
        for &(key, value) in entries {
            match lookup(key, index)? {
                Some(true) => return Ok(Some(value)),
                Some(false) => {}
                None => return Ok(None),
            }
        }
        Ok(Some(default))
    }

    /// The position of `selector` among `constructor`'s fields in the
    /// datatype `sort`; `None` when `constructor` has no such field (the
    /// selector is then unspecified there, and the reading is open).
    fn field_position(&self, sort: SortId, constructor: Spur, selector: Spur) -> Option<usize> {
        let sorts = &self.ctx.terms.sorts;
        let def = sorts.get_datatype(sorts.datatype_name(sort)?)?;
        let declared = def
            .constructors
            .iter()
            .find(|c| sorts.resolve_spur(c.name) == self.ctx.terms.resolve_str(constructor))?;
        declared.selectors.iter().position(|&(field, _)| {
            sorts.resolve_spur(field) == self.ctx.terms.resolve_str(selector)
        })
    }

    /// Whether `constructor` is a constructor of the datatype `sort`.
    fn has_constructor(&self, sort: SortId, constructor: Spur) -> bool {
        let sorts = &self.ctx.terms.sorts;
        sorts
            .datatype_name(sort)
            .and_then(|name| sorts.get_datatype(name))
            .is_some_and(|def| {
                def.constructors
                    .iter()
                    .any(|c| sorts.resolve_spur(c.name) == self.ctx.terms.resolve_str(constructor))
            })
    }

    fn is_scalar_sort(&self, sort: SortId) -> bool {
        matches!(
            self.ctx.terms.sorts.get(sort).map(|s| &s.kind),
            Some(SortKind::Bool | SortKind::Int | SortKind::Real | SortKind::BitVec(_))
        )
    }

    /// Whether `term` has a datatype- or uninterpreted-sorted sub-term (or a
    /// witness) — memoised, depth-bounded (a term past the bound counts as
    /// having one, so it is read structurally rather than handed whole to
    /// the scalar evaluator).
    fn has_valued_sort(&self, term: TermId, _depth: u32) -> bool {
        self.valued_sorts.get(&term).copied().unwrap_or(true)
    }
}

fn boolean(holds: bool) -> GroundValue {
    GroundValue::Scalar(EvalVal::Bool(holds))
}

fn number_value(number: num_rational::BigRational) -> GroundValue {
    GroundValue::Scalar(EvalVal::NumBig(Box::new(number)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deep_constructor_values_use_a_flat_arena() {
        std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let (mut ctx, sort, _) = context();
                let mut a = ctx.terms.mk_dt_constructor("nil", [], sort);
                let mut b = a;
                let zero = ctx.terms.mk_int(0);
                let one = ctx.terms.mk_int(1);
                a = ctx.terms.mk_dt_constructor("cons", [zero, a], sort);
                b = ctx.terms.mk_dt_constructor("cons", [one, b], sort);
                for _ in 0..20_000 {
                    a = ctx.terms.mk_dt_constructor("cons", [zero, a], sort);
                    b = ctx.terms.mk_dt_constructor("cons", [zero, b], sort);
                }
                let equality = ctx
                    .terms
                    .intern_term(TermKind::Eq(a, b), ctx.terms.sorts.bool_sort);
                // The comparison work cap may decline, but construction, copying,
                // comparison, and destruction must never recurse on the list.
                assert_ne!(
                    ctx.ground_truth(equality, &FxHashSet::default()),
                    Some(true)
                );
            })
            .expect("worker")
            .join()
            .expect("heap walk");
    }

    #[test]
    fn exact_big_values_compare_across_numeric_representations() {
        let (mut ctx, sort, _) = context();
        let tail = ctx.terms.mk_dt_constructor("nil", [], sort);
        let huge = ctx.terms.mk_int(num_bigint::BigInt::from(1) << 129usize);
        let cons = ctx.terms.mk_dt_constructor("cons", [huge, tail], sort);
        let select = ctx
            .terms
            .mk_dt_selector("hd", cons, ctx.terms.sorts.int_sort);
        let equality = ctx
            .terms
            .intern_term(TermKind::Eq(select, huge), ctx.terms.sorts.bool_sort);
        assert_eq!(
            ctx.ground_truth(equality, &FxHashSet::default()),
            Some(true)
        );
    }

    /// A context with the list datatype `L`, an uninterpreted sort `U`, and
    /// one constant of each declared: `(context, L, U)`.
    fn context() -> (Context, SortId, SortId) {
        let mut ctx = Context::new();
        let script = "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
                      (declare-sort U 0)\n(declare-const l1 L)\n(declare-const u1 U)\n";
        assert!(ctx.execute_script(script).is_ok());
        let sort_of = |ctx: &Context, name: &str| {
            ctx.declared_consts
                .iter()
                .find(|decl| decl.name == name)
                .map(|decl| decl.sort)
        };
        let (Some(list), Some(uninterpreted)) = (sort_of(&ctx, "l1"), sort_of(&ctx, "u1")) else {
            panic!("the declarations are in scope");
        };
        (ctx, list, uninterpreted)
    }

    /// `[n₀, n₁, …]` as a constructor term.
    fn list(ctx: &mut Context, sort: SortId, items: &[i64]) -> TermId {
        let mut out = ctx.terms.mk_dt_constructor("nil", [], sort);
        for &item in items.iter().rev() {
            let head = ctx.terms.mk_int(item);
            out = ctx.terms.mk_dt_constructor("cons", [head, out], sort);
        }
        out
    }

    /// `d00239`'s first check: an equality between an `ite` over
    /// `(+ 1 (- 1))` and a list, and a `distinct` of lists — both open to the
    /// exact evaluator, both read by value, and nothing interned for it.
    #[test]
    fn an_ite_over_a_closed_condition_and_a_distinct_of_lists_are_read() {
        let (mut ctx, sort, _) = context();
        let none = FxHashSet::default();
        let one = ctx.terms.mk_int(1);
        let minus_one = ctx.terms.mk_neg(one);
        let zero_sum = ctx.terms.mk_add([one, minus_one]);
        let zero = ctx.terms.mk_int(0);
        let condition = ctx.terms.mk_eq(zero_sum, zero);
        let then_list = list(&mut ctx, sort, &[2, 2]);
        let else_list = list(&mut ctx, sort, &[6]);
        let chosen = ctx.terms.mk_ite(condition, then_list, else_list);
        let other = list(&mut ctx, sort, &[5, 2]);
        let equality = ctx.terms.mk_eq(chosen, other);
        let same = list(&mut ctx, sort, &[2, 2]);
        let holds = ctx.terms.mk_eq(chosen, same);
        let a = list(&mut ctx, sort, &[3]);
        let b = list(&mut ctx, sort, &[0, 2]);
        let apart = ctx.terms.mk_distinct([a, b]);
        let c = list(&mut ctx, sort, &[3]);
        let repeated = ctx.terms.mk_distinct([a, b, c]);
        let interned = ctx.terms.len();
        assert_eq!(ctx.ground_truth(equality, &none), Some(false));
        assert_eq!(ctx.ground_truth(holds, &none), Some(true));
        assert_eq!(ctx.ground_truth(apart, &none), Some(true));
        assert_eq!(ctx.ground_truth(repeated, &none), Some(false));
        assert_eq!(ctx.terms.len(), interned, "the reading interns no term");
    }

    /// A read of a printed store chain into a datatype: by value, at a key
    /// it names and at one it does not (the default); a selector of the
    /// value read.
    #[test]
    fn a_read_of_a_list_valued_store_chain_is_decided() {
        let (mut ctx, sort, _) = context();
        let none = FxHashSet::default();
        let int = ctx.terms.sorts.int_sort;
        let array_sort = ctx.terms.sorts.array(int, sort);
        let nil = list(&mut ctx, sort, &[]);
        let base = ctx
            .terms
            .mk_apply(nixie_core::smtlib::CONST_ARRAY_FUNC, [nil], array_sort);
        let zero = ctx.terms.mk_int(0);
        let one_list = list(&mut ctx, sort, &[1]);
        let chain = ctx.terms.mk_store(base, zero, one_list);
        let read_zero = ctx.terms.mk_select(chain, zero);
        let two_list = list(&mut ctx, sort, &[2]);
        let wrong = ctx.terms.mk_eq(read_zero, two_list);
        assert_eq!(ctx.ground_truth(wrong, &none), Some(false), "a[0] = [1]");
        let three = ctx.terms.mk_int(3);
        let read_three = ctx.terms.mk_select(chain, three);
        let default = ctx.terms.mk_eq(read_three, nil);
        assert_eq!(ctx.ground_truth(default, &none), Some(true), "a[3] = nil");
        let shorter = list(&mut ctx, sort, &[]);
        let longer = list(&mut ctx, sort, &[1, 1]);
        let apart = ctx.terms.mk_distinct([read_zero, shorter, longer]);
        assert_eq!(
            ctx.ground_truth(apart, &none),
            Some(true),
            "[1], [], [1, 1]"
        );
    }

    /// An array of arrays into an uninterpreted sort (recheck 17's `b05`,
    /// `#P2b-89` one level down): a read of a read is decided by value, and
    /// two array values compare by their entries and defaults.
    #[test]
    fn a_read_of_a_read_of_an_array_of_arrays_is_decided() {
        let (mut ctx, _, uninterpreted) = context();
        let int = ctx.terms.sorts.int_sort;
        let inner_sort = ctx.terms.sorts.array(int, uninterpreted);
        let outer_sort = ctx.terms.sorts.array(int, inner_sort);
        let w0 = ctx.terms.mk_var("w0", uninterpreted);
        let w1 = ctx.terms.mk_var("w1", uninterpreted);
        let witnesses: FxHashSet<TermId> = [w0, w1].into_iter().collect();
        let zero = ctx.terms.mk_int(0);
        let one = ctx.terms.mk_int(1);
        let inner_base = ctx
            .terms
            .mk_apply(nixie_core::smtlib::CONST_ARRAY_FUNC, [w0], inner_sort);
        let outer_base = ctx.terms.mk_apply(
            nixie_core::smtlib::CONST_ARRAY_FUNC,
            [inner_base],
            outer_sort,
        );
        // `a = [0 ↦ [0 ↦ w0]]`, read at `a[0][0]` and at `a[1][0]` (the
        // outer default, whose default is `w0` as well).
        let entry = ctx.terms.mk_store(inner_base, zero, w0);
        let printed = ctx.terms.mk_store(outer_base, zero, entry);
        let at_zero = ctx.terms.mk_select(printed, zero);
        let read_zero = ctx.terms.mk_select(at_zero, zero);
        let at_one = ctx.terms.mk_select(printed, one);
        let read_one = ctx.terms.mk_select(at_one, zero);
        let holds = ctx.terms.mk_eq(read_zero, w0);
        assert_eq!(ctx.ground_truth(holds, &witnesses), Some(true));
        let other = ctx.terms.mk_eq(read_one, w1);
        assert_eq!(
            ctx.ground_truth(other, &witnesses),
            Some(false),
            "a[1][0] reads the default w0, not w1"
        );
        // Two inner arrays: equal by value though spelled apart, and apart
        // where an entry differs; over `Int`, two defaults that differ make
        // them differ.
        let same = ctx.terms.mk_eq(at_zero, entry);
        assert_eq!(ctx.ground_truth(same, &witnesses), Some(true));
        let changed = ctx.terms.mk_store(inner_base, zero, w1);
        let apart = ctx.terms.mk_eq(at_zero, changed);
        assert_eq!(ctx.ground_truth(apart, &witnesses), Some(false));
        let other_base = ctx
            .terms
            .mk_apply(nixie_core::smtlib::CONST_ARRAY_FUNC, [w1], inner_sort);
        let defaults = ctx.terms.mk_eq(inner_base, other_base);
        assert_eq!(ctx.ground_truth(defaults, &witnesses), Some(false));
    }

    /// Witnesses compare by identity (two witnesses are two elements); a
    /// declared constant is no value, and its comparison stays open.
    #[test]
    fn witnesses_compare_by_identity_and_a_symbol_stays_open() {
        let (mut ctx, sort, uninterpreted) = context();
        let w0 = ctx.terms.mk_var("w0", uninterpreted);
        let w1 = ctx.terms.mk_var("w1", uninterpreted);
        let witnesses: FxHashSet<TermId> = [w0, w1].into_iter().collect();
        let apart = ctx.terms.mk_eq(w0, w1);
        assert_eq!(ctx.ground_truth(apart, &witnesses), Some(false));
        let symbol = ctx.terms.mk_var("l1", sort);
        let one_list = list(&mut ctx, sort, &[1]);
        let open = ctx.terms.mk_eq(symbol, one_list);
        assert_eq!(ctx.ground_truth(open, &witnesses), None);
        let u1 = ctx.terms.mk_var("u1", uninterpreted);
        let open = ctx.terms.mk_eq(w0, u1);
        assert_eq!(ctx.ground_truth(open, &witnesses), None);
    }
}
