//! Exact concrete evaluation of ground terms under a candidate interpretation.
//!
//! Every satisfiability verdict produced by the nonlinear search paths in this
//! crate is a *claim about a witness*, and this module is what turns the claim
//! into a check. Given a candidate interpretation (`Interpretation`) that
//! pins every free leaf a formula mentions, `holds_under` recomputes each
//! assertion from its leaves in exact arithmetic and reports whether the whole
//! set is definitely true.
//!
//! Three properties are deliberate:
//!
//! * **Exact.** Values are `BigRational`, never a machine float and never a
//!   fixed-width rational, so no intermediate product silently wraps or
//!   rounds. A search that overflows a machine word cannot launder a wrong
//!   answer past this gate.
//! * **Total or nothing.** Anything the evaluator does not understand — an
//!   operator outside its grammar, a leaf the interpretation left unassigned,
//!   a division by zero (which SMT-LIB leaves uninterpreted, so this module
//!   refuses to invent a value for it) — yields [`None`], never a guess. A
//!   caller that cannot obtain a definite `true` must answer `Unknown`.
//! * **Iterative.** The walk uses an explicit work stack with memoisation over
//!   the hash-consed DAG, so an assertion nested a hundred thousand levels deep
//!   is answered rather than overflowing the native stack, and a shared
//!   sub-term is evaluated once no matter how many parents reference it.
//!
//! ## Arrays
//!
//! An array value is a *root* (the free array symbol the value ultimately
//! rests on) plus the sequence of writes layered over it. `select` resolves a
//! read by scanning the writes newest-first and falling back to the root's
//! own cell table in the interpretation — read-over-write, evaluated rather
//! than axiomatised. Index values must be numeric; anything else is outside
//! the grammar and answers `None`.

use nixie_core::ast::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;

/// A value in a candidate interpretation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// An Int- or Real-sorted value. Integrality is the caller's invariant:
    /// this module only guarantees exact rational arithmetic.
    Num(BigRational),
    /// A Bool-sorted value.
    Truth(bool),
    /// An array value: a root symbol plus the writes layered over it.
    Mapping(ArrayValue),
}

impl Value {
    /// The numeric payload, or `None` for a non-numeric value.
    #[must_use]
    pub fn as_num(&self) -> Option<&BigRational> {
        match self {
            Value::Num(n) => Some(n),
            _ => None,
        }
    }

    /// The Boolean payload, or `None` for a non-Boolean value.
    #[must_use]
    pub fn as_truth(&self) -> Option<bool> {
        match self {
            Value::Truth(b) => Some(*b),
            _ => None,
        }
    }
}

/// An array value: reads resolve against `writes` newest-first, then against
/// the root symbol's cell table in the [`Interpretation`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayValue {
    /// The free array symbol this value is layered on.
    pub root: TermId,
    /// Writes applied over `root`, oldest first; a later write shadows an
    /// earlier one at the same index.
    pub writes: Vec<(BigRational, Value)>,
}

/// A candidate interpretation: a value for every free leaf a formula mentions.
///
/// "Leaf" means what this evaluator cannot decompose: a `Var`, an
/// uninterpreted application, a `div`/`mod` node it declines to interpret, and
/// an array root's individual cells.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Interpretation {
    /// Numeric leaves.
    numeric: FxHashMap<TermId, BigRational>,
    /// Boolean leaves.
    truths: FxHashMap<TermId, bool>,
    /// Cells of free array symbols, keyed by `(root, index value)`.
    cells: BTreeMap<(TermId, BigRational), Value>,
    /// Value returned for a cell of `root` that `cells` does not list.
    fallbacks: FxHashMap<TermId, Value>,
}

impl Interpretation {
    /// An interpretation that assigns nothing.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Pin a numeric leaf.
    pub fn pin_num(&mut self, term: TermId, value: BigRational) {
        self.numeric.insert(term, value);
    }

    /// Pin a numeric leaf to an integer.
    pub fn pin_int(&mut self, term: TermId, value: BigInt) {
        self.numeric.insert(term, BigRational::from_integer(value));
    }

    /// Pin a Boolean leaf.
    pub fn pin_truth(&mut self, term: TermId, value: bool) {
        self.truths.insert(term, value);
    }

    /// Pin one cell of a free array symbol.
    pub fn pin_cell(&mut self, root: TermId, index: BigRational, value: Value) {
        self.cells.insert((root, index), value);
    }

    /// Set the value every unlisted cell of `root` takes.
    pub fn pin_fallback(&mut self, root: TermId, value: Value) {
        self.fallbacks.insert(root, value);
    }

    /// The pinned value of a numeric leaf, if any.
    #[must_use]
    pub fn num_of(&self, term: TermId) -> Option<&BigRational> {
        self.numeric.get(&term)
    }

    /// The pinned value of a Boolean leaf, if any.
    #[must_use]
    pub fn truth_of(&self, term: TermId) -> Option<bool> {
        self.truths.get(&term).copied()
    }

    /// Every pinned numeric leaf, in unspecified order.
    pub fn numeric_entries(&self) -> impl Iterator<Item = (TermId, &BigRational)> {
        self.numeric.iter().map(|(&t, v)| (t, v))
    }

    /// Every pinned Boolean leaf, in unspecified order.
    pub fn truth_entries(&self) -> impl Iterator<Item = (TermId, bool)> {
        self.truths.iter().map(|(&t, &v)| (t, v))
    }

    /// How many numeric leaves are pinned.
    #[must_use]
    pub fn num_count(&self) -> usize {
        self.numeric.len()
    }

    /// Resolve a read of `root` at `index`.
    fn read_root(&self, root: TermId, index: &BigRational) -> Option<Value> {
        if let Some(v) = self.cells.get(&(root, index.clone())) {
            return Some(v.clone());
        }
        self.fallbacks.get(&root).cloned()
    }
}

/// Whether some term in `formulas` evaluates to a definite **`false`** under
/// `interp`.
///
/// This is [`holds_under`]'s strict-negative dual, and the right question for
/// a caller that already has an independent licence for its `Sat` verdict and
/// is deciding whether to *publish* a candidate witness as the model: an
/// evaluator that abstains on an opaque leaf (an array read the interpretation
/// says nothing about, an unpinned Boolean) must not veto the publication —
/// abstention is "this check cannot help", not "the witness is wrong" — while
/// a definite `false` the witness *does* determine is a proof that publishing
/// it would print values contradicting the very assertions they answer.
///
/// (Upstream v0.3.3's `adopt_nl_witness` uses the all-positive form because
/// its dispatcher's verdict *is* the verification; this fork's nonlinear
/// model searches carry their own goal-specific verification, so publication
/// is gated on the weaker, still-sound "definitely not a model" test.)
#[must_use]
pub fn refuted_under(formulas: &[TermId], manager: &TermManager, interp: &Interpretation) -> bool {
    let mut memo: FxHashMap<TermId, Value> = FxHashMap::default();
    formulas.iter().any(|&f| {
        matches!(
            evaluate_memo(f, manager, interp, &mut memo),
            Some(Value::Truth(false))
        )
    })
}

/// Whether every term in `formulas` evaluates to a definite `true` under
/// `interp`.
///
/// `false` covers all three failure modes at once — some formula is definitely
/// false, or some formula could not be evaluated at all — because a caller
/// about to report `Sat` must treat them identically: only a *complete*
/// positive verification licenses the verdict.
/// A fourth failure mode is folded in on top of those three: an interpretation
/// that is not a *function* on the uninterpreted applications the formulas
/// mention. This module reads an application's value out of the
/// interpretation by term identity, so `f(x)` and `f(y)` can be pinned apart
/// even where the same interpretation makes `x` and `y` equal — a witness that
/// the candidate is not a model at all, however many formulas it satisfies.
/// `congruence_holds` rejects exactly that.
#[must_use]
pub fn holds_under(formulas: &[TermId], manager: &TermManager, interp: &Interpretation) -> bool {
    let mut memo: FxHashMap<TermId, Value> = FxHashMap::default();
    let every_formula_true = formulas.iter().all(|&f| {
        matches!(
            evaluate_memo(f, manager, interp, &mut memo),
            Some(Value::Truth(true))
        )
    });
    every_formula_true && congruence_holds(formulas, manager, interp, &memo)
}

/// Whether the evaluated values respect congruence: two applications of the
/// same symbol whose arguments denote pairwise-identical elements must carry
/// the same value.
///
/// Only applications reachable from `formulas` matter, and only those whose
/// arguments all evaluated — an application the walk never demanded cannot
/// affect any formula's truth value.
///
/// "Identical element" is decided by [`same_value`], not by [`Value`]'s derived
/// `PartialEq`. The two differ on arrays: `store(store(a, i, v), i, v)` and
/// `store(a, i, v)` carry different write lists but denote the same array, and
/// a structural comparison would call their `f`-applications unrelated and let
/// a real congruence violation through. Where `same_value` cannot decide (two
/// distinct array roots, whose unlisted cells the interpretation says nothing
/// about) this refuses — `false`, the same answer it gives an outright
/// violation, because both leave the caller without a verified model.
fn congruence_holds(
    formulas: &[TermId],
    manager: &TermManager,
    interp: &Interpretation,
    memo: &FxHashMap<TermId, Value>,
) -> bool {
    let mut groups: Vec<(nixie_core::interner::Spur, Vec<Value>, Value)> = Vec::new();
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    let mut stack: Vec<TermId> = formulas.to_vec();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(node) = manager.get(id) else {
            continue;
        };
        if let TermKind::Apply { func, args } = &node.kind {
            let argument_values: Option<Vec<Value>> =
                args.iter().map(|a| memo.get(a).cloned()).collect();
            if let (Some(argument_values), Some(own)) = (argument_values, memo.get(&id)) {
                for (other_func, other_args, other_value) in &groups {
                    if *other_func != *func {
                        continue;
                    }
                    match denote_same_tuple(other_args, &argument_values, interp) {
                        // Same arguments: the two applications must agree, and
                        // an undecidable agreement is not an agreement.
                        Some(true) => {
                            if same_value(other_value, own, interp) != Some(true) {
                                return false;
                            }
                        }
                        Some(false) => {}
                        // Cannot tell whether congruence even applies here.
                        None => return false,
                    }
                }
                groups.push((*func, argument_values, own.clone()));
            }
        }
        push_operands(&node.kind, &mut stack);
        if let TermKind::Ite(cond, then_branch, else_branch) = &node.kind {
            stack.push(*cond);
            stack.push(*then_branch);
            stack.push(*else_branch);
        }
    }
    true
}

/// Whether two argument tuples denote pairwise-identical elements.
///
/// A single definitely-different pair settles the whole tuple, so that answer
/// wins over any undecidable pair elsewhere in it; `None` is reserved for a
/// tuple with no decided difference but at least one pair [`same_value`]
/// declined to rule on.
fn denote_same_tuple(left: &[Value], right: &[Value], interp: &Interpretation) -> Option<bool> {
    if left.len() != right.len() {
        return Some(false);
    }
    let mut undecided = false;
    for (a, b) in left.iter().zip(right.iter()) {
        // Structural identity already implies denotational identity (same
        // root, same writes in the same order), so the cheap test stands in
        // for the semantic one whenever it succeeds.
        if a == b {
            continue;
        }
        match same_value(a, b, interp) {
            Some(true) => {}
            Some(false) => return Some(false),
            None => undecided = true,
        }
    }
    if undecided { None } else { Some(true) }
}

/// Evaluate one term under `interp`, or `None` when the evaluator declines.
#[must_use]
pub fn evaluate(term: TermId, manager: &TermManager, interp: &Interpretation) -> Option<Value> {
    let mut memo: FxHashMap<TermId, Value> = FxHashMap::default();
    evaluate_memo(term, manager, interp, &mut memo)
}

/// Evaluate `term`, reusing (and extending) an existing memo table.
///
/// The walk is an explicit post-order over the hash-consed DAG. `Ite` is the
/// one lazy operator: its condition is evaluated first and only the selected
/// branch is then demanded, so a branch that is undefined under this
/// interpretation (a division by zero the condition guards against, say) does
/// not sink the whole evaluation.
pub fn evaluate_memo(
    term: TermId,
    manager: &TermManager,
    interp: &Interpretation,
    memo: &mut FxHashMap<TermId, Value>,
) -> Option<Value> {
    /// What the walker is doing with a node this visit.
    enum Task {
        /// Schedule the node's operands, then revisit it.
        Open(TermId),
        /// All operands are memoised: fold them into the node's own value.
        Close(TermId),
    }

    let mut work: Vec<Task> = vec![Task::Open(term)];
    while let Some(task) = work.pop() {
        match task {
            Task::Open(id) => {
                if memo.contains_key(&id) {
                    continue;
                }
                let kind = manager.get(id).map(|t| t.kind.clone())?;
                // `Ite` demands its condition first and its branch second, so
                // it re-opens rather than scheduling every operand up front.
                if let TermKind::Ite(cond, then_branch, else_branch) = kind {
                    match memo.get(&cond) {
                        Some(Value::Truth(taken)) => {
                            let branch = if *taken { then_branch } else { else_branch };
                            work.push(Task::Close(id));
                            work.push(Task::Open(branch));
                        }
                        Some(_) => return None,
                        None => {
                            work.push(Task::Open(id));
                            work.push(Task::Open(cond));
                        }
                    }
                    continue;
                }
                let mut operands: Vec<TermId> = Vec::new();
                push_operands(&kind, &mut operands);
                work.push(Task::Close(id));
                for operand in operands {
                    work.push(Task::Open(operand));
                }
            }
            Task::Close(id) => {
                if memo.contains_key(&id) {
                    continue;
                }
                let value = fold_node(id, manager, interp, memo)?;
                memo.insert(id, value);
            }
        }
    }
    memo.get(&term).cloned()
}

/// The operands a node needs evaluated before it can be folded. A node whose
/// kind is a leaf (or is outside the grammar, and will be refused when folded)
/// contributes none.
fn push_operands(kind: &TermKind, out: &mut Vec<TermId>) {
    match kind {
        TermKind::Not(a) | TermKind::Neg(a) => out.push(*a),
        TermKind::And(args) | TermKind::Or(args) | TermKind::Add(args) | TermKind::Mul(args) => {
            out.extend(args.iter().copied());
        }
        TermKind::Distinct(args) => out.extend(args.iter().copied()),
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Select(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::Store(a, i, v) => {
            out.push(*a);
            out.push(*i);
            out.push(*v);
        }
        // An application's own value is opaque, but its arguments still have
        // to be evaluated: [`congruence_holds`] compares applications by the
        // *values* of their arguments, not by argument syntax.
        TermKind::Apply { args, .. } => out.extend(args.iter().copied()),
        // `Ite` is handled by the caller (lazy branch demand); every other
        // kind is either a leaf or outside the grammar.
        _ => {}
    }
}

/// Compute a node's value from its already-memoised operands.
fn fold_node(
    id: TermId,
    manager: &TermManager,
    interp: &Interpretation,
    memo: &FxHashMap<TermId, Value>,
) -> Option<Value> {
    let node = manager.get(id)?;
    let kind = &node.kind;
    let get = |t: TermId| memo.get(&t).cloned();
    let num = |t: TermId| memo.get(&t).and_then(Value::as_num).cloned();
    let truth = |t: TermId| memo.get(&t).and_then(Value::as_truth);

    match kind {
        TermKind::True => Some(Value::Truth(true)),
        TermKind::False => Some(Value::Truth(false)),
        TermKind::IntConst(n) => Some(Value::Num(BigRational::from_integer(n.clone()))),
        TermKind::RealConst(r) => Some(Value::Num(BigRational::new(
            BigInt::from(*r.numer()),
            BigInt::from(*r.denom()),
        ))),

        TermKind::Not(a) => truth(*a).map(|b| Value::Truth(!b)),
        TermKind::And(args) => {
            let mut acc = true;
            for &a in args {
                acc &= truth(a)?;
            }
            Some(Value::Truth(acc))
        }
        TermKind::Or(args) => {
            let mut acc = false;
            for &a in args {
                acc |= truth(a)?;
            }
            Some(Value::Truth(acc))
        }
        TermKind::Xor(a, b) => Some(Value::Truth(truth(*a)? ^ truth(*b)?)),
        TermKind::Implies(a, b) => Some(Value::Truth(!truth(*a)? || truth(*b)?)),
        TermKind::Ite(cond, then_branch, else_branch) => {
            // The *condition* picks the branch — never "whichever branch is
            // already memoised". The memo spans the whole hash-consed DAG, so
            // the branch this `ite` did not select is frequently in it anyway
            // (some other parent demanded the identical sub-term), and reading
            // it back would report the wrong branch's value. `truth` collapses
            // "condition not memoised" and "condition is not Boolean" into
            // `None`, both of which are reasons to decline rather than guess.
            get(if truth(*cond)? {
                *then_branch
            } else {
                *else_branch
            })
        }

        TermKind::Eq(a, b) => same_value(&get(*a)?, &get(*b)?, interp).map(Value::Truth),
        TermKind::Distinct(args) => {
            let values: Vec<Value> = args.iter().map(|&a| get(a)).collect::<Option<_>>()?;
            for (i, left) in values.iter().enumerate() {
                for right in &values[i + 1..] {
                    if same_value(left, right, interp)? {
                        return Some(Value::Truth(false));
                    }
                }
            }
            Some(Value::Truth(true))
        }

        TermKind::Neg(a) => {
            let v = num(*a)?;
            // i64 fast path: an integral machine-width negation stays
            // integral, so the bignum normalization never runs.  i64::MIN
            // (checked_neg None) and wide values fall back exactly.
            let fast = v
                .to_i64()
                .filter(|_| v.is_integer())
                .and_then(|x| x.checked_neg())
                .map(|x| BigRational::from_integer(BigInt::from(x)));
            Some(Value::Num(fast.unwrap_or_else(|| -v)))
        }
        TermKind::Add(args) => {
            // Dual-track accumulator: stay in i64 while every operand and
            // the running sum are machine-width integers (denominator 1, so
            // the Ratio normalization gcd — a BigInt div_rem per bignum
            // Add/Mul — never runs); promote to BigRational on the first
            // non-integral, wide, or overflowing element and continue
            // exactly from there.  Checked ops only, so every corner falls
            // back rather than wrapping.  (~13% of a QF_NIA ground-eval
            // profile was that gcd; scan #2 item #3.)
            let mut small: Option<i64> = Some(0);
            let mut acc = BigRational::zero();
            for &a in args {
                let v = num(a)?;
                let vi = v.to_i64().filter(|_| v.is_integer());
                match (small, vi) {
                    (Some(s), Some(x)) => match s.checked_add(x) {
                        Some(s2) => small = Some(s2),
                        None => {
                            acc += BigRational::from_integer(BigInt::from(s));
                            acc += v;
                            small = None;
                        }
                    },
                    (Some(s), None) => {
                        acc += BigRational::from_integer(BigInt::from(s));
                        acc += v;
                        small = None;
                    }
                    (None, _) => acc += v,
                }
            }
            Some(Value::Num(
                small.map_or(acc, |s| BigRational::from_integer(BigInt::from(s))),
            ))
        }
        TermKind::Mul(args) => {
            // Same dual-track discipline as Add.  No short-circuit on zero:
            // every operand is still evaluated (`num(a)?`), matching the old
            // fold exactly including its None propagation.
            let mut small: Option<i64> = Some(1);
            let mut acc = BigRational::one();
            for &a in args {
                let v = num(a)?;
                let vi = v.to_i64().filter(|_| v.is_integer());
                match (small, vi) {
                    (Some(s), Some(x)) => match s.checked_mul(x) {
                        Some(s2) => small = Some(s2),
                        None => {
                            acc *= BigRational::from_integer(BigInt::from(s));
                            acc *= v;
                            small = None;
                        }
                    },
                    (Some(s), None) => {
                        acc *= BigRational::from_integer(BigInt::from(s));
                        acc *= v;
                        small = None;
                    }
                    (None, _) => acc *= v,
                }
            }
            Some(Value::Num(
                small.map_or(acc, |s| BigRational::from_integer(BigInt::from(s))),
            ))
        }
        TermKind::Sub(a, b) => {
            let x = num(*a)?;
            let y = num(*b)?;
            let fast = (|| {
                let xi = x.to_i64().filter(|_| x.is_integer())?;
                let yi = y.to_i64().filter(|_| y.is_integer())?;
                xi.checked_sub(yi)
                    .map(|d| BigRational::from_integer(BigInt::from(d)))
            })();
            Some(Value::Num(fast.unwrap_or_else(|| x - y)))
        }
        TermKind::Div(a, b) => euclidean(manager, node.sort, num(*a)?, num(*b)?, DivPart::Quotient),
        TermKind::Mod(a, b) => euclidean(manager, node.sort, num(*a)?, num(*b)?, DivPart::Residue),
        TermKind::Lt(a, b) => Some(Value::Truth(num(*a)? < num(*b)?)),
        TermKind::Le(a, b) => Some(Value::Truth(num(*a)? <= num(*b)?)),
        TermKind::Gt(a, b) => Some(Value::Truth(num(*a)? > num(*b)?)),
        TermKind::Ge(a, b) => Some(Value::Truth(num(*a)? >= num(*b)?)),

        TermKind::Store(base, index, value) => {
            let Value::Mapping(mut layered) = get(*base)? else {
                return None;
            };
            layered.writes.push((num(*index)?, get(*value)?));
            Some(Value::Mapping(layered))
        }
        TermKind::Select(base, index) => {
            let Value::Mapping(layered) = get(*base)? else {
                return None;
            };
            let at = num(*index)?;
            for (written_at, written) in layered.writes.iter().rev() {
                if *written_at == at {
                    return Some(written.clone());
                }
            }
            interp.read_root(layered.root, &at)
        }

        // Leaves. An array-sorted leaf becomes a root with no writes; a
        // numeric or Boolean one is read straight out of the interpretation.
        _ => leaf_value(id, manager, interp),
    }
}

/// Which half of the Euclidean division pair a node asks for.
enum DivPart {
    /// `div`.
    Quotient,
    /// `mod`.
    Residue,
}

/// Evaluate `div` / `mod`.
///
/// Integer operands follow SMT-LIB's Euclidean convention (`0 ≤ r < |n|`,
/// whatever the operands' signs); Real operands use exact field division. A
/// zero divisor is left *uninterpreted* by the standard, so rather than invent
/// a value that a later `(get-value ...)` might contradict, this returns
/// `None` and the caller degrades to `Unknown`.
fn euclidean(
    manager: &TermManager,
    sort: nixie_core::sort::SortId,
    dividend: BigRational,
    divisor: BigRational,
    part: DivPart,
) -> Option<Value> {
    if divisor.is_zero() {
        return None;
    }
    if sort != manager.sorts.int_sort {
        return match part {
            DivPart::Quotient => Some(Value::Num(dividend / divisor)),
            // `mod` is an integer operator; a Real-sorted one is outside the
            // grammar this module claims to evaluate.
            DivPart::Residue => None,
        };
    }
    if !dividend.is_integer() || !divisor.is_integer() {
        return None;
    }
    // i64 fast path: AProVE/VeryMax-style workloads evaluate div/mod on
    // machine-width operands constantly, and the bignum `/`-`*`-`-` below
    // was ~14% of a QF_NIA profile (scan #2 item #3).  Same Euclidean
    // convention as the bignum path; `checked_*` falls back to exact bignums
    // on every corner (zero divisor handled above, i64::MIN / -1, overflow).
    if let (Some(mi), Some(ni)) = (
        num_traits::ToPrimitive::to_i64(dividend.numer()),
        num_traits::ToPrimitive::to_i64(divisor.numer()),
    ) && let (Some(quotient), Some(residue)) = (mi.checked_div(ni), mi.checked_rem(ni))
    {
        // Truncating division first, then correct the remainder into
        // `[0, |n|)` — the same convention as the bignum path below.  All
        // arithmetic stays checked: any corner (i64::MIN/-1 overflowed in
        // checked_div above; the corrections are in-range by construction)
        // falls through to the exact bignum path instead of wrapping.
        let corrected = if residue < 0 {
            if ni > 0 {
                Some((quotient.checked_sub(1)?, residue.checked_add(ni)?))
            } else {
                Some((quotient.checked_add(1)?, residue.checked_sub(ni)?))
            }
        } else {
            Some((quotient, residue))
        };
        if let Some((quotient, residue)) = corrected {
            return Some(Value::Num(BigRational::from_integer(BigInt::from(
                match part {
                    DivPart::Quotient => quotient,
                    DivPart::Residue => residue,
                },
            ))));
        }
    }
    let m = dividend.to_integer();
    let n = divisor.to_integer();
    // Truncating division first, then correct the remainder into `[0, |n|)`.
    let mut quotient = &m / &n;
    let mut residue = &m - &quotient * &n;
    if residue.is_negative() {
        if n.is_positive() {
            quotient -= BigInt::one();
            residue += &n;
        } else {
            quotient += BigInt::one();
            residue -= &n;
        }
    }
    Some(Value::Num(BigRational::from_integer(match part {
        DivPart::Quotient => quotient,
        DivPart::Residue => residue,
    })))
}

/// The value of a term the evaluator treats as opaque.
fn leaf_value(id: TermId, manager: &TermManager, interp: &Interpretation) -> Option<Value> {
    let node = manager.get(id)?;
    if manager
        .sorts
        .get(node.sort)
        .is_some_and(|s| matches!(s.kind, nixie_core::sort::SortKind::Array { .. }))
    {
        return Some(Value::Mapping(ArrayValue {
            root: id,
            writes: Vec::new(),
        }));
    }
    if node.sort == manager.sorts.bool_sort {
        return interp.truth_of(id).map(Value::Truth);
    }
    if node.sort == manager.sorts.int_sort || node.sort == manager.sorts.real_sort {
        return interp.num_of(id).cloned().map(Value::Num);
    }
    None
}

/// Whether two values are the same element of their sort.
///
/// Arrays compare *extensionally*, which is what SMT-LIB's `=` means for them:
/// two array values are equal when every index reads the same. Only the finite
/// set of indices either value writes, plus the roots' listed cells, can
/// differ, so the comparison is decidable here — with one exception. Two
/// *distinct* roots differ wherever the interpretation left them unlisted, and
/// this module has no license to declare them equal or unequal on that
/// evidence, so it returns `None` (refuse) rather than guessing.
fn same_value(left: &Value, right: &Value, interp: &Interpretation) -> Option<bool> {
    let mut work = vec![(left, right)];
    let mut undecided = false;
    while let Some((left, right)) = work.pop() {
        match (left, right) {
            (Value::Num(a), Value::Num(b)) => {
                if a != b {
                    return Some(false);
                }
            }
            (Value::Truth(a), Value::Truth(b)) => {
                if a != b {
                    return Some(false);
                }
            }
            (Value::Mapping(a), Value::Mapping(b)) => {
                let mut probes = std::collections::BTreeSet::new();
                probes.extend(a.writes.iter().chain(&b.writes).map(|(index, _)| index));
                probes.extend(interp.cells.keys().filter_map(|(root, index)| {
                    (*root == a.root || *root == b.root).then_some(index)
                }));
                for index in probes {
                    match (
                        read_layered(a, index, interp),
                        read_layered(b, index, interp),
                    ) {
                        (Some(av), Some(bv)) => work.push((av, bv)),
                        _ => undecided = true,
                    }
                }
                if a.root != b.root {
                    match (interp.fallbacks.get(&a.root), interp.fallbacks.get(&b.root)) {
                        (Some(av), Some(bv)) => work.push((av, bv)),
                        _ => undecided = true,
                    }
                }
            }
            _ => undecided = true,
        }
    }
    (!undecided).then_some(true)
}

/// Read one index without cloning a potentially nested array value.
fn read_layered<'a>(
    value: &'a ArrayValue,
    index: &BigRational,
    interp: &'a Interpretation,
) -> Option<&'a Value> {
    value
        .writes
        .iter()
        .rev()
        .find_map(|(at, value)| (at == index).then_some(value))
        .or_else(|| interp.cells.get(&(value.root, index.clone())))
        .or_else(|| interp.fallbacks.get(&value.root))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    #[test]
    fn test_pr31_eval_product_equation() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("qx", int_sort);
        let y = tm.mk_var("qy", int_sort);
        let product = tm.mk_mul(vec![x, y]);
        let twelve = tm.mk_int(12);
        let goal = tm.mk_eq(product, twelve);

        let mut interp = Interpretation::empty();
        interp.pin_int(x, BigInt::from(3));
        interp.pin_int(y, BigInt::from(4));
        assert!(holds_under(&[goal], &tm, &interp));

        let mut wrong = Interpretation::empty();
        wrong.pin_int(x, BigInt::from(3));
        wrong.pin_int(y, BigInt::from(5));
        assert!(!holds_under(&[goal], &tm, &wrong));
    }

    #[test]
    fn test_pr31_eval_unassigned_leaf_refuses() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("ux", int_sort);
        let zero = tm.mk_int(0);
        let goal = tm.mk_ge(x, zero);
        let interp = Interpretation::empty();
        assert_eq!(evaluate(goal, &tm, &interp), None);
        assert!(!holds_under(&[goal], &tm, &interp));
    }

    #[test]
    fn test_pr31_eval_euclidean_div_mod_signs() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let m = tm.mk_var("dm", int_sort);
        let n = tm.mk_var("dn", int_sort);
        let quotient = tm.mk_div(m, n);
        let residue = tm.mk_mod(m, n);

        // (div (- 7) 2) = -4 and (mod (- 7) 2) = 1.
        let mut interp = Interpretation::empty();
        interp.pin_int(m, BigInt::from(-7));
        interp.pin_int(n, BigInt::from(2));
        assert_eq!(
            evaluate(quotient, &tm, &interp).and_then(|v| v.as_num().cloned()),
            Some(rat(-4))
        );
        assert_eq!(
            evaluate(residue, &tm, &interp).and_then(|v| v.as_num().cloned()),
            Some(rat(1))
        );

        // (div 7 (- 2)) = -3 and (mod 7 (- 2)) = 1.
        let mut interp = Interpretation::empty();
        interp.pin_int(m, BigInt::from(7));
        interp.pin_int(n, BigInt::from(-2));
        assert_eq!(
            evaluate(quotient, &tm, &interp).and_then(|v| v.as_num().cloned()),
            Some(rat(-3))
        );
        assert_eq!(
            evaluate(residue, &tm, &interp).and_then(|v| v.as_num().cloned()),
            Some(rat(1))
        );
    }

    /// The i64 fast path in `euclidean` must agree with the exact bignum
    /// fallback on every corner it can take, and must FALL BACK on the
    /// corners it cannot (i64::MIN / -1 overflows the checked machine ops;
    /// wider-than-i64 operands route to bignums directly).  Pins the
    /// equivalence by evaluating the same value pairs through the public
    /// path and comparing against the mathematically expected Euclidean
    /// results (regression for the fast path added in scan #2 item #3).
    #[test]
    fn test_euclidean_fast_path_matches_bignum_fallback() {
        let tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        // (m, n) pairs chosen to hit: both signs, |n| = 1, exact division,
        // correction on both branches, i64 rails, and the overflow fallback.
        let cases: &[(i64, i64)] = &[
            (7, 2),
            (-7, 2),
            (7, -2),
            (-7, -2),
            (6, 3),
            (-6, 3),
            (6, -3),
            (-6, -3),
            (5, 1),
            (5, -1),
            (-5, -1),
            (i64::MAX, 3),
            (i64::MIN + 1, 3),
            (i64::MIN, i64::MAX),
            (i64::MIN, -1), // checked_div overflow: must fall back to bignums
        ];
        for &(m, n) in cases {
            let bm = BigInt::from(m);
            let bn = BigInt::from(n);
            let expected_q = &bm / &bn
                + if (&bm - (&bm / &bn) * &bn).is_negative() {
                    if bn.is_positive() {
                        BigInt::from(-1)
                    } else {
                        BigInt::one()
                    }
                } else {
                    BigInt::zero()
                };
            let expected_r = &bm - &expected_q * &bn;
            // Reference: 0 <= r < |n| by the Euclidean convention.
            assert!(!expected_r.is_negative() && expected_r < bn.abs());

            let q = euclidean(
                &tm,
                int_sort,
                BigRational::from(bm.clone()),
                BigRational::from(bn.clone()),
                DivPart::Quotient,
            )
            .and_then(|v| v.as_num().cloned());
            let r = euclidean(
                &tm,
                int_sort,
                BigRational::from(bm.clone()),
                BigRational::from(bn.clone()),
                DivPart::Residue,
            )
            .and_then(|v| v.as_num().cloned());
            assert_eq!(
                q,
                Some(BigRational::from(expected_q.clone())),
                "quotient {m}/{n}"
            );
            assert_eq!(
                r,
                Some(BigRational::from(expected_r.clone())),
                "residue {m}%{n}"
            );
        }
        // Wider-than-i64 operands route through bignums (the fallback path).
        let big = BigInt::from(i64::MAX as i128 + 7);
        let q = euclidean(
            &tm,
            int_sort,
            BigRational::from(big.clone()),
            BigRational::from_integer(BigInt::from(3)),
            DivPart::Quotient,
        )
        .and_then(|v| v.as_num().cloned());
        assert_eq!(q, Some(BigRational::from_integer(&big / BigInt::from(3))));
    }

    #[test]
    fn test_pr31_eval_zero_divisor_refuses() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let m = tm.mk_var("zm", int_sort);
        let zero = tm.mk_int(0);
        let quotient = tm.mk_div(m, zero);
        let mut interp = Interpretation::empty();
        interp.pin_int(m, BigInt::from(5));
        assert_eq!(evaluate(quotient, &tm, &interp), None);
    }

    #[test]
    fn test_pr31_eval_ite_skips_undefined_branch() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("ix", int_sort);
        let zero = tm.mk_int(0);
        let one = tm.mk_int(1);
        let guard = tm.mk_eq(x, zero);
        let risky = tm.mk_div(one, x);
        let selected = tm.mk_ite(guard, zero, risky);
        let goal = tm.mk_eq(selected, zero);

        // x = 0 takes the safe branch; the `div` by zero is never demanded.
        let mut interp = Interpretation::empty();
        interp.pin_int(x, BigInt::from(0));
        assert!(holds_under(&[goal], &tm, &interp));
    }

    /// An `Ite` must take the value of the branch its *condition* selected,
    /// never of whichever branch happens to be in the shared memo already.
    ///
    /// The shape below is the one that made this go wrong. Terms are
    /// hash-consed, so the literal `5` inside the `ite` and the literal `5` in
    /// the trailing `(= y 5)` conjunct are one and the same node. The walker
    /// folds the conjuncts back-to-front, so `(= y 5)` memoises that shared `5`
    /// *before* the `ite` is folded — and a fold that merely asked "is the then
    /// branch memoised?" then answered `5` for an `ite` whose condition is
    /// false and whose else branch is `7`. That turns an unsatisfiable
    /// assertion into a `true`, i.e. a fabricated model.
    #[test]
    fn test_pr31_ite_memo_respects_condition() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("mx", int_sort);
        let y = tm.mk_var("my", int_sort);
        let zero = tm.mk_int(0);
        let five = tm.mk_int(5);
        let seven = tm.mk_int(7);

        let x_is_zero = tm.mk_eq(x, zero);
        let selected = tm.mk_ite(x_is_zero, five, seven);
        let x_is_nonzero = tm.mk_not(x_is_zero);
        let y_matches_ite = tm.mk_eq(y, selected);
        let y_is_five = tm.mk_eq(y, five);
        let conjunction = tm.mk_and(vec![x_is_nonzero, y_matches_ite, y_is_five]);

        // x = 1 falsifies the condition, so the `ite` is 7 and `y` would have
        // to be both 7 and 5. No interpretation satisfies this.
        let mut interp = Interpretation::empty();
        interp.pin_int(x, BigInt::from(1));
        interp.pin_int(y, BigInt::from(5));
        assert!(
            !holds_under(&[conjunction], &tm, &interp),
            "x != 0 selects the else branch (7), so y = 5 cannot hold"
        );

        // The same assertion split into separately-ordered formulas, so the
        // shared `5` is memoised by an earlier formula rather than by an
        // earlier conjunct.
        let split = [y_is_five, x_is_nonzero, y_matches_ite];
        assert!(
            !holds_under(&split, &tm, &interp),
            "formula order must not change which branch an ite reports"
        );

        // And the interpretation that *does* satisfy it still evaluates true,
        // so the guard is not simply refusing everything.
        let mut satisfying = Interpretation::empty();
        satisfying.pin_int(x, BigInt::from(1));
        satisfying.pin_int(y, BigInt::from(7));
        let consistent = tm.mk_and(vec![x_is_nonzero, y_matches_ite]);
        assert!(holds_under(&[consistent], &tm, &satisfying));
    }

    /// The mirror image: the *else* term pre-memoised while the condition
    /// selects the then branch. This direction was never mis-folded (the walk
    /// always memoises the branch it demanded, so the then branch was already
    /// present), so this is a standing guard against the fix being written
    /// backwards rather than a second reproduction.
    #[test]
    fn test_pr31_ite_memo_guard_for_prememoised_else_branch() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("gx", int_sort);
        let y = tm.mk_var("gy", int_sort);
        let zero = tm.mk_int(0);
        let five = tm.mk_int(5);
        let seven = tm.mk_int(7);

        let x_is_zero = tm.mk_eq(x, zero);
        let selected = tm.mk_ite(x_is_zero, five, seven);
        let y_matches_ite = tm.mk_eq(y, selected);
        let y_is_seven = tm.mk_eq(y, seven);
        let conjunction = tm.mk_and(vec![x_is_zero, y_matches_ite, y_is_seven]);

        let mut interp = Interpretation::empty();
        interp.pin_int(x, BigInt::from(0));
        interp.pin_int(y, BigInt::from(7));
        assert!(
            !holds_under(&[conjunction], &tm, &interp),
            "x = 0 selects the then branch (5), so y = 7 cannot hold"
        );

        let mut satisfying = Interpretation::empty();
        satisfying.pin_int(x, BigInt::from(0));
        satisfying.pin_int(y, BigInt::from(5));
        let consistent = tm.mk_and(vec![x_is_zero, y_matches_ite]);
        assert!(holds_under(&[consistent], &tm, &satisfying));
    }

    #[test]
    fn test_pr31_eval_read_over_write() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("ra", array_sort);
        let i = tm.mk_int(1);
        let j = tm.mk_int(2);
        let v = tm.mk_int(9);
        let written = tm.mk_store(a, i, v);
        let read_same = tm.mk_select(written, i);
        let read_other = tm.mk_select(written, j);

        let mut interp = Interpretation::empty();
        interp.pin_fallback(a, Value::Num(rat(0)));
        assert_eq!(
            evaluate(read_same, &tm, &interp).and_then(|v| v.as_num().cloned()),
            Some(rat(9))
        );
        assert_eq!(
            evaluate(read_other, &tm, &interp).and_then(|v| v.as_num().cloned()),
            Some(rat(0))
        );
    }

    /// The congruence check must compare array-sorted arguments the way `=`
    /// does — extensionally — not by the write list they happen to carry.
    ///
    /// `a` and `store(store(a, i, v), i, v)` are the same array whenever
    /// `a[i] = v`, but they are structurally different [`Value::Mapping`]s
    /// (empty write list vs. two redundant writes). Pinning `f` apart on the
    /// two is therefore a congruence violation, and an interpretation carrying
    /// it is not a model however many formulas it satisfies.
    #[test]
    fn test_pr31_congruence_compares_arrays_extensionally() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("ca", array_sort);
        let index = tm.mk_int(1);
        let value = tm.mk_int(4);
        let rewritten = tm.mk_store(a, index, value);
        let rewritten_twice = tm.mk_store(rewritten, index, value);

        let plain = tm.mk_apply("cf", [a], int_sort);
        let layered = tm.mk_apply("cf", [rewritten_twice], int_sort);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let first = tm.mk_eq(plain, one);
        let second = tm.mk_eq(layered, two);

        // `a` reads 4 everywhere, so the two writes of 4 at index 1 change
        // nothing and the two arguments denote the same array.
        let mut interp = Interpretation::empty();
        interp.pin_fallback(a, Value::Num(rat(4)));
        interp.pin_int(plain, BigInt::from(1));
        interp.pin_int(layered, BigInt::from(2));
        assert!(
            !holds_under(&[first, second], &tm, &interp),
            "f applied to the same array twice cannot take two different values"
        );

        // Make the arrays genuinely different (`a[1]` is now 9, so the writes
        // do change something) and the same pinning is a legitimate model.
        let mut apart = Interpretation::empty();
        apart.pin_fallback(a, Value::Num(rat(9)));
        apart.pin_int(plain, BigInt::from(1));
        apart.pin_int(layered, BigInt::from(2));
        assert!(holds_under(&[first, second], &tm, &apart));
    }

    #[test]
    fn test_pr31_eval_distinct_roots_refuse_equality() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("ea", array_sort);
        let b = tm.mk_var("eb", array_sort);
        let goal = tm.mk_eq(a, b);
        let interp = Interpretation::empty();
        assert_eq!(evaluate(goal, &tm, &interp), None);
    }

    #[test]
    fn test_pr31_eval_deep_term_does_not_overflow() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("deep", int_sort);
        let one = tm.mk_int(1);
        let mut acc = x;
        for _ in 0..100_000 {
            acc = tm.mk_add(vec![acc, one]);
        }
        let hundred_thousand = tm.mk_int(100_000);
        let goal = tm.mk_eq(acc, hundred_thousand);
        let mut interp = Interpretation::empty();
        interp.pin_int(x, BigInt::from(0));
        assert!(holds_under(&[goal], &tm, &interp));
    }
}

#[cfg(test)]
mod publication_array_regressions {
    use super::*;

    #[test]
    fn equality_checks_root_cells_and_complete_fallbacks() {
        let mut tm = TermManager::new();
        let sort = tm.sorts.array(tm.sorts.int_sort, tm.sorts.int_sort);
        let a = tm.mk_var("a", sort);
        let b = tm.mk_var("b", sort);
        let eq = tm.mk_eq(a, b);
        let zero = Value::Num(BigRational::from_integer(0.into()));
        let one = Value::Num(BigRational::from_integer(1.into()));
        let mut interp = Interpretation::empty();
        interp.pin_fallback(a, zero.clone());
        interp.pin_fallback(b, zero);
        assert_eq!(evaluate(eq, &tm, &interp), Some(Value::Truth(true)));
        let index = BigRational::from_integer(BigInt::from(1) << 130);
        interp.pin_cell(a, index.clone(), one.clone());
        assert_eq!(evaluate(eq, &tm, &interp), Some(Value::Truth(false)));
        interp.pin_cell(b, index, one);
        assert_eq!(evaluate(eq, &tm, &interp), Some(Value::Truth(true)));
    }
}
