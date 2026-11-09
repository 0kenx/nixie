//! The query-free half of the published-model certificate (re-fix pass 15,
//! decisions (67), (68)): the goal, closed by the printed model, decided by
//! exact evaluation.
//!
//! Once every declared constant is replaced by its printed value and every
//! uninterpreted function by its printed table (`printed_check`), the only
//! symbols an assertion still has are bound variables.  The certificate's
//! queries (`solver::array_completion_certify::printed`) decide most goals;
//! this module decides the ones they leave open — a vacuous binder over a
//! datatype, an `exists` whose witness no named point gives, a negated
//! universal, a nonlinear body over a bounded integer box, a small
//! bit-vector domain — by evaluation alone, three-valued:
//!
//! * every maximal closed sub-term (no bound variable in it) is folded to its
//!   value first, so a body's array reads and table lookups are literals;
//! * a quantifier over `Bool`, a bit-vector sort of at most 2^12 values, or
//!   an `Int` a universal's guard bounds to a finite box is enumerated
//!   exhaustively — decided `true` or `false`;
//! * an `exists` over `Int` / `Real` is witnessed at the body's own literals
//!   and their neighbours — decided `true` when one holds, open otherwise;
//! * a universal over an unbounded domain is decided `true` only by
//!   `mbqi::model_certify`'s region enumeration, which checks its own
//!   fragment first, and is open otherwise;
//! * a variable the body does not mention drops out (every sort is
//!   non-empty).
//!
//! Only `Some(true)` for every assertion certifies; `None` never does.
//! Sound by construction: every answer is an evaluation of the printed model.

use super::*;
use crate::prelude::{FxHashMap, FxHashSet};

mod datatype_reads;
mod ground_values;

/// Evaluations one certification may spend.
const MAX_DECIDE_STEPS: usize = 20_000;

/// Points one quantifier may enumerate.
const MAX_ENUMERATED_POINTS: usize = 4_096;

/// Widest bit-vector sort a quantifier is enumerated over.
const MAX_ENUMERATED_BV_WIDTH: u32 = 12;

/// `Real` literals beyond which a witness search takes no pairwise
/// midpoints.
const MAX_REAL_WITNESS_LITERALS: usize = 12;

/// One bound variable's domain: its points, and whether they are every value
/// the variable can take where the body can hold.
struct Domain {
    points: Vec<TermId>,
    exhaustive: bool,
}

enum DecisionOp {
    Not,
    All(bool),
    Implies,
    Ite,
    Equal(bool),
    Quant {
        universal: bool,
        exhaustive: bool,
        fallback: Option<TermId>,
    },
}
struct Decision {
    op: DecisionOp,
    terms: Vec<TermId>,
    values: Vec<Option<bool>>,
}
impl Decision {
    fn new(op: DecisionOp, terms: Vec<TermId>) -> Self {
        Self {
            op,
            terms,
            values: Vec::new(),
        }
    }
}

impl Context {
    /// The query-free certificate: `true` when every assertion of `goal`,
    /// closed by `printed`, evaluates to `true` (see the module docs).
    pub(in crate::context) fn certified_by_evaluation(
        &mut self,
        goal: &[TermId],
        printed: &FxHashMap<TermId, TermId>,
    ) -> bool {
        // A selector or tester over a substituted constructor value folds
        // (`TermManager::fold_constructor_accessors`, decision (72)(d)).
        let closed: Vec<TermId> = goal
            .iter()
            .map(|&assertion| {
                let closed = self.terms.substitute(assertion, printed);
                self.terms.fold_constructor_accessors(closed)
            })
            .collect();

        if closed.iter().any(|&assertion| {
            self.terms
                .free_vars_including_patterns(assertion)
                .iter()
                .any(|&var| !self.is_publication_witness(var))
        }) {
            return false;
        }
        if crate::mbqi::model_certify::certify(&closed, &FxHashMap::default(), &self.terms) {
            return true;
        }
        let mut budget = MAX_DECIDE_STEPS;
        closed.iter().all(|&assertion| {
            let result = self.decide_closed(assertion, &mut budget);
            result == Some(true)
        })
    }

    /// One assertion of the goal, closed by `printed`, shown true by exact
    /// evaluation — the per-assertion form of
    /// [`Self::certified_by_evaluation`].
    pub(in crate::context) fn assertion_certified_by_evaluation(
        &mut self,
        assertion: TermId,
        printed: &FxHashMap<TermId, TermId>,
    ) -> bool {
        let closed = self.terms.substitute(assertion, printed);
        let closed = self.terms.fold_constructor_accessors(closed);
        if self
            .terms
            .free_vars_including_patterns(closed)
            .iter()
            .any(|&var| !self.is_publication_witness(var))
        {
            return false;
        }
        let mut budget = MAX_DECIDE_STEPS;
        self.decide_closed(closed, &mut budget) == Some(true)
            || crate::mbqi::model_certify::certify(&[closed], &FxHashMap::default(), &self.terms)
    }

    /// The truth value of a closed Boolean term, where evaluation decides it.
    fn decide_closed(&mut self, term: TermId, budget: &mut usize) -> Option<bool> {
        enum Frame {
            Eval(TermId),
            Resume(Decision),
        }
        let mut stack = vec![Frame::Eval(term)];
        let mut answer = None;
        while let Some(frame) = stack.pop() {
            let decision = match frame {
                Frame::Eval(term) => {
                    if *budget == 0 {
                        answer = None;
                        continue;
                    }
                    *budget -= 1;
                    let term = self.terms.fold_constructor_accessors(term);
                    let term = self.fold_datatype_reads(term);
                    let term = self.fold_closed_subterms(term);
                    if !self.has_quantifier(term) {
                        answer = self.evaluate_bool(term);
                        continue;
                    }
                    let Some(kind) = self.terms.get(term).map(|t| t.kind.clone()) else {
                        answer = None;
                        continue;
                    };
                    let plan = match kind {
                        TermKind::Forall { vars, body, .. } => {
                            self.quantifier_decision(true, &vars, body)
                        }
                        TermKind::Exists { vars, body, .. } => {
                            self.quantifier_decision(false, &vars, body)
                        }
                        TermKind::Not(a) => Some(Decision::new(DecisionOp::Not, vec![a])),
                        TermKind::And(a) => Some(Decision::new(DecisionOp::All(true), a.to_vec())),
                        TermKind::Or(a) => Some(Decision::new(DecisionOp::All(false), a.to_vec())),
                        TermKind::Implies(a, b) => {
                            Some(Decision::new(DecisionOp::Implies, vec![a, b]))
                        }
                        TermKind::Ite(a, b, c) => {
                            Some(Decision::new(DecisionOp::Ite, vec![a, b, c]))
                        }
                        TermKind::Eq(a, b) if self.is_bool(a) => {
                            Some(Decision::new(DecisionOp::Equal(true), vec![a, b]))
                        }
                        TermKind::Xor(a, b) => {
                            Some(Decision::new(DecisionOp::Equal(false), vec![a, b]))
                        }
                        _ => None,
                    };
                    let Some(plan) = plan else {
                        answer = None;
                        continue;
                    };
                    plan
                }
                Frame::Resume(mut decision) => {
                    decision.values.push(answer);
                    decision
                }
            };
            let count = decision.values.len();
            let decisive = match decision.op {
                DecisionOp::All(wanted)
                | DecisionOp::Quant {
                    universal: wanted, ..
                } => decision
                    .values
                    .last()
                    .copied()
                    .flatten()
                    .filter(|&v| v != wanted),
                DecisionOp::Implies if count == 1 && decision.values[0] == Some(false) => {
                    Some(true)
                }
                _ => None,
            };
            if let Some(value) = decisive {
                answer = Some(value);
                continue;
            }
            // A known ITE condition only evaluates the selected branch.
            let complete = if matches!(decision.op, DecisionOp::Ite)
                && count >= 1
                && decision.values[0].is_some()
            {
                count == 2
            } else {
                count == decision.terms.len()
            };
            if complete {
                answer = match decision.op {
                    DecisionOp::Not => decision.values.first().copied().flatten().map(|v| !v),
                    DecisionOp::All(wanted) => decision
                        .values
                        .iter()
                        .all(|v| *v == Some(wanted))
                        .then_some(wanted),
                    DecisionOp::Implies => match decision.values.as_slice() {
                        [Some(false), ..] | [_, Some(true)] => Some(true),
                        [Some(true), Some(false)] => Some(false),
                        _ => None,
                    },
                    DecisionOp::Ite => match decision.values.as_slice() {
                        [Some(_), value] => *value,
                        [None, Some(a), Some(b)] if a == b => Some(*a),
                        _ => None,
                    },
                    DecisionOp::Equal(equal) => match decision.values.as_slice() {
                        [Some(a), Some(b)] => Some((a == b) == equal),
                        _ => None,
                    },
                    DecisionOp::Quant {
                        universal,
                        exhaustive,
                        fallback,
                    } => {
                        if exhaustive && decision.values.iter().all(|v| *v == Some(universal)) {
                            Some(universal)
                        } else if let Some(q) = fallback {
                            crate::mbqi::model_certify::certify(
                                &[q],
                                &FxHashMap::default(),
                                &self.terms,
                            )
                            .then_some(true)
                        } else {
                            None
                        }
                    }
                };
            } else {
                let next = if matches!(decision.op, DecisionOp::Ite) && count == 1 {
                    match decision.values[0] {
                        Some(false) => 2,
                        _ => 1,
                    }
                } else {
                    count
                };
                let Some(&term) = decision.terms.get(next) else {
                    answer = None;
                    continue;
                };
                stack.push(Frame::Resume(decision));
                stack.push(Frame::Eval(term));
            }
        }
        answer
    }

    /// `∀vars. body` (`universal`) or `∃vars. body`, decided by enumerating
    /// the variables' domains (see the module docs).
    fn quantifier_decision(
        &mut self,
        universal: bool,
        vars: &[(nixie_core::interner::Spur, SortId)],
        body: TermId,
    ) -> Option<Decision> {
        let body = self.terms.simplify(body);
        if let Some(TermKind::Distinct(args)) = self.terms.get(body).map(|t| &t.kind) {
            let mut seen = FxHashSet::default();
            if args.iter().any(|arg| !seen.insert(*arg)) {
                // All SMT sorts are nonempty. A repeated argument makes the
                // body false for every assignment, under either quantifier.
                return Some(Decision::new(
                    DecisionOp::All(true),
                    vec![self.terms.mk_false()],
                ));
            }
        }
        let mut bound: Vec<TermId> = Vec::with_capacity(vars.len());
        let mut domains: Vec<Domain> = Vec::with_capacity(vars.len());
        let free = self.terms.free_vars_including_patterns(body);
        for &(name, sort) in vars {
            let text = self.terms.resolve_str(name).to_string();
            let var = self.terms.mk_var(&text, sort);
            if !free.contains(&var) {
                // Not mentioned: every sort is non-empty, so it drops out.
                continue;
            }
            let domain = self.domain_of(var, sort, body, universal)?;
            bound.push(var);
            domains.push(domain);
        }
        if bound.is_empty() {
            return Some(Decision::new(DecisionOp::All(true), vec![body]));
        }
        if domains.iter().any(|d| d.exhaustive && d.points.is_empty()) {
            // A guard box with no integer in it: the universal is vacuous.
            return Some(Decision::new(DecisionOp::All(universal), Vec::new()));
        }
        let mut total: usize = 1;
        for domain in &domains {
            if domain.points.is_empty() {
                return None;
            }
            total = total
                .checked_mul(domain.points.len())
                .filter(|&t| t <= MAX_ENUMERATED_POINTS)?;
        }
        let exhaustive = domains.iter().all(|d| d.exhaustive);
        let mut instances = Vec::with_capacity(total);
        let mut position: Vec<usize> = vec![0; domains.len()];
        for _ in 0..total {
            let map: FxHashMap<TermId, TermId> = bound
                .iter()
                .zip(&position)
                .zip(&domains)
                .map(|((&var, &i), domain)| (var, domain.points[i]))
                .collect();
            let instance = self.terms.substitute(body, &map);
            instances.push(instance);
            for (slot, domain) in position.iter_mut().zip(&domains).rev() {
                *slot += 1;
                if *slot < domain.points.len() {
                    break;
                }
                *slot = 0;
            }
        }
        let fallback = universal.then(|| self.rebuild_forall(vars, body));
        Some(Decision::new(
            DecisionOp::Quant {
                universal,
                exhaustive,
                fallback,
            },
            instances,
        ))
    }

    /// The domain a bound variable is enumerated over, or `None` when no
    /// enumeration can speak for it.
    fn domain_of(
        &mut self,
        var: TermId,
        sort: SortId,
        body: TermId,
        universal: bool,
    ) -> Option<Domain> {
        match self.terms.sorts.get(sort).map(|s| s.kind.clone())? {
            SortKind::Bool => Some(Domain {
                points: vec![self.terms.mk_false(), self.terms.mk_true()],
                exhaustive: true,
            }),
            SortKind::BitVec(width) if width <= MAX_ENUMERATED_BV_WIDTH => Some(Domain {
                points: (0u32..(1u32 << width))
                    .map(|v| self.terms.mk_bitvec(v, width))
                    .collect(),
                exhaustive: true,
            }),
            SortKind::Int => {
                if universal
                    && let Some(TermKind::Implies(guard, _)) =
                        self.terms.get(body).map(|t| t.kind.clone())
                    && let Some((lo, hi)) = int_bounds_of(guard, var, &self.terms)
                {
                    if hi < lo {
                        return Some(Domain {
                            points: Vec::new(),
                            exhaustive: true,
                        });
                    }
                    let width = usize::try_from(&hi - &lo + 1u8).ok()?;
                    if width > MAX_ENUMERATED_POINTS {
                        return None;
                    }
                    let mut points = Vec::with_capacity(width);
                    let mut value = lo;
                    while value <= hi {
                        points.push(self.terms.mk_int(value.clone()));
                        value += 1u8;
                    }
                    return Some(Domain {
                        points,
                        exhaustive: true,
                    });
                }
                // The body's literals, their sums and differences (a boundary
                // `c₁ = x + c₂` sits at `c₁ - c₂`), and the neighbours of each.
                let mut literals: Vec<BigInt> = vec![BigInt::zero()];
                for literal in self.literals_of(body) {
                    if let Some(TermKind::IntConst(n)) =
                        self.terms.get(literal).map(|t| t.kind.clone())
                    {
                        literals.push(n);
                    }
                }
                literals.sort();
                literals.dedup();
                let mut centres: Vec<BigInt> = literals.clone();
                if literals.len() <= MAX_REAL_WITNESS_LITERALS {
                    for a in &literals {
                        for b in &literals {
                            centres.push(a - b);
                            centres.push(a + b);
                        }
                    }
                }
                let mut values: Vec<BigInt> = Vec::with_capacity(centres.len() * 3);
                for c in centres {
                    values.extend([&c - 1u8, c.clone(), c + 1u8]);
                }
                values.sort();
                values.dedup();
                Some(Domain {
                    points: values.into_iter().map(|v| self.terms.mk_int(v)).collect(),
                    exhaustive: false,
                })
            }
            SortKind::Real => {
                let one = num_rational::Rational64::from_integer(1);
                let mut literals: Vec<num_rational::Rational64> = self
                    .literals_of(body)
                    .into_iter()
                    .filter_map(|t| match self.terms.get(t).map(|d| &d.kind) {
                        Some(TermKind::RealConst(r)) => Some(*r),
                        Some(TermKind::IntConst(n)) => i64::try_from(n.clone())
                            .ok()
                            .map(num_rational::Rational64::from_integer),
                        _ => None,
                    })
                    .collect();
                literals.sort();
                literals.dedup();
                let mut values: Vec<num_rational::Rational64> =
                    vec![num_rational::Rational64::from_integer(0)];
                for &r in &literals {
                    values.push(r);
                    values.extend(num_traits::CheckedSub::checked_sub(&r, &one));
                    values.extend(num_traits::CheckedAdd::checked_add(&r, &one));
                }
                if literals.len() <= MAX_REAL_WITNESS_LITERALS {
                    for window in literals.windows(2) {
                        if let [a, b] = window {
                            values.extend(
                                num_traits::CheckedAdd::checked_add(a, b)
                                    .map(|s| s / num_rational::Rational64::from_integer(2)),
                            );
                        }
                    }
                }
                values.sort();
                values.dedup();
                Some(Domain {
                    points: values.into_iter().map(|v| self.terms.mk_real(v)).collect(),
                    exhaustive: false,
                })
            }
            SortKind::Uninterpreted(_) if self.is_uninterpreted_sort(sort) => {
                let mut points = self
                    .published
                    .witness_domains
                    .get(&sort)
                    .cloned()
                    .unwrap_or_default();
                if points.is_empty() {
                    let name =
                        nixie_core::reserved::reserved_name("ucw", &format!("nonempty{}", sort.0));
                    let value = self.terms.mk_var(&name, sort);
                    points.push(value);
                    self.published.witness_domains.insert(sort, points.clone());
                }
                // This is an explicit finite interpretation of an
                // uninterpreted sort, not a sample of an interpreted domain.
                Some(Domain {
                    points,
                    exhaustive: true,
                })
            }
            SortKind::Datatype(_) => {
                // An enumeration is exactly its constructors; over a datatype
                // with a field, the constructor values the body names are
                // witness candidates only.
                if let Some(constructors) = self.enumeration_values(sort) {
                    return Some(Domain {
                        points: constructors,
                        exhaustive: true,
                    });
                }
                let mut points: Vec<TermId> = self
                    .constructor_values_of(body)
                    .into_iter()
                    .filter(|&t| self.terms.get(t).is_some_and(|d| d.sort == sort))
                    .collect();
                // Concrete constructors are witnesses, never an exhaustive
                // domain for a recursive datatype. Include one finite value
                // of each constructor even when the body names none.
                let constructors = self
                    .terms
                    .sorts
                    .datatype_name(sort)
                    .and_then(|name| self.terms.sorts.get_datatype(name))
                    .map(|def| {
                        def.constructors
                            .iter()
                            .map(|ctor| {
                                (
                                    self.terms.sorts.resolve_spur(ctor.name).to_string(),
                                    ctor.selectors
                                        .iter()
                                        .map(|(_, sort)| *sort)
                                        .collect::<Vec<_>>(),
                                )
                            })
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                for (name, fields) in constructors {
                    let args: Option<Vec<_>> = fields
                        .into_iter()
                        .map(|field| {
                            crate::solver::model_builder::ground_default_term(
                                &mut self.terms,
                                field,
                            )
                        })
                        .collect();
                    if let Some(args) = args {
                        let value = self.terms.mk_dt_constructor(&name, args, sort);
                        if !points.contains(&value) {
                            points.push(value);
                        }
                    }
                }
                Some(Domain {
                    points,
                    exhaustive: false,
                })
            }
            _ => None,
        }
    }

    /// Every constructor of `sort` as a term, when every constructor is
    /// nullary.
    fn enumeration_values(&mut self, sort: SortId) -> Option<Vec<TermId>> {
        let name = self.terms.sorts.datatype_name(sort)?.to_string();
        let names: Vec<String> = {
            let def = self.terms.sorts.get_datatype(&name)?;
            if def.constructors.is_empty()
                || def.constructors.iter().any(|c| !c.selectors.is_empty())
            {
                return None;
            }
            def.constructors
                .iter()
                .map(|c| self.terms.sorts.resolve_spur(c.name).to_string())
                .collect()
        };
        Some(
            names
                .iter()
                .map(|n| self.terms.mk_dt_constructor(n, [], sort))
                .collect(),
        )
    }

    /// Every ground constructor value `term` spells.
    fn constructor_values_of(&self, term: TermId) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = vec![term];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }
            let Some(data) = self.terms.get(current) else {
                continue;
            };
            if super::array_model::is_constructor_value(current, &self.terms) {
                out.push(current);
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
        out.sort_unstable_by_key(|t| t.raw());
        out
    }

    /// Every numeric literal of `term`.
    fn literals_of(&self, term: TermId) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = vec![term];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }
            let Some(data) = self.terms.get(current) else {
                continue;
            };
            if matches!(data.kind, TermKind::IntConst(_) | TermKind::RealConst(_)) {
                out.push(current);
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
        out.sort_unstable_by_key(|t| t.raw());
        out
    }

    /// `term` with every maximal closed, quantifier-free, scalar sub-term that
    /// is not already a literal replaced by its value.
    fn fold_closed_subterms(&mut self, term: TermId) -> TermId {
        let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut stack: Vec<TermId> = vec![term];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }
            let Some(data) = self.terms.get(current).cloned() else {
                continue;
            };
            let foldable = !is_literal_term(&data.kind)
                && !matches!(data.kind, TermKind::Forall { .. } | TermKind::Exists { .. })
                && self.is_scalar_sort(data.sort)
                && !self.has_quantifier(current)
                && self
                    .terms
                    .free_vars_including_patterns(current)
                    .iter()
                    .all(|&var| self.is_publication_witness(var));
            if foldable && let Some(value) = self.value_term_of(current) {
                map.insert(current, value);
                continue;
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
        if map.is_empty() {
            term
        } else {
            self.terms.substitute(term, &map)
        }
    }

    /// The literal a closed quantifier-free scalar term evaluates to.
    fn value_term_of(&mut self, term: TermId) -> Option<TermId> {
        let sort = self.terms.get(term)?.sort;
        if sort == self.terms.sorts.bool_sort {
            let witnesses = self.publication_witness_set();
            if let Some(value) = self.ground_truth(term, &witnesses) {
                return Some(self.terms.mk_bool(value));
            }
        }
        let value = match crate::solver::array_completion_certify::evaluate_closed_value(
            &self.solver,
            term,
            &mut self.terms,
        ) {
            Some(value) => value,
            None => {
                let simplified = self.terms.simplify(term);
                crate::solver::array_completion_certify::evaluate_closed_value(
                    &self.solver,
                    simplified,
                    &mut self.terms,
                )?
            }
        };
        Some(match value {
            crate::solver::EvalVal::Bool(flag) => self.terms.mk_bool(flag),
            crate::solver::EvalVal::NumBig(number) => {
                if sort == self.terms.sorts.int_sort {
                    if !number.is_integer() {
                        return None;
                    }
                    self.terms.mk_int(number.to_integer())
                } else if sort == self.terms.sorts.real_sort {
                    let n = self.terms.mk_int(number.numer().clone());
                    let d = self.terms.mk_int(number.denom().clone());
                    self.terms.mk_rdiv(n, d)
                } else {
                    return None;
                }
            }
            crate::solver::EvalVal::Num(number) => {
                if sort == self.terms.sorts.int_sort {
                    if *number.denom() != 1 {
                        return None;
                    }
                    self.terms.mk_int(*number.numer())
                } else {
                    self.terms.mk_real(number)
                }
            }
            crate::solver::EvalVal::Bv { value, width } => self.terms.mk_bitvec(value, width),
        })
    }

    fn is_publication_witness(&self, term: TermId) -> bool {
        self.published
            .witness_domains
            .values()
            .any(|domain| domain.contains(&term))
    }

    fn publication_witness_set(&self) -> FxHashSet<TermId> {
        self.published
            .witness_domains
            .values()
            .flatten()
            .copied()
            .collect()
    }

    /// A closed quantifier-free Boolean term's value.
    fn evaluate_bool(&mut self, term: TermId) -> Option<bool> {
        let witnesses = self.publication_witness_set();
        match crate::solver::array_completion_certify::evaluate_closed(
            &self.solver,
            term,
            &mut self.terms,
        ) {
            Some(value) => Some(value),
            None => {
                let simplified = self.terms.simplify(term);
                crate::solver::array_completion_certify::evaluate_closed(
                    &self.solver,
                    simplified,
                    &mut self.terms,
                )
                .or_else(|| self.ground_truth(simplified, &witnesses))
            }
        }
    }

    /// `∀vars. body` rebuilt.
    fn rebuild_forall(
        &mut self,
        vars: &[(nixie_core::interner::Spur, SortId)],
        body: TermId,
    ) -> TermId {
        let names: Vec<(String, SortId)> = vars
            .iter()
            .map(|&(name, sort)| (self.terms.resolve_str(name).to_string(), sort))
            .collect();
        let binders: Vec<(&str, SortId)> = names.iter().map(|(n, s)| (n.as_str(), *s)).collect();
        self.terms.mk_forall(binders, body)
    }

    /// Whether `term` holds a quantifier.
    fn has_quantifier(&self, term: TermId) -> bool {
        let mut stack: Vec<TermId> = vec![term];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }
            let Some(data) = self.terms.get(current) else {
                continue;
            };
            if matches!(data.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                return true;
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
        false
    }

    /// Whether `term` is `Bool`-sorted.
    fn is_bool(&self, term: TermId) -> bool {
        self.terms
            .get(term)
            .is_some_and(|t| t.sort == self.terms.sorts.bool_sort)
    }

    /// Whether `sort` is `Bool`, `Int`, `Real` or a bit-vector sort.
    fn is_scalar_sort(&self, sort: SortId) -> bool {
        matches!(
            self.terms.sorts.get(sort).map(|s| &s.kind),
            Some(SortKind::Bool | SortKind::Int | SortKind::Real | SortKind::BitVec(_))
        )
    }
}

/// Whether a term kind is a literal of a scalar sort.
fn is_literal_term(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
    )
}

/// The integer interval `[lo, hi]` a guard conjunction confines `var` to,
/// read from its top-level conjuncts `var ⊕ c` / `c ⊕ var` with integer
/// literals `c`; `None` when a side is unbounded.
fn int_bounds_of(
    guard: TermId,
    var: TermId,
    terms: &nixie_core::ast::TermManager,
) -> Option<(BigInt, BigInt)> {
    let conjuncts: Vec<TermId> = match terms.get(guard).map(|t| &t.kind) {
        Some(TermKind::And(args)) => args.to_vec(),
        _ => vec![guard],
    };
    let literal = |term: TermId| match terms.get(term).map(|t| &t.kind) {
        Some(TermKind::IntConst(n)) => Some(n.clone()),
        _ => None,
    };
    let mut lo: Option<BigInt> = None;
    let mut hi: Option<BigInt> = None;
    for conjunct in conjuncts {
        let Some(kind) = terms.get(conjunct).map(|t| t.kind.clone()) else {
            continue;
        };
        let (l, r, op) = match kind {
            TermKind::Le(l, r) => (l, r, "<="),
            TermKind::Lt(l, r) => (l, r, "<"),
            TermKind::Ge(l, r) => (l, r, ">="),
            TermKind::Gt(l, r) => (l, r, ">"),
            // `var = c` is the one-point box `[c, c]`.
            TermKind::Eq(l, r) => {
                let pinned = if l == var {
                    literal(r)
                } else if r == var {
                    literal(l)
                } else {
                    None
                };
                if let Some(c) = pinned {
                    if lo.as_ref().is_none_or(|x| c > *x) {
                        lo = Some(c.clone());
                    }
                    if hi.as_ref().is_none_or(|x| c < *x) {
                        hi = Some(c);
                    }
                }
                continue;
            }
            _ => continue,
        };
        let (op, c) = if l == var {
            let Some(c) = literal(r) else { continue };
            (op, c)
        } else if r == var {
            let Some(c) = literal(l) else { continue };
            let mirrored = match op {
                "<=" => ">=",
                "<" => ">",
                ">=" => "<=",
                _ => "<",
            };
            (mirrored, c)
        } else {
            continue;
        };
        let (bound, is_upper) = match op {
            "<=" => (c, true),
            "<" => (c - 1u8, true),
            ">=" => (c, false),
            _ => (c + 1u8, false),
        };
        if is_upper {
            if hi.as_ref().is_none_or(|h| bound < *h) {
                hi = Some(bound);
            }
        } else if lo.as_ref().is_none_or(|l| bound > *l) {
            lo = Some(bound);
        }
    }
    Some((lo?, hi?))
}
