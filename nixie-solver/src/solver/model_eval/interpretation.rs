//! Evaluation of a proposed interpretation, independent of live theory state.
//!
//! Array certificates and published values use this reading. The search's
//! array-axiom checks keep their opaque select leaves: evaluating read-over-write
//! there would let an axiom validate itself before its SAT clause was asserted.

use super::*;
use nixie_core::sort::{SortId, SortKind};

#[derive(Debug, Clone, Copy)]
pub(super) enum ScalarSort {
    Bool,
    Int,
    Real,
    Bv(u32),
}

impl ScalarSort {
    fn of(sort: SortId, manager: &TermManager) -> Option<Self> {
        match manager.sorts.get(sort)?.kind {
            SortKind::Bool => Some(Self::Bool),
            SortKind::Int => Some(Self::Int),
            SortKind::Real => Some(Self::Real),
            SortKind::BitVec(width) if width > 0 => Some(Self::Bv(width)),
            _ => None,
        }
    }

    pub(super) fn validate(self, value: &EvalVal) -> EvalOutcome {
        let valid = match (self, value) {
            (Self::Bool, EvalVal::Bool(_)) => true,
            (Self::Bv(expected), EvalVal::Bv { width, .. }) => expected == *width,
            (Self::Int, _) => value.to_big().is_some_and(|n| n.is_integer()),
            (Self::Real, _) => value.to_big().is_some(),
            _ => false,
        };
        if valid {
            EvalOutcome::Value(value.clone())
        } else {
            EvalOutcome::UNDETERMINED
        }
    }
}

#[derive(Debug)]
enum SelectState {
    Index(TermId),
    Level { level: usize, index: EvalVal },
    Value(TermId),
}

/// A literal store chain, traversed outermost first. A nonliteral default is
/// evaluated by the same heap driver, so neither defaults nor model aliases
/// introduce recursive calls to the evaluator.
#[derive(Debug)]
pub(super) struct Select {
    levels: Vec<(TermId, TermId)>,
    default: Option<TermId>,
    state: SelectState,
}

impl Select {
    pub(super) fn accept(&mut self, result: EvalOutcome) -> Option<EvalOutcome> {
        match &self.state {
            SelectState::Index(_) => match result {
                EvalOutcome::Value(index) => {
                    self.state = SelectState::Level { level: 0, index };
                    None
                }
                other => Some(other.demote()),
            },
            SelectState::Level { level, index } => {
                let EvalOutcome::Value(stored_index) = result else {
                    return Some(result.demote());
                };
                match combine_eq_certify(index, &stored_index) {
                    EvalOutcome::Value(EvalVal::Bool(true)) => {
                        let Some(&(_, value)) = self.levels.get(*level) else {
                            return Some(EvalOutcome::UNDETERMINED);
                        };
                        self.state = SelectState::Value(value);
                        None
                    }
                    EvalOutcome::Value(EvalVal::Bool(false)) => {
                        self.state = SelectState::Level {
                            level: level + 1,
                            index: index.clone(),
                        };
                        None
                    }
                    other => Some(other.demote()),
                }
            }
            SelectState::Value(_) => Some(result),
        }
    }

    pub(super) fn request(&mut self) -> Step {
        match &self.state {
            SelectState::Index(index) => Step::Need(*index),
            SelectState::Level { level, .. } => match self.levels.get(*level) {
                Some(&(index, _)) => Step::Need(index),
                None => match self.default {
                    Some(value) => {
                        self.state = SelectState::Value(value);
                        Step::Need(value)
                    }
                    None => Step::Done(EvalOutcome::UNDETERMINED),
                },
            },
            SelectState::Value(value) => Step::Need(*value),
        }
    }
}

impl Solver {
    /// Fold a supplied interpretation without consulting arithmetic, BV, EUF,
    /// SAT caches, or certificate-mode flags. Unsupported operations decline.
    pub(in crate::solver) fn eval_under_interpretation(
        &self,
        term: TermId,
        model: &Model,
        manager: &TermManager,
    ) -> EvalOutcome {
        Self::eval_with_reader(term, 0, |term, depth| {
            self.open_interpretation(term, model, manager, depth)
        })
    }

    fn open_interpretation(
        &self,
        term: TermId,
        model: &Model,
        manager: &TermManager,
        depth: u32,
    ) -> Opened {
        if depth > ENCODE_DEPTH_LIMIT {
            return Opened::Done(EvalOutcome::UNDETERMINED);
        }
        let Some(data) = manager.get(term) else {
            return Opened::Done(EvalOutcome::UNDETERMINED);
        };
        match &data.kind {
            TermKind::Var(_) | TermKind::Apply { .. } => {
                let Some(value) = model.get(term) else {
                    return Opened::Done(EvalOutcome::UNDETERMINED);
                };
                let Some(sort) = ScalarSort::of(data.sort, manager) else {
                    return Opened::Done(EvalOutcome::UNDETERMINED);
                };
                Opened::Frame(Frame::unary(value, EagerKind::ModelValue(sort), depth))
            }
            TermKind::Select(array, index) => {
                let mut base = *array;
                let mut levels = Vec::new();
                let mut seen = FxHashSet::default();
                // Model aliases can cycle even though the term DAG cannot.
                let default = loop {
                    if seen.len() >= 4096 || !seen.insert(base) {
                        return Opened::Done(EvalOutcome::UNDETERMINED);
                    }
                    let Some(node) = manager.get(base) else {
                        return Opened::Done(EvalOutcome::UNDETERMINED);
                    };
                    if let TermKind::Store(inner, at, value) = node.kind {
                        levels.push((at, value));
                        base = inner;
                    } else if let Some(value) =
                        super::super::array_axioms::const_array_default(base, manager)
                    {
                        break Some(value);
                    } else if matches!(node.kind, TermKind::Var(_) | TermKind::Apply { .. }) {
                        match model.get(base) {
                            Some(value)
                                if manager.get(value).is_some_and(|v| v.sort == node.sort) =>
                            {
                                base = value
                            }
                            _ => break None,
                        }
                    } else {
                        break None;
                    }
                };
                let state = if levels.is_empty() {
                    match default {
                        Some(value) => SelectState::Value(value),
                        None => return Opened::Done(EvalOutcome::UNDETERMINED),
                    }
                } else {
                    SelectState::Index(*index)
                };
                Opened::Frame(Frame::new(
                    Op::Select(Select {
                        levels,
                        default,
                        state,
                    }),
                    depth,
                ))
            }
            TermKind::Eq(a, b) if a == b && manager.get(*a).is_some() => {
                Opened::Done(EvalOutcome::boolean(true))
            }
            TermKind::Eq(a, b) => Opened::Frame(Frame::binary(*a, *b, EagerKind::EqCertify, depth)),
            TermKind::Distinct(args) => Opened::Frame(Frame::new(
                Op::ExactDistinct {
                    operands: args.clone(),
                },
                depth,
            )),
            TermKind::Lt(a, b) => Opened::Frame(Frame::binary(
                *a,
                *b,
                EagerKind::ExactStrict { less: true },
                depth,
            )),
            TermKind::Gt(a, b) => Opened::Frame(Frame::binary(
                *a,
                *b,
                EagerKind::ExactStrict { less: false },
                depth,
            )),
            TermKind::Div(a, b) if data.sort == manager.sorts.real_sort => {
                Opened::Frame(Frame::binary(*a, *b, EagerKind::RealDiv, depth))
            }
            // These branches of the shared opener only describe operands or
            // literals. They neither read live theory state nor model caches.
            TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::Not(_)
            | TermKind::And(_)
            | TermKind::Or(_)
            | TermKind::Implies(..)
            | TermKind::Ite(..)
            | TermKind::Add(_)
            | TermKind::Sub(..)
            | TermKind::Mul(_)
            | TermKind::Neg(_)
            | TermKind::Div(..)
            | TermKind::Mod(..)
            | TermKind::Le(..)
            | TermKind::Ge(..)
            | TermKind::BvNot(_)
            | TermKind::BvAnd(..)
            | TermKind::BvOr(..)
            | TermKind::BvXor(..)
            | TermKind::BvAdd(..)
            | TermKind::BvSub(..)
            | TermKind::BvMul(..)
            | TermKind::BvUdiv(..)
            | TermKind::BvSdiv(..)
            | TermKind::BvUrem(..)
            | TermKind::BvSrem(..)
            | TermKind::BvShl(..)
            | TermKind::BvLshr(..)
            | TermKind::BvAshr(..)
            | TermKind::BvConcat(..)
            | TermKind::BvExtract { .. }
            | TermKind::BvUlt(..)
            | TermKind::BvUle(..)
            | TermKind::BvSlt(..)
            | TermKind::BvSle(..) => self.open_in_model(term, model, manager, depth),
            _ => Opened::Done(EvalOutcome::UNDETERMINED),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn proposed_scalars_are_exact_and_never_read_the_tableau() {
        let mut tm = TermManager::new();
        let x = tm.mk_var("x", tm.sorts.int_sort);
        let five = tm.mk_int(5);
        let eq = tm.mk_eq(x, five);
        let lt = tm.mk_lt(x, five);
        let mut model = Model::new();
        model.set(x, five);
        let solver = Solver::new();
        assert_eq!(
            solver.eval_in_model_outcome(eq, &model, &tm, 0),
            EvalOutcome::UNDETERMINED
        );
        assert_eq!(
            solver.eval_under_interpretation(eq, &model, &tm),
            EvalOutcome::boolean(true)
        );
        assert_eq!(
            solver.eval_under_interpretation(lt, &model, &tm),
            EvalOutcome::boolean(false)
        );
        assert_eq!(
            solver.eval_under_interpretation(x, &Model::new(), &tm),
            EvalOutcome::UNDETERMINED
        );
    }

    #[test]
    fn structural_select_does_not_change_the_axiom_reading() {
        let mut tm = TermManager::new();
        let int = tm.sorts.int_sort;
        let sort = tm.sorts.array(int, int);
        let big = tm.mk_int(BigInt::from(1) << 129usize);
        let one = tm.mk_int(1);
        let forty_two = tm.mk_int(42);
        let array = tm.mk_apply(nixie_core::reserved::CONST_ARRAY_FUNC, [big], sort);
        let stored = tm.mk_store(array, one, one);
        let read = tm.intern_term(TermKind::Select(stored, one), int);
        let zero = tm.mk_int(0);
        let miss = tm.intern_term(TermKind::Select(stored, zero), int);
        let mut model = Model::new();
        model.set(read, forty_two);
        let solver = Solver::new();
        assert_eq!(
            solver.eval_in_model_outcome(read, &model, &tm, 0),
            EvalOutcome::number(Rational64::from_integer(42))
        );
        assert_eq!(
            solver.eval_under_interpretation(read, &model, &tm),
            EvalOutcome::number(Rational64::from_integer(1))
        );
        assert_eq!(
            solver.eval_under_interpretation(miss, &model, &tm),
            parse_value_term(big, &tm)
        );
    }

    #[test]
    fn compound_defaults_and_real_division_are_exact() {
        let mut tm = TermManager::new();
        let real = tm.sorts.real_sort;
        let int = tm.sorts.int_sort;
        let two = tm.mk_real(Rational64::from_integer(2));
        let three = tm.mk_real(Rational64::from_integer(3));
        let fraction = tm.intern_term(TermKind::Div(two, three), real);
        let sort = tm.sorts.array(int, real);
        let array = tm.mk_apply(nixie_core::reserved::CONST_ARRAY_FUNC, [fraction], sort);
        let unpinned = tm.mk_var("i", int);
        let read = tm.intern_term(TermKind::Select(array, unpinned), real);
        let value = Solver::new().eval_under_interpretation(read, &Model::new(), &tm);
        let EvalOutcome::Value(value) = value else {
            panic!("closed default must evaluate");
        };
        assert_eq!(
            value.to_big(),
            Some(num_rational::BigRational::new(2.into(), 3.into()))
        );
        let zero = tm.mk_real(Rational64::from_integer(0));
        let div_zero = tm.intern_term(TermKind::Div(two, zero), real);
        assert_eq!(
            Solver::new().eval_under_interpretation(div_zero, &Model::new(), &tm),
            EvalOutcome::UNDETERMINED
        );
    }

    #[test]
    fn alias_chains_and_cycles_use_the_heap_in_both_readings() {
        std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let mut tm = TermManager::new();
                let mut model = Model::new();
                let mut previous = tm.mk_int(7);
                for index in 0..20_000 {
                    let var = tm.mk_var(&format!("alias{index}"), tm.sorts.int_sort);
                    model.set(var, previous);
                    previous = var;
                }
                let solver = Solver::new();
                solver.eq_collision_verifies.set(true);
                assert_eq!(
                    solver.eval_under_interpretation(previous, &model, &tm),
                    EvalOutcome::UNDETERMINED
                );
                assert_eq!(
                    solver.eval_in_model_outcome(previous, &model, &tm, 0),
                    EvalOutcome::UNDETERMINED
                );
                model.set(previous, previous);
                assert_eq!(
                    solver.eval_under_interpretation(previous, &model, &tm),
                    EvalOutcome::UNDETERMINED
                );
                assert_eq!(
                    solver.eval_in_model_outcome(previous, &model, &tm, 0),
                    EvalOutcome::UNDETERMINED
                );
            })
            .expect("test worker")
            .join()
            .expect("heap walk must not overflow");
    }

    #[test]
    fn proposed_scalar_values_must_match_their_sort() {
        let mut tm = TermManager::new();
        let bv8 = tm.sorts.bitvec(8);
        let x = tm.mk_var("x", bv8);
        let bad = tm.mk_bitvec(15u8, 4);
        let mut model = Model::new();
        model.set(x, bad);
        assert_eq!(
            Solver::new().eval_under_interpretation(x, &model, &tm),
            EvalOutcome::UNDETERMINED
        );
        let int = tm.mk_var("n", tm.sorts.int_sort);
        let half = tm.mk_real(Rational64::new(1, 2));
        model.set(int, half);
        assert_eq!(
            Solver::new().eval_under_interpretation(int, &model, &tm),
            EvalOutcome::UNDETERMINED
        );
    }
}
