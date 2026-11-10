//! Bounded datatype model completion, retaining original and encoded field pins.
//!
//! Proposals change only unmentioned fields and entire proven equality classes.
//! They must remove a decided collision without creating another collision or
//! breaking a known equality. The normal model-certification gates still decide
//! whether the complete interpretation can be published.

use super::*;
use nixie_sat::{LBool, Var};
use num_rational::BigRational;

const MAX_OFFSET: i64 = 8;
const MAX_REPAIR_WORK: usize = 1_000_000;

type Pair = (TermId, TermId);
type Adjacency = FxHashMap<TermId, Vec<TermId>>;

struct Requirements<'a> {
    disequalities: &'a [Pair],
    equalities: &'a Adjacency,
}

#[derive(Default)]
struct Violations {
    datatype: FxHashSet<Pair>,
    numeric: FxHashSet<Var>,
    equality: FxHashSet<Pair>,
}

impl Violations {
    fn probe_improves(&self, before: &Self) -> bool {
        self.datatype.is_subset(&before.datatype)
            && self.numeric.is_subset(&before.numeric)
            && self.equality.is_subset(&before.equality)
            && (self.datatype.len() < before.datatype.len()
                || self.numeric.len() < before.numeric.len())
    }
}

fn probe_spend(work: &mut usize) -> Option<()> {
    *work = work.checked_sub(1)?;
    Some(())
}

impl Solver {
    pub(super) fn probe_separate_datatype_models(
        &self,
        decls: &FxHashMap<SortId, DeclInfo>,
        hints: &FxHashMap<TermId, Vec<String>>,
        injectivity_pairs: &[Pair],
        model: &mut Model,
        manager: &mut TermManager,
    ) {
        let (mut disequalities, equalities) = self.decided_dt_equalities(model, manager);
        disequalities.extend(injectivity_pairs.iter().copied());
        disequalities.sort_unstable();
        disequalities.dedup();
        if disequalities.is_empty() {
            return;
        }
        let mut roots = self.assertions.clone();
        roots.extend(self.certificate_assertions.iter().copied());
        roots.extend(self.ground_instance_roots.iter().copied());
        let pinned = assertion_subterms(&roots, manager);
        let requirements = Requirements {
            disequalities: &disequalities,
            equalities: &equalities,
        };
        let mut work = MAX_REPAIR_WORK;
        for &(left, right) in &disequalities {
            if model.get(left).is_none() || model.get(left) != model.get(right) {
                continue;
            }
            // A fixed constructor on the right can force the left side to move.
            for (term, other) in [(right, left), (left, right)] {
                let Some(class) =
                    self.probe_separation_class(term, &equalities, manager, &mut work)
                else {
                    return;
                };
                if class.contains(&other) {
                    break;
                }
                if self.probe_separate_dt_value(
                    term,
                    &class,
                    &pinned,
                    decls,
                    hints,
                    &requirements,
                    model,
                    manager,
                    &mut work,
                ) {
                    break;
                }
                if work == 0 {
                    return;
                }
            }
        }
    }

    fn probe_separation_class(
        &self,
        term: TermId,
        equalities: &Adjacency,
        manager: &TermManager,
        work: &mut usize,
    ) -> Option<Vec<TermId>> {
        // Both helpers scan their graphs. Charge those scans before starting;
        // repeated unsuccessful repairs must not multiply unbounded EUF work.
        for neighbours in equalities.values() {
            *work = work.checked_sub(neighbours.len().checked_add(1)?)?;
        }
        *work = work.checked_sub(self.model_euf().all_node_indices().len())?;
        let mut class = equality_class(term, equalities);
        let sort = manager.get(term).map(|node| node.sort);
        let euf = self.model_euf();
        if let Some(node) = euf.term_to_node(term) {
            for member in euf.class_members(euf.find_immutable(node)) {
                if let Some(term) = euf.node_term(member)
                    && manager.get(term).map(|node| node.sort) == sort
                {
                    class.push(term);
                }
            }
        }
        class.sort_unstable();
        class.dedup();
        Some(class)
    }

    #[allow(clippy::too_many_arguments)]
    fn probe_separate_dt_value(
        &self,
        term: TermId,
        class: &[TermId],
        pinned: &FxHashSet<TermId>,
        decls: &FxHashMap<SortId, DeclInfo>,
        hints: &FxHashMap<TermId, Vec<String>>,
        requirements: &Requirements<'_>,
        model: &mut Model,
        manager: &mut TermManager,
        work: &mut usize,
    ) -> bool {
        let Some(sort) = manager.get(term).map(|node| node.sort) else {
            return false;
        };
        let Some(decl) = decls.get(&sort) else {
            return false;
        };
        let Some(TermKind::DtConstructor { constructor, args }) = model
            .get(term)
            .and_then(|value| manager.get(value))
            .map(|node| node.kind.clone())
        else {
            return false;
        };
        let name = manager.resolve_str(constructor).to_string();
        let Some(constructor) = decl.constructors.iter().find(|c| c.name == name) else {
            return false;
        };
        if constructor.fields.len() != args.len() {
            return false;
        }
        let hinted = hints.get(&term).cloned().unwrap_or_default();
        let mut order: Vec<_> = (0..constructor.fields.len()).collect();
        for hint in hinted.iter().rev() {
            if let Some(position) = constructor.fields.iter().position(|f| &f.selector == hint) {
                order.retain(|&i| i != position);
                order.insert(0, position);
            }
        }
        let mut changed = false;
        for position in order {
            if probe_spend(work).is_none() {
                return changed;
            }
            let field = &constructor.fields[position];
            let Some(remaining) = work.checked_sub(class.len()) else {
                return changed;
            };
            *work = remaining;
            if probe_field_is_pinned(
                class,
                &name,
                position,
                &field.selector,
                field.sort,
                pinned,
                manager,
            ) {
                continue;
            }
            let Some(TermKind::DtConstructor { args, .. }) = model
                .get(term)
                .and_then(|value| manager.get(value))
                .map(|node| node.kind.clone())
            else {
                return changed;
            };
            if args.len() != constructor.fields.len() {
                return changed;
            }
            let current = args[position];
            let mut candidates = Vec::new();
            if field.sort == manager.sorts.int_sort || field.sort == manager.sorts.real_sort {
                let Some(number) =
                    super::super::array_completion_certify::evaluate_closed_value_pure(
                        self, current, manager,
                    )
                    .and_then(|value| value.to_big())
                else {
                    continue;
                };
                for offset in 1..=MAX_OFFSET {
                    let value = &number + BigRational::from_integer(offset.into());
                    let value = if field.sort == manager.sorts.int_sort {
                        if !value.is_integer() {
                            continue;
                        }
                        manager.mk_int(value.to_integer())
                    } else {
                        let numerator = manager.mk_int(value.numer().clone());
                        let denominator = manager.mk_int(value.denom().clone());
                        manager.mk_rdiv(numerator, denominator)
                    };
                    candidates.push(value);
                }
            } else if manager.sorts.is_datatype(field.sort) {
                let Some(field_decl) = resolve_decl(field.sort, manager) else {
                    continue;
                };
                for candidate_constructor in field_decl.constructors {
                    if probe_spend(work).is_none() {
                        return changed;
                    }
                    let mut args = Vec::new();
                    for field in &candidate_constructor.fields {
                        let Some(value) = ground_default_term(manager, field.sort) else {
                            break;
                        };
                        args.push(value);
                    }
                    if args.len() == candidate_constructor.fields.len() {
                        candidates.push(manager.mk_dt_constructor(
                            &candidate_constructor.name,
                            args,
                            field.sort,
                        ));
                    }
                }
            }
            let Some(before) = self.probe_separation_violations(model, requirements, manager, work)
            else {
                return changed;
            };
            for candidate in candidates {
                if candidate == current {
                    continue;
                }
                let mut new_args = args.to_vec();
                new_args[position] = candidate;
                let value = manager.mk_dt_constructor(&name, new_args, sort);
                let mut trial = model.clone();
                for &member in class {
                    let accessor = manager.mk_dt_selector(&field.selector, member, field.sort);
                    trial.set(accessor, candidate);
                    trial.set(member, value);
                }
                let Some(after) =
                    self.probe_separation_violations(&trial, requirements, manager, work)
                else {
                    return changed;
                };
                if !after.probe_improves(&before) {
                    continue;
                }
                *model = trial;
                changed = true;
                break;
            }
            if changed && !hinted.iter().any(|hint| hint == &field.selector) {
                return true;
            }
        }
        changed
    }

    fn probe_separation_violations(
        &self,
        model: &Model,
        requirements: &Requirements<'_>,
        manager: &TermManager,
        work: &mut usize,
    ) -> Option<Violations> {
        let mut result = Violations::default();
        for &(left, right) in requirements.disequalities {
            probe_spend(work)?;
            if let (Some(a), Some(b)) = (model.get(left), model.get(right))
                && a == b
            {
                result.datatype.insert((left, right));
            }
        }
        for (&left, neighbours) in requirements.equalities {
            for &right in neighbours {
                probe_spend(work)?;
                if left < right
                    && let (Some(a), Some(b)) = (model.get(left), model.get(right))
                    && a != b
                {
                    result.equality.insert((left, right));
                }
            }
        }
        for (&var, constraint) in &self.var_to_constraint {
            probe_spend(work)?;
            let Constraint::Eq(left, right) = *constraint else {
                continue;
            };
            if self.sat.model_value(var) != LBool::False {
                continue;
            }
            if !manager.get(left).is_some_and(|node| {
                node.sort == manager.sorts.int_sort || node.sort == manager.sorts.real_sort
            }) {
                continue;
            }
            let a = self
                .eval_datatype_repair(left, model, manager)
                .value_owned()
                .and_then(|value| value.to_big());
            let b = self
                .eval_datatype_repair(right, model, manager)
                .value_owned()
                .and_then(|value| value.to_big());
            if let (Some(a), Some(b)) = (a, b)
                && a == b
            {
                result.numeric.insert(var);
            }
        }
        Some(result)
    }
}

/// Constructor arguments constrain their fields even if purification hid them
/// from the source DAG. Only a reconstruction `C(sel_C(t), ...)` leaves a field
/// free; literal constructor classes cannot be re-valued.
fn probe_field_is_pinned(
    class: &[TermId],
    constructor: &str,
    position: usize,
    selector: &str,
    sort: SortId,
    pinned: &FxHashSet<TermId>,
    manager: &mut TermManager,
) -> bool {
    let selector_name = manager.intern_str(selector);
    for &member in class {
        let accessor = manager.mk_dt_selector(selector, member, sort);
        if pinned.contains(&accessor) {
            return true;
        }
        if let Some(TermKind::DtConstructor {
            constructor: name,
            args,
        }) = manager.get(member).map(|node| &node.kind)
        {
            if manager.resolve_str(*name) != constructor {
                return true;
            }
            let Some(&field) = args.get(position) else {
                return true;
            };
            if !matches!(manager.get(field).map(|node| &node.kind),
                Some(TermKind::DtSelector { selector, arg }) if *selector == selector_name && class.contains(arg))
            {
                return true;
            }
        }
    }
    false
}
