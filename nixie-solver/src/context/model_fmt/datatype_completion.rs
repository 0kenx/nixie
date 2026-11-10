//! Bounded concrete constructor proposals, accepted only by exact evaluation
//! of every original assertion under the resulting printed interpretation.
use super::*;

impl Context {
    pub(super) fn repair_datatype_publication(&mut self) -> bool {
        let declarations: Vec<_> = self
            .declared_consts
            .iter()
            .filter(|d| self.terms.sorts.datatype_name(d.sort).is_some())
            .map(|d| (d.term, d.sort))
            .collect();
        if declarations.is_empty() || declarations.len() > 64 {
            return false;
        }
        let Some(original) = self.published_model().cloned() else {
            return false;
        };
        let mut pools: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
        let mut definitions = Vec::new();
        let mut stack: Vec<_> = declarations.iter().map(|(_, sort)| *sort).collect();
        let mut seen = FxHashSet::default();
        while let Some(sort) = stack.pop() {
            if !seen.insert(sort) {
                continue;
            }
            if seen.len() > 64 {
                return false;
            }
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
                });
            if let Some(constructors) = constructors {
                for (_, fields) in &constructors {
                    stack.extend(fields.iter().copied());
                }
                definitions.push((sort, constructors));
            } else if sort == self.terms.sorts.bool_sort {
                pools.insert(sort, vec![self.terms.mk_false(), self.terms.mk_true()]);
            } else if let Some(value) =
                crate::solver::model_builder::ground_default_term(&mut self.terms, sort)
            {
                pools.insert(sort, vec![value]);
            }
        }
        // Monotone finite construction: recursive sorts acquire only finite
        // values. Round/size limits restrict proposals, never certification.
        for _ in 0..4 {
            let mut changed = false;
            for (sort, constructors) in &definitions {
                for (name, fields) in constructors {
                    let mut tuples = vec![Vec::new()];
                    for field in fields {
                        let Some(values) = pools.get(field) else {
                            tuples.clear();
                            break;
                        };
                        if tuples
                            .len()
                            .checked_mul(values.len())
                            .is_none_or(|n| n > 128)
                        {
                            tuples.clear();
                            break;
                        }
                        tuples = tuples
                            .into_iter()
                            .flat_map(|tuple| {
                                values.iter().map(move |&value| {
                                    let mut args = tuple.clone();
                                    args.push(value);
                                    args
                                })
                            })
                            .collect();
                    }
                    for args in tuples {
                        let value = self.terms.mk_dt_constructor(name, args, *sort);
                        let pool = pools.entry(*sort).or_default();
                        if pool.len() < 128 && !pool.contains(&value) {
                            pool.push(value);
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let domains: Option<Vec<_>> = declarations
            .iter()
            .map(|(_, sort)| pools.get(sort).cloned())
            .collect();
        let Some(domains) = domains else {
            return false;
        };
        if domains.iter().any(Vec::is_empty) {
            return false;
        }
        let saved = self.published.model.take();
        let mut distinct = original.clone();
        for (index, ((term, _), domain)) in declarations.iter().zip(&domains).enumerate() {
            let Some(&value) = domain.get(index % domain.len()) else {
                self.published.model = saved;
                return false;
            };
            distinct.set(*term, value);
        }
        self.published.model = Some(distinct);
        if self.datatype_proposal_holds() {
            return true;
        }
        let Some(total) = domains
            .iter()
            .try_fold(1usize, |n, d| n.checked_mul(d.len()).filter(|&n| n <= 256))
        else {
            self.published.model = saved;
            return false;
        };
        for mut ordinal in 0..total {
            let mut model = original.clone();
            for ((term, _), domain) in declarations.iter().zip(&domains) {
                let Some(&value) = domain.get(ordinal % domain.len()) else {
                    self.published.model = saved;
                    return false;
                };
                ordinal /= domain.len();
                model.set(*term, value);
            }
            self.published.model = Some(model);
            if self.datatype_proposal_holds() {
                return true;
            }
        }
        self.published.model = saved;
        false
    }

    pub(super) fn datatype_proposal_holds(&mut self) -> bool {
        if let Some((printed, mut parse)) = self.printed_constants()
            && let Ok(funcs) = self.printed_functions(&mut parse)
        {
            let goal: Vec<_> = self
                .certified_goal()
                .into_iter()
                .map(|t| self.expand_printed_functions(t, &funcs))
                .collect();
            return self.certified_by_evaluation(&goal, &printed);
        }
        false
    }
}
