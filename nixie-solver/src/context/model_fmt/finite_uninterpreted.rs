//! Bounded finite interpretations for pure quantified UF.
//!
//! Following CVC5's finite-model checking, enumerate every tuple of each
//! chosen universe, including function closure. Unsatisfiability at a bound
//! says nothing about larger models. A successful proposal is independently
//! evaluated against all original assertions before publication.
use super::*;

const MAX_POINTS: usize = 4096;

fn tuples(sorts: &[SortId], domains: &FxHashMap<SortId, Vec<TermId>>) -> Option<Vec<Vec<TermId>>> {
    let mut rows = vec![Vec::new()];
    for sort in sorts {
        let domain = domains.get(sort)?;
        if rows.len().checked_mul(domain.len())? > MAX_POINTS {
            return None;
        }
        rows = rows
            .into_iter()
            .flat_map(|row| {
                domain.iter().map(move |&value| {
                    let mut next = row.clone();
                    next.push(value);
                    next
                })
            })
            .collect();
    }
    Some(rows)
}

impl Context {
    pub(super) fn publish_finite_uninterpreted(&mut self) -> bool {
        let goal = self.certified_goal();
        let mut sorts = FxHashSet::default();
        let mut seen = FxHashSet::default();
        let mut stack = goal.clone();
        let mut quantified = false;
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > 4096 {
                return false;
            }
            let Some(node) = self.terms.get(term) else {
                return false;
            };
            sorts.insert(node.sort);
            match &node.kind {
                TermKind::Forall { vars, .. } | TermKind::Exists { vars, .. } => {
                    quantified = true;
                    sorts.extend(vars.iter().map(|(_, sort)| *sort));
                }
                TermKind::True
                | TermKind::False
                | TermKind::Var(_)
                | TermKind::Apply { .. }
                | TermKind::Eq(..)
                | TermKind::Distinct(_)
                | TermKind::And(_)
                | TermKind::Or(_)
                | TermKind::Not(_)
                | TermKind::Implies(..)
                | TermKind::Xor(..)
                | TermKind::Ite(..) => {}
                _ => return false,
            }
            stack.extend(nixie_core::ast::traversal::get_children(&node.kind));
        }
        if !quantified {
            return false;
        }
        for decl in &self.declared_consts {
            sorts.insert(decl.sort);
        }
        for decl in &self.declared_funs {
            if decl.interpreted {
                continue;
            }
            sorts.insert(decl.ret_sort);
            sorts.extend(decl.arg_sorts.iter().copied());
        }
        if sorts
            .iter()
            .any(|&s| s != self.terms.sorts.bool_sort && !self.is_uninterpreted_sort(s))
        {
            return false;
        }
        let mut sorts: Vec<_> = sorts.into_iter().collect();
        sorts.sort_unstable_by_key(|s| s.0);
        let saved = self.published.clone();
        for size in 1..=4 {
            let mut domains = FxHashMap::default();
            let mut symbols = FxHashMap::default();
            for &sort in &sorts {
                let values = if sort == self.terms.sorts.bool_sort {
                    vec![self.terms.mk_false(), self.terms.mk_true()]
                } else {
                    (0..size)
                        .map(|i| {
                            let name = self.format_uninterpreted_witness(sort, i);
                            let name = name
                                .strip_prefix('|')
                                .and_then(|s| s.strip_suffix('|'))
                                .unwrap_or(&name);
                            symbols.insert(name.to_string(), sort);
                            self.terms.mk_var(name, sort)
                        })
                        .collect()
                };
                domains.insert(sort, values);
            }
            if let Some(proposal) = self.finite_uf_proposal(&goal, &domains, symbols) {
                self.published = proposal;
                // This independent, query-free certificate checks the actual
                // rendered functions, constants, and chosen finite universes.
                if self.datatype_proposal_holds() {
                    return true;
                }
            }
            self.published = saved.clone();
        }
        false
    }

    fn finite_uf_proposal(
        &mut self,
        goal: &[TermId],
        domains: &FxHashMap<SortId, Vec<TermId>>,
        symbols: FxHashMap<String, SortId>,
    ) -> Option<PublishedModel> {
        let mut constraints = Vec::new();
        let mut work = MAX_POINTS;
        for &assertion in goal {
            constraints.push(expand(assertion, domains, &mut work, &mut self.terms)?);
        }
        for (&sort, values) in domains {
            if sort != self.terms.sorts.bool_sort {
                constraints.push(self.terms.mk_distinct(values.clone()));
            }
        }
        let mut observations = self
            .declared_consts
            .iter()
            .map(|d| (d.term, d.sort))
            .collect::<Vec<_>>();
        let mut applications = Vec::new();
        for decl in self.declared_funs.clone() {
            if decl.interpreted || decl.arg_sorts.is_empty() {
                continue;
            }
            for args in tuples(&decl.arg_sorts, domains)? {
                if observations.len() >= MAX_POINTS {
                    return None;
                }
                let term = self.terms.mk_apply(&decl.name, args.clone(), decl.ret_sort);
                observations.push((term, decl.ret_sort));
                applications.push((decl.name.clone(), args, term, decl.ret_sort));
            }
        }
        for &(term, sort) in &observations {
            if sort == self.terms.sorts.bool_sort {
                continue;
            }
            let choices: Vec<_> = domains
                .get(&sort)?
                .iter()
                .map(|&v| self.terms.mk_eq(term, v))
                .collect();
            constraints.push(self.terms.mk_or(choices));
        }
        let query = self.terms.mk_and(constraints);
        let solver = self
            .solver
            .publication_candidate_query(query, &mut self.terms)?;
        let model = solver.model()?;
        let mut values = FxHashMap::default();
        for (term, sort) in observations {
            let value = if sort == self.terms.sorts.bool_sort {
                let Some(crate::solver::EvalVal::Bool(value)) = solver
                    .eval_under_interpretation(term, model, &self.terms)
                    .value_owned()
                else {
                    return None;
                };
                self.terms.mk_bool(value)
            } else {
                let class = solver.euf_class_representative(term)?;
                domains
                    .get(&sort)?
                    .iter()
                    .copied()
                    .find(|&v| solver.euf_class_representative(v) == Some(class))?
            };
            let domain = domains.get(&sort)?;
            let index = domain.iter().position(|&v| v == value)?;
            let selected = crate::policy_control::index(index, domain.len(), u64::from(term.raw()));
            values.insert(term, *domain.get(selected)?);
        }
        let mut proposed = PublishedModel::default();
        let mut model = crate::solver::Model::new();
        for decl in &self.declared_consts {
            let value = *values.get(&decl.term)?;
            model.set(decl.term, value);
            proposed.literal_values.insert(
                decl.term,
                nixie_core::smtlib::Printer::new(&self.terms).print_term(value),
            );
        }
        for (name, args, term, sort) in applications {
            let value = *values.get(&term)?;
            let printer = nixie_core::smtlib::Printer::new(&self.terms);
            let default = printer.print_term(*domains.get(&sort)?.first()?);
            let table = proposed
                .function_overrides
                .entry(name)
                .or_insert_with(|| (Vec::new(), default, args.len()));
            table.0.push((
                args.into_iter().map(|t| printer.print_term(t)).collect(),
                printer.print_term(value),
            ));
        }
        proposed.model = Some(model);
        proposed.witness_symbols = symbols;
        Some(proposed)
    }
}

/// Postorder elimination also handles alternating and negated quantifiers:
/// each binder becomes its exact finite conjunction or disjunction.
fn expand(
    root: TermId,
    domains: &FxHashMap<SortId, Vec<TermId>>,
    work: &mut usize,
    terms: &mut nixie_core::TermManager,
) -> Option<TermId> {
    let mut stack = vec![(root, false)];
    let mut done = FxHashMap::default();
    while let Some((term, finish)) = stack.pop() {
        if done.contains_key(&term) {
            continue;
        }
        let kind = terms.get(term)?.kind.clone();
        if !finish {
            *work = work.checked_sub(1)?;
            stack.push((term, true));
            for child in nixie_core::ast::traversal::get_children(&kind) {
                stack.push((child, false));
            }
            continue;
        }
        let result = match kind {
            TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
                let universal = matches!(terms.get(term)?.kind, TermKind::Forall { .. });
                let body = *done.get(&body)?;
                let sorts: Vec<_> = vars.iter().map(|(_, sort)| *sort).collect();
                let mut variables = Vec::new();
                for &(name, sort) in &vars {
                    let name = terms.resolve_str(name).to_string();
                    variables.push(terms.mk_var(&name, sort));
                }
                let rows = tuples(&sorts, domains)?;
                *work = work.checked_sub(rows.len())?;
                let instances: Vec<_> = rows
                    .into_iter()
                    .map(|row| {
                        let substitution = variables.iter().copied().zip(row).collect();
                        terms.substitute(body, &substitution)
                    })
                    .collect();
                if universal {
                    terms.mk_and(instances)
                } else {
                    terms.mk_or(instances)
                }
            }
            _ => {
                let replacements = nixie_core::ast::traversal::get_children(&kind)
                    .into_iter()
                    .map(|child| Some((child, *done.get(&child)?)))
                    .collect::<Option<FxHashMap<_, _>>>()?;
                terms.substitute(term, &replacements)
            }
        };
        done.insert(term, result);
    }
    done.get(&root).copied()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn propose(source: &str) -> (Context, bool) {
        let mut ctx = Context::new();
        ctx.execute_script(source).expect("script");
        ctx.last_result = Some(SolverResult::Sat);
        let result = ctx.publish_finite_uninterpreted();
        (ctx, result)
    }

    #[test]
    fn incompatible_quantifiers_cannot_share_different_interpretations() {
        let (_, valid) = propose(
            "(declare-sort U 0)(declare-fun p (U) Bool)
            (assert (forall ((x U)) (p x)))(assert (exists ((x U)) (not (p x))))",
        );
        assert!(!valid);
    }

    #[test]
    fn finite_function_results_are_closed_and_queries_read_the_same_table() {
        let (mut ctx, valid) = propose(
            "(declare-sort U 0)(declare-const a U)(declare-fun f (U) U)
            (assert (forall ((x U)) (= (f (f x)) x)))
            (assert (forall ((x U)) (not (= (f x) x))))",
        );
        assert!(valid);
        let a = ctx
            .declared_consts
            .iter()
            .find(|d| d.name == "a")
            .expect("a")
            .term;
        let sort = ctx.terms.get(a).expect("sort").sort;
        let fa = ctx.terms.mk_apply("f", vec![a], sort);
        let ffa = ctx.terms.mk_apply("f", vec![fa], sort);
        let involution = ctx.terms.mk_eq(ffa, a);
        let fixed = ctx.terms.mk_eq(fa, a);
        let keys = ["(= (f (f a)) a)", "(= (f a) a)", "a", "(f a)"].map(str::to_owned);
        let out = ctx.format_get_value(&[involution, fixed, a, fa], &keys);
        assert!(out.contains("((= (f (f a)) a) true)"), "{out}");
        assert!(out.contains("((= (f a) a) false)"), "{out}");
        assert!(out.contains("(f a) @uc_U_"), "{out}");
    }

    #[test]
    fn negated_alternation_is_expanded_with_its_original_polarity() {
        let (_, valid) = propose(
            "(declare-sort U 0)(assert (not (forall ((x U)) (exists ((y U)) (distinct x y)))))",
        );
        assert!(valid);
        let (_, invalid) =
            propose("(declare-sort U 0)(assert (not (forall ((x U)) (exists ((y U)) (= x y)))))");
        assert!(!invalid);
    }
}
