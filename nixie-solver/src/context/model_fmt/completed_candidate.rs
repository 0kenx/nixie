//! Reuse MBQI's concrete tables and macro bodies as publication proposals.
//! A saved search candidate is not itself publication evidence: every emitted
//! function and constant is checked together against the original assertions.
use super::*;
use crate::mbqi::model_checker::{
    choose_else_table, completed_function_body, eval_completed_ground,
};

impl Context {
    pub(super) fn publish_completed_candidate(&mut self) -> bool {
        let Some(candidate) = self.solver.completed_publication_candidate().cloned() else {
            return false;
        };

        let else_table = choose_else_table(&candidate, &mut self.terms);
        let mut roots = Vec::new();
        let mut constants = Vec::new();
        for decl in self.declared_consts.clone() {
            let Ok(value) =
                eval_completed_ground(decl.term, &candidate, &else_table, &mut self.terms)
            else {
                return false;
            };
            roots.push((value, FxHashSet::default()));
            constants.push((decl.term, value));
        }
        let mut functions = Vec::new();
        for decl in self.declared_funs.clone() {
            if decl.interpreted || decl.arg_sorts.is_empty() {
                continue;
            }
            let mut parameters = FxHashSet::default();
            let mut arguments = Vec::new();
            for (i, sort) in decl.arg_sorts.iter().copied().enumerate() {
                let arg = self.terms.mk_var(
                    &nixie_core::reserved::reserved_name("publication-parameter", &i.to_string()),
                    sort,
                );
                let Some(TermKind::Var(name)) = self.terms.get(arg).map(|t| t.kind.clone()) else {
                    return false;
                };
                parameters.insert(name);
                arguments.push(arg);
            }
            let app = self
                .terms
                .mk_apply(&decl.name, arguments.clone(), decl.ret_sort);
            let Ok(body) =
                completed_function_body(app, &parameters, &candidate, &else_table, &mut self.terms)
            else {
                return false;
            };
            roots.push((body, parameters));
            functions.push((decl.name, arguments, body));
        }
        // Replace each semantic element by one fresh, typed printed witness.
        // Function parameters remain symbolic and can never become witnesses.
        let mut replacement = FxHashMap::default();
        let mut elements: FxHashMap<(SortId, TermId), TermId> = FxHashMap::default();
        let mut counters: FxHashMap<SortId, usize> = FxHashMap::default();
        let mut witness_symbols = FxHashMap::default();
        for (root, parameters) in roots {
            for var in self.terms.free_vars_including_patterns(root) {
                let Some(node) = self.terms.get(var) else {
                    return false;
                };
                let TermKind::Var(name) = node.kind else {
                    return false;
                };
                if parameters.contains(&name) {
                    continue;
                }
                let sort = node.sort;
                let Ok(value) =
                    eval_completed_ground(var, &candidate, &else_table, &mut self.terms)
                else {
                    return false;
                };
                if self.is_uninterpreted_sort(sort) {
                    let witness = if let Some(&witness) = elements.get(&(sort, value)) {
                        witness
                    } else {
                        let next = counters.entry(sort).or_default();
                        let text = self.format_uninterpreted_witness(sort, *next);
                        *next += 1;
                        let name = text
                            .strip_prefix('|')
                            .and_then(|s| s.strip_suffix('|'))
                            .unwrap_or(&text);
                        let witness = self.terms.mk_var(name, sort);
                        witness_symbols.insert(name.to_string(), sort);
                        elements.insert((sort, value), witness);
                        witness
                    };
                    replacement.insert(var, witness);
                } else if value != var && self.terms.free_vars_including_patterns(value).is_empty()
                {
                    replacement.insert(var, value);
                } else {
                    return false;
                }
            }
        }

        let saved = self.published.clone();
        let mut proposed = PublishedModel::default();
        let mut model = crate::solver::Model::new();
        for (term, value) in constants {
            let value = self.terms.substitute(value, &replacement);
            model.set(term, value);
            proposed
                .literal_values
                .insert(term, self.format_value(value));
        }
        for (name, parameters, body) in functions {
            let body = self.terms.substitute(body, &replacement);
            let mut rename = FxHashMap::default();
            for (i, &parameter) in parameters.iter().enumerate() {
                let Some(sort) = self.terms.get(parameter).map(|t| t.sort) else {
                    self.published = saved;
                    return false;
                };
                rename.insert(parameter, self.terms.mk_var(&format!("x!{i}"), sort));
            }
            let body = self.terms.substitute(body, &rename);
            let arity = parameters.len();
            if !bounded_print_tree(body, &self.terms) {
                return false;
            }
            let text = nixie_core::smtlib::Printer::new(&self.terms).print_term(body);

            proposed
                .function_overrides
                .insert(name, (Vec::new(), text, arity));
        }
        proposed.model = Some(model);
        proposed.witness_symbols = witness_symbols;
        self.published = proposed;
        let certificate = self.certify_printed_goal();

        if certificate.is_ok() {
            return true;
        }
        self.published = saved;
        false
    }
}

/// Bound the unfolded output, not merely the number of shared DAG nodes.
fn bounded_print_tree(root: TermId, manager: &nixie_core::ast::TermManager) -> bool {
    let mut sizes: FxHashMap<TermId, usize> = FxHashMap::default();
    let mut work = vec![(root, false)];
    while let Some((term, finish)) = work.pop() {
        if sizes.contains_key(&term) {
            continue;
        }
        let Some(node) = manager.get(term) else {
            return false;
        };
        let children = nixie_core::ast::traversal::get_children(&node.kind);
        if finish {
            let mut size = 1usize;
            for child in children {
                let Some(child_size) = sizes.get(&child) else {
                    return false;
                };
                size = size.saturating_add(*child_size);
                if size > 100_000 {
                    return false;
                }
            }
            sizes.insert(term, size);
        } else {
            work.push((term, true));
            work.extend(children.into_iter().map(|child| (child, false)));
        }
    }
    true
}
