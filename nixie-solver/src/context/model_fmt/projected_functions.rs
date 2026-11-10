//! Numeric projection proposals. As in MBQI's relevant-set completion, each
//! interval maps to a representative; only an independent certificate of the
//! entire printed interpretation can accept the proposal.
use super::*;

impl Context {
    pub(super) fn repair_projected_functions(&mut self) -> bool {
        let Some(model) = self.published_model().cloned() else {
            return false;
        };
        let classes = self.build_class_values(&model);
        let names: Vec<_> = self
            .declared_funs
            .iter()
            .filter(|d| {
                !d.interpreted
                    && d.arg_sorts.len() == 1
                    && (d.arg_sorts[0] == self.terms.sorts.int_sort
                        || d.arg_sorts[0] == self.terms.sorts.real_sort)
            })
            .map(|d| d.name.clone())
            .collect();
        if names.is_empty() || names.len() > 12 {
            return false;
        }
        let saved = self.published.function_overrides.clone();
        let mut replacements = Vec::new();
        for name in names {
            let Some(((entries, _, _), _)) =
                self.func_interp_reading(&name, &model, &classes, false)
            else {
                continue;
            };
            if entries.is_empty() || entries.len() > 128 {
                continue;
            }
            let mut points = Vec::new();
            let mut readable = true;
            for (args, value) in entries {
                let [arg] = args.as_slice() else {
                    readable = false;
                    break;
                };
                let Ok(term) = nixie_core::smtlib::parse_term(arg, &mut self.terms) else {
                    readable = false;
                    break;
                };
                let number = match self
                    .solver
                    .eval_under_interpretation(term, &crate::solver::Model::new(), &self.terms)
                    .value_owned()
                {
                    Some(crate::solver::EvalVal::Num(n)) => {
                        num_rational::BigRational::new((*n.numer()).into(), (*n.denom()).into())
                    }
                    Some(crate::solver::EvalVal::NumBig(n)) => *n,
                    _ => {
                        readable = false;
                        break;
                    }
                };
                points.push((number, arg.clone(), value));
            }
            if !readable {
                continue;
            }
            points.sort();
            if points
                .windows(2)
                .any(|w| w[0].0 == w[1].0 && w[0].2 != w[1].2)
            {
                continue;
            }
            let mut outputs: Vec<_> = points.iter().map(|p| p.2.clone()).collect();
            crate::policy_control::rotate(&mut outputs, points.len() as u64);
            for (point, value) in points.iter_mut().zip(outputs) {
                point.2 = value;
            }
            let Some((_, _, last)) = points.last() else {
                continue;
            };
            let mut body = last.clone();
            for (_, arg, value) in points.iter().rev().skip(1) {
                body = format!("(ite (<= x!0 {arg}) {value} {body})");
            }
            replacements.push((name, (Vec::new(), body, 1)));
        }
        if replacements.is_empty() {
            return false;
        }
        self.published.function_overrides.extend(replacements);
        if self.certify_printed_goal().is_ok() {
            return true;
        }
        self.published.function_overrides = saved;
        false
    }
}
