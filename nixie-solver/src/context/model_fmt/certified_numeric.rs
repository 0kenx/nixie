//! Publish the total numeric interpretation the existing exact certifier
//! actually verified, including affine defaults over the reals.
use super::*;
use crate::mbqi::model_certify::real::interp::RealFunc;
use crate::mbqi::model_certify::value::CertValue;
use crate::mbqi::model_certify::{CertifiedInterpretation, certified_interpretation};

fn rational(value: &num_rational::BigRational) -> String {
    if value.denom().is_one() {
        format!("(to_real {})", render_integer(value.numer()))
    } else {
        format!(
            "(/ (to_real {}) (to_real {}))",
            render_integer(value.numer()),
            render_integer(value.denom())
        )
    }
}

fn value_text(value: &CertValue) -> String {
    match value {
        CertValue::Int(n) => render_integer(n),
        CertValue::Real(r) => rational(r),
        CertValue::Bool(b) => b.to_string(),
    }
}

impl Context {
    pub(super) fn publish_numeric_certificate(&mut self) -> bool {
        let Some(model) = self.solver.model() else {
            return false;
        };
        let Some(certified) =
            certified_interpretation(&self.certified_goal(), model.assignments(), &self.terms)
        else {
            return false;
        };
        let mut constants = FxHashMap::default();
        let mut tables = FxHashMap::default();
        match certified {
            CertifiedInterpretation::Discrete(interp) => {
                constants = interp.consts;
                for (name, func) in interp.funcs {
                    let name = self.terms.resolve_str(name).to_string();
                    let Some(decl) = self.declared_funs.iter().find(|d| d.name == name) else {
                        return false;
                    };
                    let mut entries: Vec<_> = func
                        .entries
                        .into_iter()
                        .map(|(args, value)| {
                            (
                                args.iter().map(value_text).collect::<Vec<_>>(),
                                value_text(&value),
                            )
                        })
                        .collect();
                    entries.sort();
                    if entries
                        .iter()
                        .any(|(args, _)| args.len() != decl.arg_sorts.len())
                    {
                        return false;
                    }
                    tables.insert(
                        name,
                        (entries, value_text(&func.default), decl.arg_sorts.len()),
                    );
                }
            }
            CertifiedInterpretation::Real(interp) => {
                constants.extend(
                    interp
                        .consts
                        .into_iter()
                        .map(|(name, value)| (name, CertValue::Real(value))),
                );
                constants.extend(
                    interp
                        .bool_consts
                        .into_iter()
                        .map(|(name, value)| (name, CertValue::Bool(value))),
                );
                for (name, func) in interp.funcs {
                    let name = self.terms.resolve_str(name).to_string();
                    let Some(decl) = self.declared_funs.iter().find(|d| d.name == name) else {
                        return false;
                    };
                    if decl.arg_sorts != [self.terms.sorts.real_sort] {
                        return false;
                    }
                    let (entries, default) = match func {
                        RealFunc::Num { pins, default } => (
                            pins.into_iter()
                                .map(|(arg, value)| (vec![rational(&arg)], rational(&value)))
                                .collect(),
                            format!(
                                "(+ (* {} x!0) {})",
                                rational(&default.a),
                                rational(&default.b)
                            ),
                        ),
                        RealFunc::Bool { pins, default } => (
                            pins.into_iter()
                                .map(|(arg, value)| (vec![rational(&arg)], value.to_string()))
                                .collect(),
                            default.to_string(),
                        ),
                    };
                    tables.insert(name, (entries, default, 1));
                }
            }
        }
        let mut model = crate::solver::Model::new();
        for (name, value) in constants {
            let name = self.terms.resolve_str(name).to_string();
            let sort = match value {
                CertValue::Bool(_) => self.terms.sorts.bool_sort,
                CertValue::Int(_) => self.terms.sorts.int_sort,
                CertValue::Real(_) => self.terms.sorts.real_sort,
            };
            let var = self.terms.mk_var(&name, sort);
            let Ok(value) = nixie_core::smtlib::parse_term(&value_text(&value), &mut self.terms)
            else {
                return false;
            };
            model.set(var, value);
        }
        // Atomic installation: no partly rendered certificate can escape.
        self.published.model = Some(model);
        self.published.function_overrides = tables;
        true
    }
}
