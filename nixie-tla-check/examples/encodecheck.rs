//! Cross-check the encoder against the evaluator on every ground definition.
//!
//! The evaluator is validated against TLC by `bench/tla_eval`. Checking the
//! encoder against the evaluator therefore validates it against TLA+ semantics
//! transitively, without needing a second oracle:
//!
//! * a definition the evaluator says is `TRUE` must encode to a formula whose
//!   **negation is unsatisfiable**, and which is itself satisfiable;
//! * one it says is `FALSE` must encode to an unsatisfiable formula;
//! * one that evaluates to an integer `n` must make `t = n` valid.
//!
//! The terms are ground, so each is a closed formula and the solver's answer
//! is a decision, not a search.

use std::collections::BTreeMap;

use nixie_core::TermManager;
use nixie_solver::SolverResult;

/// The evaluator's value as an encoder value, so the two can be compared.
///
/// Returns `None` for a value the encoder has no representation for yet —
/// tuples, records and functions — so those are skipped rather than claimed.
fn literal_of(
    v: &nixie_tla::Value,
    tm: &mut TermManager,
) -> Option<std::rc::Rc<nixie_tla_check::Value>> {
    use nixie_tla_check::{Member, SetCell, Value as EV};
    let out = match v {
        nixie_tla::Value::Bool(b) => EV::Scalar(tm.mk_bool(*b)),
        nixie_tla::Value::Int(n) => EV::Scalar(tm.mk_int(num_bigint::BigInt::from(*n))),
        nixie_tla::Value::Set(xs) => {
            let yes = tm.mk_bool(true);
            let mut members = Vec::with_capacity(xs.len());
            for x in xs {
                members.push(Member {
                    value: literal_of(x, tm)?,
                    present: yes,
                });
            }
            EV::Set(SetCell { members })
        }
        // Strings, tuples, records and functions have no literal form here yet.
        _ => return None,
    };
    Some(std::rc::Rc::new(out))
}

fn main() {
    let lib = std::env::var("NIXIE_TLA_LIB").ok();
    let mut checked = 0usize;
    let mut agreed = 0usize;
    let mut disagreed: Vec<String> = Vec::new();
    let mut unencodable: BTreeMap<String, usize> = BTreeMap::new();
    let mut unknown = 0usize;
    let mut unknown_names: Vec<String> = Vec::new();

    for path in std::env::args().skip(1) {
        let mut loader = nixie_tla_syntax::Loader::new();
        if let Some(l) = &lib {
            for d in l.split(':').filter(|d| !d.is_empty()) {
                loader = loader.with_search_path(d);
            }
        }
        let Ok(spec) = loader.load(std::path::Path::new(&path)) else {
            continue;
        };
        let Some(module) = spec.root_module() else {
            continue;
        };
        let names: Vec<String> = module
            .units
            .iter()
            .filter_map(|u| match &u.kind {
                nixie_tla_syntax::UnitKind::OpDef { name, params, .. } if params.is_empty() => {
                    Some(name.name.clone())
                }
                _ => None,
            })
            .collect();

        for name in names {
            let mut low = nixie_tla::Lowerer::new();
            low.add_spec(&spec);
            let Ok(k) = low.lower_named(module, &name) else {
                continue;
            };
            let Ok(value) = nixie_tla::Evaluator::new().eval(&k) else {
                continue;
            };

            let mut tm = TermManager::new();
            let mut enc = nixie_tla_check::Encoder::new();
            let encoded = match enc.encode_value(&k, &mut tm) {
                Ok(t) => t,
                Err(e) => {
                    *unencodable.entry(format!("{e}")).or_default() += 1;
                    continue;
                }
            };

            // Build the claim the evaluator is making, as a formula. A
            // set-valued definition is claimed by *extensional equality* with
            // the literal set the evaluator produced, which is what checks the
            // arena's values rather than only Booleans about them.
            let Some(literal) = literal_of(&value, &mut tm) else {
                continue;
            };
            let Some(same) = nixie_tla_check::arena::eq_values(&encoded, &literal, &mut tm) else {
                *unencodable
                    .entry("shape clash between evaluator and encoder".to_string())
                    .or_default() += 1;
                continue;
            };
            let claim = match &value {
                // `A == FALSE` is claimed as `~A`, not `A = FALSE`, so a
                // Boolean definition still exercises the propositional path.
                nixie_tla::Value::Bool(false) => tm.mk_not(match &*encoded {
                    nixie_tla_check::Value::Scalar(t) => *t,
                    nixie_tla_check::Value::Set(_) => continue,
                }),
                _ => same,
            };
            checked += 1;

            // The claim must be *valid*: its negation unsatisfiable.
            let negated = tm.mk_not(claim);
            let mut solver = nixie_solver::Solver::new();
            solver.assert(negated, &mut tm);
            match solver.check(&mut tm) {
                SolverResult::Unsat => agreed += 1,
                SolverResult::Sat => disagreed.push(format!(
                    "{}!{name}: evaluator says {value}, solver found a counterexample",
                    path.rsplit('/').next().unwrap_or(&path)
                )),
                SolverResult::Unknown => {
                    unknown += 1;
                    unknown_names.push(format!(
                        "{}!{name} (evaluator: {value})",
                        path.rsplit('/').next().unwrap_or(&path)
                    ));
                }
            }
        }
    }

    println!("{checked} ground definitions cross-checked against the solver");
    println!("  encoder agrees with the evaluator : {agreed}");
    println!("  DISAGREEMENTS                     : {}", disagreed.len());
    println!("  solver returned Unknown           : {unknown}");
    for d in disagreed.iter().take(20) {
        println!("    {d}");
    }
    for u in unknown_names.iter().take(10) {
        println!("    UNKNOWN {u}");
    }
    let mut v: Vec<_> = unencodable.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!("  not encodable yet:");
    for (r, n) in v.iter().take(10) {
        println!("    {n:6}  {r}");
    }
    if !disagreed.is_empty() {
        std::process::exit(1);
    }
}
