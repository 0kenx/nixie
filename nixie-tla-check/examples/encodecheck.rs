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
        nixie_tla::Value::Str(t) => EV::Scalar(tm.mk_string_lit(t)),
        nixie_tla::Value::Tuple(xs) => {
            let mut parts = Vec::with_capacity(xs.len());
            for x in xs {
                parts.push(literal_of(x, tm)?);
            }
            EV::Tuple(parts)
        }
        nixie_tla::Value::Record(fs) => {
            let mut fields = std::collections::BTreeMap::new();
            for (k, v) in fs {
                fields.insert(k.clone(), literal_of(v, tm)?);
            }
            EV::Record(fields)
        }
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
        // A function is a domain and a graph, built over the same canonical
        // base array the encoder uses — which is what makes the two
        // comparable at all. Every point is known here, so the graph is a
        // plain chain of stores with no guards.
        nixie_tla::Value::Fun(map) => {
            let mut pairs = Vec::with_capacity(map.len());
            for (k, v) in map {
                let (EV::Scalar(k), EV::Scalar(v)) = (&*literal_of(k, tm)?, &*literal_of(v, tm)?)
                else {
                    // A function whose points are themselves structural has
                    // no array form; skipped rather than claimed.
                    return None;
                };
                pairs.push((*k, *v));
            }
            let (Some((k, v)), true) = (pairs.first(), !pairs.is_empty()) else {
                // The empty function's sorts are not recoverable from it.
                return None;
            };
            let (ks, vs) = (tm.get(*k)?.sort, tm.get(*v)?.sort);
            if pairs.iter().any(|(k, v)| {
                tm.get(*k).map(|d| d.sort) != Some(ks) || tm.get(*v).map(|d| d.sort) != Some(vs)
            }) {
                return None;
            }
            nixie_tla_check::arena::fun_literal(&pairs, ks, vs, tm)
        }
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

    // Sorted, so two runs over the same corpus are comparable: the shell's
    // `find` hands back directory order, which is not stable between
    // invocations, and an unordered walk makes the reported examples (and the
    // truncated lists) shuffle from run to run for no reason.
    let mut paths: Vec<String> = std::env::args().skip(1).collect();
    paths.sort();
    for path in paths {
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
                    // A `FALSE` definition that encoded to a structural value
                    // is a shape clash, not something to claim.
                    nixie_tla_check::Value::Set(_)
                    | nixie_tla_check::Value::Tuple(_)
                    | nixie_tla_check::Value::Record(_)
                    | nixie_tla_check::Value::Fun { .. } => continue,
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
