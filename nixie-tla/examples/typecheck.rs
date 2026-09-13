//! Run type inference over every definition of every module given, and tally.
//!
//! The corpus is the measurement: a type system that works on the examples in
//! its own test file says nothing. Every previous slice of this front end
//! found its real bugs here rather than in a unit test.
//!
//! Usage: `cargo run -p nixie-tla --example typecheck -- FILE...`
//! with `NIXIE_TLA_LIB` a `:`-separated search path for `EXTENDS`.

use std::collections::BTreeMap;

fn main() {
    let lib = std::env::var("NIXIE_TLA_LIB").ok();
    let mut total = 0usize;
    let mut typed = 0usize;
    let mut failed: BTreeMap<String, usize> = BTreeMap::new();
    let mut examples: BTreeMap<String, String> = BTreeMap::new();
    let mut shapes: BTreeMap<String, usize> = BTreeMap::new();
    let mut free_shapes: BTreeMap<String, usize> = BTreeMap::new();

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
            total += 1;
            let mut inf = nixie_tla::Inference::new();
            match inf.infer(&k) {
                Ok(t) => {
                    typed += 1;
                    let rendered = match inf.to_type(t) {
                        Ok(ty) => shape_name(&ty),
                        Err(_) => "<too large>".to_string(),
                    };
                    *shapes.entry(rendered).or_default() += 1;
                    let frees: Vec<nixie_tla::TyId> = inf.free_names().map(|(_, id)| id).collect();
                    for id in frees {
                        let s = match inf.to_type(id) {
                            Ok(ty) => shape_name(&ty),
                            Err(_) => "<too large>".to_string(),
                        };
                        *free_shapes.entry(s).or_default() += 1;
                    }
                }
                Err(e) => {
                    let key = kind_of(&e);
                    *failed.entry(key.clone()).or_default() += 1;
                    examples
                        .entry(key)
                        .or_insert_with(|| format!("{}!{name}: {e}", base(&path)));
                }
            }
        }
    }

    println!("{total} definitions lowered");
    println!(
        "  typed        : {typed}  ({:.1}%)",
        100.0 * typed as f64 / total.max(1) as f64
    );
    println!("  not typed    : {}", total - typed);
    let mut f: Vec<_> = failed.into_iter().collect();
    f.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (k, n) in &f {
        println!("    {n:6}  {k}");
        if let Some(ex) = examples.get(k) {
            println!("            e.g. {ex}");
        }
    }
    println!("  definition types:");
    dump(&shapes);
    println!("  free-name types (constants and state variables):");
    dump(&free_shapes);
}

fn dump(m: &BTreeMap<String, usize>) {
    let mut v: Vec<_> = m.iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    for (k, n) in v.iter().take(14) {
        println!("    {n:6}  {k}");
    }
}

fn base(p: &str) -> &str {
    p.rsplit('/').next().unwrap_or(p)
}

/// Group an error by kind, not by the names it happens to mention.
fn kind_of(e: &nixie_tla::TypeError) -> String {
    use nixie_tla::TypeError as T;
    match e {
        // Grouped by the *pair of shapes*, not the names involved: "Str vs
        // Int" and "Set vs function" are different problems and a single
        // "type mismatch" bucket hides which one dominates.
        T::Mismatch { left, right } => {
            return format!("type mismatch: {} vs {}", outer(left), outer(right));
        }
        T::Occurs { .. } => "occurs check",
        T::NoField { .. } => "missing record field",
        T::Ambiguous { .. } => "ambiguous shape (tuple / sequence / function)",
        T::TupleIndex { .. } => "tuple index out of range",
        T::BudgetExhausted { .. } => "budget exhausted",
        T::ArenaFull { .. } => "arena full",
    }
    .to_string()
}

/// The head of a rendered type, so a tally groups by shape.
fn outer(s: &str) -> String {
    let s = s.trim();
    for (p, n) in [
        ("Set(", "Set"),
        ("Seq(", "Seq"),
        ("<<", "tuple"),
        ("[", "record"),
        ("(", "function"),
        ("'", "'var"),
    ] {
        if s.starts_with(p) {
            return n.to_string();
        }
    }
    s.to_string()
}

/// The outermost constructor, so the tally is about shapes not element types.
fn shape_name(t: &nixie_tla::Type) -> String {
    use nixie_tla::Type as T;
    match t {
        T::Bool => "Bool".into(),
        T::Int => "Int".into(),
        T::Str => "Str".into(),
        T::Set(e) => format!("Set({})", shape_name(e)),
        T::Seq(_) => "Seq(_)".into(),
        T::Fun(_, _) => "(_ -> _)".into(),
        T::Tuple(xs) => format!("<<{} components>>", xs.len()),
        T::Rec { open, .. } => if *open {
            "[.. open record]"
        } else {
            "[record]"
        }
        .into(),
        T::Var(_) => "'unconstrained".into(),
    }
}
