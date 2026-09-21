//! `pcalcheck` — definition parity between two translations of the same
//! PlusCal algorithm (ours and the oracle's).
//!
//! Compares what the *parser* sees, not what a grep sees: the oracle lays
//! `LET`-bound definitions out at column 0 inside an action, which a
//! line-oriented diff would report as extra top-level definitions. Names
//! and levels come from [`nixie_tla_syntax::level::check_module`], so a
//! missing action or a mis-levelled one is a failure by itself.

use std::collections::BTreeMap;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 2 {
        eprintln!("usage: pcalcheck OURS.tla GOLDEN.tla");
        std::process::exit(2);
    }
    let lib = std::env::var("NIXIE_TLA_LIB").unwrap_or_default();
    let mut bad = 0usize;
    let (ours, golden) = match (defs(&args[0], &lib), defs(&args[1], &lib)) {
        (Ok(o), Ok(g)) => (o, g),
        (Err(e), _) | (_, Err(e)) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    };
    let mut names: Vec<&String> = ours.keys().chain(golden.keys()).collect();
    names.sort();
    names.dedup();
    for name in names {
        match (ours.get(name), golden.get(name)) {
            (Some((_, l1)), Some((_, l2))) => {
                if l1 != l2 {
                    println!("{name}: level {l1:?} vs {l2:?}");
                    bad += 1;
                }
            }
            (Some(_), None) => {
                println!("{name}: only in ours");
                bad += 1;
            }
            (None, Some(_)) => {
                println!("{name}: only in golden");
                bad += 1;
            }
            (None, None) => unreachable!("name came from one of the maps"),
        }
    }
    println!("{} definitions, {} mismatch(es)", ours.len(), bad);
    std::process::exit(if bad == 0 { 0 } else { 1 });
}

type Defs = BTreeMap<String, (String, Option<nixie_tla_syntax::Level>)>;

fn defs(path: &str, lib: &str) -> Result<Defs, String> {
    let mut loader = nixie_tla_syntax::Loader::new();
    for d in lib.split(':').filter(|d| !d.is_empty()) {
        loader = loader.with_search_path(d);
    }
    let spec = loader
        .load(std::path::Path::new(path))
        .map_err(|e| format!("{path}: {e}"))?;
    let Some(module) = spec.root_module() else {
        return Err(format!("{path}: no root module"));
    };
    let report = nixie_tla_syntax::level::check_module(module);
    let mut out = BTreeMap::new();
    for u in &module.units {
        if let nixie_tla_syntax::UnitKind::OpDef { name, params, .. } = &u.kind
            && params.is_empty()
        {
            let level = report
                .trusted_level_of(&name.name)
                .or_else(|| report.level_of(&name.name));
            out.insert(name.name.clone(), (String::new(), level));
        }
    }
    Ok(out)
}
