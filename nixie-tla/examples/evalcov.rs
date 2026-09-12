//! Evaluate every ground definition of each module, and emit a TLC probe.
//!
//! With `--probe-dir D`, writes one probe module per source module that TLC can
//! run, plus a JSON-ish manifest of what this evaluator computed. Comparing the
//! two is the semantic check that structural parity cannot give.

use std::collections::BTreeMap;
use std::io::Write;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut probe_dir: Option<String> = None;
    if let Some(i) = args.iter().position(|a| a == "--probe-dir") {
        probe_dir = args.get(i + 1).cloned();
        args.drain(i..=i + 1);
    }
    let lib = std::env::var("NIXIE_TLA_LIB").ok();

    let mut evaluated = 0usize;
    let mut lowered = 0usize;
    let mut by_reason: BTreeMap<String, usize> = BTreeMap::new();

    for path in args {
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
        // Constants and variables no longer exclude a module. Only *ground*
        // definitions are probed — one that mentions a constant or a variable
        // has a free name and is not evaluated here at all — so the
        // declarations can be given dummy assignments purely to make TLC run
        // the module. That widens the sample from constant-free modules to
        // essentially all of them.
        //
        // A constant of non-zero arity is the exception: TLC's configuration
        // language cannot assign an operator, so those modules are skipped.
        if module.constants().iter().any(|c| c.arity > 0) {
            continue;
        }
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

        let mut ok: Vec<(String, String)> = Vec::new();
        for name in names {
            let mut low = nixie_tla::Lowerer::new();
            low.add_spec(&spec);
            let Ok(k) = low.lower_named(module, &name) else {
                continue;
            };
            lowered += 1;
            match nixie_tla::Evaluator::new().eval(&k) {
                Ok(v) => {
                    evaluated += 1;
                    ok.push((name, v.to_string()));
                }
                Err(e) => {
                    let r = match e {
                        nixie_tla::EvalErrorKind::Unsupported(s) => format!("unsupported: {s}"),
                        nixie_tla::EvalErrorKind::FreeName(_) => "free name".to_string(),
                        other => format!("{other}"),
                    };
                    *by_reason.entry(r).or_default() += 1;
                }
            }
        }

        if let Some(dir) = &probe_dir
            && !ok.is_empty()
        {
            // Every declared name in scope has to be assigned, including those
            // inherited through EXTENDS: TLC requires the spec to constrain
            // every variable it can see.
            let mut vars: Vec<String> = Vec::new();
            let mut consts: Vec<String> = Vec::new();
            let mut defined: Vec<String> = Vec::new();
            for (_, m) in &spec.modules {
                vars.extend(m.variables().iter().map(|v| v.name.clone()));
                consts.extend(m.constants().iter().map(|c| c.name.name.clone()));
                for u in &m.units {
                    if let nixie_tla_syntax::UnitKind::OpDef { name, .. } = &u.kind {
                        defined.push(name.name.clone());
                    }
                }
            }
            // A configuration entry *overrides* a definition. The `MC` idiom
            // declares `CONSTANT N` in a base module and defines `N == 3` in
            // the model module; assigning `N = N` there would replace the real
            // value with a model value, and TLC would print `N` where this
            // evaluator prints 3. Only genuinely undefined constants are
            // assigned.
            consts.retain(|c| !defined.contains(c));
            vars.sort();
            vars.dedup();
            consts.sort();
            consts.dedup();
            write_probe(dir, &path, module, &ok, &vars, &consts);
        }
    }

    println!("{lowered} ground-module definitions lowered, {evaluated} evaluated");
    let mut v: Vec<_> = by_reason.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (r, n) in v.iter().take(12) {
        println!("  {n:6}  {r}");
    }
}

/// Write `<Name>Probe.tla` next to a manifest of this evaluator's answers.
///
/// The probe EXTENDS the *original* module, so TLC evaluates the source
/// definition -- not a re-printed kernel term. That distinction is what makes
/// the comparison a test of lowering rather than only of the evaluator.
fn write_probe(
    dir: &str,
    src_path: &str,
    module: &nixie_tla_syntax::ast::Module,
    ok: &[(String, String)],
    vars: &[String],
    consts: &[String],
) {
    let _ = std::fs::create_dir_all(dir);
    let name = &module.name.name;
    // The probe is written to the scratch directory, never beside the source:
    // the corpora are read-only reference checkouts. TLC finds the module it
    // extends through `-DTLA-Library`, which the runner sets to the source
    // directory.
    let Some(src_dir) = std::path::Path::new(src_path).parent() else {
        return;
    };
    let probe = format!("{name}NixieProbe");
    let mut body = format!("---- MODULE {probe} ----\nEXTENDS {name}, TLC\nVARIABLE nixieDummy\n");
    body.push_str("NixieProbeInit ==\n    /\\ nixieDummy = 0\n");
    // Dummy assignments: the probed definitions are ground, so none of them
    // can observe these.
    for v in vars {
        body.push_str(&format!("    /\\ {v} = 0\n"));
    }
    for (n, _) in ok {
        body.push_str(&format!("    /\\ PrintT(<<\"{n}\", {n}>>)\n"));
    }
    let unchanged = if vars.is_empty() {
        "nixieDummy".to_string()
    } else {
        format!("<<nixieDummy, {}>>", vars.join(", "))
    };
    body.push_str(&format!("NixieProbeNext == UNCHANGED {unchanged}\n====\n"));
    let out = std::path::Path::new(dir);
    let _ = std::fs::write(out.join(format!("{probe}.tla")), body);
    // A constant is assigned a model value of the same name: TLC treats it as
    // an uninterpreted element, which is all that is needed to make the module
    // run.
    let mut cfg = String::from("INIT NixieProbeInit\nNEXT NixieProbeNext\n");
    if !consts.is_empty() {
        cfg.push_str("CONSTANTS\n");
        for c in consts {
            cfg.push_str(&format!("    {c} = {c}\n"));
        }
    }
    let _ = std::fs::write(out.join(format!("{probe}.cfg")), cfg);
    // Manifest: what we computed, plus where TLC must look for the module the
    // probe extends.
    let manifest = out.join(format!("{probe}.expected"));
    if let Ok(mut f) = std::fs::File::create(manifest) {
        // Absolute: TLC runs with its working directory at the probe, so a
        // path relative to the corpus listing would not resolve.
        let lib = std::fs::canonicalize(src_dir).unwrap_or_else(|_| src_dir.to_path_buf());
        let _ = writeln!(f, "#lib\t{}", lib.display());
        for (n, v) in ok {
            let _ = writeln!(f, "{n}\t{v}");
        }
    }
}
