//! Why are levels untrusted? Attribute each one to a cause.
//!
//! A diagnostic: the parity suite reports how many definitions were skipped as
//! untrusted, but not *why*. Knowing whether the cause is unresolved `EXTENDS`
//! or the max-rule limitation decides which is worth implementing.
//!
//! With `NIXIE_TLA_RESOLVE=1`, follows `EXTENDS` first, which is the point of
//! the comparison.

use std::collections::BTreeMap;
use std::path::Path;

fn main() {
    let resolve = std::env::var_os("NIXIE_TLA_RESOLVE").is_some();
    let lib = std::env::var("NIXIE_TLA_LIB").ok();
    let mut total = 0usize;
    let mut trusted = 0usize;
    let mut names = BTreeMap::<String, usize>::new();
    let mut files = 0usize;
    let mut missing_modules = BTreeMap::<String, usize>::new();

    for path in std::env::args().skip(1) {
        let p = Path::new(&path);
        let reports = if resolve {
            let mut loader = nixie_tla_syntax::Loader::new();
            if let Some(l) = &lib {
                loader = loader.with_search_path(l);
            }
            let Ok(spec) = loader.load(p) else { continue };
            for m in &spec.missing {
                *missing_modules.entry(m.clone()).or_default() += 1;
            }
            let root = spec.root.clone();
            nixie_tla_syntax::check_spec(&spec)
                .into_iter()
                .filter(|(n, _)| *n == root)
                .collect::<Vec<_>>()
        } else {
            let Ok(src) = std::fs::read_to_string(p) else {
                continue;
            };
            let Ok(parsed) = nixie_tla_syntax::parse_file(&src) else {
                continue;
            };
            vec![(
                String::new(),
                nixie_tla_syntax::check_module(&parsed.module),
            )]
        };
        if reports.is_empty() {
            continue;
        }
        files += 1;
        for (_, r) in reports {
            total += r.definitions.len();
            trusted += r.trusted_count();
            for n in &r.unresolved {
                *names.entry(n.clone()).or_default() += 1;
            }
        }
    }
    println!(
        "resolve={resolve}  {files} files, {total} definitions, {trusted} trusted, {} untrusted ({:.1}% trusted)",
        total - trusted,
        100.0 * trusted as f64 / total.max(1) as f64
    );
    let mut v: Vec<_> = names.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!("distinct unresolved names: {}", v.len());
    for (name, n) in v.iter().take(15) {
        println!("  {n:5}  {name}");
    }
    if !missing_modules.is_empty() {
        let mut m: Vec<_> = missing_modules.into_iter().collect();
        m.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
        println!("missing modules: {}", m.len());
        for (name, n) in m.iter().take(15) {
            println!("  {n:5}  {name}");
        }
    }
}
