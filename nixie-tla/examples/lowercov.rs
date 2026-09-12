//! Lowering coverage: try to lower every top-level definition in each module.
//!
//! The same measure-then-build loop the parser and level checker were grown
//! with. Prints the failure modes by frequency so the next gap to close is the
//! one the corpus actually hits.

use std::collections::BTreeMap;

fn main() {
    let mut ok = 0usize;
    let mut fail = 0usize;
    let mut files = 0usize;
    let mut nodes = 0usize;
    let mut by_reason: BTreeMap<String, usize> = BTreeMap::new();
    let mut sample: BTreeMap<String, String> = BTreeMap::new();

    let lib = std::env::var("NIXIE_TLA_LIB").ok();
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
        files += 1;
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
            match low.lower_named(module, &name) {
                Ok(k) => {
                    ok += 1;
                    nodes += k.size();
                }
                Err(e) => {
                    fail += 1;
                    let reason = match &e.kind {
                        nixie_tla::LowerErrorKind::Unsupported { construct, .. } => {
                            construct.clone()
                        }
                        other => format!("{other}"),
                    };
                    sample.entry(reason.clone()).or_insert_with(|| {
                        format!("{}:{}", path.rsplit('/').next().unwrap_or(&path), e.span)
                    });
                    *by_reason.entry(reason).or_default() += 1;
                }
            }
        }
    }
    // A definition like `Spec == Init /\ [][Next]_vars` is not an expression
    // at all -- it is spec structure, and rejecting it is correct. Counting
    // those as coverage failures understates how much of the expression
    // language is actually lowered.
    const STRUCTURE: &[&str] = &[
        "a subscripted action (`[A]_v` / `<<A>>_v`)",
        "a fairness condition (`WF_` / `SF_`)",
        "the temporal operator `[]`",
        "the temporal operator `<>`",
        "the operator `~>`",
        "the operator `-+->`",
        "`ENABLED`",
        "an unbounded quantifier",
        "a temporal quantifier (`\\AA` / `\\EE`)",
    ];
    let structural: usize = by_reason
        .iter()
        .filter(|(r, _)| STRUCTURE.contains(&r.as_str()))
        .map(|(_, n)| *n)
        .sum();
    let total = ok + fail;
    let expr_total = total - structural;
    println!(
        "{files} files, {total} definitions: {ok} lowered, {fail} rejected; {nodes} kernel nodes"
    );
    println!("  {structural} are spec structure (temporal / action / ENABLED), correctly rejected");
    println!(
        "  expression coverage: {ok}/{expr_total} = {:.1}%",
        100.0 * ok as f64 / expr_total.max(1) as f64
    );
    let mut v: Vec<_> = by_reason.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (reason, n) in v.iter().take(25) {
        let s = sample.get(reason).map(String::as_str).unwrap_or("");
        println!("  {n:6}  {reason}   [{s}]");
    }
}
