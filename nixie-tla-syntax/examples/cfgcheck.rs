//! Parse every `.cfg` beside the corpus specifications and report what failed.
//!
//! The same shape as the parser parity run: a percentage says nothing, a
//! breakdown of *why* a file was rejected sizes the remaining work.

use std::collections::BTreeMap;

fn main() {
    let mut paths: Vec<String> = std::env::args().skip(1).collect();
    paths.sort();
    let mut ok = 0usize;
    let mut failed: Vec<String> = Vec::new();
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    let mut behavior: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut assignments = 0usize;
    let mut replacements = 0usize;
    let mut module_qualified = 0usize;
    let mut module_qualified_assign = 0usize;
    let mut model_values = 0usize;
    let mut with_invariant = 0usize;
    let mut unused: BTreeMap<&'static str, usize> = BTreeMap::new();

    for path in &paths {
        let Ok(src) = std::fs::read_to_string(path) else {
            continue;
        };
        match nixie_tla_syntax::parse_config(&src) {
            Ok(cfg) => {
                ok += 1;
                *behavior
                    .entry(match cfg.behavior {
                        nixie_tla_syntax::BehaviorSpec::InitNext { .. } => "INIT/NEXT",
                        nixie_tla_syntax::BehaviorSpec::Temporal(_) => "SPECIFICATION",
                        nixie_tla_syntax::BehaviorSpec::Unspecified => "none",
                    })
                    .or_default() += 1;
                assignments += cfg.assignments.len();
                replacements += cfg.replacements.len();
                module_qualified += cfg.module_qualified_replacements().len();
                module_qualified_assign += cfg.module_qualified_assignments().len();
                model_values += cfg
                    .assignments
                    .values()
                    .filter(|v| has_model_value(v))
                    .count();
                if !cfg.invariants.is_empty() {
                    with_invariant += 1;
                }
                for u in cfg.unused_options() {
                    *unused.entry(u).or_default() += 1;
                }
            }
            Err(e) => {
                let file = path.rsplit('/').next().unwrap_or(path);
                failed.push(format!("{file}: {e}"));
                *kinds.entry(kind_of(&e)).or_default() += 1;
            }
        }
    }

    println!("{} config files", paths.len());
    println!("  parsed  : {ok}");
    println!("  rejected: {}", failed.len());
    for f in failed.iter().take(20) {
        println!("    {f}");
    }
    if !kinds.is_empty() {
        println!("  by kind:");
        let mut v: Vec<_> = kinds.into_iter().collect();
        v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
        for (k, n) in v {
            println!("    {n:5}  {k}");
        }
    }
    println!("  behaviour specification:");
    for (k, n) in &behavior {
        println!("    {n:5}  {k}");
    }
    println!("  CONSTANT assignments        : {assignments}");
    println!("    of which model-valued     : {model_values}");
    println!("  CONSTANT replacements (`<-`): {replacements}");
    println!("    of which module-qualified : {module_qualified}");
    println!("  module-qualified assignments: {module_qualified_assign}");
    println!("  files naming an INVARIANT   : {with_invariant}");
    if !unused.is_empty() {
        println!("  parsed but not acted on:");
        for (k, n) in &unused {
            println!("    {n:5}  {k}");
        }
    }
}

fn has_model_value(v: &nixie_tla_syntax::ConfigValue) -> bool {
    use nixie_tla_syntax::ConfigValue as V;
    match v {
        V::ModelValue(_) => true,
        V::Set(xs) => xs.iter().any(has_model_value),
        V::Int(_) | V::Str(_) | V::Bool(_) | V::ModuleQualified { .. } => false,
    }
}

fn kind_of(e: &nixie_tla_syntax::ConfigError) -> String {
    use nixie_tla_syntax::ConfigErrorKind as K;
    match &e.kind {
        K::UnexpectedChar(c) => format!("unexpected character {c:?}"),
        K::UnterminatedString => "unterminated string".into(),
        K::UnterminatedComment => "unterminated block comment".into(),
        K::NotAnOperator(o) => format!("`{o}` is not a TLA+ operator"),
        K::Unexpected { expected, .. } => format!("expected {expected}"),
        K::TwoBehaviourSpecs { .. } => "two behaviour specifications".into(),
        K::ConflictingCheckDeadlock => "conflicting CHECK_DEADLOCK".into(),
    }
}
