//! Try to bounded-model-check every module in the corpus, and tally why not.
//!
//! The point is the *breakdown*: it sizes the remaining work by naming which
//! construct blocks each specification, rather than reporting a single
//! coverage number that says nothing about what to build next.
//!
//! Usage: `cargo run -p nixie-tla-check --example bmccheck -- FILE...`

use std::collections::BTreeMap;

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, SetupError};

/// Names specifications conventionally use, most specific first.
const INITS: &[&str] = &["Init", "Initial", "InitialState"];
const NEXTS: &[&str] = &["Next", "Step", "Trans"];
const INVS: &[&str] = &["Inv", "Invariant", "TypeOK", "TypeInvariant", "Safety"];
/// Apalache's constant-initializer convention (`--cinit=ConstInit`). A
/// specification that pins its constants here carries no `ASSUME`, so ignoring
/// it makes every constant arbitrary and manufactures counterexamples.
const CINITS: &[&str] = &["ConstInit", "CInit", "ConstantInit"];

fn main() {
    let lib = std::env::var("NIXIE_TLA_LIB").ok();
    let depth: u32 = std::env::var("NIXIE_BMC_DEPTH")
        .ok()
        .and_then(|d| d.parse().ok())
        .unwrap_or(4);

    let mut modules = 0usize;
    let mut with_triple = 0usize;
    let mut prepared = 0usize;
    let mut checked = 0usize;
    let mut no_violation = 0usize;
    let mut violations: Vec<String> = Vec::new();
    let mut unknown = 0usize;
    let mut weakened = 0usize;
    let mut cfg_unaware = 0usize;
    let mut blocked: BTreeMap<String, usize> = BTreeMap::new();
    let mut blocked_eg: BTreeMap<String, String> = BTreeMap::new();

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
        modules += 1;

        let defined: Vec<&str> = module
            .units
            .iter()
            .filter_map(|u| match &u.kind {
                nixie_tla_syntax::UnitKind::OpDef { name, params, .. } if params.is_empty() => {
                    Some(name.name.as_str())
                }
                _ => None,
            })
            .collect();
        let pick = |cands: &[&str]| -> Option<String> {
            cands
                .iter()
                .find(|c| defined.contains(c))
                .map(|c| (*c).to_string())
        };
        let (Some(init), Some(next), Some(inv)) = (pick(INITS), pick(NEXTS), pick(INVS)) else {
            continue;
        };
        with_triple += 1;

        let cinit = pick(CINITS);
        let constraints: Vec<&str> = cinit.iter().map(String::as_str).collect();

        let file = path.rsplit('/').next().unwrap_or(&path).to_string();
        let mut tm = TermManager::new();
        let mut bmc = match Bmc::prepare(&spec, module, &init, &next, &inv, &constraints, &mut tm) {
            Ok(b) => b,
            Err(e) => {
                let key = reason(&e);
                *blocked.entry(key.clone()).or_default() += 1;
                blocked_eg.entry(key).or_insert(format!("{file}: {e}"));
                continue;
            }
        };
        prepared += 1;
        match bmc.check(depth, &mut tm) {
            Ok(Outcome::NoViolationWithin(_)) => {
                checked += 1;
                no_violation += 1;
            }
            Ok(Outcome::Violation { step }) => {
                checked += 1;
                // A dropped assumption weakens the search, so a counterexample
                // found under one may be an artefact rather than a real trace.
                // Reported separately: conflating the two would overstate the
                // result exactly where it is least justified.
                let d = bmc.dropped_assumptions();
                if d > 0 {
                    weakened += 1;
                }
                // A `.cfg` can replace a CONSTANT or even a definition
                // (`ConfigReplacements.tla` replaces `Value`), so a verdict
                // reached without reading it may be about a different
                // specification. Flagged rather than silently reported.
                let has_cfg = std::path::Path::new(&path).with_extension("cfg").exists();
                if has_cfg {
                    cfg_unaware += 1;
                }
                let mut notes = Vec::new();
                if d > 0 {
                    notes.push(format!("{d} assumption(s) dropped"));
                }
                if has_cfg {
                    notes.push("a .cfg exists and was not read".to_string());
                }
                violations.push(format!(
                    "{file}!{inv} violated after {step} step(s){}",
                    if notes.is_empty() {
                        String::new()
                    } else {
                        format!(" [{} - may be spurious]", notes.join("; "))
                    }
                ));
            }
            Ok(Outcome::Unknown(_)) => {
                checked += 1;
                unknown += 1;
            }
            Err(e) => {
                let key = reason(&e);
                *blocked.entry(key.clone()).or_default() += 1;
                blocked_eg.entry(key).or_insert(format!("{file}: {e}"));
            }
        }
    }

    println!("{modules} modules loaded");
    println!("  with an Init/Next/Inv triple : {with_triple}");
    println!("  prepared (typed and sorted)  : {prepared}");
    println!("  actually checked at depth {depth}  : {checked}");
    println!("    no violation within the bound : {no_violation}");
    println!("    violations found              : {}", violations.len());
    println!("      of which under dropped ASSUMEs : {weakened}");
    println!("      of which with an unread .cfg   : {cfg_unaware}");
    println!("    solver undecided              : {unknown}");
    for v in violations.iter().take(15) {
        println!("      {v}");
    }
    println!("  blocked, by cause:");
    let mut b: Vec<_> = blocked.into_iter().collect();
    b.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (k, n) in b.iter().take(12) {
        println!("    {n:5}  {k}");
        if let Some(e) = blocked_eg.get(k) {
            println!("           e.g. {e}");
        }
    }
}

/// Group by cause, not by the names each instance mentions.
fn reason(e: &SetupError) -> String {
    match e {
        SetupError::NoSuchDefinition(_) => "no such definition".into(),
        SetupError::Lower { .. } => "does not lower to the kernel".into(),
        SetupError::Types(_) => "does not type check".into(),
        SetupError::Level { role, .. } => format!("wrong TLA+ level for {role}"),
        SetupError::NoSort { ty, .. } => format!("state type has no sort yet: {}", head(ty)),
        SetupError::Encode { why, .. } => format!("no encoding yet: {}", head(why)),
    }
}

/// The leading shape of a rendered type or message.
fn head(s: &str) -> String {
    let s = s.trim();
    for (p, n) in [
        ("Set(", "Set"),
        ("Seq(", "Seq"),
        ("<<", "tuple"),
        ("[", "record"),
        ("(", "function"),
        ("'", "unconstrained"),
    ] {
        if s.starts_with(p) {
            return n.to_string();
        }
    }
    s.chars().take(60).collect()
}
