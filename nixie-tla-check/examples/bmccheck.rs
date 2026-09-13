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
    let mut with_cfg = 0usize;
    let no_cfg = std::env::var("NIXIE_BMC_NO_CFG").is_ok_and(|v| v == "1");
    // `NIXIE_BMC_LIST=1` prints one `file<TAB>outcome` line per specification
    // instead of the summary, so two runs can be diffed spec by spec. A
    // summary that moves by one is not a finding until you can name the one.
    let list = std::env::var("NIXIE_BMC_LIST").is_ok_and(|v| v == "1");
    // A deterministic per-query budget. Some specifications now reach the
    // solver with hundreds of set and datatype terms and do not finish in any
    // useful time — `Consensus_epr.tla` ran for twenty minutes and counting —
    // and a corpus harness that hangs is not a measurement. Conflicts rather
    // than seconds, so the same input gives the same verdict on any machine;
    // the numbers stopped being reproducible the last time something here
    // depended on the clock.
    let limit: u64 = std::env::var("NIXIE_BMC_CONFLICTS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(20_000);
    let mut prepared = 0usize;
    let mut checked = 0usize;
    let mut no_violation = 0usize;
    let mut violations: Vec<String> = Vec::new();
    let mut unknown = 0usize;
    let mut weakened = 0usize;
    let mut cfg_unaware = 0usize;
    let mut blocked: BTreeMap<String, usize> = BTreeMap::new();
    let mut blocked_eg: BTreeMap<String, String> = BTreeMap::new();

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
        // The `.cfg` is authoritative where it exists: it names the entry
        // points and pins the constants. The naming convention is the
        // *fallback*, used only for what the file does not say.
        let cfg_path = std::path::Path::new(&path).with_extension("cfg");
        // The control. `NIXIE_BMC_NO_CFG=1` runs the *same binary* over the
        // same corpus with the configuration ignored, which is the only
        // honest way to say what reading it bought: comparing against an
        // older build would also be comparing against every other change.
        let cfg = match if no_cfg {
            Err(std::io::Error::other("disabled"))
        } else {
            std::fs::read_to_string(&cfg_path)
        } {
            Ok(text) => match nixie_tla_syntax::parse_config(&text) {
                Ok(c) => {
                    with_cfg += 1;
                    Some(c)
                }
                Err(e) => {
                    let key = "the .cfg does not parse".to_string();
                    *blocked.entry(key.clone()).or_default() += 1;
                    blocked_eg
                        .entry(key)
                        .or_insert(format!("{}: {e}", path.rsplit('/').next().unwrap_or(&path)));
                    continue;
                }
            },
            Err(_) => None,
        };
        let from_cfg = cfg.as_ref().map(|c| &c.behavior);
        let cfg_init_next = match from_cfg {
            Some(nixie_tla_syntax::BehaviorSpec::InitNext { init, next }) => {
                Some((init.clone(), next.clone()))
            }
            _ => None,
        };
        let cfg_inv = cfg.as_ref().and_then(|c| c.invariants.first().cloned());

        let (init, next) = match cfg_init_next {
            Some(p) => p,
            None => match (pick(INITS), pick(NEXTS)) {
                (Some(i), Some(n)) => (i, n),
                _ => continue,
            },
        };
        let Some(inv) = cfg_inv
            .filter(|i| defined.contains(&i.as_str()))
            .or_else(|| pick(INVS))
        else {
            continue;
        };
        with_triple += 1;

        let cinit = pick(CINITS);
        let constraints: Vec<&str> = cinit.iter().map(String::as_str).collect();

        let file = path.rsplit('/').next().unwrap_or(&path).to_string();
        let mut tm = TermManager::new();
        let empty = nixie_tla_syntax::TlcConfig::default();
        let use_cfg = cfg.as_ref().unwrap_or(&empty);
        let roles = nixie_tla_check::bmc::Roles {
            init: &init,
            next: &next,
            inv: &inv,
            constraints: &constraints,
        };
        let mut bmc = match Bmc::prepare_with_config(&spec, module, roles, use_cfg, &mut tm) {
            Ok(mut b) => {
                // Deterministic, so two runs over the corpus agree; see
                // `Bmc::set_conflict_limit`.
                b.set_conflict_limit(limit);
                b
            }
            Err(e) => {
                let key = reason(&e);
                if list {
                    println!("{path}\tblocked\t{key}");
                }
                *blocked.entry(key.clone()).or_default() += 1;
                blocked_eg.entry(key).or_insert(format!("{file}: {e}"));
                continue;
            }
        };
        prepared += 1;
        match bmc.check(depth, &mut tm) {
            Ok(Outcome::NoViolationWithin(_)) => {
                if list {
                    println!("{path}\tno-violation");
                }
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
                // The `.cfg` is read now, so the flag is no longer "a file
                // exists that we ignored" but the sharper "the file said
                // something we did not act on".
                let unapplied = bmc.unapplied_config().to_vec();
                if !unapplied.is_empty() || (no_cfg && cfg_path.exists()) {
                    cfg_unaware += 1;
                }
                let mut notes = Vec::new();
                if d > 0 {
                    notes.push(format!("{d} assumption(s) dropped"));
                }
                if no_cfg && cfg_path.exists() {
                    notes.push("a .cfg exists and was not read".to_string());
                } else if !unapplied.is_empty() {
                    notes.push(format!(
                        "the .cfg's {} was not applied",
                        unapplied.join(", ")
                    ));
                }
                if list {
                    println!("{path}\tviolation\t{step}");
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
                if list {
                    println!("{path}\tundecided");
                }
                checked += 1;
                unknown += 1;
            }
            // A specification that prepared and then failed to *encode* is
            // as blocked as one that never prepared, and must appear in the
            // per-spec list too — it went missing there at first, which is
            // exactly the silent gap a spec-by-spec diff exists to catch.
            Err(e) => {
                let key = reason(&e);
                if list {
                    println!("{path}\tblocked\t{key}");
                }
                *blocked.entry(key.clone()).or_default() += 1;
                blocked_eg.entry(key).or_insert(format!("{file}: {e}"));
            }
        }
    }

    if list {
        return;
    }
    println!("{modules} modules loaded");
    println!("  with a .cfg that parsed      : {with_cfg}");
    println!("  with an Init/Next/Inv triple : {with_triple}");
    println!("  prepared (typed and sorted)  : {prepared}");
    println!("  actually checked at depth {depth}  : {checked}");
    println!("    no violation within the bound : {no_violation}");
    println!("    violations found              : {}", violations.len());
    println!("      of which under dropped ASSUMEs : {weakened}");
    println!("      of which with unapplied .cfg   : {cfg_unaware}");
    println!("    solver undecided              : {unknown}");
    for v in violations.iter().take(64) {
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
        SetupError::Replacement { why, .. } => {
            format!("the .cfg's `<-` could not be applied: {why}")
        }
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
