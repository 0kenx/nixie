//! `obligation-gen` — emit a deterministic corpus of certificate-carrying
//! instances plus per-instance metadata and a manifest.
//!
//! Usage:
//!   obligation-gen [--seeds N] [--size small|medium|large] \
//!                 [--family NAME|all] [--stress mild|heavy] \
//!                 [--out DIR] [--list]

use nixie_obligation::registry::{self, Size};
use nixie_obligation::stress::StressCfg;
use std::path::PathBuf;
use std::process::ExitCode;

struct Opts {
    seeds: u64,
    size: Size,
    family: String,
    stress: Option<StressCfg>,
    out: PathBuf,
    list: bool,
}

fn parse_args() -> Result<Opts, String> {
    let mut o = Opts {
        seeds: 3,
        size: Size::Medium,
        family: "all".into(),
        stress: None,
        out: PathBuf::from("obligation-corpus"),
        list: false,
    };
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--seeds" => {
                i += 1;
                o.seeds = args
                    .get(i)
                    .and_then(|v| v.parse::<u64>().ok())
                    .ok_or("--seeds needs an integer")?;
            }
            "--size" => {
                i += 1;
                o.size = Size::parse(args.get(i).ok_or("--size needs small|medium|large")?)
                    .ok_or("--size needs small|medium|large")?;
            }
            "--family" => {
                i += 1;
                o.family = args
                    .get(i)
                    .ok_or("--family needs a family name or 'all'")?
                    .clone();
            }
            "--stress" => {
                i += 1;
                o.stress = Some(match args.get(i).map(|s| s.as_str()) {
                    Some("mild") => StressCfg::mild(),
                    Some("heavy") => StressCfg::heavy(),
                    _ => return Err("--stress needs mild|heavy".into()),
                });
            }
            "--out" => {
                i += 1;
                o.out = PathBuf::from(args.get(i).ok_or("--out needs a path")?);
            }
            "--list" => o.list = true,
            other => return Err(format!("unknown argument {other:?}")),
        }
        i += 1;
    }
    Ok(o)
}

fn main() -> ExitCode {
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("obligation-gen: {e}");
            return ExitCode::FAILURE;
        }
    };
    let families: Vec<&str> = if opts.family == "all" {
        registry::FAMILIES.to_vec()
    } else {
        vec![opts.family.as_str()]
    };
    let mut instances = Vec::new();
    for &f in &families {
        for seed in 0..opts.seeds {
            match registry::generate_family(f, seed, opts.size, opts.stress.as_ref()) {
                Ok(v) => instances.extend(v),
                Err(e) => {
                    eprintln!("obligation-gen: {f} seed {seed}: {e}");
                    return ExitCode::FAILURE;
                }
            }
        }
    }
    if opts.list {
        for inst in &instances {
            println!(
                "{:<55} {:>12} expected={:?}",
                inst.name,
                match inst.kind {
                    nixie_obligation::InstanceKind::Smt2 => "smt2",
                    nixie_obligation::InstanceKind::Cnf => "cnf",
                },
                inst.expected.iter().map(|a| a.name()).collect::<Vec<_>>()
            );
        }
        return ExitCode::SUCCESS;
    }
    if let Err(e) = std::fs::create_dir_all(&opts.out) {
        eprintln!("obligation-gen: cannot create {}: {e}", opts.out.display());
        return ExitCode::FAILURE;
    }
    for inst in &instances {
        let path = opts.out.join(format!("{}.{}", inst.name, inst.extension()));
        if let Err(e) = std::fs::write(&path, &inst.script) {
            eprintln!("obligation-gen: cannot write {}: {e}", path.display());
            return ExitCode::FAILURE;
        }
        let meta = opts.out.join(format!("{}.meta.json", inst.name));
        if let Err(e) = std::fs::write(&meta, inst.meta_json()) {
            eprintln!("obligation-gen: cannot write {}: {e}", meta.display());
            return ExitCode::FAILURE;
        }
    }
    let manifest = opts.out.join("manifest.json");
    if let Err(e) = std::fs::write(&manifest, registry::manifest_json(&instances)) {
        eprintln!("obligation-gen: cannot write {}: {e}", manifest.display());
        return ExitCode::FAILURE;
    }
    let mut per_family: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for inst in &instances {
        *per_family.entry(inst.family).or_insert(0) += 1;
    }
    println!(
        "wrote {} instances to {}",
        instances.len(),
        opts.out.display()
    );
    for (f, n) in per_family {
        println!("  {f:<12} {n}");
    }
    ExitCode::SUCCESS
}
