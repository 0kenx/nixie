//! Family registry: parameter sets per size, deterministic corpus assembly.

use crate::stress::{self, StressCfg};
use crate::{Instance, Rng, boundary, capacity, gap, memory, parity, reconverge};

pub const FAMILIES: &[&str] = &[
    "parity",
    "capacity",
    "gap",
    "reconverge",
    "memory",
    "boundary",
];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Size {
    Small,
    Medium,
    Large,
}

impl Size {
    pub fn name(self) -> &'static str {
        match self {
            Size::Small => "small",
            Size::Medium => "medium",
            Size::Large => "large",
        }
    }

    pub fn parse(s: &str) -> Option<Size> {
        match s {
            "small" => Some(Size::Small),
            "medium" => Some(Size::Medium),
            "large" => Some(Size::Large),
            _ => None,
        }
    }
}

pub fn generate_family(
    family: &str,
    seed: u64,
    size: Size,
    stress_cfg: Option<&StressCfg>,
) -> Result<Vec<Instance>, String> {
    if !FAMILIES.contains(&family) {
        return Err(format!(
            "unknown family {family:?}; known: {}",
            FAMILIES.join(", ")
        ));
    }
    let suffix = size.name().to_string();
    let mut insts = match family {
        "parity" => {
            let (v, e) = match size {
                Size::Small => (10, 8),
                Size::Medium => (26, 20),
                Size::Large => (60, 45),
            };
            parity::generate(
                seed,
                &parity::Params {
                    vertices: v,
                    extra_edges: e,
                },
                &suffix,
            )?
        }
        "capacity" => {
            let (o, x, dmin, dmax) = match size {
                Size::Small => (5, 2, 2, 3),
                Size::Medium => (9, 3, 2, 4),
                Size::Large => (14, 4, 3, 4),
            };
            capacity::generate(
                seed,
                &capacity::Params {
                    objects: o,
                    extra_resources: x,
                    allowed_min: dmin,
                    allowed_max: dmax,
                    deficit: 1,
                },
                &suffix,
            )?
        }
        "gap" => {
            let (v, k) = match size {
                Size::Small => (4, 0),
                Size::Medium => (7, 3),
                Size::Large => (11, 9),
            };
            gap::generate(
                seed,
                &gap::Params {
                    vars: v,
                    scale_log10: k,
                },
                &suffix,
            )?
        }
        "reconverge" => {
            let (k, w) = match size {
                Size::Small => (3, 16),
                Size::Medium => (4, 32),
                Size::Large => (5, 64),
            };
            reconverge::generate(
                seed,
                &reconverge::Params {
                    inputs: k,
                    width: w,
                },
                &suffix,
            )?
        }
        "memory" => {
            let n = match size {
                Size::Small => 10,
                Size::Medium => 26,
                Size::Large => 50,
            };
            memory::generate(seed, &memory::Params { writes: n }, &suffix)?
        }
        "boundary" => {
            let f = match size {
                Size::Small => 5,
                Size::Medium => 10,
                Size::Large => 20,
            };
            boundary::generate(seed, &boundary::Params { facts: f }, &suffix)?
        }
        _ => unreachable!("checked above"),
    };
    if let Some(cfg) = stress_cfg {
        for inst in &mut insts {
            match inst.kind {
                crate::InstanceKind::Smt2 => {
                    let mut rng = Rng::new(seed ^ 0x57_5E_55);
                    inst.script = stress::apply_smt2(&inst.script, cfg, &mut rng, &inst.logic);
                    inst.tags.push("rep-stress");
                }
                crate::InstanceKind::Cnf => {
                    inst.script = stress::apply_cnf(&inst.script, cfg.cnf_dup);
                    inst.tags.push("clause-dup");
                }
            }
        }
    }
    Ok(insts)
}

/// Full corpus: every family x seed.
pub fn generate_all(
    seeds: u64,
    size: Size,
    stress_cfg: Option<&StressCfg>,
) -> Result<Vec<Instance>, String> {
    let mut out = Vec::new();
    for &family in FAMILIES {
        for seed in 0..seeds {
            out.extend(generate_family(family, seed, size, stress_cfg)?);
        }
    }
    Ok(out)
}

/// Manifest listing file names plus per-instance metadata.
pub fn manifest_json(instances: &[Instance]) -> String {
    let mut s = String::from("{\n  \"instances\": [\n");
    for (i, inst) in instances.iter().enumerate() {
        s.push_str("    {\n");
        s.push_str(&format!(
            "      \"file\": \"{}.{}\",\n",
            inst.name,
            inst.extension()
        ));
        s.push_str(&format!("  \"family\": \"{}\",\n", inst.family));
        s.push_str(&format!(
            "  \"expected\": [{}],\n",
            inst.expected
                .iter()
                .map(|a| format!("\"{}\"", a.name()))
                .collect::<Vec<_>>()
                .join(", ")
        ));
        s.push_str("      \"kind\": ");
        s.push_str(match inst.kind {
            crate::InstanceKind::Smt2 => "\"smt2\"\n",
            crate::InstanceKind::Cnf => "\"cnf\"\n",
        });
        s.push_str("    }");
        if i + 1 < instances.len() {
            s.push(',');
        }
        s.push('\n');
    }
    s.push_str("  ]\n}\n");
    s
}
