//! Capacity / Hall-deficit obstruction (production `Capacity`).
//!
//! Each object must occupy exactly one resource (capacity 1); every object
//! has a set of allowed resources. SAT instances ship a planted injection;
//! UNSAT instances contain a subset S of objects whose combined allowed
//! resources are fewer than |S| — a Hall violation, certified explicitly.
//! Controls: choice-set overlap (a "hot pool" of resources), deficit size,
//! symmetry, distance from feasibility.
//!
//! Realizations: Bool (exactly-one + pairwise AMO), LIA (0/1 sums), UF
//! (uninterpreted `use` with bounds + pairwise distinct applications —
//! congruence meets arithmetic), CNF, and an incremental push/pop history.

use crate::{Answer, Instance, InstanceKind, Rng};
use std::collections::BTreeSet;
use std::fmt::Write as _;

pub struct Params {
    pub objects: usize,
    pub extra_resources: usize,
    pub allowed_min: usize,
    pub allowed_max: usize,
    pub deficit: usize,
}

pub struct Data {
    pub objects: usize,
    pub resources: usize,
    /// allowed[i] = resources object i may occupy (non-empty, sorted).
    pub allowed: Vec<Vec<usize>>,
    /// SAT certificate: injection object -> resource.
    pub plant: Option<Vec<usize>>,
    /// UNSAT certificate: (S, R') with union(allowed[S]) ⊆ R' and |R'| < |S|.
    pub hall: Option<(Vec<usize>, Vec<usize>)>,
}

impl Data {
    pub fn answer(&self) -> Answer {
        if self.hall.is_some() {
            Answer::Unsat
        } else {
            Answer::Sat
        }
    }

    pub fn verify(&self) -> Result<(), String> {
        if self.allowed.len() != self.objects {
            return Err("capacity: allowed size mismatch".into());
        }
        for (i, a) in self.allowed.iter().enumerate() {
            if a.is_empty() {
                return Err(format!("capacity: object {i} has empty allowed set"));
            }
            if a.windows(2).any(|w| w[0] >= w[1]) {
                return Err(format!("capacity: allowed[{i}] not sorted/distinct"));
            }
            if a.iter().any(|&r| r >= self.resources) {
                return Err(format!("capacity: allowed[{i}] out of range"));
            }
        }
        match (&self.plant, &self.hall) {
            (Some(phi), None) => {
                let mut seen = BTreeSet::new();
                for (i, &r) in phi.iter().enumerate() {
                    if r >= self.resources || !self.allowed[i].contains(&r) {
                        return Err(format!("capacity: plant({i}) = {r} not in allowed"));
                    }
                    if !seen.insert(r) {
                        return Err("capacity: plant not injective".into());
                    }
                }
                Ok(())
            }
            (None, Some((s, rp))) => {
                if rp.len() >= s.len() {
                    return Err("capacity: Hall set not deficient".into());
                }
                let rps = rp.iter().collect::<BTreeSet<_>>();
                for &i in s {
                    for &r in &self.allowed[i] {
                        if !rps.contains(&r) {
                            return Err(format!(
                                "capacity: allowed[{i}] leaks outside R' (resource {r})"
                            ));
                        }
                    }
                }
                Ok(())
            }
            _ => Err("capacity: exactly one of plant/hall must be set".into()),
        }
    }
}

/// Variant-specific tweaks for the incremental history.
pub enum Variant {
    Main,
    Incremental,
}

pub fn build(seed: u64, p: &Params, sat: bool, variant: Variant) -> Result<Data, String> {
    if p.objects < 2 {
        return Err("capacity: need >= 2 objects".into());
    }
    if p.extra_resources < 2 {
        return Err("capacity: need >= 2 extra resources".into());
    }
    if p.allowed_min == 0 || p.allowed_max < p.allowed_min {
        return Err("capacity: bad allowed range".into());
    }
    let mut rng = Rng::new(seed ^ 0xCA0A_C17A ^ ((sat as u64) * 7919));
    let m = p.objects + p.extra_resources;
    let reserve_top = matches!(variant, Variant::Incremental);
    let usable = if reserve_top { m - 1 } else { m };
    let hot = (usable / 2).max(1);

    let mut allowed: Vec<Vec<usize>> = Vec::with_capacity(p.objects);

    if sat {
        let mut perm: Vec<usize> = (0..usable).collect();
        rng.shuffle(&mut perm);
        let phi: Vec<usize> = perm[..p.objects].to_vec();
        for i in 0..p.objects {
            let singleton_first = matches!(variant, Variant::Incremental) && i == 0;
            let mut set = BTreeSet::new();
            set.insert(phi[i]);
            if !singleton_first {
                let target = rng.range_usize(p.allowed_min, p.allowed_max);
                let mut guard = 0;
                while set.len() < target && guard < 100 {
                    guard += 1;
                    let r = if rng.chance(2, 3) {
                        rng.index(hot)
                    } else {
                        rng.index(usable)
                    };
                    if r != phi[i] {
                        set.insert(r);
                    }
                }
            }
            allowed.push(set.into_iter().collect());
        }
        let d = Data {
            objects: p.objects,
            resources: m,
            allowed,
            plant: Some(phi),
            hall: None,
        };
        d.verify()?;
        Ok(d)
    } else {
        let s_size = p.objects / 2 + 1;
        if p.deficit == 0 || p.deficit >= s_size {
            return Err("capacity: deficit must be in 1..s".into());
        }
        let r_size = s_size - p.deficit;
        let mut all: Vec<usize> = (0..p.objects).collect();
        rng.shuffle(&mut all);
        let s_set: BTreeSet<usize> = all[..s_size].iter().copied().collect();
        for i in 0..p.objects {
            if s_set.contains(&i) {
                let k = rng.range_usize(1, r_size.min(p.allowed_max));
                let mut pool: Vec<usize> = (0..r_size).collect();
                rng.shuffle(&mut pool);
                pool.truncate(k);
                pool.sort_unstable();
                allowed.push(pool);
            } else {
                let k = rng.range_usize(p.allowed_min, p.allowed_max);
                let mut pool: Vec<usize> = (0..usable).collect();
                rng.shuffle(&mut pool);
                pool.truncate(k);
                pool.sort_unstable();
                allowed.push(pool);
            }
        }
        let d = Data {
            objects: p.objects,
            resources: m,
            allowed,
            plant: None,
            hall: Some((s_set.into_iter().collect(), (0..r_size).collect())),
        };
        d.verify()?;
        Ok(d)
    }
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

fn bool_name(i: usize, j: usize) -> String {
    format!("r_{i}_{j}")
}

fn bool_asserts(d: &Data) -> Vec<String> {
    let mut a = Vec::new();
    for i in 0..d.objects {
        let lits: Vec<String> = d.allowed[i].iter().map(|&j| bool_name(i, j)).collect();
        a.push(format!("(assert (or {}))", lits.join(" ")));
        for x in 0..d.allowed[i].len() {
            for y in (x + 1)..d.allowed[i].len() {
                a.push(format!(
                    "(assert (or (not {}) (not {})))",
                    bool_name(i, d.allowed[i][x]),
                    bool_name(i, d.allowed[i][y])
                ));
            }
        }
    }
    for j in 0..d.resources {
        let users: Vec<usize> = (0..d.objects)
            .filter(|i| d.allowed[*i].contains(&j))
            .collect();
        for x in 0..users.len() {
            for y in (x + 1)..users.len() {
                a.push(format!(
                    "(assert (or (not {}) (not {})))",
                    bool_name(users[x], j),
                    bool_name(users[y], j)
                ));
            }
        }
    }
    a
}

fn bool_decls(d: &Data) -> Vec<String> {
    let mut v = Vec::new();
    for i in 0..d.objects {
        for &j in &d.allowed[i] {
            v.push(format!("(declare-const {} Bool)", bool_name(i, j)));
        }
    }
    v
}

fn witness_text(d: &Data) -> Option<String> {
    d.plant.as_ref().map(|phi| {
        let parts: Vec<String> = phi
            .iter()
            .enumerate()
            .map(|(i, &r)| format!("use({i})={r}"))
            .collect();
        format!("planted injection: {}", parts.join(", "))
    })
}

fn certificate(d: &Data) -> String {
    match (&d.plant, &d.hall) {
        (Some(phi), _) => {
            let parts: Vec<String> = phi
                .iter()
                .enumerate()
                .map(|(i, &r)| format!("{i}->{r}"))
                .collect();
            format!(
                "Planted injection (verified injective, within allowed sets): {}",
                parts.join(", ")
            )
        }
        (_, Some((s, rp))) => format!(
            "Hall violation: subset S = {:?} of objects has union(allowed) ⊆ R' = {:?} with |R'| = {} < |S| = {}; with capacity 1 per resource no assignment exists.",
            s,
            rp,
            rp.len(),
            s.len()
        ),
        _ => "no certificate".to_string(),
    }
}

pub fn generate(seed: u64, p: &Params, suffix: &str) -> Result<Vec<Instance>, String> {
    let mut out = Vec::new();
    for &sat in &[true, false] {
        let d = build(seed, p, sat, Variant::Main)?;
        let tag = if sat { "sat" } else { "unsat" };
        let answer = d.answer();

        // Bool realization
        let mut script = format!(";; capacity bool {tag}\n(set-logic QF_UF)\n");
        for l in bool_decls(&d).into_iter().chain(bool_asserts(&d)) {
            script.push_str(&l);
            script.push('\n');
        }
        script.push_str("(check-sat)\n");
        out.push(Instance {
            family: "capacity",
            name: format!("capacity-bool-{tag}-s{seed}-{suffix}"),
            logic: "QF_UF".into(),
            script,
            kind: InstanceKind::Smt2,
            expected: vec![answer],
            witness: witness_text(&d),
            certificate: certificate(&d),
            tags: vec!["capacity", "bool"],
        });

        // LIA realization
        let mut script = format!(";; capacity lia {tag}\n(set-logic QF_LIA)\n");
        for i in 0..d.objects {
            for &j in &d.allowed[i] {
                let _ = writeln!(script, "(declare-const x_{i}_{j} Int)");
                let _ = writeln!(script, "(assert (>= x_{i}_{j} 0))");
                let _ = writeln!(script, "(assert (<= x_{i}_{j} 1))");
            }
            let terms: Vec<String> = d.allowed[i].iter().map(|&j| format!("x_{i}_{j}")).collect();
            let _ = writeln!(script, "(assert (= (+ {}) 1))", terms.join(" "));
        }
        for j in 0..d.resources {
            let users: Vec<String> = (0..d.objects)
                .filter(|i| d.allowed[*i].contains(&j))
                .map(|i| format!("x_{i}_{j}"))
                .collect();
            if users.len() > 1 {
                let _ = writeln!(script, "(assert (<= (+ {}) 1))", users.join(" "));
            }
        }
        script.push_str("(check-sat)\n");
        out.push(Instance {
            family: "capacity",
            name: format!("capacity-lia-{tag}-s{seed}-{suffix}"),
            logic: "QF_LIA".into(),
            script,
            kind: InstanceKind::Smt2,
            expected: vec![answer],
            witness: witness_text(&d),
            certificate: certificate(&d),
            tags: vec!["capacity", "lia"],
        });

        // UF realization: uninterpreted `use` with bounded range.
        let mut script = format!(";; capacity uf {tag}\n(set-logic QF_UFLIA)\n");
        let _ = writeln!(script, "(declare-fun use (Int) Int)");
        for i in 0..d.objects {
            let _ = writeln!(
                script,
                "(assert (and (>= (use {i}) 0) (<= (use {i}) {})))",
                d.resources - 1
            );
            let opts: Vec<String> = d.allowed[i]
                .iter()
                .map(|&j| format!("(= (use {i}) {j})"))
                .collect();
            let _ = writeln!(script, "(assert (or {}))", opts.join(" "));
        }
        let apps: Vec<String> = (0..d.objects).map(|i| format!("(use {i})")).collect();
        let _ = writeln!(script, "(assert (distinct {}))", apps.join(" "));
        script.push_str("(check-sat)\n");
        out.push(Instance {
            family: "capacity",
            name: format!("capacity-uf-{tag}-s{seed}-{suffix}"),
            logic: "QF_UFLIA".into(),
            script,
            kind: InstanceKind::Smt2,
            expected: vec![answer],
            witness: witness_text(&d),
            certificate: certificate(&d),
            tags: vec!["capacity", "uf", "congruence"],
        });

        // CNF realization
        let (script, w) = cnf_script(&d, &format!("capacity-cnf-{tag}-s{seed}-{suffix}"));
        out.push(Instance {
            family: "capacity",
            name: format!("capacity-cnf-{tag}-s{seed}-{suffix}"),
            logic: String::new(),
            script,
            kind: InstanceKind::Cnf,
            expected: vec![answer],
            witness: w,
            certificate: certificate(&d),
            tags: vec!["capacity", "cnf"],
        });
    }

    // Incremental history from a SAT base.
    let d = build(seed, p, true, Variant::Incremental)?;
    let phi0 = match &d.plant {
        Some(phi) => phi[0],
        None => return Err("capacity: incremental variant needs a plant".into()),
    };
    let stuck_obj = 0usize;
    let new_a = phi0; // the new object's only allowed resource
    let free_res = d.resources - 1; // reserved top resource
    let new_obj = d.objects;
    let n2 = d.objects + 1;
    let mut script = ";; capacity incremental\n(set-logic QF_UF)\n".to_string();
    for l in bool_decls(&d).into_iter().chain(bool_asserts(&d)) {
        script.push_str(&l);
        script.push('\n');
    }
    script.push_str("(check-sat)\n");
    // Scope 1: a new object whose only allowed resource is phi(0), which
    // object 0 (singleton allowed set) must also take.
    script.push_str("(push 1)\n");
    let _ = writeln!(script, "(declare-const r_{new_obj}_{new_a} Bool)");
    let _ = writeln!(script, "(assert r_{new_obj}_{new_a})");
    let _ = writeln!(
        script,
        "(assert (or (not r_{stuck_obj}_{new_a}) (not r_{new_obj}_{new_a})))"
    );
    script.push_str("(check-sat)\n(pop 1)\n(check-sat)\n");
    // Scope 2: the new object takes the reserved top resource.
    script.push_str("(push 1)\n");
    let _ = writeln!(script, "(declare-const r_{n2}_{free_res} Bool)");
    let _ = writeln!(script, "(assert r_{n2}_{free_res})");
    script.push_str("(check-sat)\n(pop 1)\n(check-sat)\n");
    out.push(Instance {
        family: "capacity",
        name: format!("capacity-incremental-s{seed}-{suffix}"),
        logic: "QF_UF".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![
            Answer::Sat,
            Answer::Unsat,
            Answer::Sat,
            Answer::Sat,
            Answer::Sat,
        ],
        witness: witness_text(&d),
        certificate: format!(
            "{} Under scope 1 a new object only allows resource {new_a}, which object {stuck_obj} (singleton allowed set) must also take -> unsat; popping restores sat. Under scope 2 the new object takes reserved resource {free_res} -> sat.",
            certificate(&d)
        ),
        tags: vec!["capacity", "incremental", "push-pop"],
    });
    Ok(out)
}

fn cnf_script(d: &Data, name: &str) -> (String, Option<String>) {
    let var = |i: usize, j: usize| (i * d.resources + j) as i32 + 1;
    let mut n_vars = 0i32;
    for i in 0..d.objects {
        for &j in &d.allowed[i] {
            n_vars = n_vars.max(var(i, j));
        }
    }
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    for i in 0..d.objects {
        clauses.push(d.allowed[i].iter().map(|&j| var(i, j)).collect());
        for x in 0..d.allowed[i].len() {
            for y in (x + 1)..d.allowed[i].len() {
                clauses.push(vec![-var(i, d.allowed[i][x]), -var(i, d.allowed[i][y])]);
            }
        }
    }
    for j in 0..d.resources {
        let users: Vec<usize> = (0..d.objects)
            .filter(|i| d.allowed[*i].contains(&j))
            .collect();
        for x in 0..users.len() {
            for y in (x + 1)..users.len() {
                clauses.push(vec![-var(users[x], j), -var(users[y], j)]);
            }
        }
    }
    let mut s = String::new();
    let _ = writeln!(s, "c generated by nixie-obligation: {name}");
    let _ = writeln!(
        s,
        "c capacity instance: {} objects, {} resources",
        d.objects, d.resources
    );
    if let Some(phi) = &d.plant {
        let parts: Vec<String> = phi
            .iter()
            .enumerate()
            .map(|(i, &r)| format!("{}->{}", i, r))
            .collect();
        let _ = writeln!(s, "c witness: {}", parts.join(" "));
    }
    let _ = writeln!(s, "p cnf {n_vars} {}", clauses.len());
    for cl in &clauses {
        let lits: Vec<String> = cl.iter().map(|l| l.to_string()).collect();
        let _ = writeln!(s, "{} 0", lits.join(" "));
    }
    (s, witness_text(d))
}
