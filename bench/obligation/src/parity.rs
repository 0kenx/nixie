//! Graph-parity obstruction (production `GlobalObstruction`).
//!
//! A Boolean variable per edge of a connected graph; at every vertex the
//! XOR of incident edges is fixed to a charge `c_v`. Every edge occurs in
//! exactly two vertex equations, so XOR-ing *all* equations gives
//! `0 = xor(c_v)`: the instance is UNSAT iff the total charge is odd, and
//! *every proper subset* of the equations is satisfiable (the incidence
//! matrix of a connected graph has row rank V-1 over GF(2)). The
//! contradiction cannot be localized — that is the point.
//!
//! Realizations:
//! * `mixed-bool-int`: some vertex equations as Bool XOR chains, others as
//!   LIA sums `sum(i_e) = c_v + 2*k_v`, edge values linked across sorts —
//!   the obstruction must be reconciled across theories.
//! * `mixed-boundary`: same, but the link `i_e = ite(b_e,1,0)` is replaced
//!   by an exact div/mod chain that maps the two Booleans to 0/1 — the
//!   `Boundary` production joined into the obstruction.
//! * `bv`: width-1 BV XOR chains.
//! * `cnf`: Tseitin-encoded DIMACS for the pure SAT core.
//! * `incremental`: charge variables toggled under push/pop scopes.

use crate::{Answer, Instance, InstanceKind, Rng, fold_binary};
use std::collections::BTreeSet;
use std::fmt::Write as _;

pub struct Params {
    pub vertices: usize,
    pub extra_edges: usize,
}

pub struct Data {
    pub vertices: usize,
    pub edges: Vec<(usize, usize)>,
    /// 0/1 charge per vertex. Total parity decides sat/unsat.
    pub charges: Vec<u64>,
    /// Per-vertex realization group: `true` = Bool XOR, `false` = LIA sum.
    pub bool_group: Vec<bool>,
    /// Satisfying edge assignment, present iff the total charge is even.
    pub witness: Option<Vec<u64>>,
}

impl Data {
    pub fn answer(&self) -> Answer {
        let total: u64 = self.charges.iter().sum();
        if total.is_multiple_of(2) {
            Answer::Sat
        } else {
            Answer::Unsat
        }
    }

    /// Re-verify the certificate against the semantic structures.
    pub fn verify(&self) -> Result<(), String> {
        if self.charges.len() != self.vertices || self.bool_group.len() != self.vertices {
            return Err("parity: size mismatch".into());
        }
        if self.vertices < 2 || self.edges.len() < self.vertices - 1 {
            return Err("parity: graph too small / disconnected".into());
        }
        for &(a, b) in &self.edges {
            if a == b || a >= self.vertices || b >= self.vertices {
                return Err("parity: bad edge endpoint".into());
            }
        }
        for c in &self.charges {
            if *c > 1 {
                return Err("parity: charge not in {0,1}".into());
            }
        }
        match (&self.witness, self.answer()) {
            (Some(x), Answer::Sat) => {
                for v in 0..self.vertices {
                    let s: u64 = self
                        .edges
                        .iter()
                        .enumerate()
                        .filter(|(_, e)| e.0 == v || e.1 == v)
                        .map(|(ei, _)| x[ei])
                        .sum();
                    if s % 2 != self.charges[v] {
                        return Err(format!("parity: witness fails vertex {v}"));
                    }
                }
                Ok(())
            }
            (None, Answer::Unsat) => Ok(()),
            (Some(_), Answer::Unsat) => Err("parity: witness for odd charge total".into()),
            (None, Answer::Sat) => Err("parity: missing witness for even charge total".into()),
            _ => Err("parity: unexpected answer class".into()),
        }
    }

    /// Minimality of the obstruction: dropping any single vertex equation
    /// must leave a satisfiable system. Used by tests (and documented in
    /// the certificate); O(V * V*E) bit-eliminations.
    pub fn verify_minimal_obstruction(&self) -> Result<(), String> {
        for drop in 0..self.vertices {
            if solve_subset(self.vertices, &self.edges, &self.charges, drop).is_none() {
                return Err(format!(
                    "parity: dropping vertex {drop} leaves an unsatisfiable subsystem (obstruction not minimal)"
                ));
            }
        }
        Ok(())
    }
}

/// Solve `xor_{e incident to v} x_e = charges[v]` over GF(2) for the full
/// system. See [`solve_subset`].
pub fn solve_parity(n: usize, edges: &[(usize, usize)], charges: &[u64]) -> Option<Vec<u64>> {
    solve_subset(n, edges, charges, usize::MAX)
}

/// Solve with one vertex row dropped (`drop == usize::MAX` keeps all).
pub fn solve_subset(
    n: usize,
    edges: &[(usize, usize)],
    charges: &[u64],
    drop: usize,
) -> Option<Vec<u64>> {
    let n_e = edges.len();
    let mut rows: Vec<Vec<u8>> = Vec::new();
    for v in 0..n {
        if v == drop {
            continue;
        }
        let mut r = vec![0u8; n_e + 1];
        for (ei, (a, b)) in edges.iter().enumerate() {
            if *a == v || *b == v {
                r[ei] = 1;
            }
        }
        r[n_e] = charges[v] as u8;
        rows.push(r);
    }
    gaussian_solve(&mut rows, n_e)
}

fn gaussian_solve(rows: &mut [Vec<u8>], n_e: usize) -> Option<Vec<u64>> {
    let mut pivot_cols: Vec<usize> = Vec::new();
    let mut pivot_row = 0usize;
    for col in 0..n_e {
        let found = (pivot_row..rows.len()).find(|&r| rows[r][col] == 1);
        if let Some(r) = found {
            rows.swap(pivot_row, r);
            for r2 in 0..rows.len() {
                if r2 != pivot_row && rows[r2][col] == 1 {
                    for c in 0..=n_e {
                        rows[r2][c] ^= rows[pivot_row][c];
                    }
                }
            }
            pivot_cols.push(col);
            pivot_row += 1;
        }
    }
    // Consistency: a zero LHS with rhs 1 is unsatisfiable.
    for r in 0..rows.len() {
        if rows[r][..n_e].iter().all(|&x| x == 0) && rows[r][n_e] == 1 {
            return None;
        }
    }
    let mut x = vec![0u64; n_e];
    // Back-substitute in decreasing pivot-column order so that later
    // variables are already final when used. In RREF the row with pivot
    // `col` is exactly the row that was installed when `col` became a
    // pivot (they were pushed in order).
    for (ri, &col) in pivot_cols.iter().enumerate().rev() {
        let mut s = rows[ri][n_e];
        for c in (col + 1)..n_e {
            if rows[ri][c] == 1 {
                s ^= x[c] as u8;
            }
        }
        x[col] = s as u64;
    }
    Some(x)
}

/// Build one dataset: connected random graph, random charges with the
/// requested total parity, mixed realization groups, and (for even
/// parity) a verified satisfying assignment.
pub fn build(seed: u64, p: &Params, odd: bool) -> Result<Data, String> {
    let n = p.vertices.max(2);
    let mut rng = Rng::new(seed ^ 0x1D0C_0FFE ^ (odd as u64));
    let mut edges: Vec<(usize, usize)> = Vec::with_capacity(n - 1 + p.extra_edges);
    let mut seen: BTreeSet<(usize, usize)> = BTreeSet::new();
    for v in 1..n {
        let a = rng.index(v);
        edges.push((a, v));
        seen.insert((a.min(v), a.max(v)));
    }
    let target = (n - 1) + p.extra_edges;
    let mut guard = 0usize;
    while edges.len() < target && guard < target * 30 {
        guard += 1;
        let a = rng.index(n);
        let b = rng.index(n);
        if a == b {
            continue;
        }
        let key = (a.min(b), a.max(b));
        if seen.contains(&key) {
            continue;
        }
        seen.insert(key);
        edges.push((a, b));
    }
    let mut charges: Vec<u64> = (0..n).map(|_| rng.range_i64(0, 1) as u64).collect();
    let total: u64 = charges.iter().sum();
    if total % 2 != odd as u64 {
        charges[0] ^= 1;
    }
    let mut bool_group: Vec<bool> = (0..n).map(|_| rng.chance(1, 2)).collect();
    bool_group[0] = true;
    if n > 1 {
        bool_group[1] = false;
    }
    let witness = solve_parity(n, &edges, &charges);
    let data = Data {
        vertices: n,
        edges,
        charges,
        bool_group,
        witness,
    };
    data.verify()?;
    Ok(data)
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

struct Parts {
    decls: Vec<String>,
    asserts: Vec<String>,
}

fn charge_rhs(d: &Data, v: usize, charge_vars: bool) -> String {
    if charge_vars {
        if d.bool_group[v] {
            format!("chb{v}")
        } else {
            format!("ch{v}")
        }
    } else if d.bool_group[v] {
        if d.charges[v] == 1 {
            "true".to_string()
        } else {
            "false".to_string()
        }
    } else {
        format!("{}", d.charges[v])
    }
}

fn mixed_parts(d: &Data, charge_vars: bool, wrap: Option<&str>) -> Parts {
    let mut decls = Vec::new();
    let mut asserts = Vec::new();
    for (ei, &(a, b)) in d.edges.iter().enumerate() {
        let touches_bool = d.bool_group[a] || d.bool_group[b];
        let touches_int = !d.bool_group[a] || !d.bool_group[b];
        if touches_bool {
            decls.push(format!("(declare-const b{ei} Bool)"));
        }
        if touches_int {
            decls.push(format!("(declare-const i{ei} Int)"));
        }
        if touches_bool && touches_int {
            match wrap {
                None => asserts.push(format!("(assert (= i{ei} (ite b{ei} 1 0)))")),
                Some(template) => asserts.push(format!(
                    "(assert (= i{ei} {}))",
                    template.replace("{v}", &format!("b{ei}"))
                )),
            }
        }
    }
    for v in 0..d.vertices {
        let incident: Vec<usize> = d
            .edges
            .iter()
            .enumerate()
            .filter(|(_, e)| e.0 == v || e.1 == v)
            .map(|(ei, _)| ei)
            .collect();
        if d.bool_group[v] {
            let terms: Vec<String> = incident.iter().map(|&ei| format!("b{ei}")).collect();
            asserts.push(format!(
                "(assert (= {} {}))",
                fold_binary("xor", &terms, "false"),
                charge_rhs(d, v, charge_vars)
            ));
        } else {
            decls.push(format!("(declare-const k{v} Int)"));
            let terms: Vec<String> = incident.iter().map(|&ei| format!("i{ei}")).collect();
            let lhs = if terms.is_empty() {
                "0".to_string()
            } else {
                format!("(+ {})", terms.join(" "))
            };
            asserts.push(format!(
                "(assert (= {lhs} (+ {} (* 2 k{v}))))",
                charge_rhs(d, v, charge_vars)
            ));
        }
    }
    if charge_vars {
        for v in 0..d.vertices {
            if d.bool_group[v] {
                decls.push(format!("(declare-const chb{v} Bool)"));
                asserts.push(format!(
                    "(assert (= chb{v} {}))",
                    if d.charges[v] == 1 { "true" } else { "false" }
                ));
            } else {
                decls.push(format!("(declare-const ch{v} Int)"));
                asserts.push(format!("(assert (= ch{v} {}))", d.charges[v]));
            }
        }
    }
    Parts { decls, asserts }
}

fn header(logic: &str, name: &str) -> String {
    format!(";; generated by nixie-obligation: {name}\n(set-logic {logic})\n")
}

fn witness_text(d: &Data) -> Option<String> {
    d.witness.as_ref().map(|x| {
        let parts: Vec<String> = x
            .iter()
            .enumerate()
            .map(|(ei, &v)| {
                if d.bool_group[d.edges[ei].0] || d.bool_group[d.edges[ei].1] {
                    format!("b{ei}={}", v == 1)
                } else {
                    format!("i{ei}={v}")
                }
            })
            .collect();
        format!("edge values: {}", parts.join(", "))
    })
}

/// Search for an exact div/mod chain mapping `true -> 1`, `false -> 0`:
/// `(mod (div (ite b C1 C0) D) 2)` with C0 an even multiple of D and C1 an
/// odd multiple of D (possibly negative — Euclidean semantics probed).
fn find_wrap(rng: &mut Rng) -> String {
    for _ in 0..64 {
        let d = rng.range_i64(3, 16);
        let t = rng.range_i64(1, 4);
        let s = rng.range_i64(0, 3);
        let (c0, c1) = if rng.chance(1, 2) {
            (2 * d * t, d * (2 * s + 1))
        } else {
            (-(d * (2 * s + 1)), -(2 * d * t))
        };
        if crate::smt_mod(crate::smt_div(c1, d), 2) == 1
            && crate::smt_mod(crate::smt_div(c0, d), 2) == 0
        {
            return format!("(mod (div (ite {{v}} {c1} {c0}) {d}) 2)");
        }
    }
    // Deterministic fallback, verified by construction (d=7: 21 -> 3 -> 1,
    // 14 -> 2 -> 0).
    "(mod (div (ite {v} 21 14) 7) 2)".to_string()
}

pub fn generate(seed: u64, p: &Params, suffix: &str) -> Result<Vec<Instance>, String> {
    let mut out = Vec::new();
    for &odd in &[false, true] {
        let d = build(seed, p, odd)?;
        let tag = if odd { "unsat" } else { "sat" };
        let answer = d.answer();

        // mixed Bool+Int
        let parts = mixed_parts(&d, false, None);
        let mut script = header("QF_LIA", "parity mixed-bool-int");
        for l in parts.decls.iter().chain(parts.asserts.iter()) {
            script.push_str(l);
            script.push('\n');
        }
        script.push_str("(check-sat)\n");
        out.push(Instance {
            family: "parity",
            name: format!("parity-mixedboolint-{tag}-s{seed}-{suffix}"),
            logic: "QF_LIA".into(),
            script,
            kind: InstanceKind::Smt2,
            expected: vec![answer],
            witness: witness_text(&d),
            certificate: certificate(&d),
            tags: vec!["global-obstruction", "mixed-bool-int"],
        });

        // BV realization
        let mut script = header("QF_BV", "parity bv1-xor");
        for ei in 0..d.edges.len() {
            let _ = writeln!(script, "(declare-const x{ei} (_ BitVec 1))");
        }
        for v in 0..d.vertices {
            let terms: Vec<String> = d
                .edges
                .iter()
                .enumerate()
                .filter(|(_, e)| e.0 == v || e.1 == v)
                .map(|(ei, _)| format!("x{ei}"))
                .collect();
            let _ = writeln!(
                script,
                "(assert (= {} (_ bv{} 1)))",
                fold_binary("bvxor", &terms, "(_ bv0 1)"),
                d.charges[v]
            );
        }
        script.push_str("(check-sat)\n");
        out.push(Instance {
            family: "parity",
            name: format!("parity-bv-{tag}-s{seed}-{suffix}"),
            logic: "QF_BV".into(),
            script,
            kind: InstanceKind::Smt2,
            expected: vec![answer],
            witness: witness_text(&d),
            certificate: certificate(&d),
            tags: vec!["global-obstruction", "bv"],
        });

        // CNF (Tseitin XOR chains)
        let (script, w) = cnf_script(&d, &format!("parity-cnf-{tag}-s{seed}-{suffix}"));
        out.push(Instance {
            family: "parity",
            name: format!("parity-cnf-{tag}-s{seed}-{suffix}"),
            logic: String::new(),
            script,
            kind: InstanceKind::Cnf,
            expected: vec![answer],
            witness: w,
            certificate: certificate(&d),
            tags: vec!["global-obstruction", "cnf", "tseitin"],
        });

        if odd {
            // Boundary-joined: exact div/mod link between the Bool and Int
            // copies of each shared edge.
            let mut rng = Rng::new(seed ^ 0xB0A5);
            let wrap = find_wrap(&mut rng);
            let parts = mixed_parts(&d, false, Some(&wrap));
            let mut script = header("QF_LIA", "parity mixed-boundary");
            for l in parts.decls.iter().chain(parts.asserts.iter()) {
                script.push_str(l);
                script.push('\n');
            }
            script.push_str("(check-sat)\n");
            out.push(Instance {
                family: "parity",
                name: format!("parity-mixedboundary-unsat-s{seed}-{suffix}"),
                logic: "QF_LIA".into(),
                script,
                kind: InstanceKind::Smt2,
                expected: vec![Answer::Unsat],
                witness: None,
                certificate: format!(
                    "{} Link chain: {} (exact on both input constants, verified in the generator).",
                    certificate(&d),
                    wrap.replace("{v}", "b_e")
                ),
                tags: vec!["global-obstruction", "mixed-bool-int", "boundary-join"],
            });
        } else {
            // Incremental history: charge variables toggled under scopes.
            let parts = mixed_parts(&d, true, None);
            let mut rng = Rng::new(seed ^ 0x1D0C_11E5);
            let v0 = rng.index(d.vertices);
            let mut v1 = rng.index(d.vertices);
            if v1 == v0 {
                v1 = (v1 + 1) % d.vertices;
            }
            let mut expected = vec![Answer::Sat];
            let mut script = header("QF_LIA", "parity incremental charge toggles");
            for l in parts.decls.iter().chain(parts.asserts.iter()) {
                script.push_str(l);
                script.push('\n');
            }
            script.push_str("(check-sat)\n");
            for v in [v0, v1] {
                let flipped = if d.bool_group[v] {
                    if d.charges[v] == 1 { "false" } else { "true" }.to_string()
                } else {
                    format!("{}", 1 - d.charges[v])
                };
                script.push_str("(push 1)\n");
                script.push_str("(assert (= ");
                script.push_str(&charge_rhs(&d, v, true));
                script.push_str(&format!(" {flipped}))\n"));
                script.push_str("(check-sat)\n");
                expected.push(Answer::Unsat);
                script.push_str("(pop 1)\n(check-sat)\n");
                expected.push(Answer::Sat);
            }
            out.push(Instance {
                family: "parity",
                name: format!("parity-incremental-s{seed}-{suffix}"),
                logic: "QF_LIA".into(),
                script,
                kind: InstanceKind::Smt2,
                expected,
                witness: witness_text(&d),
                certificate: format!(
                    "{} Each scoped toggle flips exactly one charge, making the total odd; popping restores it.",
                    certificate(&d)
                ),
                tags: vec!["global-obstruction", "incremental", "push-pop"],
            });
        }
    }
    Ok(out)
}

fn certificate(d: &Data) -> String {
    let total: u64 = d.charges.iter().sum();
    if total % 2 == 1 {
        format!(
            "Total vertex charge is odd (sum c_v = {total}); every edge appears in exactly two vertex equations, so XOR-ing all {} equations yields 0 = 1. Any proper subset is satisfiable (connected incidence matrix has GF(2) row rank V-1).",
            d.vertices
        )
    } else {
        format!(
            "Total vertex charge is even (sum c_v = {total}); the witness was computed by GF(2) Gaussian elimination and verified against every vertex equation in the generator."
        )
    }
}

fn cnf_script(d: &Data, name: &str) -> (String, Option<String>) {
    let n_e = d.edges.len();
    let mut next_var: i32 = n_e as i32;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    for v in 0..d.vertices {
        let incident: Vec<i32> = d
            .edges
            .iter()
            .enumerate()
            .filter(|(_, e)| e.0 == v || e.1 == v)
            .map(|(ei, _)| (ei as i32) + 1)
            .collect();
        if incident.is_empty() {
            continue;
        }
        // z = l1; z' = z XOR l: (¬z ∨ ¬l ∨ z')(¬z ∨ l ∨ ¬z')(z ∨ ¬l ∨ ¬z')(z ∨ l ∨ z')
        let mut z = incident[0];
        for &l in &incident[1..] {
            next_var += 1;
            let zp = next_var;
            clauses.push(vec![-z, -l, zp]);
            clauses.push(vec![-z, l, -zp]);
            clauses.push(vec![z, -l, -zp]);
            clauses.push(vec![z, l, zp]);
            z = zp;
        }
        if d.charges[v] == 1 {
            clauses.push(vec![z]);
        } else {
            clauses.push(vec![-z]);
        }
    }
    let mut s = String::new();
    let _ = writeln!(s, "c generated by nixie-obligation: {name}");
    let _ = writeln!(
        s,
        "c graph-parity obstruction: {} vertices, {} edges, total charge {}",
        d.vertices,
        n_e,
        d.charges.iter().sum::<u64>()
    );
    if let Some(x) = &d.witness {
        let vals: Vec<String> = x.iter().map(|&v| v.to_string()).collect();
        let _ = writeln!(s, "c witness edge values: {}", vals.join(" "));
    }
    let _ = writeln!(s, "p cnf {next_var} {}", clauses.len());
    for cl in &clauses {
        let lits: Vec<String> = cl.iter().map(|l| l.to_string()).collect();
        let _ = writeln!(s, "{} 0", lits.join(" "));
    }
    (s, witness_text(d))
}
