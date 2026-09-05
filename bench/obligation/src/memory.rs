//! Alias-ambiguous memory histories (production `Ambiguity`), shaped after
//! SMT-LIB `storecomm`: two orderings of the same array writes.
//!
//! * UNSAT (`distinct-asserted`): with pairwise-distinct indices, any
//!   permutation of non-overlapping writes yields the *same* array, so a
//!   disequality on a read is refuted — but the solver must reason through
//!   the write histories to see it.
//! * UNSAT (`offset-implied`): distinctness is *implied* by
//!   `idx_k = base + k*step, step > 0` — arithmetic has to discharge the
//!   aliasing question before array reasoning can conclude.
//! * SAT (`alias`): exactly one pair of writes shares an index and the two
//!   histories order them differently with distinct values — the arrays
//!   differ at that index; the generator verifies this by simulation.
//! * Incremental: all of the above under push/pop scopes.

use crate::{Answer, Instance, InstanceKind, Rng};
use std::collections::HashMap;
use std::fmt::Write as _;

pub struct Params {
    pub writes: usize,
}

pub struct Data {
    pub n: usize,
    /// Second history: step k applies write `order2[k]`.
    pub order2: Vec<usize>,
    /// SAT variant: (i, j) with i < j, idx_i = idx_j, ordered differently
    /// in the two histories.
    pub alias: Option<(usize, usize)>,
}

impl Data {
    /// Simulate both histories over concrete distinct addresses; the final
    /// arrays must agree for the UNSAT variant.
    fn simulate(&self, addrs: &[i64], vals: &[i64]) -> (HashMap<i64, i64>, HashMap<i64, i64>) {
        let mut a1: HashMap<i64, i64> = HashMap::new();
        let mut a2: HashMap<i64, i64> = HashMap::new();
        for k in 0..self.n {
            a1.insert(addrs[k], vals[k]);
        }
        for &k in &self.order2 {
            a2.insert(addrs[k], vals[k]);
        }
        (a1, a2)
    }

    pub fn verify(&self) -> Result<(), String> {
        if self.order2.len() != self.n {
            return Err("memory: order2 size mismatch".into());
        }
        let mut check = vec![false; self.n];
        for &k in &self.order2 {
            if k >= self.n || check[k] {
                return Err("memory: order2 not a permutation".into());
            }
            check[k] = true;
        }
        let mut rng = Rng::new(0x5C2A_11CE);
        match self.alias {
            None => {
                for _ in 0..24 {
                    let mut addrs: Vec<i64> = Vec::new();
                    let mut seen = std::collections::BTreeSet::new();
                    while addrs.len() < self.n {
                        let a = rng.range_i64(-1000, 1000);
                        if seen.insert(a) {
                            addrs.push(a);
                        }
                    }
                    let vals: Vec<i64> = (0..self.n).map(|_| rng.range_i64(-1000, 1000)).collect();
                    let (a1, a2) = self.simulate(&addrs, &vals);
                    if a1 != a2 {
                        return Err("memory: reorder changed the array (construction bug)".into());
                    }
                }
                Ok(())
            }
            Some((i, j)) => {
                if i >= j || j >= self.n {
                    return Err("memory: bad alias pair".into());
                }
                let pos_i = self.order2.iter().position(|&k| k == i);
                let pos_j = self.order2.iter().position(|&k| k == j);
                match (pos_i, pos_j) {
                    (Some(pi), Some(pj)) => {
                        if pj >= pi {
                            return Err(
                                "memory: alias pair not reordered in the second history".into()
                            );
                        }
                        // Simulate with the aliased index and distinct values.
                        let mut addrs: Vec<i64> = Vec::new();
                        let mut seen = std::collections::BTreeSet::new();
                        while addrs.len() < self.n {
                            let a = rng.range_i64(-1000, 1000);
                            if seen.insert(a) {
                                addrs.push(a);
                            }
                        }
                        addrs[j] = addrs[i];
                        let mut vals: Vec<i64> = (0..self.n).map(|k| k as i64).collect();
                        vals[i] = 7;
                        vals[j] = 9;
                        let (a1, a2) = self.simulate(&addrs, &vals);
                        match (a1.get(&addrs[i]), a2.get(&addrs[i])) {
                            (Some(v1), Some(v2)) if v1 != v2 => Ok(()),
                            _ => Err("memory: aliased histories agree at the alias (bug)".into()),
                        }
                    }
                    _ => Err("memory: alias pair missing from order2".into()),
                }
            }
        }
    }
}

pub enum Variant {
    Reorder { offset_implied: bool },
    Alias,
}

pub fn build(seed: u64, p: &Params, variant: &Variant) -> Result<Data, String> {
    if p.writes < 4 {
        return Err("memory: need >= 4 writes".into());
    }
    let n = p.writes;
    let mut rng = Rng::new(seed ^ 0xA11A_0000);
    match variant {
        Variant::Reorder { .. } => {
            let mut order2: Vec<usize> = (0..n).collect();
            rng.shuffle(&mut order2);
            if order2 == (0..n).collect::<Vec<_>>() {
                order2.swap(0, n - 1);
            }
            let d = Data {
                n,
                order2,
                alias: None,
            };
            d.verify()?;
            Ok(d)
        }
        Variant::Alias => {
            let i = rng.index(n - 1);
            let j = i + 1 + rng.index(n - 1 - i);
            let mut order2: Vec<usize> = (0..n).collect();
            rng.shuffle(&mut order2);
            let pi = order2.iter().position(|&k| k == i).unwrap_or(0);
            let pj = order2.iter().position(|&k| k == j).unwrap_or(0);
            // Ensure the aliased writes are ordered differently: history 1
            // writes i then j (i < j ascending); history 2 must write j
            // before i, i.e. pos(j) < pos(i).
            if pi < pj {
                order2.swap(pi, pj);
            }
            let d = Data {
                n,
                order2,
                alias: Some((i, j)),
            };
            d.verify()?;
            Ok(d)
        }
    }
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

fn store_chain(n: usize, order: &[usize], idx: &dyn Fn(usize) -> String) -> String {
    let mut t = String::from("a0");
    for &k in order.iter().take(n) {
        t = format!("(store {t} {} v{k})", idx(k));
    }
    t
}

fn decls_and_distinct(n: usize, offset_implied: bool, skip: Option<usize>) -> String {
    let mut s = String::new();
    s.push_str("(declare-const a0 (Array Int Int))\n");
    if offset_implied {
        let _ = writeln!(s, "(declare-const base Int)");
        let _ = writeln!(s, "(declare-const step Int)");
        let _ = writeln!(s, "(assert (> step 0))");
        for k in 0..n {
            let _ = writeln!(s, "(define-fun idx{k} () Int (+ base (* {k} step)))");
        }
    } else {
        for k in 0..n {
            let _ = writeln!(s, "(declare-const idx{k} Int)");
        }
        let mut lits: Vec<String> = Vec::new();
        for k in 0..n {
            if Some(k) != skip {
                lits.push(format!("idx{k}"));
            }
        }
        let _ = writeln!(s, "(assert (distinct {}))", lits.join(" "));
    }
    for k in 0..n {
        let _ = writeln!(s, "(declare-const v{k} Int)");
    }
    s
}

pub fn generate(seed: u64, p: &Params, suffix: &str) -> Result<Vec<Instance>, String> {
    let mut out = Vec::new();
    let identity: Vec<usize> = (0..p.writes).collect();
    let idx_sym = |k: usize| format!("idx{k}");

    // UNSAT, distinctness asserted.
    let d = build(
        seed,
        p,
        &Variant::Reorder {
            offset_implied: false,
        },
    )?;
    let a1 = store_chain(d.n, &identity, &idx_sym);
    let a2 = store_chain(d.n, &d.order2, &idx_sym);
    let mut script =
        String::from(";; memory reorder, distinctness asserted (UNSAT)\n(set-logic QF_AUFLIA)\n");
    script.push_str(&decls_and_distinct(d.n, false, None));
    let _ = writeln!(script, "(define-fun a1 () (Array Int Int) {a1})");
    let _ = writeln!(script, "(define-fun a2 () (Array Int Int) {a2})");
    let _ = writeln!(
        script,
        "(assert (distinct (select a1 idx0) (select a2 idx0)))"
    );
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "memory",
        name: format!("memory-reorder-distinct-unsat-s{seed}-{suffix}"),
        logic: "QF_AUFLIA".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Unsat],
        witness: None,
        certificate: format!(
            "With pairwise-distinct indices the {} writes never overlap, so any permutation produces the same array (verified by simulating both histories over 24 random distinct-address valuations in the generator); hence select(a1, q) = select(a2, q) for every q.",
            d.n
        ),
        tags: vec!["ambiguity", "arrays", "storecomm", "reorder"],
    });

    // UNSAT, distinctness implied by arithmetic.
    let d2 = build(
        seed ^ 0x00F0_F5E7,
        p,
        &Variant::Reorder {
            offset_implied: true,
        },
    )?;
    let a1 = store_chain(d2.n, &identity, &idx_sym);
    let a2 = store_chain(d2.n, &d2.order2, &idx_sym);
    let mut script = String::from(
        ";; memory reorder, distinctness implied by arithmetic (UNSAT)\n(set-logic QF_AUFLIA)\n",
    );
    script.push_str(&decls_and_distinct(d2.n, true, None));
    let _ = writeln!(script, "(define-fun a1 () (Array Int Int) {a1})");
    let _ = writeln!(script, "(define-fun a2 () (Array Int Int) {a2})");
    let _ = writeln!(
        script,
        "(assert (distinct (select a1 idx0) (select a2 idx0)))"
    );
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "memory",
        name: format!("memory-reorder-offset-unsat-s{seed}-{suffix}"),
        logic: "QF_AUFLIA".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Unsat],
        witness: None,
        certificate:
            "idx_k = base + k*step with step > 0 forces distinctness through arithmetic; with non-overlapping writes both histories again produce the same array."
                .into(),
        tags: vec!["ambiguity", "arrays", "storecomm", "arith-implied-distinct"],
    });

    // SAT alias.
    let d3 = build(seed ^ 0x000A_11A5, p, &Variant::Alias)?;
    if let Some((i, j)) = d3.alias {
        let a1 = store_chain(d3.n, &identity, &idx_sym);
        let a2 = store_chain(d3.n, &d3.order2, &idx_sym);
        let mut script = String::from(
            ";; memory alias, reordered pair with distinct values (SAT)\n(set-logic QF_AUFLIA)\n",
        );
        script.push_str(&decls_and_distinct(d3.n, false, Some(j)));
        let _ = writeln!(script, "(assert (= idx{i} idx{j}))");
        let _ = writeln!(script, "(assert (distinct v{i} v{j}))");
        let _ = writeln!(script, "(define-fun a1 () (Array Int Int) {a1})");
        let _ = writeln!(script, "(define-fun a2 () (Array Int Int) {a2})");
        let _ = writeln!(
            script,
            "(assert (distinct (select a1 idx{i}) (select a2 idx{i})))"
        );
        script.push_str("(check-sat)\n");
        out.push(Instance {
            family: "memory",
            name: format!("memory-alias-sat-s{seed}-{suffix}"),
            logic: "QF_AUFLIA".into(),
            script,
            kind: InstanceKind::Smt2,
            expected: vec![Answer::Sat],
            witness: Some(format!(
                "idx_k = k for k != {j}, idx_{j} = idx_{i} = {i}; v_{i} = 7, v_{j} = 9, v_k = k otherwise (verified by simulation)"
            )),
            certificate: format!(
                "Writes {i} and {j} share an index (asserted), carry distinct values (asserted), and appear in opposite order in the two histories, so the final arrays differ at that index (verified by simulating both histories in the generator)."
            ),
            tags: vec!["ambiguity", "arrays", "alias", "sat"],
        });
    }

    // Incremental history.
    let d4 = build(
        seed ^ 0x01DC_1234,
        p,
        &Variant::Reorder {
            offset_implied: false,
        },
    )?;
    if let Some((i, j)) = build(seed ^ 0x000A_11A5, p, &Variant::Alias)?.alias {
        let a1r = store_chain(d4.n, &identity, &idx_sym);
        let a2r = store_chain(d4.n, &d4.order2, &idx_sym);
        let a1a = store_chain(d4.n, &identity, &idx_sym);
        let a2a = {
            // second history for the alias case, from the alias dataset
            let da = build(seed ^ 0x000A_11A5, p, &Variant::Alias)?;
            store_chain(da.n, &da.order2, &idx_sym)
        };
        let mut script = String::from(";; memory incremental history\n(set-logic QF_AUFLIA)\n");
        // Base: all indices distinct *except* the aliased pair, so the
        // alias scope below is consistent with the base level.
        script.push_str(&decls_and_distinct(d4.n, false, Some(j)));
        script.push_str("(check-sat)\n");
        // Scope 1 restores full distinctness (idx_j against *everyone*,
        // not just idx_i) -> reorder equality -> unsat.
        script.push_str("(push 1)\n");
        let mut all_idx: Vec<String> = (0..d4.n).map(|k| format!("idx{k}")).collect();
        let _ = writeln!(script, "(assert (distinct {}))", all_idx.join(" "));
        all_idx.clear();
        let _ = writeln!(script, "(define-fun b1 () (Array Int Int) {a1r})");
        let _ = writeln!(script, "(define-fun b2 () (Array Int Int) {a2r})");
        let _ = writeln!(
            script,
            "(assert (distinct (select b1 idx0) (select b2 idx0)))"
        );
        script.push_str("(check-sat)\n(pop 1)\n(check-sat)\n");
        // Scope 2 aliases the pair with distinct values -> arrays differ.
        script.push_str("(push 1)\n");
        let _ = writeln!(script, "(assert (= idx{i} idx{j}))");
        let _ = writeln!(script, "(assert (distinct v{i} v{j}))");
        let _ = writeln!(script, "(define-fun c1 () (Array Int Int) {a1a})");
        let _ = writeln!(script, "(define-fun c2 () (Array Int Int) {a2a})");
        let _ = writeln!(
            script,
            "(assert (distinct (select c1 idx{i}) (select c2 idx{i})))"
        );
        script.push_str("(check-sat)\n(pop 1)\n(check-sat)\n");
        out.push(Instance {
            family: "memory",
            name: format!("memory-incremental-s{seed}-{suffix}"),
            logic: "QF_AUFLIA".into(),
            script,
            kind: InstanceKind::Smt2,
            expected: vec![
                Answer::Sat,
                Answer::Unsat,
                Answer::Sat,
                Answer::Sat,
                Answer::Sat,
            ],
            witness: None,
            certificate:
                "Scope 1 asserts a reorder disequality over distinct indices (unsat); scope 2 asserts the aliased variant (sat). Each answer follows from the corresponding static certificate above."
                    .into(),
            tags: vec!["ambiguity", "arrays", "incremental", "push-pop"],
        });
    }
    Ok(out)
}
