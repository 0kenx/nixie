//! Reconvergence (production `Reconverge`): two provably equivalent
//! computations with different structure, asserted to differ.
//!
//! Boolean arm: a random truth table computed once as a Shannon `ite`
//! tree and once in algebraic normal form (XOR of AND monomials).
//! Equivalence is brute-force verified over all `2^k` inputs in the
//! generator; a near-miss variant flips exactly one table entry, making
//! the disequality satisfiable at exactly that one input (needle).
//!
//! BV arm: random bit-permutation networks built from nested
//! extract/concat. The UNSAT case wires a permutation and its inverse in
//! sequence (round-trip = identity, verified by composition); the SAT
//! near-miss composes a single transposition, fixable exactly by inputs
//! with the two bits equal.

use crate::{Answer, Instance, InstanceKind, Rng, fold_binary};
use std::fmt::Write as _;

pub struct Params {
    /// Truth-table input count, 2 <= k <= 6 (2^k leaves).
    pub inputs: usize,
    /// BV width in {8, 16, 32, 64}.
    pub width: usize,
}

pub struct Data {
    pub k: usize,
    pub table: Vec<bool>,
    pub table2: Vec<bool>,
    /// Index at which table and table2 differ (the needle).
    pub flip: usize,
    pub anf: Vec<bool>,
    pub anf2: Vec<bool>,
    pub w: usize,
    /// P: output bit i takes input bit P[i].
    pub perm: Vec<usize>,
    /// Q with P[Q[i]] = i for all i (round-trip identity).
    pub q_ident: Vec<usize>,
    /// Q with P[Q[i]] = transposition(swap)(i).
    pub q_swap: Vec<usize>,
    pub swap: (usize, usize),
    pub witness_bv: u64,
}

fn mobius(t: &[bool]) -> Vec<bool> {
    let n = t.len();
    let mut a = t.to_vec();
    let mut bit = 1usize;
    while bit < n {
        for mask in 0..n {
            if mask & bit != 0 {
                a[mask] ^= a[mask ^ bit];
            }
        }
        bit <<= 1;
    }
    a
}

fn eval_anf(anf: &[bool], k: usize, input: usize) -> bool {
    let mut acc = false;
    for mask in 0..(1usize << k) {
        if anf[mask] && (mask & input) == mask {
            acc ^= true;
        }
    }
    acc
}

impl Data {
    pub fn verify(&self) -> Result<(), String> {
        if self.table.len() != (1 << self.k) {
            return Err("reconverge: table size mismatch".into());
        }
        // Shannon tree *is* the table; ANF must reproduce it exactly.
        for input in 0..(1usize << self.k) {
            if eval_anf(&self.anf, self.k, input) != self.table[input] {
                return Err(format!("reconverge: ANF disagrees at input {input}"));
            }
            if eval_anf(&self.anf2, self.k, input) != self.table2[input] {
                return Err(format!("reconverge: ANF2 disagrees at input {input}"));
            }
        }
        // Needle: tables differ exactly at self.flip.
        let diffs: Vec<usize> = (0..self.table.len())
            .filter(|&i| self.table[i] != self.table2[i])
            .collect();
        if diffs != vec![self.flip] {
            return Err("reconverge: near-miss tables differ at more than one point".into());
        }
        // BV: bijections and compositions.
        if !is_perm(&self.perm) || !is_perm(&self.q_ident) || !is_perm(&self.q_swap) {
            return Err("reconverge: not a bijection".into());
        }
        for j in 0..self.w {
            if self.perm[self.w - 1 - self.q_ident[j]] != self.w - 1 - j {
                return Err("reconverge: round-trip is not the identity".into());
            }
        }
        for j in 0..self.w {
            let target = self.w - 1 - j;
            let expect = match target {
                x if x == self.swap.0 => self.swap.1,
                x if x == self.swap.1 => self.swap.0,
                _ => target,
            };
            if self.perm[self.w - 1 - self.q_swap[j]] != expect {
                return Err("reconverge: swap composition mismatch".into());
            }
        }
        // Witness: sigma(witness) == witness where sigma swaps the two bits.
        let x = self.witness_bv;
        if x.count_ones() > self.w as u32 {
            return Err("reconverge: witness wider than bitvec".into());
        }
        let masked = if self.w == 64 {
            x
        } else {
            x & ((1u64 << self.w) - 1)
        };
        let a = (masked >> self.swap.0) & 1;
        let b = (masked >> self.swap.1) & 1;
        if a != b {
            return Err("reconverge: witness bits not equal".into());
        }
        Ok(())
    }
}

fn is_perm(p: &[usize]) -> bool {
    let mut seen = vec![false; p.len()];
    for &v in p {
        if v >= p.len() || seen[v] {
            return false;
        }
        seen[v] = true;
    }
    true
}

pub fn build(seed: u64, p: &Params) -> Result<Data, String> {
    if p.inputs < 2 || p.inputs > 6 {
        return Err("reconverge: inputs must be in 2..=6".into());
    }
    if !matches!(p.width, 8 | 16 | 32 | 64) {
        return Err("reconverge: width must be 8/16/32/64".into());
    }
    let mut rng = Rng::new(seed ^ 0x0B5E_0B5E);
    let k = p.inputs;
    let n = 1usize << k;
    let mut table: Vec<bool> = (0..n).map(|_| rng.chance(1, 2)).collect();
    if table.iter().all(|&b| b) {
        table[0] = false;
    }
    if table.iter().all(|&b| !b) {
        table[0] = true;
    }
    let flip = rng.index(n);
    let mut table2 = table.clone();
    table2[flip] = !table2[flip];

    let w = p.width;
    let mut perm: Vec<usize> = (0..w).collect();
    rng.shuffle(&mut perm);
    let mut pinv = vec![0usize; w];
    for (i, &v) in perm.iter().enumerate() {
        pinv[v] = i;
    }
    // Concat slot i holds output bit w-1-i and extracts input bit perm[i]
    // directly, so the realized bit map is pi(b) = perm[w-1-b]. Composing
    // the Q-net after the P-net realizes Q . rev . P . rev on bit numbers;
    // that is the identity iff Q = rev . pinv . rev, i.e.
    // q_ident[j] = w-1-pinv[w-1-j].
    let q_ident: Vec<usize> = (0..w).map(|j| w - 1 - pinv[w - 1 - j]).collect();
    let swap = (rng.index(w), (rng.index(w) + 1 + rng.index(w - 1)) % w);
    let sigma = |i: usize| -> usize {
        if i == swap.0 {
            swap.1
        } else if i == swap.1 {
            swap.0
        } else {
            i
        }
    };
    // sigma composed with the same reversal conjugation: the emitted
    // composition realizes P[w-1-Q[j]] on bit numbers, and we want that to
    // be sigma(w-1-j), so q_swap[j] = w-1-pinv[sigma(w-1-j)].
    let q_swap: Vec<usize> = (0..w).map(|j| w - 1 - pinv[sigma(w - 1 - j)]).collect();
    let mut witness_bv = rng.next_u64();
    if w < 64 {
        witness_bv &= (1u64 << w) - 1;
    }
    let bit0 = (witness_bv >> swap.0) & 1;
    witness_bv = (witness_bv & !(1u64 << swap.1)) | (bit0 << swap.1);

    let d = Data {
        k,
        anf: mobius(&table),
        anf2: mobius(&table2),
        table,
        table2,
        flip,
        w,
        perm,
        q_ident,
        q_swap,
        swap,
        witness_bv,
    };
    d.verify()?;
    Ok(d)
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

fn shannon(vars: &[String], table: &[bool], bit: usize, base: usize) -> String {
    if bit == vars.len() {
        return if table[base] {
            "true".into()
        } else {
            "false".to_string()
        };
    }
    let hi = shannon(vars, table, bit + 1, base | (1 << bit));
    let lo = shannon(vars, table, bit + 1, base);
    format!("(ite {} {hi} {lo})", vars[bit])
}

fn anf_expr(anf: &[bool], vars: &[String]) -> String {
    let k = vars.len();
    let mut monomials: Vec<String> = Vec::new();
    for mask in 0..(1usize << k) {
        if !anf[mask] {
            continue;
        }
        if mask == 0 {
            monomials.push("true".into());
        } else {
            let bits: Vec<String> = (0..k)
                .filter(|b| mask & (1 << b) != 0)
                .map(|b| vars[b].clone())
                .collect();
            monomials.push(format!("(and {})", bits.join(" ")));
        }
    }
    fold_binary("xor", &monomials, "false")
}

/// Nested concat of single-bit extracts implementing permutation `p`
/// (output bit i = input bit p[i]) over the expression `x`.
fn perm_net(p: &[usize], x: &str) -> String {
    let pieces: Vec<String> = p
        .iter()
        .map(|&b| format!("((_ extract {b} {b}) {x})"))
        .collect();
    let mut acc = match pieces.last() {
        None => return x.to_string(),
        Some(l) => l.clone(),
    };
    for piece in pieces[..pieces.len() - 1].iter().rev() {
        acc = format!("(concat {piece} {acc})");
    }
    acc
}

pub fn generate(seed: u64, p: &Params, suffix: &str) -> Result<Vec<Instance>, String> {
    let d = build(seed, p)?;
    let vars: Vec<String> = (0..d.k).map(|b| format!("b{b}")).collect();
    let mut out = Vec::new();

    // Boolean UNSAT: same table, two structures.
    let a = shannon(&vars, &d.table, 0, 0);
    let b = anf_expr(&d.anf, &vars);
    let mut script = ";; reconverge bool unsat (Shannon vs ANF)\n(set-logic QF_UF)\n".to_string();
    for v in &vars {
        let _ = writeln!(script, "(declare-const {v} Bool)");
    }
    let _ = writeln!(script, "(assert (not (= {a} {b})))");
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "reconverge",
        name: format!("reconverge-bool-unsat-s{seed}-{suffix}"),
        logic: "QF_UF".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Unsat],
        witness: None,
        certificate: format!(
            "Both expressions compute the same 2^{}-entry truth table (Shannon ite tree vs algebraic normal form); equivalence brute-force verified over all inputs in the generator.",
            d.k
        ),
        tags: vec!["reconverge", "bool", "equivalence"],
    });

    // Boolean needle SAT: tables differ exactly at `flip`.
    let b2 = anf_expr(&d.anf2, &vars);
    let mut script =
        ";; reconverge bool sat (needle: single differing input)\n(set-logic QF_UF)\n".to_string();
    for v in &vars {
        let _ = writeln!(script, "(declare-const {v} Bool)");
    }
    let _ = writeln!(script, "(assert (not (= {a} {b2})))");
    script.push_str("(check-sat)\n");
    let wbits: Vec<String> = (0..d.k)
        .map(|b| format!("b{b}={}", (d.flip >> b) & 1 == 1))
        .collect();
    out.push(Instance {
        family: "reconverge",
        name: format!("reconverge-bool-sat-s{seed}-{suffix}"),
        logic: "QF_UF".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Sat],
        witness: Some(format!("unique satisfying input: {}", wbits.join(", "))),
        certificate: format!(
            "The two truth tables differ at exactly one input (index {}), so the disequality is satisfiable precisely there.",
            d.flip
        ),
        tags: vec!["reconverge", "bool", "needle"],
    });

    // BV UNSAT: permutation round-trip asserted != identity.
    let net_p = perm_net(&d.perm, "x");
    let net_q = perm_net(&d.q_ident, "t");
    let mut script =
        ";; reconverge bv unsat (perm round-trip = identity)\n(set-logic QF_BV)\n".to_string();
    let _ = writeln!(script, "(declare-const x (_ BitVec {}))", d.w);
    // `let` is a term construct, not a command: it must live inside the
    // assert (a top-level let is invalid SMT2 and z3 rejects it).
    let _ = writeln!(
        script,
        "(assert (let ((t {net_p})) (let ((u {net_q})) (not (= u x)))))"
    );
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "reconverge",
        name: format!("reconverge-bv-unsat-s{seed}-{suffix}"),
        logic: "QF_BV".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Unsat],
        witness: None,
        certificate: format!(
            "Extract/concat networks for a random {}-bit permutation and its exact inverse applied in sequence compose to the identity (verified by composition in the generator), so u = x always.",
            d.w
        ),
        tags: vec!["reconverge", "bv", "extract-concat", "equivalence"],
    });

    // BV SAT near-miss: composition is a single transposition.
    let net_qs = perm_net(&d.q_swap, "t");
    let mut script =
        ";; reconverge bv sat (composition = single transposition)\n(set-logic QF_BV)\n"
            .to_string();
    let _ = writeln!(script, "(declare-const x (_ BitVec {}))", d.w);
    let _ = writeln!(
        script,
        "(assert (let ((t {net_p})) (let ((u {net_qs})) (not (= u x)))))"
    );
    script.push_str("(check-sat)\n");
    out.push(Instance {
        family: "reconverge",
        name: format!("reconverge-bv-sat-s{seed}-{suffix}"),
        logic: "QF_BV".into(),
        script,
        kind: InstanceKind::Smt2,
        expected: vec![Answer::Sat],
        witness: Some(format!("x = #x{:0width$x} (bits {} and {} equal)", d.witness_bv, d.swap.0, d.swap.1, width = d.w.div_ceil(4))),
        certificate: format!(
            "The composition swaps exactly bits {} and {}, so u = x iff those bits of x are equal; the exhibited witness satisfies this (verified in the generator).",
            d.swap.0, d.swap.1
        ),
        tags: vec!["reconverge", "bv", "extract-concat", "needle"],
    });
    Ok(out)
}
