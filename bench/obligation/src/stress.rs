//! Representation stress (semantics-preserving wrappers).
//!
//! These do not change the answer of the instance they are applied to —
//! they add *tautologies over fresh variables* or duplicate clauses — but
//! they stress parsing, simplification, hash-consing and stack discipline:
//! deep nesting over user-controlled terms is a known bug class for
//! recursive walkers (see AGENTS.md: "Deep input must not overflow the
//! stack").

use crate::Rng;
use std::fmt::Write as _;

pub struct StressCfg {
    /// Depth of the nested `not` chain (forced even for tautology).
    pub bool_depth: usize,
    /// Depth of the nested arithmetic constant chain.
    pub int_depth: usize,
    /// Clause duplication factor for DIMACS instances.
    pub cnf_dup: usize,
}

impl StressCfg {
    pub fn mild() -> Self {
        StressCfg {
            bool_depth: 500,
            int_depth: 500,
            cnf_dup: 2,
        }
    }

    pub fn heavy() -> Self {
        StressCfg {
            bool_depth: 5000,
            int_depth: 5000,
            cnf_dup: 3,
        }
    }
}

/// Which arithmetic chain a logic admits. Bool is in every SMT-LIB logic;
/// Int/Real only in the arithmetic ones; BV gets its own xor chain.
fn chain_kind(logic: &str) -> &'static str {
    let l = logic.to_ascii_uppercase();
    if l.contains("BV") {
        "bv"
    } else if l.contains("LRA") || l.contains("NRA") || l == "RDL" {
        "real"
    } else if l.contains("IA") || l.is_empty() || l == "ALL" {
        "int"
    } else {
        "none"
    }
}

/// Insert a self-contained stress block immediately before the first
/// `(check-sat)` of an SMT2 script. Every added assertion is a tautology
/// over fresh variables, so sat/unsat is preserved exactly:
///  * `sdb`: `(not^d sdb) = sdb` with d even — a d-deep term the solver
///    must walk without native recursion blowing the stack.
///  * `sdi`/`sdv`: a d-deep constant chain equal to its exact value —
///    deep arithmetic with a only-if-fully-evaluated result. Int chains
///    are only emitted for arithmetic logics, BV xor chains for BV.
pub fn apply_smt2(script: &str, cfg: &StressCfg, rng: &mut Rng, logic: &str) -> String {
    let mut block = String::new();
    block.push_str(";; --- rep-stress: deep tautologies over fresh variables ---\n");
    let d = cfg.bool_depth.max(2) & !1; // even
    let _ = writeln!(block, "(declare-const sdb Bool)");
    let mut chain = String::from("sdb");
    for _ in 0..d {
        chain = format!("(not {chain})");
    }
    let _ = writeln!(block, "(assert (= {chain} sdb))");

    match chain_kind(logic) {
        "int" => {
            let _ = writeln!(block, "(declare-const sdi Int)");
            // fallthrough to shared constant-chain builder below
            let mut consts: Vec<i64> = Vec::with_capacity(cfg.int_depth);
            let mut sum: i128 = 0;
            for i in 0..cfg.int_depth {
                let c = if i % 97 == 0 {
                    rng.range_i64(-1_000_000, 1_000_000)
                } else {
                    rng.range_i64(-9, 9)
                };
                sum += c as i128;
                consts.push(c);
            }
            let mut term = String::from("0");
            for &c in consts.iter().rev() {
                if c < 0 {
                    term = format!("(+ (- {}) {term})", -c);
                } else {
                    term = format!("(+ {c} {term})");
                }
            }
            let _ = writeln!(block, "(assert (= sdi {term}))");
            let _ = writeln!(block, "(assert (= sdi {sum}))");
        }
        "real" => {
            let _ = writeln!(block, "(declare-const sdr Real)");
            let mut consts: Vec<i64> = Vec::with_capacity(cfg.int_depth);
            let mut sum: i128 = 0;
            for i in 0..cfg.int_depth {
                let c = if i % 97 == 0 {
                    rng.range_i64(-1_000_000, 1_000_000)
                } else {
                    rng.range_i64(-9, 9)
                };
                sum += c as i128;
                consts.push(c);
            }
            let mut term = String::from("0.0");
            for &c in consts.iter().rev() {
                let lit = if c < 0 {
                    format!("(- {}.0)", -c)
                } else {
                    format!("{c}.0")
                };
                term = format!("(+ {lit} {term})");
            }
            let sum_lit = if sum < 0 {
                format!("(- {}.0)", -sum)
            } else {
                format!("{sum}.0")
            };
            let _ = writeln!(block, "(assert (= sdr {term}))");
            let _ = writeln!(block, "(assert (= sdr {sum_lit}))");
        }
        "bv" => {
            let _ = writeln!(block, "(declare-const sdv (_ BitVec 32))");
            // bvxor chain whose constants XOR to 0 -> chain = sdv.
            let mut xored: u32 = 0;
            let mut consts: Vec<u32> = Vec::with_capacity(cfg.int_depth);
            for _ in 0..cfg.int_depth {
                let c = rng.next_u64() as u32;
                xored ^= c;
                consts.push(c);
            }
            consts[0] ^= xored; // neutralize the total
            let mut term = String::from("sdv");
            for &c in consts.iter().rev() {
                term = format!("(bvxor {term} (_ bv{c} 32))");
            }
            let _ = writeln!(block, "(assert (= {term} sdv))");
        }
        _ => {}
    }

    match script.find("(check-sat)") {
        Some(idx) => {
            let mut out = String::with_capacity(script.len() + block.len());
            out.push_str(&script[..idx]);
            out.push_str(&block);
            out.push_str(&script[idx..]);
            out
        }
        None => {
            let mut out = String::from(script);
            out.push_str(&block);
            out
        }
    }
}

/// Duplicate every clause of a DIMACS script `dup` times (duplicated
/// clauses never change satisfiability) and fix the header count.
pub fn apply_cnf(script: &str, dup: usize) -> String {
    if dup <= 1 {
        return script.to_string();
    }
    let mut out = String::new();
    let mut n_clauses = 0usize;
    for line in script.lines() {
        let t = line.trim();
        if t.starts_with('c') || t.is_empty() || t.starts_with("p cnf") {
            out.push_str(line);
            out.push('\n');
            continue;
        }
        if t.ends_with('0') {
            for _ in 0..dup {
                out.push_str(line);
                out.push('\n');
                n_clauses += 1;
            }
            continue;
        }
        // Clause spanning a missing trailing newline etc. — copy verbatim.
        out.push_str(line);
        out.push('\n');
    }
    // Patch the header count.
    if let Some(pos) = out.find("p cnf ")
        && let Some(nl) = out[pos..].find('\n')
    {
        let header = out[pos..pos + nl].to_string();
        let parts: Vec<&str> = header.split_whitespace().collect();
        if parts.len() == 4 {
            let patched = format!("p cnf {} {}", parts[2], n_clauses);
            out.replace_range(pos..pos + nl, &patched);
        }
    }
    out
}
