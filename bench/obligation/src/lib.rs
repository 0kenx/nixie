//! `nixie-obligation` — certificate-carrying generator of hard-by-construction
//! SMT-LIB2 / DIMACS instances.
//!
//! A grammar fuzzer samples the *syntactic* space of a logic and mostly
//! produces formulas that simplify or solve trivially: disconnected
//! constraints, constant-foldable terms, contradictions already visible to
//! preprocessing. This crate instead generates *reasoning obligations*:
//! constraint networks whose difficulty is a mathematical property of the
//! construction, and each instance ships an independently checkable
//! certificate for its expected answer.
//!
//! The grammar is layered:
//!
//! * **Obligation productions** (what makes an instance hard):
//!   - `parity`: a graph-parity obstruction — every proper subset of the
//!     constraints is satisfiable, the contradiction needs all of them.
//!   - `capacity`: competition for insufficient resources (Hall deficit).
//!   - `gap`: an abstraction gap — rational-feasible, integer-infeasible
//!     linear systems with a modular infeasibility certificate.
//!   - `reconverge`: two provably equivalent computations with different
//!     structure (Shannon tree vs ANF; extract/concat bit-permutation
//!     round-trips) asserted to differ.
//!   - `memory`: alias-ambiguous array write histories (storecomm-shaped).
//!   - `boundary`: exact div/mod/rounding boundary distinctions.
//! * **Theory realizations**: each production is realized in Bool/CNF,
//!   LIA, BV, arrays or UF — and, for parity, mixed within one instance so
//!   the obstruction must be reconciled *across* theories.
//! * **Representation stress** (semantics-preserving): deep term chains,
//!   duplicated clauses, scaled constants.
//! * **Query histories**: push/pop scripts where every `check-sat` has its
//!   own derived expected answer.
//!
//! Every generated [`Instance`] carries `expected: Vec<Answer>` (one entry
//! per `check-sat`), a human-readable certificate, and — for satisfiable
//! instances — a witness. `obligation-run` checks a solver against the
//! certificate and cross-checks the *generator itself* with Z3 (and
//! CaDiCaL for CNF), so a generator bug is reported separately from a
//! solver bug.

// Dense constructions (incidence matrices, GF(2) elimination rows, ANF
// masks) are index-driven on purpose: rewriting them as iterator chains
// would obscure the correspondence with the mathematical construction.
#![allow(clippy::needless_range_loop)]

pub mod boundary;
pub mod capacity;
pub mod gap;
pub mod memory;
pub mod parity;
pub mod reconverge;
pub mod registry;
pub mod stress;

use std::fmt;

/// Expected result of one `check-sat`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Answer {
    Sat,
    Unsat,
    Unknown,
}

impl Answer {
    pub fn name(self) -> &'static str {
        match self {
            Answer::Sat => "sat",
            Answer::Unsat => "unsat",
            Answer::Unknown => "unknown",
        }
    }

    /// Parse one line of solver output. Understands both SMT-LIB style
    /// (`sat`/`unsat`) and SAT-competition style (`s SATISFIABLE`, ...).
    pub fn parse_line(line: &str) -> Option<Answer> {
        match line.trim() {
            "sat" | "s SATISFIABLE" => Some(Answer::Sat),
            "unsat" | "s UNSATISFIABLE" => Some(Answer::Unsat),
            "unknown" | "s UNKNOWN" | "s INDETERMINATE" => Some(Answer::Unknown),
            _ => None,
        }
    }
}

impl fmt::Display for Answer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Physical encoding of an instance.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InstanceKind {
    Smt2,
    Cnf,
}

/// One generated problem.
#[derive(Clone, Debug)]
pub struct Instance {
    pub family: &'static str,
    /// Deterministic, filesystem-safe: `family-variant-s<seed>-<suffix>`.
    pub name: String,
    /// SMT-LIB logic name (SMT2 instances only; empty = omit set-logic).
    pub logic: String,
    /// Full script text (SMT2 or DIMACS).
    pub script: String,
    pub kind: InstanceKind,
    /// Expected answer per `check-sat`, in order.
    pub expected: Vec<Answer>,
    /// Assignment exhibiting satisfiability (SAT instances only).
    pub witness: Option<String>,
    /// Why the expected answer is known, in generator-verifiable terms.
    pub certificate: String,
    pub tags: Vec<&'static str>,
}

impl Instance {
    pub fn extension(&self) -> &'static str {
        match self.kind {
            InstanceKind::Smt2 => "smt2",
            InstanceKind::Cnf => "cnf",
        }
    }

    fn kind_name(&self) -> &'static str {
        match self.kind {
            InstanceKind::Smt2 => "smt2",
            InstanceKind::Cnf => "cnf",
        }
    }

    /// Machine-readable sidecar for the runner / artifact triage.
    pub fn meta_json(&self) -> String {
        let mut s = String::new();
        s.push_str("{\n");
        s.push_str(&format!("  \"family\": \"{}\",\n", json_str(self.family)));
        s.push_str(&format!("  \"name\": \"{}\",\n", json_str(&self.name)));
        s.push_str(&format!("  \"kind\": \"{}\",\n", self.kind_name()));
        if !self.logic.is_empty() {
            s.push_str(&format!("  \"logic\": \"{}\",\n", json_str(&self.logic)));
        }
        s.push_str(&format!(
            "  \"expected\": [{}],\n",
            self.expected
                .iter()
                .map(|a| format!("\"{}\"", a.name()))
                .collect::<Vec<_>>()
                .join(", ")
        ));
        s.push_str(&format!(
            "  \"tags\": [{}],\n",
            self.tags
                .iter()
                .map(|t| format!("\"{}\"", json_str(t)))
                .collect::<Vec<_>>()
                .join(", ")
        ));
        s.push_str(&format!(
            "  \"certificate\": \"{}\",\n",
            json_str(&self.certificate)
        ));
        match &self.witness {
            Some(w) => s.push_str(&format!("  \"witness\": \"{}\"\n", json_str(w))),
            None => s.push_str("  \"witness\": null\n"),
        }
        s.push_str("}\n");
        s
    }
}

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// Deterministic PRNG (SplitMix64) — same construction as
/// `bench/z3_parity`'s generator. Dependency-free on purpose so a seed
/// always reproduces the same corpus.
#[derive(Debug, Clone)]
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng {
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
        }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform `i64` in `[lo, hi_inclusive]`.
    pub fn range_i64(&mut self, lo: i64, hi_inclusive: i64) -> i64 {
        assert!(hi_inclusive >= lo, "Rng::range_i64: empty range");
        let span = (hi_inclusive - lo) as u64 + 1;
        lo + (self.next_u64() % span) as i64
    }

    /// Uniform `usize` in `[lo, hi_inclusive]`.
    pub fn range_usize(&mut self, lo: usize, hi_inclusive: usize) -> usize {
        assert!(hi_inclusive >= lo, "Rng::range_usize: empty range");
        self.range_i64(lo as i64, hi_inclusive as i64) as usize
    }

    /// Uniform index into `[0, len)`.
    pub fn index(&mut self, len: usize) -> usize {
        assert!(len > 0, "Rng::index: empty");
        (self.next_u64() % len as u64) as usize
    }

    /// True with probability `numerator / denominator`.
    pub fn chance(&mut self, numerator: u64, denominator: u64) -> bool {
        self.next_u64() % denominator < numerator
    }

    pub fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            let j = self.index(i + 1);
            v.swap(i, j);
        }
    }
}

/// SMT-LIB Euclidean remainder: result in `[0, b)` for `b > 0`.
pub fn smt_mod(a: i64, b: i64) -> i64 {
    assert!(b > 0);
    a.rem_euclid(b)
}

/// SMT-LIB Euclidean quotient for `b > 0` (floor division).
pub fn smt_div(a: i64, b: i64) -> i64 {
    assert!(b > 0);
    a.div_euclid(b)
}

/// Binary fold of an associative operator, e.g. xor. `terms` must be
/// non-empty for a meaningful result; an empty slice folds to `unit`.
pub fn fold_binary(op: &str, terms: &[String], unit: &str) -> String {
    match terms.split_first() {
        None => unit.to_string(),
        Some((first, rest)) => rest
            .iter()
            .fold(first.clone(), |acc, t| format!("({op} {acc} {t})")),
    }
}
