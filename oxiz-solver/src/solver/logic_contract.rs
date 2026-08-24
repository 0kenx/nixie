//! Logic contract: an exact registry of SMT-LIB logics and the
//! capability language used to validate asserted formulas against their
//! declared header and to route engines structurally.
//!
//! Priority-0 layer (`docs/2026-08-established-research-candidates.md`):
//! a declared logic is a **contract over the permitted input language**,
//! not a routing hint. Three concerns stay separate:
//!
//! * `DeclaredLogic` — what the header says (known spec, `ALL`, missing,
//!   or an unsupported name);
//! * `Capabilities` — what the asserted formula actually requires,
//!   collected structurally from the parsed DAG;
//! * engine routing — derived from `Capabilities`, refined (never
//!   widened) by the declared spec.
//!
//! The registry entries follow the SMT-LIB 2.7 logic catalog
//! (<https://smt-lib.org/logics-all.shtml>). Semantics are decoded from
//! the entry TABLE, never from substrings of names — the acceptance tests
//! pin exactly the failure modes substring decoding produces (an invented
//! name containing "NIA" must not install the nonlinear backend).

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::sort::{SortId, SortKind};

/// One logic specification: which theories, quantifiers and arithmetic
/// fragments the contract permits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LogicSpec {
    /// Uninterpreted functions and free sorts beyond the built-ins.
    pub uf: bool,
    /// Arithmetic is present at all (else the entry forbids arith atoms).
    pub arith: bool,
    /// Nonlinear multiplication permitted.
    pub nonlinear: bool,
    /// Integer (vs real) arithmetic. `false` + `arith` = real-only.
    pub integer: bool,
    /// Difference-logic shape only (every atom a difference of two vars).
    pub diff: bool,
    /// Arrays.
    pub arrays: bool,
    /// Bit-vectors.
    pub bv: bool,
    /// Floating point.
    pub fp: bool,
    /// Strings / sequences.
    pub strings: bool,
    /// Datatypes.
    pub datatypes: bool,
    /// Quantifiers permitted.
    pub quantifiers: bool,
}

impl LogicSpec {
    /// All-false spec (the table's base).
    const NONE: Self = Self {
        uf: false,
        arith: false,
        nonlinear: false,
        integer: false,
        diff: false,
        arrays: false,
        bv: false,
        fp: false,
        strings: false,
        datatypes: false,
        quantifiers: false,
    };

    const fn linear_arith(integer: bool, diff: bool) -> Self {
        Self {
            arith: true,
            integer,
            diff,
            ..Self::NONE
        }
    }
}

/// The supported logics. `QF_ANIA` (an OxiZ/competition extension: arrays
/// of integer-sorted indices over nonlinear integer arithmetic) carries
/// its own entry; its semantics never decode from its name.
const REGISTRY: &[(&str, LogicSpec)] = &[
    // --- Uninterpreted functions ---
    (
        "QF_UF",
        LogicSpec {
            uf: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UF",
        LogicSpec {
            uf: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    // --- Arithmetic (quantifier-free) ---
    ("QF_LIA", LogicSpec::linear_arith(true, false)),
    ("QF_LRA", LogicSpec::linear_arith(false, false)),
    (
        "QF_NIA",
        LogicSpec {
            arith: true,
            integer: true,
            nonlinear: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_NRA",
        LogicSpec {
            arith: true,
            nonlinear: true,
            ..LogicSpec::NONE
        },
    ),
    ("QF_IDL", LogicSpec::linear_arith(true, true)),
    ("QF_RDL", LogicSpec::linear_arith(false, true)),
    (
        "QF_NIRA",
        LogicSpec {
            arith: true,
            integer: true,
            nonlinear: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "LIA",
        LogicSpec {
            arith: true,
            integer: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "LRA",
        LogicSpec {
            arith: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "NIA",
        LogicSpec {
            arith: true,
            integer: true,
            nonlinear: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "NRA",
        LogicSpec {
            arith: true,
            nonlinear: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "NIRA",
        LogicSpec {
            arith: true,
            integer: true,
            nonlinear: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "IDL",
        LogicSpec {
            arith: true,
            integer: true,
            diff: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "RDL",
        LogicSpec {
            arith: true,
            diff: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    // --- Combinations ---
    (
        "QF_UFLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFLRA",
        LogicSpec {
            uf: true,
            arith: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFIDL",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            diff: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFNRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFLRA",
        LogicSpec {
            uf: true,
            arith: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            arrays: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_AUFLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ALIA",
        LogicSpec {
            arith: true,
            integer: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ALRA",
        LogicSpec {
            arith: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ANIA",
        LogicSpec {
            arith: true,
            integer: true,
            nonlinear: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ALNIA",
        LogicSpec {
            arith: true,
            integer: true,
            nonlinear: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ALNRA",
        LogicSpec {
            arith: true,
            nonlinear: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_AUFNIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            nonlinear: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_AUFNRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFLIRA",
        LogicSpec {
            uf: true,
            arith: true,
            arrays: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFNIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            nonlinear: true,
            arrays: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            arrays: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ABV",
        LogicSpec {
            arrays: true,
            bv: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_AUFBV",
        LogicSpec {
            uf: true,
            arrays: true,
            bv: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ABVFP",
        LogicSpec {
            arrays: true,
            bv: true,
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_AUFBVFP",
        LogicSpec {
            uf: true,
            arrays: true,
            bv: true,
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    // --- Bit-vectors ---
    (
        "QF_BV",
        LogicSpec {
            bv: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "BV",
        LogicSpec {
            bv: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFBV",
        LogicSpec {
            uf: true,
            bv: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFBVFP",
        LogicSpec {
            uf: true,
            bv: true,
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    // --- Arrays ---
    (
        "QF_AX",
        LogicSpec {
            arrays: true,
            ..LogicSpec::NONE
        },
    ),
    // --- Floating point ---
    (
        "QF_FP",
        LogicSpec {
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "FP",
        LogicSpec {
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_FPBV",
        LogicSpec {
            fp: true,
            bv: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_BVFP",
        LogicSpec {
            bv: true,
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_FPLRA",
        LogicSpec {
            fp: true,
            arith: true,
            ..LogicSpec::NONE
        },
    ),
    // --- Strings ---
    (
        "QF_S",
        LogicSpec {
            strings: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_SLIA",
        LogicSpec {
            strings: true,
            arith: true,
            integer: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "S",
        LogicSpec {
            strings: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    // --- Datatypes ---
    (
        "QF_UFDT",
        LogicSpec {
            uf: true,
            datatypes: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_DT",
        LogicSpec {
            datatypes: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFDTLIA",
        LogicSpec {
            uf: true,
            datatypes: true,
            arith: true,
            integer: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFDTLIRA",
        LogicSpec {
            uf: true,
            datatypes: true,
            arith: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFNIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            nonlinear: true,
            ..LogicSpec::NONE
        },
    ),
    // --- SMT-LIB catalog completion (2026-08-24) ---
    // The 43 benchmark-catalog logics the table above was missing, decoded
    // with the cvc5 grammar (`src/theory/logic_info.cpp`): a leading `QF_`
    // drops quantifiers; `A`=arrays, `UF`, `BV`, `FP`, `DT`, `S`; one
    // arithmetic suffix sets linear/nonlinear, integer/real/diff.  Mixed
    // Int+Real shapes (`LIRA`/`NIRA`) follow the table's shipped convention
    // (`AUFLIRA`, `AUFNIRA`, `QF_UFDTLIRA`): `integer: false` — provenance
    // is deliberately unenforced in `validate`, the flag only routes the
    // linear fallback.  The completeness test pins the full 89-name catalog.
    (
        "ABV",
        LogicSpec {
            arrays: true,
            bv: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "ABVFP",
        LogicSpec {
            arrays: true,
            bv: true,
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "ABVFPLRA",
        LogicSpec {
            arith: true,
            arrays: true,
            bv: true,
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "ALIA",
        LogicSpec {
            arith: true,
            integer: true,
            arrays: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "ANIA",
        LogicSpec {
            arith: true,
            nonlinear: true,
            integer: true,
            arrays: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFBV",
        LogicSpec {
            uf: true,
            arrays: true,
            bv: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFBVDTLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            arrays: true,
            bv: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFBVDTNIA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            integer: true,
            arrays: true,
            bv: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFBVDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            arrays: true,
            bv: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFBVFP",
        LogicSpec {
            uf: true,
            arrays: true,
            bv: true,
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFBVFPDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            arrays: true,
            bv: true,
            fp: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFDTLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            arrays: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFDTLIRA",
        LogicSpec {
            uf: true,
            arith: true,
            arrays: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            arrays: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "AUFFPDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            arrays: true,
            fp: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "BVFP",
        LogicSpec {
            bv: true,
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "BVFPLRA",
        LogicSpec {
            arith: true,
            bv: true,
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "FPLRA",
        LogicSpec {
            arith: true,
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_ABVFPLRA",
        LogicSpec {
            arith: true,
            arrays: true,
            bv: true,
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_BVFPLRA",
        LogicSpec {
            arith: true,
            bv: true,
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_LIRA",
        LogicSpec {
            arith: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_SNIA",
        LogicSpec {
            arith: true,
            nonlinear: true,
            integer: true,
            strings: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFBVDT",
        LogicSpec {
            uf: true,
            bv: true,
            datatypes: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFDTNIA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            integer: true,
            datatypes: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFFP",
        LogicSpec {
            uf: true,
            fp: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "QF_UFFPDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            fp: true,
            datatypes: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBV",
        LogicSpec {
            uf: true,
            bv: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBVDT",
        LogicSpec {
            uf: true,
            bv: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBVDTLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            bv: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBVDTNIA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            integer: true,
            bv: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBVDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            bv: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBVFP",
        LogicSpec {
            uf: true,
            bv: true,
            fp: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBVFPDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            bv: true,
            fp: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFBVLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            bv: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFDT",
        LogicSpec {
            uf: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFDTLIA",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFDTLIRA",
        LogicSpec {
            uf: true,
            arith: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFDTNIA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            integer: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFFPDTNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            fp: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFIDL",
        LogicSpec {
            uf: true,
            arith: true,
            integer: true,
            diff: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFNIA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            integer: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "UFNIRA",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
    (
        "ALL",
        LogicSpec {
            uf: true,
            arith: true,
            nonlinear: true,
            integer: true,
            arrays: true,
            bv: true,
            fp: true,
            strings: true,
            datatypes: true,
            quantifiers: true,
            ..LogicSpec::NONE
        },
    ),
];

/// Look up a declared logic name. `Ok(None)` = `ALL` (permissive);
/// `Err(())` = unsupported name (the caller must not partially
/// reconfigure the solver for it).
pub fn lookup(name: &str) -> Result<Option<&'static LogicSpec>, ()> {
    if name == "ALL" {
        return Ok(None);
    }
    for (n, spec) in REGISTRY {
        if *n == name {
            return Ok(Some(spec));
        }
    }
    Err(())
}

/// What the asserted formula actually requires, collected structurally.
/// Field semantics are REQUIREMENTS: a formula that contains a
/// multiplication of two non-constant arith terms sets `nonlinear`,
/// whatever the header claims.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Capabilities {
    pub quantifiers: bool,
    pub uf: bool,
    pub arith: bool,
    pub nonlinear: bool,
    pub integer_terms: bool,
    pub real_terms: bool,
    pub arrays: bool,
    pub bv: bool,
    pub fp: bool,
    pub strings: bool,
    pub datatypes: bool,
}

impl Capabilities {
    /// Collect requirements from one assertion DAG (explicit heap stack;
    /// terms are hash-consed so `visited` prunes the shared subterms).
    /// `None` = a term the walk could not classify — the caller must
    /// treat the formula as unvalidated rather than guess.
    pub fn collect(assertion: TermId, manager: &TermManager) -> Option<Self> {
        let mut caps = Self::default();
        let mut visited: std::collections::HashSet<TermId> = std::collections::HashSet::new();
        let mut stack: Vec<TermId> = vec![assertion];
        let int_sort = manager.sorts.int_sort;
        let real_sort = manager.sorts.real_sort;
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let data = manager.get(t)?;
            match &data.kind {
                TermKind::Var(_) => {
                    // Int/Real sorts alone are decoration (a UF argument in
                    // a logic without arithmetic); the arith capability is
                    // set by OPERATIONS and comparisons.  THEORY-sorted
                    // variables are definitional uses of that theory: a
                    // String variable is strings capability.
                    if data.sort == int_sort {
                        caps.integer_terms = true;
                    } else if data.sort == real_sort {
                        caps.real_terms = true;
                    } else if let Some(fam) = sort_family(data.sort, manager) {
                        match fam {
                            SortFamily::Array => caps.arrays = true,
                            SortFamily::Bv => caps.bv = true,
                            SortFamily::Fp => caps.fp = true,
                            SortFamily::String => caps.strings = true,
                            SortFamily::Datatype => caps.datatypes = true,
                            SortFamily::Other => {}
                        }
                    }
                }
                TermKind::Apply { func: _, args } => {
                    // Sort-driven classification (structural, no name
                    // matching): classify by the RESULT-SORT family first.
                    // `((as const (Array Int Int)) v)` is an Apply with an
                    // Array result — an array constructor, not UF (the
                    // first version of this arm sent every non-bool/non-
                    // arith apply to `uf` and rejected valid QF_ANIA).
                    // Under-detection in exotic corners (a genuine UF
                    // function with an array result under an array logic
                    // without UF) fails SAFE: no false rejection.
                    let fam = sort_family(data.sort, manager);
                    match fam {
                        Some(SortFamily::Array) => caps.arrays = true,
                        Some(SortFamily::Bv) => caps.bv = true,
                        Some(SortFamily::Fp) => caps.fp = true,
                        Some(SortFamily::String) => caps.strings = true,
                        Some(SortFamily::Datatype) => caps.datatypes = true,
                        // This AST represents many BUILTINS as generic
                        // Apply (`str.len`, `str.indexof`, …, and declared
                        // functions) — sort shape alone cannot separate
                        // them.  The DEFINITIONAL UF signal is an
                        // uninterpreted RESULT sort; Int/Bool-result
                        // applications (builtins, `h: Bool -> Int` UF
                        // decoration) pass unflagged.  Under-detection
                        // fails safe: it declines to reject, never
                        // rejects a valid file.
                        Some(SortFamily::Other) | None
                            if matches!(
                                manager.sorts.get(data.sort).map(|sd| &sd.kind),
                                Some(SortKind::Uninterpreted(_))
                            ) =>
                        {
                            caps.uf = true;
                        }
                        _ => {}
                    }
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermKind::Not(a) | TermKind::Implies(a, _) => {
                    stack.push(*a);
                }
                TermKind::And(args) | TermKind::Or(args) => {
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermKind::Xor(a, b) | TermKind::Eq(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Distinct(args) => {
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermKind::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermKind::Add(args) | TermKind::Mul(args) => {
                    caps.arith = true;
                    if data.sort == int_sort {
                        caps.integer_terms = true;
                    }
                    if data.sort == real_sort {
                        caps.real_terms = true;
                    }
                    // Nonlinear iff a Mul multiplies two operands that
                    // are not CONCRETE COEFFICIENTS.  SMT-LIB's QF_LIA
                    // permits "multiplication only by concrete
                    // coefficients" — a coefficient is a numeric literal,
                    // possibly negated (`(- 1)` is NOT folded by the
                    // parser; treating `Neg(IntConst)` as nonconstant
                    // misclassified every Dillig-family LIA benchmark as
                    // nonlinear).
                    if let TermKind::Mul(ops) = &data.kind {
                        let nonconst = ops
                            .iter()
                            .filter(|&&op| {
                                manager
                                    .get(op)
                                    .is_some_and(|od| !is_concrete_coefficient(&od.kind, manager))
                            })
                            .count();
                        if nonconst >= 2 {
                            caps.nonlinear = true;
                        }
                    }
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b) => {
                    // A comparison over STRINGS-DERIVED operands (e.g.
                    // `(>= (str.len s) 6)`) is strings capability — QF_S's
                    // signature includes the length function and its
                    // comparisons (z3 accepts them).  Only comparisons
                    // whose operands are genuinely arith terms set the
                    // arith capability.  One-level test: an operand that
                    // is an application with a String-sorted argument is
                    // strings-derived.
                    let string_derived = [a, b].iter().any(|&op| {
                        manager
                            .get(*op)
                            .is_some_and(|od| is_string_derived(&od.kind, od.sort, manager))
                    });
                    if string_derived {
                        caps.strings = true;
                    } else {
                        caps.arith = true;
                    }
                    for &a in [a, b] {
                        stack.push(a);
                        if let Some(ad) = manager.get(a)
                            && ad.sort == int_sort
                        {
                            caps.integer_terms = true;
                        } else if let Some(ad) = manager.get(a)
                            && ad.sort == real_sort
                        {
                            caps.real_terms = true;
                        }
                    }
                }
                TermKind::Sub(a, b) | TermKind::Div(a, b) | TermKind::Mod(a, b) => {
                    caps.arith = true;
                    if data.sort == int_sort {
                        caps.integer_terms = true;
                    }
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Neg(a) => {
                    // Negation of a literal (`(- 1)`) is a literal —
                    // string conversions compare against `-1` sentinels
                    // routinely; only negation of a non-constant term is
                    // an arithmetic operation.
                    if manager.get(*a).is_some_and(|ad| {
                        !matches!(ad.kind, TermKind::IntConst(_) | TermKind::RealConst(_))
                    }) {
                        caps.arith = true;
                    }
                    stack.push(*a);
                }
                TermKind::IntConst(_) | TermKind::RealConst(_) => {
                    if data.sort == int_sort {
                        caps.integer_terms = true;
                    } else if data.sort == real_sort {
                        caps.real_terms = true;
                    }
                }
                TermKind::Select(a, _) | TermKind::Store(a, _, _) => {
                    caps.arrays = true;
                    stack.push(*a);
                    // Index/value children flow through the generic walk
                    // below via their own kinds once popped; push them here.
                    if let TermKind::Store(_, i, v) = &data.kind {
                        stack.push(*i);
                        stack.push(*v);
                    } else if let TermKind::Select(_, i) = &data.kind {
                        stack.push(*i);
                    }
                }
                TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => {
                    caps.quantifiers = true;
                    stack.push(*body);
                }
                TermKind::True | TermKind::False | TermKind::BitVecConst { .. } => {}
                _ => {
                    // Unhandled kind (`str.len` and the other string/regex/
                    // BV/FP builtins with dedicated TermKinds): classify by
                    // sort FAMILY only.  An Int-RESULT sort must NOT set
                    // `arith` (str.len returns Int but is a strings
                    // builtin — the fallback's old arith-by-sort arm
                    // rejected every QF_S length constraint).  Arith
                    // capability comes exclusively from the explicit
                    // operation/comparison arms above.
                    if let Some(fam) = sort_family(data.sort, manager) {
                        match fam {
                            SortFamily::Array => caps.arrays = true,
                            SortFamily::Bv => caps.bv = true,
                            SortFamily::Fp => caps.fp = true,
                            SortFamily::String => caps.strings = true,
                            SortFamily::Datatype => caps.datatypes = true,
                            SortFamily::Other => {}
                        }
                    }
                    // Unhandled kinds contribute no child walk here —
                    // their operands are specific to each kind and adding
                    // them piecemeal risks misclassification; the sort
                    // classification above is the contract-relevant fact.
                }
            }
        }
        Some(caps)
    }
}

/// A numeric literal, possibly under negation — SMT-LIB's "concrete
/// coefficient" (`2`, `(- 1)`, `4.5`, `(- 0.5)`).  The parser keeps unary
/// minus as `Neg` over a literal, so both shapes are coefficients.
fn is_concrete_coefficient(kind: &TermKind, manager: &TermManager) -> bool {
    match kind {
        TermKind::IntConst(_) | TermKind::RealConst(_) => true,
        TermKind::Neg(inner) => manager
            .get(*inner)
            .is_some_and(|t| matches!(t.kind, TermKind::IntConst(_) | TermKind::RealConst(_))),
        _ => false,
    }
}

/// Whether a comparison operand is STRINGS-derived: a string-sorted term,
/// a string builtin application, or an application with a string-sorted
/// argument (`str.len`, `str.indexof`, …).  A comparison with any
/// string-derived operand is a strings-theory constraint (QF_S includes
/// the length function; z3 accepts `(>= (str.len s) 6)`), not arithmetic.
fn is_string_derived(kind: &TermKind, sort: SortId, manager: &TermManager) -> bool {
    if matches!(sort_family(sort, manager), Some(SortFamily::String)) {
        return true;
    }
    match kind {
        // Dedicated string-builtin kinds, including the Int-returning
        // ones (`StrLen`, `StrIndexOf`, `StrToCode`, `StrToInt`) that
        // make `(>= (str.len s) 6)` a strings constraint.
        TermKind::StrLen(_)
        | TermKind::StrToCode(_)
        | TermKind::StrToInt(_)
        | TermKind::StrFromCode(_)
        | TermKind::StrConcat(..)
        | TermKind::StrAt(..)
        | TermKind::StrSubstr { .. }
        | TermKind::StrContains(..)
        | TermKind::StrPrefixOf(..)
        | TermKind::StrSuffixOf(..)
        | TermKind::StrInRe(..)
        | TermKind::StrIndexOf(..)
        | TermKind::StrLe(..)
        | TermKind::StrLt(..)
        | TermKind::StrReplace { .. }
        | TermKind::StrReplaceAll { .. } => true,
        TermKind::Apply { args, .. } => args.iter().any(|&arg| {
            manager
                .get(arg)
                .is_some_and(|ad| matches!(sort_family(ad.sort, manager), Some(SortFamily::String)))
        }),
        _ => false,
    }
}

enum SortFamily {
    Array,
    Bv,
    Fp,
    String,
    Datatype,
    Other,
}

fn sort_family(s: SortId, manager: &TermManager) -> Option<SortFamily> {
    let sd = manager.sorts.get(s)?;
    Some(match sd.kind {
        SortKind::Array { .. } => SortFamily::Array,
        SortKind::BitVec(_) => SortFamily::Bv,
        SortKind::FloatingPoint { .. } => SortFamily::Fp,
        SortKind::String => SortFamily::String,
        SortKind::Uninterpreted(_) => SortFamily::Other,
        SortKind::Datatype(_) => SortFamily::Datatype,
        _ => SortFamily::Other,
    })
}

impl Capabilities {
    /// Union in place (accumulation across several assertions).
    pub fn union_with(&mut self, other: &Self) {
        self.quantifiers |= other.quantifiers;
        self.uf |= other.uf;
        self.arith |= other.arith;
        self.nonlinear |= other.nonlinear;
        self.integer_terms |= other.integer_terms;
        self.real_terms |= other.real_terms;
        self.arrays |= other.arrays;
        self.bv |= other.bv;
        self.fp |= other.fp;
        self.strings |= other.strings;
        self.datatypes |= other.datatypes;
    }
}

/// Validate collected capabilities against a declared spec. Returns the
/// first contract violation (a human message), or `None` when the body
/// conforms.
pub fn validate(spec: &LogicSpec, caps: &Capabilities) -> Option<String> {
    if caps.quantifiers && !spec.quantifiers {
        return Some("quantifiers not allowed in this logic".into());
    }
    if caps.uf && !spec.uf {
        return Some("uninterpreted functions not allowed in this logic".into());
    }
    if caps.arith && !spec.arith {
        return Some("arithmetic not allowed in this logic".into());
    }
    if caps.nonlinear && !spec.nonlinear {
        return Some("nonlinear arithmetic not allowed in this logic".into());
    }
    // NOTE: integer/real PROVENANCE is deliberately not enforced.  SMT-LIB
    // coerces Int literals to Real in mixed comparisons (`(< (+ x x) 1)`
    // under QF_NRA carries an Int-sorted `1`), and Int/Real sorts appear
    // as UF decoration in mixed scripts (`h: Bool -> Int` under QF_UF) —
    // both shapes are in-contract while setting the provenance flags, so
    // enforcing them rejects valid files.  The flags remain collected for
    // diagnostics.  The ENFORCED arithmetic distinctions are `arith`
    // (operations/comparisons) and `nonlinear` (coefficient test).
    if caps.arrays && !spec.arrays {
        return Some("arrays not allowed in this logic".into());
    }
    if caps.bv && !spec.bv {
        return Some("bit-vectors not allowed in this logic".into());
    }
    if caps.fp && !spec.fp {
        return Some("floating point not allowed in this logic".into());
    }
    if caps.strings && !spec.strings {
        return Some("strings not allowed in this logic".into());
    }
    if caps.datatypes && !spec.datatypes {
        return Some("datatypes not allowed in this logic".into());
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Grammar decode of the SMT-LIB catalog completion: quantifier presence,
    /// theory composition, and the mixed-Int+Real convention (`integer:
    /// false` — provenance unenforced, the flag routes the linear fallback)
    /// must match the cvc5 decoder semantics (`src/theory/logic_info.cpp`).
    #[test]
    fn smt_lib_catalog_decodes_grammar_semantics() {
        let spec = |n: &str| lookup(n).ok().flatten().unwrap_or_else(|| panic!("{n}"));
        // UFNIA: UF + nonlinear integer arith + quantifiers (the probe case).
        let ufnia = spec("UFNIA");
        assert!(ufnia.uf && ufnia.arith && ufnia.nonlinear && ufnia.integer && ufnia.quantifiers);
        // UFIDL: difference-logic shape, quantified.
        let ufidl = spec("UFIDL");
        assert!(ufidl.uf && ufidl.arith && ufidl.diff && ufidl.quantifiers);
        // Mixed shapes follow the shipped convention (AUFLIRA et al.).
        let ufnira = spec("UFNIRA");
        assert!(
            ufnira.uf && ufnira.arith && ufnira.nonlinear && !ufnira.integer && ufnira.quantifiers
        );
        let qf_lira = spec("QF_LIRA");
        assert!(qf_lira.arith && !qf_lira.integer && !qf_lira.quantifiers);
        // Strings + nonlinear integer arithmetic, quantifier-free.
        let qf_snia = spec("QF_SNIA");
        assert!(
            qf_snia.strings
                && qf_snia.arith
                && qf_snia.nonlinear
                && qf_snia.integer
                && !qf_snia.quantifiers
        );
        // Composition stack: UF + BV + DT + NIRA + quantifiers.
        let ufbvdtnira = spec("UFBVDTNIRA");
        assert!(
            ufbvdtnira.uf
                && ufbvdtnira.bv
                && ufbvdtnira.datatypes
                && ufbvdtnira.nonlinear
                && ufbvdtnira.quantifiers
        );
        // FP-with-arith and quantified arrays/BV shapes.
        assert!(spec("FPLRA").fp && spec("FPLRA").arith && spec("FPLRA").quantifiers);
        assert!(spec("ABV").arrays && spec("ABV").bv && spec("ABV").quantifiers);
    }

    #[test]
    fn registry_decodes_not_substring_matches() {
        // The motivating failure mode: an invented name containing NIA.
        assert!(lookup("QF_LINIA").is_err());
        assert!(lookup("MYNIA_SOLVER").is_err());
        // Real entries decode from the table.
        assert!(lookup("QF_NIA").is_ok());
        assert!(lookup("QF_ANIA").is_ok());
        // ANIA has arrays; NIA does not — semantics from the table.
        let (ania, nia) = (
            lookup("QF_ANIA").ok().flatten(),
            lookup("QF_NIA").ok().flatten(),
        );
        assert!(ania.is_some_and(|s| s.arrays));
        assert!(nia.is_some_and(|s| !s.arrays));
    }

    #[test]
    fn qf_lia_forbids_nonlinear_and_quantifiers() {
        let spec = lookup("QF_LIA").ok().flatten().copied().unwrap();
        let mut caps = Capabilities {
            arith: true,
            integer_terms: true,
            ..Capabilities::default()
        };
        assert!(validate(&spec, &caps).is_none());
        caps.nonlinear = true;
        assert!(validate(&spec, &caps).is_some());
        caps.nonlinear = false;
        caps.quantifiers = true;
        assert!(validate(&spec, &caps).is_some());
    }

    #[test]
    fn all_and_missing_are_permissive() {
        assert_eq!(lookup("ALL"), Ok(None));
        assert!(lookup("QF_UF").ok().flatten().is_some_and(|s| !s.arith));
    }
}
