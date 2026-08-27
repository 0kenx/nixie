//! Static formula features – the oxiz port of Z3's `ast/static_features`.
//!
//! # What this is
//!
//! Z3 configures its CDCL(T) search in `smt/smt_setup.cpp`.  It has three
//! config modes ([`ConfigMode`]); in two of them – `CFG_AUTO` (the default
//! under `auto_config`) and `CFG_UNKNOWN` (no logic) – it does **not** trust the
//! logic string alone.  It walks the asserted formulas once, accumulates a bag
//! of counts into a `static_features` struct, and then the per-logic
//! `setup_QF_<X>(static_features & st)` routines pick the theory plugin and the
//! search knobs (restart strategy, phase selection, relevancy level,
//! `arith_bound_prop`, …) from those counts.
//!
//! Concretely the difference-logic family is recognised structurally:
//!
//! ```text
//! // smt/smt_setup.cpp
//! is_in_diff_logic(st)  // every arith atom/term is diff-shaped
//! is_diff_logic(st)     // ...and there is some DL content
//! st.is_dense()         // (eqs+ineqs) > 9 * num_uninterp_constants
//! ```
//!
//! and `setup_QF_IDL(st)` / `setup_QF_UFIDL(st)` gate the dense-DL solver,
//! `RS_GEOMETRIC` restarts, `PS_CACHING` phase, etc. on `st.is_dense()` and
//! the clause/UF counts – **not** on the file name.
//!
//! # The "fake gate" this replaces
//!
//! oxiz used to route purely on the logic string:
//!
//! ```ignore
//! matches!(logic, "QF_UFIDL" | "UFIDL")   // config.rs VSIDS gate,
//!                                         // theory_manager is_dl_family
//! ```
//!
//! That is only the `CFG_LOGIC` half of Z3's router.  A benchmark can declare
//! `QF_UFIDL` and still contain a non-difference constraint (so the derived-
//! reason bound propagator is unsound there), or declare no logic at all and
//! be pure difference logic (so it never gets the DL-tuned path).  This module
//! collects the same features Z3 collects and exposes
//! [`StaticFeatures::is_diff_logic`] / [`StaticFeatures::is_dense`] so the knob
//! decisions can gate on the formula instead.  The logic string is still used
//! as a coarse router (which arith solver to install) – exactly Z3's split.
//!
//! # Faithfulness, and the deliberate generalisations
//!
//! The walk mirrors `static_features::collect` → `process_root` →
//! `process_all` → `update_core`, and the diff-shape predicates mirror
//! `is_diff_term` / `is_diff_atom`.  Two deviations are deliberate and each is
//! strictly more correct than Z3's structural test on oxiz's richer AST:
//!
//! * **Diff shape is computed from a linear form, not from raw `Add`/`Mul`
//!   constructor patterns.**  Z3's `is_diff_atom` recognises `(+ x (* -1 y))`
//!   literally; oxiz keeps `Sub`, `Neg`, and variadic `Add`/`Mul`, so a literal
//!   port would miss `(Sub x y)` (semantically `x - y`, plainly difference
//!   logic).  We instead reduce the atom to a linear form `Σ cᵢ·xᵢ + k` and
//!   accept it iff it has at most one `+1` coefficient and at most one `-1`
//!   coefficient – i.e. exactly `{k, ±x + k, x − y + k}` and sign variants,
//!   which is the same class Z3 accepts, independent of AST sugar and operand
//!   orientation.
//! * **`Lt`/`Gt` count as arithmetic inequalities.**  Z3's `update_core`
//!   counts only `OP_LE`/`OP_GE` (its front end normalises strict inequalities
//!   away before feature collection).  oxiz keeps `Lt`/`Gt` as distinct kinds
//!   all the way to the theory layer, so a literal le/ge-only port would
//!   silently drop every `<`/`>` atom and mis-classify a benchmark that uses
//!   them as non-arithmetic.  We count all four comparison kinds; the diff-shape
//!   test is identical.
//!
//! Everything else – clause/unit/bin-clause counting at the roots, the non-CNF
//! flag from nested gates, alien arithmetic terms (theory combination),
//! `is_dense`, `arith_k_sum_is_small`, the distinct-UF-symbol count – is a
//! direct port.

use crate::prelude::*;
use core::cmp::Ordering;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_core::sort::{SortId, SortKind};

use super::term_walk::collect_structural_children;

/// Mirror of Z3's `smt::config_mode` (the three entry points into `setup`).
///
/// Only [`ConfigMode::Logic`] is logic-string-driven; the other two collect
/// [`StaticFeatures`] first.  oxiz always collects features and lets the logic
/// string act as the coarse router, so this enum is here for documentation.
#[allow(dead_code)] // faithful Z3 port; reserved for future setup-mode routing
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConfigMode {
    /// Install theories from user params only.
    Basic,
    /// `CFG_LOGIC`: configure from `set-logic` alone (`setup_default`).
    Logic,
    /// `CFG_AUTO` (Z3 default under `auto_config`): collect features, then run
    /// the logic-named `setup_QF_X(st)`.
    Auto,
}

/// Static feature vector collected from the asserted formulas.
///
/// Field names mirror Z3's `static_features` (sans the `m_` prefix) so the two
/// can be read side by side; see `ast/static_features.h`.
#[derive(Debug, Clone, Default)]
pub struct StaticFeatures {
    // ======== clause structure (root handling in `process_root`) ========
    /// Whether every root is a clause or unit (no nested Boolean gates).
    pub cnf: bool,
    pub num_clauses: u64,
    pub num_bin_clauses: u64,
    pub num_units: u64,

    // ======== Boolean / formula structure (`update_core`) ========
    pub num_bool_exprs: u64,
    pub num_bool_constants: u64,
    pub num_nested_formulas: u64,
    pub num_ite_terms: u64,
    pub num_ite_formulas: u64,
    pub num_quantifiers: u64,
    /// `m_num_eqs`: every equality (any sort).  Not used by the DL gates; kept
    /// for parity with Z3's `display_primitive`.
    pub num_eqs: u64,

    // ======== uninterpreted symbols ========
    pub num_uninterpreted_constants: u64,
    /// Distinct uninterpreted function symbols of positive arity
    /// (`m_num_uninterpreted_functions`).
    pub num_uninterpreted_functions: u64,

    // ======== theory presence (sort families seen) ========
    pub has_int: bool,
    pub has_real: bool,
    pub has_bv: bool,
    /// Any arithmetic sort or arith head seen (drives `num_non_uf_theories`).
    has_arith: bool,
    has_array: bool,
    has_dt: bool,
    has_fp: bool,
    has_string: bool,

    // ======== arithmetic atoms and their difference-logic subsets ========
    pub num_arith_eqs: u64,
    pub num_diff_eqs: u64,
    pub num_arith_ineqs: u64,
    pub num_diff_ineqs: u64,
    /// Arithmetic "alien" terms (arith-sorted children of non-arith apps) and
    /// non-Boolean `ite` then/else branches – `m_num_arith_terms`.
    pub num_arith_terms: u64,
    pub num_diff_terms: u64,
    pub num_non_linear: u64,

    // ======== numeral magnitude (gates the small-int dense DL solver in Z3) ========
    /// Capped sum of `|numerals|` seen in arith atoms (`m_arith_k_sum`).
    arith_k_sum_abs: u64,

    // ======== cosmetic / structural ========
    pub num_exprs: u64,
    pub num_roots: u64,
    pub num_sharing: u64,

    // ======== walk scratch ========
    /// Terms whose `update_core` has already run (Z3's `m_pre_processed`,
    /// folded together with `m_post_processed` – a single visited set is
    /// equivalent because each term is counted exactly once).
    visited: FxHashSet<TermId>,
    /// Distinct UF function symbols of positive arity.
    uf_funcs: FxHashSet<Spur>,
    /// Pending walk items (Z3's `m_to_process`).
    stack: Vec<TermId>,
}

/// A linearised arithmetic term: `Σ cᵢ · xᵢ + k`.
///
/// `xᵢ` are *atomic* sub-terms – anything that is not itself an arithmetic
/// operator (variables, uninterpreted applications, selects, …) or an `ite`.
/// Coefficients are `i64`; the constant `k` is folded into `const_term`.
#[derive(Default)]
struct LinearForm {
    /// Atomic variable term → signed coefficient.
    vars: FxHashMap<TermId, i64>,
    const_term: i64,
    /// A numeral did not fit in `i64` (only affects `arith_k_sum_is_small`).
    overflow_const: bool,
    /// `true` if an `ite` was folded in as an atomic variable.
    saw_ite: bool,
    /// `false` if the term is structurally non-linear (`x*y`, `x div y`, …) and
    /// therefore not difference logic.
    linear: bool,
}

impl LinearForm {
    fn new() -> Self {
        Self {
            linear: true,
            ..Default::default()
        }
    }
}

impl StaticFeatures {
    /// Collect features from `assertions`, mirroring
    /// `static_features::collect(num_formulas, formulas)`.
    #[must_use]
    pub fn collect(manager: &TermManager, assertions: &[TermId]) -> StaticFeatures {
        let mut st = StaticFeatures {
            cnf: true,
            ..StaticFeatures::default()
        };
        for &root in assertions {
            st.process_root(manager, root);
        }
        st
    }

    // ========  ========
    // Z3-derived predicates.  These are the gates the setup routines read.
    // ========  ========

    /// `is_in_diff_logic(st)`: every arithmetic equality, inequality and alien
    /// term is difference-logic-shaped.  Mirrors `smt_setup.cpp` exactly.
    #[must_use]
    pub fn is_in_diff_logic(&self) -> bool {
        self.num_arith_eqs == self.num_diff_eqs
            && self.num_arith_terms == self.num_diff_terms
            && self.num_arith_ineqs == self.num_diff_ineqs
    }

    /// `is_diff_logic(st)`: [`Self::is_in_diff_logic`] **and** there actually is
    /// some difference-logic content.
    #[must_use]
    pub fn is_diff_logic(&self) -> bool {
        self.is_in_diff_logic()
            && (self.num_diff_ineqs > 0 || self.num_diff_eqs > 0 || self.num_diff_terms > 0)
    }

    /// `st.is_dense()`: the DL-graph-is-dense heuristic from
    /// `static_features::is_dense`.
    #[allow(dead_code)] // faithful Z3 port; reserved for dense-DL solver routing
    #[must_use]
    pub fn is_dense(&self) -> bool {
        self.num_uninterpreted_constants < 1000
            && (self.num_arith_eqs + self.num_arith_ineqs) > self.num_uninterpreted_constants * 9
    }

    /// `arith_k_sum_is_small()`: all numerals fit a small-int DL solver.
    /// Z3 uses `m_arith_k_sum < INT_MAX / 8`.
    #[allow(dead_code)] // faithful Z3 port; reserved for small-int DL solver routing
    #[must_use]
    pub fn arith_k_sum_is_small(&self) -> bool {
        self.arith_k_sum_abs < (u32::MAX as u64) / 8
    }

    /// `has_uf()`: at least one uninterpreted function symbol of arity > 0.
    #[must_use]
    pub fn has_uf(&self) -> bool {
        self.num_uninterpreted_functions > 0
    }

    /// `num_non_uf_theories()`: count of distinct non-UF theory families seen.
    #[allow(dead_code)] // faithful Z3 port; used by `inferred_logic`
    #[must_use]
    pub fn num_non_uf_theories(&self) -> u32 {
        let mut n = 0;
        if self.has_arith {
            n += 1;
        }
        if self.has_bv {
            n += 1;
        }
        if self.has_array {
            n += 1;
        }
        if self.has_dt {
            n += 1;
        }
        if self.has_fp {
            n += 1;
        }
        if self.has_string {
            n += 1;
        }
        n
    }

    /// `num_theories()`: non-UF theories plus one if there is any UF.
    #[allow(dead_code)] // faithful Z3 port; mirrors `setup_unknown(st)` theory counting
    #[must_use]
    pub fn num_theories(&self) -> u32 {
        self.num_non_uf_theories() + u32::from(self.has_uf())
    }

    /// The logic the formula's *features* imply, independent of the declared
    /// logic string – the `setup_unknown(st)` classification.  Returns `None`
    /// when the features do not single out one of the recognisable shapes
    /// (matching Z3's fall-through to the generic `setup_unknown()`).
    ///
    /// Exposed for diagnostics and for future auto-logic inference; the knob
    /// decisions in `setup_*` do not depend on it.
    #[allow(dead_code)] // diagnostics / future auto-logic inference
    #[must_use]
    pub fn inferred_logic(&self) -> Option<&'static str> {
        // Quantified ⇒ defer to the quantifier-aware setup paths (AUFLIA / …);
        // oxiz's MBQI/e-matching handles those uniformly, so we do not pretend
        // to a finer classification here.
        if self.num_quantifiers > 0 {
            return None;
        }
        // Direct port of `setup_unknown(st)`'s theory-shape cascade.  Note
        // `num_theories()` includes UF as one theory, so pure DL is 1 theory
        // and DL + UF is 2 – exactly Z3's `num_theories() == 1` / `== 2` tests.
        if self.num_non_uf_theories() == 0 {
            return Some("QF_UF");
        }
        if self.num_theories() == 1 && self.is_diff_logic() {
            if self.has_real && !self.has_int {
                return Some("QF_RDL");
            }
            if !self.has_real && self.has_int {
                return Some("QF_IDL");
            }
            return None;
        }
        if self.num_theories() == 2
            && self.has_uf()
            && self.is_diff_logic()
            && !self.has_real
            && self.has_int
        {
            return Some("QF_UFIDL");
        }
        None
    }

    // ========  ========
    // The walk.  Direct port of process_root / process_all / pre_process /
    // update_core; a single explicit stack replaces Z3's recursion.
    // ========  ========

    /// `process_root(e)`: classify the root as clause / unit / nested gate and
    /// seed the walk.  A root `(or …)` is a clause (and is itself never passed
    /// to `update_core`, matching Z3's `mark_post` in the `is_or` branch); a
    /// non-gate root is a unit; a gate root is neither.
    fn process_root(&mut self, manager: &TermManager, root: TermId) {
        // Z3: `if (is_marked_post(e)) { m_num_sharing++; return; }`.
        if self.visited.contains(&root) {
            self.num_sharing += 1;
            return;
        }
        self.num_roots += 1;

        let Some(td) = manager.get(root) else {
            return;
        };

        match &td.kind {
            // `(or l1 … ln)` → a clause.  Z3 marks it post and counts it without
            // ever running `update_core` on the `or` node itself.
            TermKind::Or(args) => {
                // Treat as fully processed so a later nested occurrence does not
                // double-count it (mirrors `mark_post`).
                self.visited.insert(root);
                self.num_clauses += 1;
                self.num_bool_exprs += 1;
                self.num_bin_clauses += u64::from(args.len() == 2);
                for &lit in args {
                    self.enqueue_stripped(manager, lit);
                }
            }
            // A non-gate root is a unit clause.
            k if !is_gate(k, manager, root) => {
                self.num_units += 1;
                self.num_clauses += 1;
                self.stack.push(root);
            }
            // A gate root (and / implies / ite / bool-eq / …) is neither clause
            // nor unit; just walk it.
            _ => self.stack.push(root),
        }
        self.drain(manager);
    }

    /// `process_all`: pop pending terms and run `update_core` exactly once each.
    fn drain(&mut self, manager: &TermManager) {
        while let Some(e) = self.stack.pop() {
            if !self.visited.insert(e) {
                self.num_sharing += 1;
                continue;
            }
            self.update_core(manager, e);
        }
    }

    /// `update_core(e)`: the heart of the counter logic.  Each branch is
    /// annotated with the Z3 field it maintains.
    fn update_core(&mut self, manager: &TermManager, e: TermId) {
        self.num_exprs += 1;
        let Some(td) = manager.get(e) else {
            return;
        };
        let sort = td.sort;

        // mark_theory(s->get_family_id()) + the precise has_int/has_real/has_bv
        // flags from the term's own sort.
        self.note_sort(manager, sort);

        let is_eq = matches!(td.kind, TermKind::Eq(_, _));
        let gate = is_gate(&td.kind, manager, e);

        // ======== nested Boolean gate ⇒ not CNF, and a nested formula ========
        if gate {
            self.cnf = false;
            self.num_nested_formulas += 1;
            if let TermKind::Ite(cond, then_br, else_br) = &td.kind {
                if sort_class(manager, sort) == SortClass::Bool {
                    self.num_ite_formulas += 1;
                } else {
                    self.num_ite_terms += 1;
                    // Z3: ite-term then/else branches that are arith-sorted
                    // count as arith terms (the condition does not).
                    let _ = cond;
                    for &branch in [then_br, else_br] {
                        self.acc_num_term(manager, branch);
                        if sort_class_term(manager, branch) == SortClass::Arith {
                            self.count_arith_term(manager, branch);
                        }
                    }
                }
            }
        }

        // ======== is_bool(e) ========
        if sort_class(manager, sort) == SortClass::Bool {
            self.num_bool_exprs += 1;
            if is_zero_arity_uninterp(&td.kind) {
                self.num_bool_constants += 1;
            }
        }

        if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
            self.num_quantifiers += 1;
        }

        // ======== arithmetic comparison atoms (le/ge/lt/gt) ========
        if let Some((lhs, rhs)) = comparison_operands(&td.kind)
            && sort_class_term(manager, lhs) == SortClass::Arith
            && sort_class_term(manager, rhs) == SortClass::Arith
        {
            self.num_arith_ineqs += 1;
            if self.atom_is_diff(manager, lhs, rhs) {
                self.num_diff_ineqs += 1;
            }
            self.acc_num_term(manager, rhs);
        }

        // ======== numeral / rational detection (m_has_rational) ========
        if let Some(v) = numeric_value(&td.kind) {
            if !v.is_integer() {
                // a non-integral rational constant ⇒ the problem uses reals.
                self.has_real = true;
            }
            self.acc_num_value(&v);
        }

        // --- equalities: m_num_eqs, and m_num_arith_eqs when one side is a
        // numeral (Z3 checks `is_numeral(arg1)`; we accept either side – see
        // the module docs). ---
        if let TermKind::Eq(lhs, rhs) = td.kind {
            self.num_eqs += 1;
            let lhs_c = sort_class_term(manager, lhs);
            let rhs_c = sort_class_term(manager, rhs);
            if lhs_c == SortClass::Arith && rhs_c == SortClass::Arith {
                let lhs_num = numeric_value_of(manager, lhs);
                let rhs_num = numeric_value_of(manager, rhs);
                if lhs_num.is_some() || rhs_num.is_some() {
                    self.num_arith_eqs += 1;
                    if self.atom_is_diff(manager, lhs, rhs) {
                        self.num_diff_eqs += 1;
                    }
                    if let Some(v) = lhs_num.or(rhs_num) {
                        self.acc_num_value(&v);
                    }
                }
            }
        }

        // ======== non-linearity + UF detection inside arith heads ========
        self.classify_arith_head(manager, &td.kind);

        // ======== uninterpreted constants / function symbols ========
        self.classify_uninterp(&td.kind);

        // --- the "alien" loop: arith-sorted children of non-arith, non-gate,
        // non-eq apps (theory combination).  Plus ite-term branches (handled
        // above).  Mirrors `if (!_is_eq && !_is_gate) { for (arg : children) …
        // if (fid_arg == afid) { m_num_arith_terms++; … } }`. ---
        if !is_eq && !gate {
            let parent_is_arith = is_arith_head(&td.kind);
            if !parent_is_arith {
                let mut children = Vec::new();
                collect_structural_children(&td.kind, &mut children);
                for &child in &children {
                    if sort_class_term(manager, child) == SortClass::Arith {
                        self.count_arith_term(manager, child);
                    }
                }
            }
        }

        // --- queue children for the walk, stripping one `not` level (Z3's
        // `m.is_not(arg, arg)` in `pre_process`). ---
        self.enqueue_children(manager, &td.kind);
    }

    // ========  ========
    // helpers folded out of update_core for readability
    // ========  ========

    /// `is_diff_term(arg)` + `acc_num(k)`: count one arith term (alien or
    /// ite-branch) and, if it is difference-logic-shaped, one diff term.
    fn count_arith_term(&mut self, manager: &TermManager, t: TermId) {
        self.num_arith_terms += 1;
        let lf = LinearFormCollector::run(manager, &[(t, 1)]);
        if lf.is_diff_term() {
            self.num_diff_terms += 1;
            if let Some(k) = lf.const_i64() {
                self.acc_num_signed(k);
            }
        }
    }

    /// `is_diff_atom(lhs, rhs)`: reduce `lhs - rhs` to a linear form and apply
    /// the difference-logic shape test.
    fn atom_is_diff(&self, manager: &TermManager, lhs: TermId, rhs: TermId) -> bool {
        let lf = LinearFormCollector::run(manager, &[(lhs, 1), (rhs, -1)]);
        lf.is_diff_atom()
    }

    /// `acc_num(expr)`: add `|numeral|` if `t` is a numeric constant.
    fn acc_num_term(&mut self, manager: &TermManager, t: TermId) {
        if let Some(td) = manager.get(t)
            && let Some(v) = numeric_value(&td.kind)
        {
            self.acc_num_value(&v);
        }
    }

    fn acc_num_value(&mut self, v: &Numeral) {
        self.arith_k_sum_abs = self.arith_k_sum_abs.saturating_add(v.abs_u64());
    }

    fn acc_num_signed(&mut self, k: i64) {
        self.arith_k_sum_abs = self.arith_k_sum_abs.saturating_add(k.unsigned_abs());
    }

    /// Set theory-presence and `has_int`/`has_real`/`has_bv` flags from a sort.
    /// Mirrors `mark_theory` + the `is_int`/`is_real`/`is_bv` probes in
    /// `update_core`.
    fn note_sort(&mut self, manager: &TermManager, sort: SortId) {
        let Some(s) = manager.sorts.get(sort) else {
            return;
        };
        match s.kind {
            SortKind::Bool => {}
            SortKind::Int => {
                self.has_arith = true;
                self.has_int = true;
            }
            SortKind::Real => {
                self.has_arith = true;
                self.has_real = true;
            }
            SortKind::BitVec(_) => self.has_bv = true,
            SortKind::Array { .. } => self.has_array = true,
            SortKind::String => self.has_string = true,
            SortKind::FloatingPoint { .. } => self.has_fp = true,
            SortKind::RoundingMode => self.has_fp = true,
            SortKind::Datatype(_) => self.has_dt = true,
            SortKind::Uninterpreted(_) | SortKind::Parameter(_) | SortKind::Parametric { .. } => {}
        }
    }

    /// Mirror of Z3's `OP_MUL` / `OP_DIV` … non-linearity classification.
    fn classify_arith_head(&mut self, manager: &TermManager, kind: &TermKind) {
        match kind {
            TermKind::Mul(args) => {
                // `(* c x)` is linear; `(* x y …)` (≥2 non-constant factors) is not.
                let non_const = args
                    .iter()
                    .filter(|a| !is_numeric_const_term(manager, **a))
                    .count();
                if non_const > 1 {
                    self.num_non_linear += 1;
                }
            }
            // Z3: div/mod by a non-constant (or zero) ⇒ non-linear + UF.
            TermKind::Div(_, b) | TermKind::Mod(_, b) if !is_numeric_const_term(manager, *b) => {
                self.num_non_linear += 1;
            }
            _ => {}
        }
    }

    /// Count uninterpreted constants (0-arity) and distinct UF function symbols.
    fn classify_uninterp(&mut self, kind: &TermKind) {
        match kind {
            TermKind::Var(_) => {
                // A declared constant (SMT-LIB `declare-const`).  Bool-sorted
                // ones also bump `num_bool_constants` (above).
                self.num_uninterpreted_constants += 1;
            }
            TermKind::Apply { func, args } => {
                if args.is_empty() {
                    self.num_uninterpreted_constants += 1;
                } else if self.uf_funcs.insert(*func) {
                    self.num_uninterpreted_functions = self.uf_funcs.len() as u64;
                }
            }
            _ => {}
        }
    }

    /// Collect `kind`'s structural children, strip one `Not` level off each
    /// (Z3's `m.is_not(arg, arg)` in `pre_process`), and queue them.
    fn enqueue_children(&mut self, manager: &TermManager, kind: &TermKind) {
        let mut children = Vec::new();
        collect_structural_children(kind, &mut children);
        for child in children {
            self.enqueue_stripped(manager, child);
        }
    }

    /// Push `t`, stripping one `Not` level if `t` is `(not x)`.
    fn enqueue_stripped(&mut self, manager: &TermManager, t: TermId) {
        let inner = manager.get(t).and_then(|td| {
            if let TermKind::Not(x) = td.kind {
                Some(x)
            } else {
                None
            }
        });
        self.stack.push(inner.unwrap_or(t));
    }
}

// ========  ========
// Free helpers
// ========  ========

/// Coarse sort class for theory counting.  Note: [`SortClass::Arith`] covers
/// both Int and Real; the `has_int`/`has_real` split is set in
/// [`StaticFeatures::note_sort`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SortClass {
    Bool,
    Arith,
    Bv,
    Array,
    Dt,
    Fp,
    String,
    Other,
}

fn sort_class(manager: &TermManager, sort: SortId) -> SortClass {
    let Some(s) = manager.sorts.get(sort) else {
        return SortClass::Other;
    };
    match s.kind {
        SortKind::Bool => SortClass::Bool,
        SortKind::Int | SortKind::Real => SortClass::Arith,
        SortKind::BitVec(_) => SortClass::Bv,
        SortKind::Array { .. } => SortClass::Array,
        SortKind::String => SortClass::String,
        SortKind::FloatingPoint { .. } => SortClass::Fp,
        // The rounding modes belong to the FP family for feature routing.
        SortKind::RoundingMode => SortClass::Fp,
        SortKind::Datatype(_) => SortClass::Dt,
        SortKind::Uninterpreted(_) | SortKind::Parameter(_) | SortKind::Parametric { .. } => {
            SortClass::Other
        }
    }
}

/// Coarse sort class of a child term.  This is what the alien / ite-branch
/// counters use to decide arith-sortedness.
fn sort_class_term(manager: &TermManager, t: TermId) -> SortClass {
    manager
        .get(t)
        .map_or(SortClass::Other, |td| sort_class(manager, td.sort))
}

/// Z3's `is_gate`: `And`/`Or`/`Xor`/`Implies`/`Ite`, plus `Eq` when it is
/// Boolean-sorted.
fn is_gate(kind: &TermKind, manager: &TermManager, e: TermId) -> bool {
    match kind {
        TermKind::And(_)
        | TermKind::Or(_)
        | TermKind::Xor(_, _)
        | TermKind::Implies(_, _)
        | TermKind::Ite(_, _, _) => true,
        TermKind::Eq(_, _) => sort_class_term(manager, e) == SortClass::Bool,
        _ => false,
    }
}

/// `True` iff `kind` is an arithmetic operator head (`Neg`/`Add`/`Sub`/`Mul`/
/// `Div`/`Mod`/`Lt`/`Le`/`Gt`/`Ge`).  Used for the alien-loop guard.
fn is_arith_head(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::Neg(_)
            | TermKind::Add(_)
            | TermKind::Sub(_, _)
            | TermKind::Mul(_)
            | TermKind::Div(_, _)
            | TermKind::Mod(_, _)
            | TermKind::Lt(_, _)
            | TermKind::Le(_, _)
            | TermKind::Gt(_, _)
            | TermKind::Ge(_, _)
    )
}

/// Operands of a comparison atom (`Lt`/`Le`/`Gt`/`Ge`), else `None`.
fn comparison_operands(kind: &TermKind) -> Option<(TermId, TermId)> {
    match kind {
        TermKind::Lt(a, b) | TermKind::Le(a, b) | TermKind::Gt(a, b) | TermKind::Ge(a, b) => {
            Some((*a, *b))
        }
        _ => None,
    }
}

/// `true` for a 0-arity uninterpreted constant (`Var` or `Apply` with no args).
fn is_zero_arity_uninterp(kind: &TermKind) -> bool {
    match kind {
        TermKind::Var(_) => true,
        TermKind::Apply { args, .. } => args.is_empty(),
        _ => false,
    }
}

/// `true` if `t` is a numeric constant term (`IntConst` / `RealConst`).
fn is_numeric_const_term(manager: &TermManager, t: TermId) -> bool {
    manager
        .get(t)
        .is_some_and(|td| matches!(td.kind, TermKind::IntConst(_) | TermKind::RealConst(_)))
}

/// A numeric constant extracted from a term kind, preserving sign and
/// fractional-ness for the `has_rational` flag and `arith_k_sum`.
#[derive(Clone, Copy)]
struct Numeral {
    /// Rational value as `(numerator, denominator)`; denominator `1` ⇒ integer.
    num: i64,
    den: i64,
    /// `true` if the constant did not fit `i64` (only downgrades
    /// `arith_k_sum_is_small`).
    overflow: bool,
}

impl Numeral {
    fn integer(n: i64) -> Self {
        Self {
            num: n,
            den: 1,
            overflow: false,
        }
    }

    fn is_integer(&self) -> bool {
        self.den == 1
    }

    /// `|num/den|` capped at `u64::MAX` (mirrors Z3 accumulating `|rational|`).
    fn abs_u64(&self) -> u64 {
        if self.den == 0 {
            return u64::MAX;
        }
        let n = (self.num as i128).unsigned_abs();
        let d = self.den as u128;
        let q = n / d;
        if q > u64::MAX as u128 || self.overflow {
            u64::MAX
        } else {
            q as u64
        }
    }
}

fn numeric_value(kind: &TermKind) -> Option<Numeral> {
    match kind {
        TermKind::IntConst(n) => Some(match n.to_i64() {
            Some(v) => Numeral::integer(v),
            None => Numeral {
                num: 0,
                den: 1,
                overflow: true,
            },
        }),
        TermKind::RealConst(r) => Some(Numeral {
            num: *r.numer(),
            den: *r.denom(),
            overflow: false,
        }),
        _ => None,
    }
}

fn numeric_value_of(manager: &TermManager, t: TermId) -> Option<Numeral> {
    manager.get(t).and_then(|td| numeric_value(&td.kind))
}

// ========  ========
// Linear-form collection (replaces Z3's structural is_diff_term/is_diff_atom)
// ========  ========

struct LinearFormCollector;

impl LinearFormCollector {
    /// Reduce `Σ multᵢ · tᵢ` to a single [`LinearForm`].  Each `(t, mult)` is
    /// pushed at the given multiplier; the collector distributes through
    /// `Neg`/`Add`/`Sub`/`Mul`, treats every non-arith non-ite term as an atomic
    /// variable, and marks `ite`, `div`, `mod`, and products of two or more
    /// variables as breaking difference logic.
    fn run(manager: &TermManager, seeds: &[(TermId, i64)]) -> LinearForm {
        let mut lf = LinearForm::new();
        let mut stack: Vec<(TermId, i64)> = seeds.iter().map(|&(t, m)| (t, m)).collect();
        while let Some((t, mult)) = stack.pop() {
            let Some(td) = manager.get(t) else {
                continue;
            };
            match &td.kind {
                TermKind::IntConst(n) => match n.to_i64() {
                    Some(v) => lf.const_term = lf.const_term.saturating_add(v.saturating_mul(mult)),
                    None => lf.overflow_const = true,
                },
                TermKind::RealConst(r) => {
                    let (num, den) = (*r.numer(), *r.denom());
                    if den == 1 {
                        lf.const_term = lf.const_term.saturating_add(num.saturating_mul(mult));
                    } else {
                        // A non-integral constant is fine for difference logic
                        // (the value of `k` is irrelevant to the shape test) but
                        // means `arith_k_sum_is_small` cannot trust the sum.
                        lf.overflow_const = true;
                    }
                }
                TermKind::Neg(a) => stack.push((*a, mult.saturating_neg())),
                TermKind::Add(args) => {
                    for a in args.iter().rev() {
                        stack.push((*a, mult));
                    }
                }
                TermKind::Sub(a, b) => {
                    stack.push((*b, mult.saturating_neg()));
                    stack.push((*a, mult));
                }
                TermKind::Mul(args) => {
                    let mut const_prod: i64 = 1;
                    let mut var_factor: Option<TermId> = None;
                    let mut var_count = 0u32;
                    let mut local_overflow = false;
                    for a in args {
                        match manager.get(*a).map(|ad| &ad.kind) {
                            Some(TermKind::IntConst(n)) => match n.to_i64() {
                                Some(v) => const_prod = const_prod.saturating_mul(v),
                                None => local_overflow = true,
                            },
                            Some(TermKind::RealConst(r)) => {
                                if *r.denom() == 1 {
                                    const_prod = const_prod.saturating_mul(*r.numer());
                                } else {
                                    local_overflow = true;
                                }
                            }
                            _ => {
                                var_count += 1;
                                if var_factor.is_none() {
                                    var_factor = Some(*a);
                                }
                            }
                        }
                    }
                    if var_count > 1 {
                        lf.linear = false;
                    } else {
                        let combined = const_prod.saturating_mul(mult);
                        if local_overflow {
                            lf.overflow_const = true;
                        }
                        match var_factor {
                            Some(v) => stack.push((v, combined)),
                            None => lf.const_term = lf.const_term.saturating_add(combined),
                        }
                    }
                }
                TermKind::Div(_, _) | TermKind::Mod(_, _) => {
                    // Division/modulo by a constant is linear in Z3's bookkeeping
                    // but is never difference-logic-shaped (coefficient `1/c`),
                    // and by a variable is non-linear.  Either way it is not DL.
                    lf.linear = false;
                }
                TermKind::Ite(_, _, _) => {
                    lf.saw_ite = true;
                    *lf.vars.entry(t).or_insert(0) += mult;
                }
                // Every other kind (Var, Apply, Select, Store, DtConstructor,
                // string/FP ops, constants already handled above, …) is an atomic
                // variable for difference-logic purposes.
                _ => {
                    *lf.vars.entry(t).or_insert(0) += mult;
                }
            }
        }
        // Drop zero coefficients (e.g. `x - x`); they do not affect the shape.
        lf.vars.retain(|_, c| *c != 0);
        lf
    }
}

impl LinearForm {
    /// `is_diff_term`: at most one variable, with coefficient `+1`.
    /// (Z3 accepts `k`, `x`, `k + x`; a negated variable is not a diff term.)
    fn is_diff_term(&self) -> bool {
        self.linear && !self.saw_ite && self.vars.len() <= 1 && self.vars.values().all(|c| *c == 1)
    }

    /// `is_diff_atom`: at most one `+1` and one `-1` coefficient, no others –
    /// i.e. the atom is `k`, `±x + k`, or `x − y + k` (up to overall sign).
    fn is_diff_atom(&self) -> bool {
        if !self.linear || self.saw_ite {
            return false;
        }
        let (mut pos, mut neg, mut other) = (0u32, 0u32, 0u32);
        for &c in self.vars.values() {
            match c.cmp(&0) {
                Ordering::Greater if c == 1 => pos += 1,
                Ordering::Less if c == -1 => neg += 1,
                _ => other += 1,
            }
        }
        other == 0 && pos <= 1 && neg <= 1
    }

    fn const_i64(&self) -> Option<i64> {
        if self.overflow_const {
            None
        } else {
            Some(self.const_term)
        }
    }
}

#[cfg(test)]
mod tests {
    //! The feature-classification tests build tiny terms through the public
    //! `TermManager` builder API (`mk_*`) and assert the Z3 predicates.  They
    //! document the exact shape each gate fires on.

    use super::*;
    use oxiz_core::ast::TermManager;

    fn int_var(m: &mut TermManager, name: &str) -> TermId {
        m.mk_var(name, m.sorts.int_sort)
    }

    fn features(m: &TermManager, assertions: &[TermId]) -> StaticFeatures {
        StaticFeatures::collect(m, assertions)
    }

    #[test]
    fn pure_idl_is_diff_and_not_uf() {
        let mut m = TermManager::new();
        let x = int_var(&mut m, "x");
        let y = int_var(&mut m, "y");
        // (<= (- x y) 5)
        let five = m.mk_int(5);
        let xy = m.mk_sub(x, y);
        let le = m.mk_le(xy, five);
        let st = features(&m, &[le]);
        assert!(st.is_diff_logic());
        assert!(st.is_in_diff_logic());
        assert!(!st.has_uf());
        assert!(st.has_int);
        assert!(!st.has_real);
        assert_eq!(st.num_arith_ineqs, 1);
        assert_eq!(st.num_diff_ineqs, 1);
        assert_eq!(st.num_uninterpreted_constants, 2);
        assert_eq!(st.inferred_logic(), Some("QF_IDL"));
    }

    #[test]
    fn ufidl_shape_detected_from_features() {
        let mut m = TermManager::new();
        let x = int_var(&mut m, "x");
        let y = int_var(&mut m, "y");
        // f : Int -> Int,  (<= (- (f x) y) 5)
        let fx = m.mk_apply("f", [x], m.sorts.int_sort);
        let five = m.mk_int(5);
        let fy = m.mk_sub(fx, y);
        let le = m.mk_le(fy, five);
        let st = features(&m, &[le]);
        assert!(st.is_diff_logic());
        assert!(st.has_uf());
        assert_eq!(st.inferred_logic(), Some("QF_UFIDL"));
    }

    #[test]
    fn sum_is_not_difference_logic() {
        let mut m = TermManager::new();
        let x = int_var(&mut m, "x");
        let y = int_var(&mut m, "y");
        // (<= (+ x y) 5)  – not DL
        let five = m.mk_int(5);
        let xy = m.mk_add([x, y]);
        let le = m.mk_le(xy, five);
        let st = features(&m, &[le]);
        assert!(!st.is_diff_logic());
        assert!(!st.is_in_diff_logic());
    }

    #[test]
    fn strict_inequality_counts() {
        let mut m = TermManager::new();
        let x = int_var(&mut m, "x");
        let y = int_var(&mut m, "y");
        // (< x y)  – strict; still DL after normalisation to x - y
        let lt = m.mk_lt(x, y);
        let st = features(&m, &[lt]);
        assert!(st.is_diff_logic());
        assert_eq!(st.num_arith_ineqs, 1);
    }

    #[test]
    fn dense_when_constants_few_and_atoms_many() {
        let mut m = TermManager::new();
        let x = int_var(&mut m, "x");
        let mut atoms = Vec::new();
        // 20 difference atoms over a single constant ⇒ dense.
        for i in 0..20_i64 {
            let k = m.mk_int(i);
            atoms.push(m.mk_le(x, k));
        }
        let st = features(&m, &atoms);
        assert!(st.is_diff_logic());
        assert!(st.is_dense(), "expected dense: {st:?}");
    }
}
