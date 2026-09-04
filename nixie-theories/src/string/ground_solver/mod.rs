//! Ground string decision procedure with model construction and verification.
//!
//! The CDCL(T) core maps every string-theory atom (`str.++`, `str.len`,
//! `str.in_re`, `str.contains`, …) to a fresh SAT variable – there is no
//! incremental string theory wired into the propagation loop. Historically the
//! only string reasoning was a small set of definite-conflict detectors in
//! `nixie-solver`, which could refute a fixed family of unsatisfiable formulas
//! but never *construct* a satisfying assignment, so every satisfiable ground
//! string benchmark fell through to an honest `Unknown`.
//!
//! This module closes that gap for the ground fragment (`QF_S` / the ground
//! part of `QF_SLIA`). It:
//!
//! 1. gathers per-variable string constraints from the asserted formula
//!    (constant equalities, length equalities/bounds, regex memberships,
//!    `prefixof`/`suffixof`/`contains` predicates, and concatenation
//!    equations),
//! 2. builds a candidate assignment for every string variable – propagating
//!    functional definitions, splitting concatenation equations by known
//!    operand lengths, and reducing the remaining regular constraints on each
//!    variable to a language-emptiness / shortest-word search over the
//!    Brzozowski derivative engine in [`super::regex_membership`], and
//! 3. **verifies** the candidate by concretely evaluating *every* assertion
//!    under it.
//!
//! The final verification step is what makes the answer sound: a `Sat` verdict
//! is returned only when a concrete witness satisfies the entire formula, so a
//! heuristic (necessarily incomplete) construction can never yield a spurious
//! `Sat`. Anything the construction cannot certify is reported as `Unknown`.

mod eval;

use super::regex::Regex;
use super::regex_membership::{WordSearch, compile_regex, search_word};
#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager, str_fold};
use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

/// Outcome of the ground string decision procedure.
///
/// `Unsat` is intentionally never produced here – refutation of ground string
/// formulas is handled by the definite-conflict detectors in `nixie-solver`,
/// which drive the same concrete evaluator through
/// [`eval_ground_bool`].  This procedure only ever *confirms* satisfiability
/// with a concrete witness (`Sat`) or gives up (`Unknown`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroundStringOutcome {
    /// A concrete model was constructed and verified against every assertion.
    Sat,
    /// No verified model could be built within the search bounds.
    Unknown,
}

/// Resource bounds shared by the per-variable regular-constraint search.
const MAX_REGEX_STATES: usize = 8000;
const MAX_REGEX_WORD_LEN: usize = 4096;
/// Recursion guard for the concrete evaluator.
const MAX_EVAL_DEPTH: usize = 4096;
/// Maximum number of complete candidate assignments the repair search verifies
/// before conceding `Unknown`.
const MAX_REPAIR_ASSIGNMENTS: usize = 256;
/// Maximum number of unconstrained variables the repair search varies
/// independently; any beyond this keep the default empty string.
const MAX_REPAIR_VARS: usize = 4;
/// Maximum number of distinct candidate words the repair search tries per
/// variable.
const MAX_REPAIR_CANDIDATES: usize = 8;
/// Extra candidates added *only* when the formula contains a `str.<` /
/// `str.<=` atom or a `str.to_code` equation, so no other formula's search
/// order changes.
const MAX_EXTRA_REPAIR_CANDIDATES: usize = 6;

/// A verified assignment of concrete strings to the string-sorted variables of
/// a ground formula, as `(variable term, value)` pairs.
pub type GroundStringModel = Vec<(TermId, String)>;

/// Attempt to decide a ground string formula by constructing and verifying a
/// concrete model.
///
/// Returns [`GroundStringOutcome::Sat`] only when a concrete assignment to every
/// string variable makes *all* `assertions` evaluate to `true`; otherwise
/// [`GroundStringOutcome::Unknown`].
#[must_use]
pub fn solve_ground_string(manager: &TermManager, assertions: &[TermId]) -> GroundStringOutcome {
    match solve_ground_string_model(manager, assertions) {
        Some(_) => GroundStringOutcome::Sat,
        None => GroundStringOutcome::Unknown,
    }
}

/// Same decision as [`solve_ground_string`], but returning the concrete witness
/// it verified instead of only the verdict.
///
/// `Some(model)` is produced exactly when every assertion evaluates to `true`
/// under `model`, so the caller may publish these values directly as the string
/// part of a `(get-model)` / `(get-value ...)` answer.  `None` means no witness
/// could be certified within the search bounds (the caller must then keep an
/// honest `Unknown`, or fall back to another model source).
#[must_use]
pub fn solve_ground_string_model(
    manager: &TermManager,
    assertions: &[TermId],
) -> Option<GroundStringModel> {
    let mut builder = ModelBuilder::new(manager, assertions);
    builder.gather();
    if !builder.build_assignment() {
        return None;
    }
    if builder.verify() || builder.repair_unconstrained() {
        return Some(builder.model.into_iter().collect());
    }
    None
}

/// Evaluate a **closed** (variable-free) Boolean term to its unique truth
/// value, or `None` when it is not closed / not fully interpreted.
///
/// This is the refutation counterpart of [`solve_ground_string_model`]: it runs
/// the very same concrete evaluator, but over an *empty* model, so a
/// [`TermKind::Var`] never receives a value and the recursion collapses to
/// `None` the moment anything unknown is reached. A `Some(v)` answer therefore
/// means `v` is the term's value in **every** interpretation – a ground fact.
///
/// Because the value of a closed term does not depend on where the term
/// appears, evaluating one is safe at any polarity. What is *not* safe is
/// treating a conditionally asserted formula as unconditional; that distinction
/// belongs to the caller (see `nixie-solver`'s `check_string.rs`, which walks
/// only through `term_walk::asserted_children`).
///
/// The evaluator is three-valued and short-circuits: `false ∧ unknown` is
/// `Some(false)`, `true ∨ unknown` is `Some(true)`, and an equality between two
/// closed operands is decided even when a sibling assertion mentions variables.
#[must_use]
pub fn eval_ground_bool(manager: &TermManager, term: TermId) -> Option<bool> {
    // An empty assertion list and an empty model: `gather` / `build_assignment`
    // are deliberately NOT run, so `model` stays empty and no variable is ever
    // interpreted.
    let builder = ModelBuilder::new(manager, &[]);
    debug_assert!(builder.model.is_empty(), "ground evaluation must be closed");
    builder.eval(term, 0)?.as_bool()
}

/// A concrete value the evaluator can produce for a ground term.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Val {
    /// A string value.
    Str(String),
    /// An integer value.
    Int(BigInt),
    /// A Boolean value.
    Bool(bool),
}

impl Val {
    fn as_str(&self) -> Option<&str> {
        match self {
            Val::Str(s) => Some(s),
            _ => None,
        }
    }
    fn as_int(&self) -> Option<&BigInt> {
        match self {
            Val::Int(n) => Some(n),
            _ => None,
        }
    }
    fn as_bool(&self) -> Option<bool> {
        match self {
            Val::Bool(b) => Some(*b),
            _ => None,
        }
    }
}

/// Collected constraints and the growing model for one `check` invocation.
struct ModelBuilder<'a> {
    manager: &'a TermManager,
    assertions: &'a [TermId],
    /// Every string-sorted variable that appears in the formula.
    string_vars: FxHashSet<TermId>,
    /// Exact length equalities `len(var) = n`.
    len_eq: FxHashMap<TermId, i64>,
    /// Length lower bounds `len(var) >= lo` (the maximum lower bound seen).
    len_lo: FxHashMap<TermId, i64>,
    /// Length upper bounds `len(var) <= hi` (the minimum upper bound seen).
    len_hi: FxHashMap<TermId, i64>,
    /// Regular-language memberships per variable: `(regex, positive)`.
    memberships: FxHashMap<TermId, Vec<(Arc<Regex>, bool)>>,
    /// The current (partial) string assignment.
    model: FxHashMap<TermId, String>,
    /// Variables that no gathered constraint restricts, in ascending `TermId`
    /// order.  They received the default empty string, and the repair search
    /// below is free to give them any other value.
    unconstrained_vars: Vec<TermId>,
}

impl<'a> ModelBuilder<'a> {
    fn new(manager: &'a TermManager, assertions: &'a [TermId]) -> Self {
        Self {
            manager,
            assertions,
            string_vars: FxHashSet::default(),
            len_eq: FxHashMap::default(),
            len_lo: FxHashMap::default(),
            len_hi: FxHashMap::default(),
            memberships: FxHashMap::default(),
            model: FxHashMap::default(),
            unconstrained_vars: Vec::new(),
        }
    }

    /// Return `true` when `term` is a string-sorted variable.
    fn is_string_var(&self, term: TermId) -> bool {
        let Some(td) = self.manager.get(term) else {
            return false;
        };
        if !matches!(td.kind, TermKind::Var(_)) {
            return false;
        }
        self.manager
            .sorts
            .get(td.sort)
            .is_some_and(nixie_core::sort::Sort::is_string)
    }

    // ========  ========
    // Constraint gathering
    // ========  ========

    /// Walk every assertion, recording string variables and the atomic
    /// constraints used to guide model construction.
    fn gather(&mut self) {
        // Collect all string variables first (traversing through every node).
        let mut stack: Vec<TermId> = self.assertions.to_vec();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if self.is_string_var(t) {
                self.string_vars.insert(t);
            }
            if let Some(td) = self.manager.get(t) {
                push_children(&td.kind, &mut stack);
            }
        }

        // Record top-level (conjunctive) atomic constraints. Assertions are an
        // implicit conjunction; we descend through `And` but treat everything
        // else structurally as an atom for constraint extraction.
        let assertions = self.assertions.to_vec();
        for a in assertions {
            self.record_atom(a);
        }
    }

    /// Extract a single asserted atom (descending through top-level `And`).
    fn record_atom(&mut self, term: TermId) {
        // An explicit worklist, not recursion: a conjunction is as deeply
        // nested as the input makes it, and this runs on whatever stack the
        // embedder gave the calling thread.  Conjuncts are pushed in reverse
        // so they pop left to right, the order the recursive descent used.
        let mut worklist = vec![term];
        while let Some(current) = worklist.pop() {
            let Some(td) = self.manager.get(current) else {
                continue;
            };
            match &td.kind {
                TermKind::And(args) => {
                    let children: Vec<TermId> = args.iter().rev().copied().collect();
                    worklist.extend(children);
                }
                TermKind::Eq(lhs, rhs) => {
                    let (lhs, rhs) = (*lhs, *rhs);
                    self.record_eq(lhs, rhs);
                }
                TermKind::StrInRe(var, re) => {
                    let (var, re) = (*var, *re);
                    self.record_membership(var, re, true);
                }
                TermKind::Not(inner) => {
                    let inner = *inner;
                    if let Some(inner_td) = self.manager.get(inner)
                        && let TermKind::StrInRe(var, re) = &inner_td.kind
                    {
                        let (var, re) = (*var, *re);
                        self.record_membership(var, re, false);
                    }
                }
                TermKind::StrContains(hay, needle) => {
                    let (hay, needle) = (*hay, *needle);
                    self.record_contains(hay, needle);
                }
                TermKind::StrPrefixOf(pre, var) => {
                    let (pre, var) = (*pre, *var);
                    self.record_prefix(pre, var);
                }
                TermKind::StrSuffixOf(suf, var) => {
                    let (suf, var) = (*suf, *var);
                    self.record_suffix(suf, var);
                }
                TermKind::Ge(a, b) => {
                    let (a, b) = (*a, *b);
                    self.record_len_ineq(a, b, IneqKind::Ge);
                }
                TermKind::Gt(a, b) => {
                    let (a, b) = (*a, *b);
                    self.record_len_ineq(a, b, IneqKind::Gt);
                }
                TermKind::Le(a, b) => {
                    let (a, b) = (*a, *b);
                    self.record_len_ineq(a, b, IneqKind::Le);
                }
                TermKind::Lt(a, b) => {
                    let (a, b) = (*a, *b);
                    self.record_len_ineq(a, b, IneqKind::Lt);
                }
                _ => {}
            }
        }
    }

    /// Extract equalities: length equalities and regex/predicate memberships are
    /// treated specially; other equalities are only consulted during the
    /// definitional / concat-splitting phase (via a fresh traversal).
    fn record_eq(&mut self, lhs: TermId, rhs: TermId) {
        // len(v) = n  (either orientation)
        if let Some((v, n)) = self.as_len_const(lhs, rhs) {
            self.len_eq.insert(v, n);
            self.set_lo(v, n);
            self.set_hi(v, n);
            return;
        }
        if let Some((v, n)) = self.as_len_const(rhs, lhs) {
            self.len_eq.insert(v, n);
            self.set_lo(v, n);
            self.set_hi(v, n);
        }
    }

    /// Record `str.contains(hay, needle)` with a constant `needle` as a
    /// membership `hay ∈ Σ* · needle · Σ*`.
    fn record_contains(&mut self, hay: TermId, needle: TermId) {
        if !self.is_string_var(hay) {
            return;
        }
        if let Some(n) = self.const_string(needle) {
            let re = Regex::concat(vec![Regex::all(), Regex::literal(&n), Regex::all()]);
            self.memberships.entry(hay).or_default().push((re, true));
        }
    }

    /// Record `str.prefixof(pre, var)` with a constant `pre` as a membership
    /// `var ∈ pre · Σ*`.
    fn record_prefix(&mut self, pre: TermId, var: TermId) {
        if !self.is_string_var(var) {
            return;
        }
        if let Some(p) = self.const_string(pre) {
            let re = Regex::concat(vec![Regex::literal(&p), Regex::all()]);
            self.memberships.entry(var).or_default().push((re, true));
        }
    }

    /// Record `str.suffixof(suf, var)` with a constant `suf` as a membership
    /// `var ∈ Σ* · suf`.
    fn record_suffix(&mut self, suf: TermId, var: TermId) {
        if !self.is_string_var(var) {
            return;
        }
        if let Some(s) = self.const_string(suf) {
            let re = Regex::concat(vec![Regex::all(), Regex::literal(&s)]);
            self.memberships.entry(var).or_default().push((re, true));
        }
    }

    /// Record a `str.in_re` membership on a variable with a ground regex.
    fn record_membership(&mut self, var: TermId, re: TermId, positive: bool) {
        if !self.is_string_var(var) {
            return;
        }
        if let Some(compiled) = compile_regex(self.manager, re) {
            self.memberships
                .entry(var)
                .or_default()
                .push((compiled, positive));
        }
    }

    /// Record a length inequality `len(v) ▷ n` (or its mirror) into the bounds.
    fn record_len_ineq(&mut self, a: TermId, b: TermId, kind: IneqKind) {
        // a ▷ b with one side `len(v)` and the other a constant.
        if let (Some(v), Some(n)) = (self.as_len(a), self.int_const(b)) {
            // len(v) ▷ n
            match kind {
                IneqKind::Ge => self.set_lo(v, n),
                IneqKind::Gt => self.set_lo(v, n + 1),
                IneqKind::Le => self.set_hi(v, n),
                IneqKind::Lt => self.set_hi(v, n - 1),
            }
            return;
        }
        if let (Some(n), Some(v)) = (self.int_const(a), self.as_len(b)) {
            // n ▷ len(v)  ==>  len(v) ◁ n
            match kind {
                IneqKind::Ge => self.set_hi(v, n),     // n >= len  => len <= n
                IneqKind::Gt => self.set_hi(v, n - 1), // n > len => len <= n-1
                IneqKind::Le => self.set_lo(v, n),     // n <= len => len >= n
                IneqKind::Lt => self.set_lo(v, n + 1), // n < len => len >= n+1
            }
        }
    }

    fn set_lo(&mut self, v: TermId, n: i64) {
        let e = self.len_lo.entry(v).or_insert(n);
        if n > *e {
            *e = n;
        }
    }
    fn set_hi(&mut self, v: TermId, n: i64) {
        let e = self.len_hi.entry(v).or_insert(n);
        if n < *e {
            *e = n;
        }
    }

    /// If `len_term` is `(str.len v)` for a string variable `v`, return `v`.
    fn as_len(&self, len_term: TermId) -> Option<TermId> {
        match &self.manager.get(len_term)?.kind {
            TermKind::StrLen(inner) if self.is_string_var(*inner) => Some(*inner),
            _ => None,
        }
    }

    /// Match `(= (str.len v) n)` shape: `len_term` is `str.len v`, `int_term`
    /// is an integer constant. Returns `(v, n)`.
    fn as_len_const(&self, len_term: TermId, int_term: TermId) -> Option<(TermId, i64)> {
        let v = self.as_len(len_term)?;
        let n = self.int_const(int_term)?;
        Some((v, n))
    }

    /// Decode an integer constant term to `i64`.
    fn int_const(&self, term: TermId) -> Option<i64> {
        match &self.manager.get(term)?.kind {
            TermKind::IntConst(n) => n.to_i64(),
            _ => None,
        }
    }

    /// Fold a ground string term (literal or constant concatenation) to a value.
    fn const_string(&self, term: TermId) -> Option<String> {
        // The `str.++` spine is walked with an explicit stack: an n-ary
        // application folds into that many nested binary nodes, so its depth is
        // input-controlled.  Pushing the right operand first makes the pops run
        // left to right, which is the order the concatenation needs.
        let mut worklist = vec![term];
        let mut out = String::new();
        while let Some(current) = worklist.pop() {
            match &self.manager.get(current)?.kind {
                TermKind::StringLit(s) => out.push_str(s),
                TermKind::StrConcat(a, b) => {
                    worklist.push(*b);
                    worklist.push(*a);
                }
                _ => return None,
            }
        }
        Some(out)
    }

    // ========  ========
    // Model construction
    // ========  ========

    /// Build a full assignment for every string variable. Returns `false` only
    /// when construction is impossible within scope (the caller then reports
    /// `Unknown`); a `true` return still requires [`Self::verify`] to confirm.
    fn build_assignment(&mut self) -> bool {
        // Fixpoint: propagate functional definitions and split concatenation
        // equations until no further variable can be pinned.
        let mut changed = true;
        let mut rounds = 0usize;
        while changed && rounds < 64 {
            changed = false;
            rounds += 1;
            changed |= self.propagate_definitions();
            changed |= self.split_concats();
        }

        // Regular-constraint construction for remaining constrained variables.
        let constrained: Vec<TermId> = self
            .string_vars
            .iter()
            .copied()
            .filter(|v| {
                !self.model.contains_key(v)
                    && (self.memberships.contains_key(v)
                        || self.len_eq.contains_key(v)
                        || self.len_lo.contains_key(v)
                        || self.len_hi.contains_key(v))
            })
            .collect();
        for v in constrained {
            if let Some(word) = self.solve_regular(v) {
                self.model.insert(v, word);
            }
        }

        // Any still-unassigned variable is unconstrained: pick the empty string.
        // Remember them – no gathered constraint mentions them, so if the whole
        // formula fails to verify, these are exactly the variables the repair
        // search may re-pick freely.  Sorted for a deterministic search order.
        let mut leftover: Vec<TermId> = self
            .string_vars
            .iter()
            .copied()
            .filter(|v| !self.model.contains_key(v))
            .collect();
        leftover.sort_unstable();
        for &v in &leftover {
            self.model.insert(v, String::new());
        }
        self.unconstrained_vars = leftover;

        true
    }

    /// Re-pick values for the *unconstrained* variables when the default
    /// assignment fails to satisfy the formula, and re-verify.
    ///
    /// The construction phase pins a variable only from an equality, a length
    /// bound or a regular constraint; anything left over is given the empty
    /// string purely as a default.  That default is a real answer for most
    /// formulas but is refuted by any disequality it happens to violate – the
    /// smallest witness being `(distinct "b" (str.++ s0 "b"))`, satisfied by
    /// every `s0` except `""`.  Without a second attempt such a trivially
    /// satisfiable formula fell through to `Unknown`.
    ///
    /// The search enumerates a small pool of candidate words over at most
    /// [`MAX_REPAIR_VARS`] of those variables, bounded by
    /// [`MAX_REPAIR_ASSIGNMENTS`] complete assignments.  Every candidate is put
    /// through the same full [`Self::verify`] as the primary construction, so
    /// this only ever converts an `Unknown` into a *witnessed* `Sat` – it can
    /// never make an unsatisfiable formula look satisfiable.
    ///
    /// Reference: Z3's `theory_seq.cpp` likewise falls back to fresh values
    /// drawn outside the formula's alphabet when a length/disequality constraint
    /// rules out the canonical one.
    fn repair_unconstrained(&mut self) -> bool {
        if self.unconstrained_vars.is_empty() {
            return false;
        }
        let candidates = self.repair_candidates();
        if candidates.len() < 2 {
            return false;
        }

        let vars: Vec<TermId> = self
            .unconstrained_vars
            .iter()
            .copied()
            .take(MAX_REPAIR_VARS)
            .collect();

        // Uniform sweep first: give every variable the same candidate.  This
        // reaches the common "all defaults are wrong for the same reason" shape
        // even when more variables are free than the odometer below can vary.
        for candidate in candidates.iter().skip(1) {
            for &v in &vars {
                self.model.insert(v, candidate.clone());
            }
            if self.verify() {
                return true;
            }
        }

        // Odometer over the candidate pool, last variable varying fastest.
        let mut choice = vec![0usize; vars.len()];
        for _ in 0..MAX_REPAIR_ASSIGNMENTS {
            // Advance to the next tuple; the all-zero tuple is the default
            // assignment the caller already refuted.
            let mut position = vars.len();
            loop {
                if position == 0 {
                    return self.restore_defaults(&vars);
                }
                position -= 1;
                choice[position] += 1;
                if choice[position] < candidates.len() {
                    break;
                }
                choice[position] = 0;
            }

            for (slot, &v) in vars.iter().enumerate() {
                self.model.insert(v, candidates[choice[slot]].clone());
            }
            if self.verify() {
                return true;
            }
        }

        self.restore_defaults(&vars)
    }

    /// Put the unconstrained variables back to their default empty string and
    /// report failure, so a rejected repair leaves no partial state behind.
    fn restore_defaults(&mut self, vars: &[TermId]) -> bool {
        for &v in vars {
            self.model.insert(v, String::new());
        }
        false
    }

    /// The candidate words the repair search tries, most likely first.
    ///
    /// The pool is `""` (the default), one and two copies of a character that
    /// occurs in no string literal of the formula – which satisfies any
    /// disequality against a literal – and then the literals themselves, which
    /// cover equations the splitter left underdetermined.
    ///
    /// Two extra families of candidates are appended for the operators whose
    /// witnesses the literal pool cannot reach – each gated on the operator
    /// actually occurring, so the pool (and therefore the odometer's search
    /// order) is byte-for-byte unchanged for every formula without one:
    ///
    /// * `str.<` / `str.<=`: every literal *extended by the fresh character*.
    ///   A strict lower bound `"abb" < x` with a strict upper bound
    ///   `x < "abc"` has no solution among the literals themselves, but
    ///   `"abb"` plus one character sits strictly between them.
    /// * `str.to_code`: the singleton string named by each integer constant
    ///   the formula equates with a `str.to_code` term, so `(= (str.to_code x)
    ///   65)` reaches `x = "A"`.
    ///
    /// Widening the pool can only ever turn `Unknown` into a *verified* `Sat`
    /// – every candidate still goes through the same full [`Self::verify`].
    fn repair_candidates(&self) -> Vec<String> {
        let literals = self.formula_literals();
        let fresh = Self::fresh_char(&literals);
        let mut pool = vec![
            String::new(),
            fresh.to_string(),
            [fresh, fresh].iter().collect(),
        ];
        for literal in &literals {
            if pool.len() >= MAX_REPAIR_CANDIDATES {
                return pool;
            }
            if !literal.is_empty() && !pool.contains(literal) {
                pool.push(literal.clone());
            }
        }
        let cap = MAX_REPAIR_CANDIDATES + MAX_EXTRA_REPAIR_CANDIDATES;
        for extra in self.operator_specific_candidates(&literals, fresh) {
            if pool.len() >= cap {
                break;
            }
            if !pool.contains(&extra) {
                pool.push(extra);
            }
        }
        pool
    }

    /// Candidate words derived from the order / character-code operators the
    /// formula actually uses; empty when it uses neither.
    fn operator_specific_candidates(&self, literals: &[String], fresh: char) -> Vec<String> {
        let mut order_atom = false;
        let mut codes: Vec<BigInt> = Vec::new();

        let mut stack: Vec<TermId> = self.assertions.to_vec();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let Some(td) = self.manager.get(t) else {
                continue;
            };
            match &td.kind {
                TermKind::StrLt(_, _) | TermKind::StrLe(_, _) => order_atom = true,
                TermKind::Eq(lhs, rhs) => {
                    if let Some(code) = self.to_code_equation(*lhs, *rhs) {
                        codes.push(code);
                    }
                }
                _ => {}
            }
            push_children(&td.kind, &mut stack);
        }

        let mut out = Vec::new();
        if order_atom {
            out.extend(literals.iter().map(|l| format!("{l}{fresh}")));
        }
        for code in codes {
            if let str_fold::FromCode::Char(c) = str_fold::str_from_code(&code) {
                let mut word = String::new();
                word.push(c);
                out.push(word);
            }
        }
        out
    }

    /// The integer constant of `(= (str.to_code _) n)` in either orientation.
    fn to_code_equation(&self, lhs: TermId, rhs: TermId) -> Option<BigInt> {
        let is_to_code = |t: TermId| {
            matches!(
                self.manager.get(t).map(|d| &d.kind),
                Some(TermKind::StrToCode(_))
            )
        };
        let int_const = |t: TermId| match self.manager.get(t).map(|d| &d.kind) {
            Some(TermKind::IntConst(n)) => Some(n.clone()),
            _ => None,
        };
        if is_to_code(lhs) {
            return int_const(rhs);
        }
        if is_to_code(rhs) {
            return int_const(lhs);
        }
        None
    }

    /// Every distinct string literal in the formula, in ascending `TermId`
    /// order so the candidate pool is deterministic.
    fn formula_literals(&self) -> Vec<String> {
        let mut stack: Vec<TermId> = self.assertions.to_vec();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut found: Vec<TermId> = Vec::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let Some(td) = self.manager.get(t) else {
                continue;
            };
            if matches!(td.kind, TermKind::StringLit(_)) {
                found.push(t);
            }
            push_children(&td.kind, &mut stack);
        }
        found.sort_unstable();
        found
            .into_iter()
            .filter_map(|t| match &self.manager.get(t)?.kind {
                TermKind::StringLit(s) => Some(s.clone()),
                _ => None,
            })
            .collect()
    }

    /// A character occurring in none of `literals`, so a word built from it is
    /// different from every string constant the formula mentions.
    fn fresh_char(literals: &[String]) -> char {
        let used: FxHashSet<char> = literals.iter().flat_map(|s| s.chars()).collect();
        ('a'..='z')
            .chain('A'..='Z')
            .chain('0'..='9')
            .find(|c| !used.contains(c))
            .unwrap_or('a')
    }

    /// Assign a variable whenever it is defined by `var = <ground/known term>`.
    fn propagate_definitions(&mut self) -> bool {
        let mut assignments: Vec<(TermId, String)> = Vec::new();
        for &a in self.assertions {
            self.collect_definitions(a, &mut assignments);
        }
        let mut changed = false;
        for (v, s) in assignments {
            if let hash_map::Entry::Vacant(slot) = self.model.entry(v) {
                slot.insert(s);
                changed = true;
            }
        }
        changed
    }

    /// Descend through top-level `And`s collecting `Eq(var, rhs)` definitions
    /// where `rhs` currently evaluates to a concrete string.
    fn collect_definitions(&self, term: TermId, out: &mut Vec<(TermId, String)>) {
        // Iterative for the same reason as `record_atom`, and with the same
        // reverse push so conjuncts are visited left to right.
        let mut worklist = vec![term];
        while let Some(current) = worklist.pop() {
            let Some(td) = self.manager.get(current) else {
                continue;
            };
            match &td.kind {
                TermKind::And(args) => worklist.extend(args.iter().rev().copied()),
                TermKind::Eq(lhs, rhs) => {
                    self.try_definition(*lhs, *rhs, out);
                    self.try_definition(*rhs, *lhs, out);
                }
                _ => {}
            }
        }
    }

    /// If `var` is an unassigned string variable and `rhs` evaluates to a
    /// concrete string, record `var := value`.
    fn try_definition(&self, var: TermId, rhs: TermId, out: &mut Vec<(TermId, String)>) {
        if !self.is_string_var(var) || self.model.contains_key(&var) {
            return;
        }
        if let Some(Val::Str(s)) = self.eval(rhs, 0) {
            out.push((var, s));
        }
    }

    /// Split concatenation equations `concat(ops) = target` whose operand
    /// lengths are all determined, assigning each unknown variable operand its
    /// positional slice of `target`.
    fn split_concats(&mut self) -> bool {
        let mut plans: Vec<(TermId, String)> = Vec::new();
        for &a in self.assertions {
            self.collect_concat_plans(a, &mut plans);
        }
        let mut changed = false;
        for (v, s) in plans {
            if let hash_map::Entry::Vacant(slot) = self.model.entry(v) {
                slot.insert(s);
                changed = true;
            }
        }
        changed
    }

    /// Descend through top-level `And`s collecting concat-split assignments.
    fn collect_concat_plans(&self, term: TermId, out: &mut Vec<(TermId, String)>) {
        // Iterative for the same reason as `record_atom`, and with the same
        // reverse push so conjuncts are visited left to right.
        let mut worklist = vec![term];
        while let Some(current) = worklist.pop() {
            let Some(td) = self.manager.get(current) else {
                continue;
            };
            match &td.kind {
                TermKind::And(args) => worklist.extend(args.iter().rev().copied()),
                TermKind::Eq(lhs, rhs) => {
                    self.try_concat_split(*lhs, *rhs, out);
                    self.try_concat_split(*rhs, *lhs, out);
                }
                _ => {}
            }
        }
    }

    /// If `concat_term` is a concatenation and `target_term` evaluates to a
    /// concrete string, try to solve for the unknown operands.
    fn try_concat_split(
        &self,
        concat_term: TermId,
        target_term: TermId,
        out: &mut Vec<(TermId, String)>,
    ) {
        let Some(td) = self.manager.get(concat_term) else {
            return;
        };
        if !matches!(td.kind, TermKind::StrConcat(_, _)) {
            return;
        }
        let Some(Val::Str(target)) = self.eval(target_term, 0) else {
            return;
        };
        let mut ops: Vec<TermId> = Vec::new();
        self.flatten_concat(concat_term, &mut ops);
        self.plan_split(&ops, &target, out);
    }

    /// Flatten a `str.++` tree into a left-to-right operand list.
    fn flatten_concat(&self, term: TermId, ops: &mut Vec<TermId>) {
        // Explicit stack, right operand pushed first so the pops yield the
        // operands left to right – same shape and same reason as
        // `Self::const_string`.
        let mut worklist = vec![term];
        while let Some(current) = worklist.pop() {
            match self.manager.get(current).map(|t| &t.kind) {
                Some(TermKind::StrConcat(a, b)) => {
                    worklist.push(*b);
                    worklist.push(*a);
                }
                _ => ops.push(current),
            }
        }
    }

    /// Given the operands of a concatenation and the target string, determine
    /// each operand's length (from a known value or an exact length equality)
    /// and, when at most one operand length is left free, assign every unknown
    /// variable operand its positional slice.
    fn plan_split(&self, ops: &[TermId], target: &str, out: &mut Vec<(TermId, String)>) {
        let target_chars: Vec<char> = target.chars().collect();
        let total = target_chars.len() as i64;

        // Determine each operand's known value (if any) and known length.
        let mut known_val: Vec<Option<String>> = Vec::with_capacity(ops.len());
        let mut known_len: Vec<Option<i64>> = Vec::with_capacity(ops.len());
        for &op in ops {
            let val = match self.eval(op, 0) {
                Some(Val::Str(s)) => Some(s),
                _ => None,
            };
            let len = match &val {
                Some(s) => Some(s.chars().count() as i64),
                None => self.len_eq.get(&op).copied(),
            };
            known_val.push(val);
            known_len.push(len);
        }

        // Identify operands whose length is still unknown.
        let free_idx: Vec<usize> = (0..ops.len()).filter(|&i| known_len[i].is_none()).collect();
        let mut lens: Vec<i64> = known_len.iter().map(|l| l.unwrap_or(0)).collect();
        match free_idx.as_slice() {
            [] => {
                let sum: i64 = lens.iter().sum();
                if sum != total {
                    return; // length conflict – refuted elsewhere
                }
            }
            [only] => {
                let sum_known: i64 = known_len.iter().flatten().sum();
                let remaining = total - sum_known;
                if remaining < 0 {
                    return;
                }
                lens[*only] = remaining;
            }
            _ => return, // too underdetermined to split
        }

        // Slice the target positionally and emit assignments for variable
        // operands whose value is not yet known.
        let mut pos: i64 = 0;
        for (i, &op) in ops.iter().enumerate() {
            let len = lens[i];
            if len < 0 || pos + len > total {
                return;
            }
            let seg: String = target_chars[pos as usize..(pos + len) as usize]
                .iter()
                .collect();
            match &known_val[i] {
                Some(existing) => {
                    if existing != &seg {
                        return; // inconsistent placement – this split cannot hold
                    }
                }
                None => {
                    if self.is_string_var(op) && !self.model.contains_key(&op) {
                        out.push((op, seg));
                    }
                }
            }
            pos += len;
        }
    }

    /// Construct a witness for a single variable from its intersected regular
    /// constraints (memberships + prefix/suffix/contains) subject to its length
    /// window, using the derivative-automaton shortest-word search.
    fn solve_regular(&self, var: TermId) -> Option<String> {
        let mut parts: Vec<Arc<Regex>> = Vec::new();
        if let Some(ms) = self.memberships.get(&var) {
            for (re, positive) in ms {
                if *positive {
                    parts.push(re.clone());
                } else {
                    parts.push(Regex::complement(re.clone()));
                }
            }
        }
        let combined = Regex::inter(parts);

        let lo = self.len_lo.get(&var).copied().unwrap_or(0).max(0) as usize;
        let hi = self.len_hi.get(&var).and_then(|h| {
            if *h < 0 {
                Some(0usize) // upper bound below zero: unsatisfiable window
            } else {
                (*h).to_usize()
            }
        });
        if let Some(h) = hi
            && lo > h
        {
            return None;
        }

        match search_word(&combined, lo, hi, MAX_REGEX_STATES, MAX_REGEX_WORD_LEN) {
            WordSearch::Found(w) => Some(w),
            WordSearch::Empty | WordSearch::Unknown => None,
        }
    }

    // ========  ========
    // Verification
    // ========  ========

    /// Verify the constructed model by concretely evaluating every assertion.
    fn verify(&self) -> bool {
        for &a in self.assertions {
            match self.eval(a, 0) {
                Some(Val::Bool(true)) => {}
                _ => return false,
            }
        }
        true
    }
}

/// Which inequality relation an atom encodes.
#[derive(Clone, Copy)]
enum IneqKind {
    Ge,
    Gt,
    Le,
    Lt,
}

/// SMT-LIB `str.to_int`: the numeric value of an all-digit non-empty string,
/// else `-1`.
///
/// Spec: the result is the base-10 value of `s` when `s` is a **non-empty**
/// word over the digits `0`–`9` (leading zeros allowed, so `"007"` is `7`), and
/// `-1` for every other string. "Every other string" notably includes `""`, any
/// string with a sign character (`"-7"` is `-1`, not `-7`), whitespace, and any
/// non-ASCII digit.
fn str_to_int(s: &str) -> BigInt {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return BigInt::from(-1);
    }
    s.parse::<BigInt>().unwrap_or_else(|_| BigInt::from(-1))
}

/// SMT-LIB `str.from_int` (a.k.a. `int.to.str`): the decimal string of a
/// non-negative integer, else the empty string.
///
/// Spec: for `n ≥ 0` the unique digit word denoting `n` with no leading zeros
/// (so `0` maps to `"0"`); for `n < 0` the empty string.
fn int_to_str(n: &BigInt) -> String {
    if *n < BigInt::from(0) {
        String::new()
    } else {
        n.to_string()
    }
}

/// Clamp an arbitrary-precision string index into `i64`, saturating at the
/// bounds.
///
/// Every index-consuming string operator treats "below `0`" and "at or past the
/// end" identically, and no in-memory string can be `i64::MAX` code points
/// long, so saturating is not an approximation here: an index that does not fit
/// in `i64` is out of range for *any* concrete string, exactly as `i64::MIN` /
/// `i64::MAX` are. Returning `None` instead would needlessly degrade a decidable
/// ground term to `Unknown`.
fn saturating_index(n: &BigInt) -> i64 {
    match n.to_i64() {
        Some(v) => v,
        None if n.sign() == Sign::Minus => i64::MIN,
        None => i64::MAX,
    }
}

/// Push every immediate sub-term of `kind` onto `out` (used to discover all
/// string variables). Traverses through every compound kind that can carry a
/// string sub-term; leaves without children push nothing.
fn push_children(kind: &TermKind, out: &mut Vec<TermId>) {
    match kind {
        TermKind::Not(a)
        | TermKind::Neg(a)
        | TermKind::StrLen(a)
        | TermKind::StrToInt(a)
        | TermKind::IntToStr(a)
        | TermKind::StrToCode(a)
        | TermKind::StrFromCode(a) => out.push(*a),
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::StrConcat(a, b)
        | TermKind::StrContains(a, b)
        | TermKind::StrPrefixOf(a, b)
        | TermKind::StrSuffixOf(a, b)
        | TermKind::StrInRe(a, b)
        | TermKind::StrAt(a, b)
        | TermKind::StrLt(a, b)
        | TermKind::StrLe(a, b)
        | TermKind::Select(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::Ite(a, b, c)
        | TermKind::StrSubstr(a, b, c)
        | TermKind::StrIndexOf(a, b, c)
        | TermKind::StrReplace(a, b, c)
        | TermKind::StrReplaceAll(a, b, c)
        | TermKind::StrReplaceRe(a, b, c)
        | TermKind::StrReplaceReAll(a, b, c)
        | TermKind::Store(a, b, c) => {
            out.push(*a);
            out.push(*b);
            out.push(*c);
        }
        TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::Distinct(args) => out.extend(args.iter().copied()),
        TermKind::Apply { args, .. } | TermKind::DtConstructor { args, .. } => {
            out.extend(args.iter().copied())
        }
        TermKind::DtTester { arg, .. } | TermKind::DtSelector { arg, .. } => out.push(*arg),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_core::smtlib::{Command, parse_script};

    /// Parse a whole SMT-LIB2 script, returning the manager and asserted terms.
    fn parse_asserts(src: &str) -> (TermManager, Vec<TermId>) {
        let mut m = TermManager::new();
        let cmds = parse_script(src, &mut m).expect("script parses");
        let mut asserts = Vec::new();
        for cmd in cmds {
            match cmd {
                Command::Assert(t) | Command::AssertNamed(t, _) => asserts.push(t),
                _ => {}
            }
        }
        (m, asserts)
    }

    fn solve(src: &str) -> GroundStringOutcome {
        let (m, asserts) = parse_asserts(src);
        solve_ground_string(&m, &asserts)
    }

    #[test]
    fn concat_with_pinned_operands() {
        let out = solve(
            r#"(declare-const x String)
               (declare-const y String)
               (assert (= (str.++ x y) "hello"))
               (assert (= x "hel"))
               (assert (= y "lo"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    #[test]
    fn concat_split_by_lengths() {
        let out = solve(
            r#"(declare-const s String)
               (declare-const t String)
               (assert (= (str.len s) 5))
               (assert (= (str.len t) 3))
               (assert (= (str.++ s t) "worldfoo"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    #[test]
    fn contains_prefix_length() {
        let out = solve(
            r#"(declare-const s String)
               (assert (str.contains s "test"))
               (assert (str.prefixof "my" s))
               (assert (>= (str.len s) 6))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    #[test]
    fn suffix_contains_upper_bound() {
        let out = solve(
            r#"(declare-const text String)
               (assert (str.suffixof ".txt" text))
               (assert (str.contains text "file"))
               (assert (<= (str.len text) 15))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    #[test]
    fn replace_pinned() {
        let out = solve(
            r#"(declare-const input String)
               (declare-const output String)
               (assert (= output (str.replace input "old" "new")))
               (assert (= input "the old way"))
               (assert (= output "the new way"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    #[test]
    fn regex_digit_suffix_prefix_length() {
        let out = solve(
            r#"(declare-const phone String)
               (assert (str.in_re phone (re.++ (re.* re.allchar) (re.++ (re.range "0" "9") (re.++ (re.range "0" "9") (re.range "0" "9"))))))
               (assert (= (str.len phone) 10))
               (assert (str.prefixof "call" phone))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    #[test]
    fn regex_lowercase_range_contains() {
        let out = solve(
            r#"(declare-const word String)
               (assert (str.in_re word (re.++ (re.range "a" "z") (re.++ (re.range "a" "z") (re.++ (re.range "a" "z") (re.* (re.range "a" "z")))))))
               (assert (>= (str.len word) 3))
               (assert (<= (str.len word) 8))
               (assert (str.contains word "test"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    #[test]
    fn unsat_length_conflict_is_unknown_here() {
        // This procedure never reports Unsat; a length conflict just fails to
        // build a verified model.
        let out = solve(
            r#"(declare-const x String)
               (assert (= (str.len x) 10))
               (assert (= x "short"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Unknown);
    }

    #[test]
    fn empty_pattern_replace_semantics() {
        // str.replace (first) with empty pattern prepends the replacement.
        let out = solve(
            r#"(declare-const r String)
               (assert (= r (str.replace "abc" "" "X")))
               (assert (= r "Xabc"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
        // The wrong reading (unchanged) must NOT verify.
        let bad = solve(
            r#"(declare-const r String)
               (assert (= r (str.replace "abc" "" "X")))
               (assert (= r "abc"))"#,
        );
        assert_eq!(bad, GroundStringOutcome::Unknown);
        // str.replace_all with empty pattern leaves the string unchanged.
        let all = solve(
            r#"(declare-const r String)
               (assert (= r (str.replace_all "abc" "" "X")))
               (assert (= r "abc"))"#,
        );
        assert_eq!(all, GroundStringOutcome::Sat);
    }

    #[test]
    fn contradiction_does_not_verify() {
        // (= s "abc") ∧ (str.contains s "xyz") is unsatisfiable – the ground
        // solver must not fabricate a Sat witness for it.
        let out = solve(
            r#"(declare-const s String)
               (assert (= s "abc"))
               (assert (str.contains s "xyz"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Unknown);
    }

    #[test]
    fn negated_membership_builds_witness() {
        // Not a "cat" but length 3 over {a..z}: some 3-letter word that is not
        // exactly "cat" is a valid witness.
        let out = solve(
            r#"(declare-const w String)
               (assert (not (str.in_re w (str.to_re "cat"))))
               (assert (str.in_re w (re.++ (re.range "a" "z") (re.++ (re.range "a" "z") (re.range "a" "z")))))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);
    }

    /// Issue #23: a disequality is the one constraint the construction phase
    /// does not gather, so an otherwise unconstrained variable defaults to `""`
    /// – exactly the value such a formula forbids.  The repair search must
    /// re-pick it instead of conceding `Unknown`.
    #[test]
    fn disequality_repairs_the_default_empty_witness() {
        // "b" != s0 ++ "b" holds for every s0 except "".
        let out = solve(
            r#"(declare-const s0 String)
               (assert (distinct "b" (str.++ s0 "b")))"#,
        );
        assert_eq!(out, GroundStringOutcome::Sat);

        // Two independently free variables.
        let two = solve(
            r#"(declare-const a String)
               (declare-const b String)
               (assert (distinct (str.++ a "x") (str.++ b "x")))"#,
        );
        assert_eq!(two, GroundStringOutcome::Sat);

        // The repair search verifies every candidate against the whole formula,
        // so an unsatisfiable disequality is still not certified.
        let unsat = solve(
            r#"(declare-const s String)
               (assert (= s "abc"))
               (assert (distinct s "abc"))"#,
        );
        assert_eq!(unsat, GroundStringOutcome::Unknown);

        // Nor may repair paper over a contradiction that involves a free
        // variable: no value of s makes `s ++ "b"` both equal and unequal.
        let contradiction = solve(
            r#"(declare-const s String)
               (assert (= (str.++ s "b") "ab"))
               (assert (distinct (str.++ s "b") "ab"))"#,
        );
        assert_eq!(contradiction, GroundStringOutcome::Unknown);
    }

    /// The repaired witness really is a model: `(get-value ...)`-style
    /// inspection of the returned assignment must show a non-default value.
    #[test]
    fn repaired_witness_is_returned_to_the_caller() {
        let (m, asserts) = parse_asserts(
            r#"(declare-const s0 String)
               (assert (distinct "b" (str.++ s0 "b")))"#,
        );
        let model = solve_ground_string_model(&m, &asserts).expect("a witness is certified");
        let (_, value) = model.first().expect("the witness assigns s0");
        assert!(!value.is_empty(), "witness must not be the empty string");
    }

    // ========  ========
    // Ground evaluation (`eval_ground_bool`) – the refutation direction.
    // ========  ========

    /// Evaluate the single assertion of `src` as a closed formula.
    fn ground(src: &str) -> Option<bool> {
        let (m, asserts) = parse_asserts(src);
        let term = *asserts.first().expect("one assertion");
        eval_ground_bool(&m, term)
    }

    /// `str.substr`: SMT-LIB gives the empty string for a start index below `0`
    /// or at/past the end, and for a length `≤ 0`; otherwise `min(n, |s| - m)`
    /// characters from `m`.
    #[test]
    fn ground_eval_substr_matches_smtlib() {
        assert_eq!(
            ground(r#"(assert (= (str.substr "abcde" 1 3) "bcd"))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.substr "abcde" 3 99) "de"))"#),
            Some(true)
        );
        // Issue #23's shape: start == |s|.
        assert_eq!(
            ground(r#"(assert (= (str.substr "aba" 3 1) ""))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.substr "aba" 7 1) ""))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.substr "abc" (- 1) 2) ""))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.substr "abc" 1 (- 2)) ""))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.substr "abc" 1 0) ""))"#),
            Some(true)
        );
        assert_eq!(ground(r#"(assert (= (str.substr "" 0 1) ""))"#), Some(true));
        // …and the negation of each true fact is decided `false`, not unknown.
        assert_eq!(
            ground(r#"(assert (not (= (str.substr "aba" 3 1) "")))"#),
            Some(false)
        );
    }

    /// A length near `i64::MAX` must not overflow the `i + l` clamp, and an
    /// index too large for `i64` is simply out of range.
    #[test]
    fn ground_eval_substr_extreme_indices() {
        assert_eq!(
            ground(r#"(assert (= (str.substr "abc" 1 9223372036854775807) "bc"))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.substr "abc" 92233720368547758070 1) ""))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.substr "abc" (- 92233720368547758070) 1) ""))"#),
            Some(true)
        );
        assert_eq!(saturating_index(&BigInt::from(7)), 7);
        assert!(saturating_index(&(BigInt::from(i64::MAX) * 4)) == i64::MAX);
        assert!(saturating_index(&(BigInt::from(i64::MIN) * 4)) == i64::MIN);
    }

    /// `str.at s i` is `str.substr s i 1`, so an out-of-range index is `""`.
    #[test]
    fn ground_eval_at_matches_smtlib() {
        assert_eq!(ground(r#"(assert (= (str.at "abc" 1) "b"))"#), Some(true));
        assert_eq!(ground(r#"(assert (= (str.at "abc" 3) ""))"#), Some(true));
        assert_eq!(
            ground(r#"(assert (= (str.at "abc" (- 1)) ""))"#),
            Some(true)
        );
    }

    /// `str.indexof s t m`: smallest occurrence at or after `m`, `-1` when
    /// `m ∉ [0, |s|]` or `t` does not occur.  The empty needle occurs at every
    /// position, so the answer is `m` itself – including `m = |s|`.
    #[test]
    fn ground_eval_indexof_matches_smtlib() {
        assert_eq!(
            ground(r#"(assert (= (str.indexof "abcabc" "abc" 0) 0))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.indexof "abcabc" "abc" 1) 3))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.indexof "abc" "z" 0) (- 1)))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.indexof "abc" "" 2) 2))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.indexof "abc" "" 3) 3))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.indexof "abc" "" 4) (- 1)))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.indexof "abc" "a" (- 1)) (- 1)))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.indexof "ab" "abc" 0) (- 1)))"#),
            Some(true)
        );
    }

    /// `str.to_int` is `-1` for anything that is not a non-empty digit word –
    /// including a leading sign – while leading zeros are fine.
    /// `str.from_int` is `""` for negatives and has no leading zeros.
    #[test]
    fn ground_eval_int_conversions_match_smtlib() {
        assert_eq!(ground(r#"(assert (= (str.to_int "42") 42))"#), Some(true));
        assert_eq!(ground(r#"(assert (= (str.to_int "0042") 42))"#), Some(true));
        assert_eq!(ground(r#"(assert (= (str.to_int "") (- 1)))"#), Some(true));
        assert_eq!(
            ground(r#"(assert (= (str.to_int "12a") (- 1)))"#),
            Some(true)
        );
        assert_eq!(
            ground(r#"(assert (= (str.to_int "-7") (- 1)))"#),
            Some(true)
        );
        assert_eq!(ground(r#"(assert (= (str.from_int 42) "42"))"#), Some(true));
        assert_eq!(ground(r#"(assert (= (str.from_int 0) "0"))"#), Some(true));
        assert_eq!(
            ground(r#"(assert (= (str.from_int (- 3)) ""))"#),
            Some(true)
        );
        assert_eq!(ground(r#"(assert (= (int.to.str 7) "7"))"#), Some(true));
    }

    /// A `distinct` is refuted as soon as *two* operands are known equal, even
    /// when a third operand is an unassigned variable.
    #[test]
    fn ground_eval_distinct_short_circuits_on_a_known_pair() {
        assert_eq!(
            ground(
                r#"(declare-const s String)
                   (assert (distinct (str.substr "aba" 3 1) "" s))"#
            ),
            Some(false)
        );
        // With no known-equal pair the presence of a variable is undecidable.
        assert_eq!(
            ground(
                r#"(declare-const s String)
                   (assert (distinct "a" "b" s))"#
            ),
            None
        );
    }

    /// A variable anywhere in the term makes the evaluation undecided – the
    /// empty model must never invent a value.
    #[test]
    fn ground_eval_declines_open_terms() {
        assert_eq!(
            ground(
                r#"(declare-const s String)
                   (assert (= (str.len s) 3))"#
            ),
            None
        );
        assert_eq!(
            ground(
                r#"(declare-const s String)
                   (assert (str.contains s "a"))"#
            ),
            None
        );
        // Three-valued short-circuiting still decides a conjunction with one
        // definitely-false ground conjunct.
        assert_eq!(
            ground(
                r#"(declare-const s String)
                   (assert (and (= s "a") (= (str.len "ab") 3)))"#
            ),
            Some(false)
        );
        // …but not one whose only ground conjunct is true.
        assert_eq!(
            ground(
                r#"(declare-const s String)
                   (assert (and (= s "a") (= (str.len "ab") 2)))"#
            ),
            None
        );
    }
}
