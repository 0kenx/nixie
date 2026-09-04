//! Independent result certification at the public solver exit gate.
//!
//! `Sat` is accepted only when a concrete model evaluates every active,
//! original assertion to `true`. `Unsat` is accepted only for the fragment
//! whose propositional skeleton is refutable without theory semantics, after a
//! fresh canonical Tseitin encoding is refuted and the resulting LRAT
//! transcript is checked. Unsupported or incomplete certificates fail closed
//! to `Unknown`.

use super::Solver;
use super::types::{CertificationMode, Model, SolverResult};
use crate::prelude::*;
use nixie_core::ast::{
    CachedEvaluator, Model as CertificateModel, ModelValue, TermId, TermKind, TermManager,
};
use nixie_sat::{Lit, Solver as SatSolver, SolverResult as SatResult};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

impl Solver {
    /// Apply the configured result certificate policy to a raw solver result.
    pub(super) fn certify_result(
        &mut self,
        raw_result: SolverResult,
        manager: &mut TermManager,
    ) -> SolverResult {
        self.certification_failure = None;
        if self.config.certification_mode != CertificationMode::Certified {
            return raw_result;
        }

        let checked = match raw_result {
            SolverResult::Sat => self.certify_sat(manager),
            SolverResult::Unsat => self.certify_unsat(manager),
            SolverResult::Unknown => return SolverResult::Unknown,
        };

        match checked {
            Ok(()) => raw_result,
            Err(reason) => {
                self.certification_failure = Some(reason);
                self.model = None;
                self.unsat_core = None;
                SolverResult::Unknown
            }
        }
    }

    /// Check a concrete witness against the original active assertion DAG.
    fn certify_sat(&self, manager: &TermManager) -> Result<(), String> {
        let model = self
            .model
            .as_ref()
            .ok_or_else(|| "candidate Sat verdict did not include a model".to_string())?;
        let mut certificate = certificate_model(model, manager);
        self.complete_uninterpreted_witnesses(&mut certificate, manager);
        let mut evaluator = CachedEvaluator::new(manager, &certificate);
        #[cfg(feature = "std")]
        if std::env::var("NIXIE_CERT_DEBUG").is_ok() {
            for (&term, value) in certificate.assignments() {
                eprintln!(
                    "[cert] {:?} -> {value:?}",
                    manager.get(term).map(|t| &t.kind)
                );
            }
        }
        for (i, &assertion) in self.certificate_assertions.iter().enumerate() {
            #[cfg(feature = "std")]
            if std::env::var("NIXIE_CERT_DEBUG").is_ok() {
                eprintln!("[cert] assertion {i} = {:?}", evaluator.eval(assertion));
            }
            match evaluator.validate_assertion(assertion) {
                Ok(true) => {}
                Ok(false) => {
                    return Err("candidate model falsifies an active assertion".to_string());
                }
                Err(error) => {
                    return Err(format!(
                        "candidate model could not be completely checked: {error}"
                    ));
                }
            }
        }
        // A per-application lookup table is a genuine first-order structure
        // only if it is well-defined: equal argument values must map to
        // equal results. The EUF congruence classes used to *propose* the
        // witness values satisfy this by construction; the check below
        // verifies it independently, so the certificate never trusts the
        // theory solver's class assignment (a broken closure can only make
        // certification fail, never pass).
        self.check_application_congruence(&mut evaluator, manager)
    }

    /// Complete the certificate with abstract witnesses for reachable
    /// terms of uninterpreted sorts.
    ///
    /// The candidate is built by a small, independent **congruence closure**
    /// over the reachable ground terms:
    ///
    /// * seed unions from the EUF congruence classes (pure candidate — a
    ///   wrong class can only fail certification, never pass it),
    /// * union both sides of equalities the assertions guarantee true
    ///   (top level and through `and` conjuncts — an equality under `or`,
    ///   `not` or `ite` is not known true and is deliberately skipped),
    /// * close under congruence: applications of one function whose
    ///   arguments are class-equal are unioned, to fixpoint.
    ///
    /// One witness index is then allocated per class root. This repairs the
    /// coverage hole where the solver satisfied an application equality at
    /// the SAT level without an EUF merge (e.g. `f` applied to an
    /// `ite`-over-uninterpreted-sort term the E-graph never interned): the
    /// asserted-equality seed unions it directly.
    ///
    /// The closure is *candidate construction only* — the assertion
    /// evaluation and [`Self::check_application_congruence`] verify the
    /// result; an unsound closure can only make certification fail.
    fn complete_uninterpreted_witnesses(
        &self,
        certificate: &mut CertificateModel,
        manager: &TermManager,
    ) {
        use nixie_core::ast::traversal::get_children;
        use nixie_core::sort::SortKind;

        // ---- 1. collect reachable terms (deterministic walk order) ----
        let mut terms: Vec<TermId> = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.certificate_assertions.clone();
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            let Some(term) = manager.get(id) else {
                continue;
            };
            terms.push(id);
            for child in get_children(&term.kind) {
                stack.push(child);
            }
        }

        let is_uninterpreted = |id: TermId| -> bool {
            manager
                .get(id)
                .and_then(|t| manager.sorts.get(t.sort))
                .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
        };

        // ---- 2. union-find over the uninterpreted-sorted terms ----
        // Parent map; a term absent from the map is its own root.
        let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();
        fn find(parent: &mut FxHashMap<TermId, TermId>, x: TermId) -> TermId {
            let mut root = x;
            while let Some(&p) = parent.get(&root)
                && p != root
            {
                root = p;
            }
            // Path compression.
            let mut cur = x;
            while let Some(&p) = parent.get(&cur)
                && p != root
            {
                parent.insert(cur, root);
                cur = p;
            }
            root
        }
        let union = |parent: &mut FxHashMap<TermId, TermId>, a: TermId, b: TermId| {
            let (ra, rb) = (find(parent, a), find(parent, b));
            if ra != rb {
                // Deterministic root choice: the larger TermId wins.
                let (keep, redirect) = if ra > rb { (ra, rb) } else { (rb, ra) };
                parent.insert(redirect, keep);
                parent.entry(keep).or_insert(keep);
            }
        };

        // Register every uninterpreted-sorted constant and application so
        // later lookups find them.
        for &id in &terms {
            if let Some(term) = manager.get(id)
                && matches!(term.kind, TermKind::Var(_) | TermKind::Apply { .. })
                && is_uninterpreted(id)
            {
                parent.entry(id).or_insert(id);
            }
        }

        // Seed 1: EUF congruence classes (rep -> first member seen).
        let mut euf_reps: FxHashMap<u32, TermId> = FxHashMap::default();
        for &id in &terms {
            if parent.contains_key(&id)
                && let Some(rep) = self.euf_class_representative(id)
                && let Some(&first) = euf_reps.get(&rep)
            {
                union(&mut parent, id, first);
            } else if parent.contains_key(&id) {
                if let Some(rep) = self.euf_class_representative(id) {
                    euf_reps.insert(rep, id);
                }
            }
        }

        // Seed 2: equalities the assertions guarantee true — the roots
        // themselves and, recursively, the conjuncts of top-level `and`s.
        // An equality anywhere else (`or`, `not`, `ite`, …) is not known
        // true; skipping it can only lose coverage, never soundness.
        let mut guarantee_stack: Vec<TermId> = self.certificate_assertions.clone();
        while let Some(id) = guarantee_stack.pop() {
            let Some(term) = manager.get(id) else {
                continue;
            };
            match &term.kind {
                TermKind::And(args) => {
                    for &arg in args.iter() {
                        guarantee_stack.push(arg);
                    }
                }
                TermKind::Eq(lhs, rhs)
                    if is_uninterpreted(*lhs)
                        && is_uninterpreted(*rhs)
                        && parent.contains_key(lhs)
                        && parent.contains_key(rhs) =>
                {
                    union(&mut parent, *lhs, *rhs);
                }
                _ => {}
            }
        }

        // Seed 3 / fixpoint: congruence — applications of one function
        // with class-equal argument tuples are unioned. Iterate until no
        // union fires (each pass is O(applies); the fixpoint is bounded by
        // the class count).
        let mut applications: Vec<TermId> = Vec::new();
        for &id in &terms {
            if let Some(term) = manager.get(id)
                && matches!(term.kind, TermKind::Apply { .. })
                && parent.contains_key(&id)
            {
                applications.push(id);
            }
        }
        loop {
            let mut changed = false;
            // signature -> one member seen with it
            let mut sigs: FxHashMap<
                (nixie_core::interner::Spur, smallvec::SmallVec<[TermId; 4]>),
                TermId,
            > = FxHashMap::default();
            for &app in &applications {
                let Some(TermKind::Apply { func, args }) = manager.get(app).map(|t| &t.kind) else {
                    continue;
                };
                let mut key: smallvec::SmallVec<[TermId; 4]> = smallvec::SmallVec::new();
                for &arg in args.iter() {
                    key.push(find(&mut parent, arg));
                }
                match sigs.entry((*func, key)) {
                    std::collections::hash_map::Entry::Occupied(first) => {
                        let first = *first.get();
                        let before_a = find(&mut parent, app);
                        let before_b = find(&mut parent, first);
                        if before_a != before_b {
                            union(&mut parent, app, first);
                            changed = true;
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(slot) => {
                        slot.insert(app);
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // ---- 3. allocate one witness per class root ----
        let mut witness_index: FxHashMap<TermId, u64> = FxHashMap::default();
        for &id in &terms {
            if let Some(term) = manager.get(id)
                && matches!(term.kind, TermKind::Var(_) | TermKind::Apply { .. })
                && is_uninterpreted(id)
            {
                let root = find(&mut parent, id);
                let next = witness_index.len() as u64;
                let index = *witness_index.entry(root).or_insert(next);
                let sort = manager.get(id).map_or(term.sort, |t| t.sort);
                certificate.assign_uninterpreted(id, sort, index);
            }
        }
    }

    /// Independent well-definedness check for the certificate's function
    /// table: over every `Apply` term reachable from the assertions that
    /// fully evaluates, group by (function, argument values) and require a
    /// single result value. An application that does not evaluate played
    /// no role in the checked verdict (the Boolean fold short-circuits
    /// past unevaluated subterms), so skipping it is sound.
    ///
    /// Values are keyed by their exact `Debug` form — for the `ModelValue`
    /// variants this is injective (each variant is prefixed distinctly and
    /// the payloads print exactly), so equal keys mean equal values and the
    /// grouping is exact.
    fn check_application_congruence(
        &self,
        evaluator: &mut CachedEvaluator<'_>,
        manager: &TermManager,
    ) -> Result<(), String> {
        use nixie_core::ast::traversal::get_children;
        use nixie_core::interner::Spur;

        let mut table: FxHashMap<(Spur, String), String> = FxHashMap::default();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.certificate_assertions.clone();
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            let Some(term) = manager.get(id) else {
                continue;
            };
            if let TermKind::Apply { func, args } = &term.kind {
                let mut arg_key = String::new();
                let mut complete = true;
                for &arg in args.iter() {
                    match evaluator.eval(arg) {
                        Some(value) => {
                            arg_key.push_str(&format!("{value:?};"));
                        }
                        None => {
                            complete = false;
                            break;
                        }
                    }
                }
                // The application's own value is part of the same
                // completeness requirement: without it the term could not
                // have contributed to any checked assertion.
                if complete && let Some(result) = evaluator.eval(id) {
                    let result_key = format!("{result:?}");
                    match table.entry((*func, arg_key)) {
                        std::collections::hash_map::Entry::Occupied(existing) => {
                            if *existing.get() != result_key {
                                return Err(
                                    "candidate function interpretation is not well-defined: congruent arguments map to different values".to_string(),
                                );
                            }
                        }
                        std::collections::hash_map::Entry::Vacant(slot) => {
                            slot.insert(result_key);
                        }
                    }
                }
            }
            for child in get_children(&term.kind) {
                stack.push(child);
            }
        }
        Ok(())
    }

    /// Check an LRAT-backed canonical refutation of the original assertions.
    #[cfg(feature = "std")]
    fn certify_unsat(&self, manager: &mut TermManager) -> Result<(), String> {
        let mut checker = BooleanLratChecker::new();
        checker.assert_all(&self.certificate_assertions, manager)?;
        // Independently verified EUF theory lemmas recorded during the
        // search (proof-carrying: nothing is trusted until each lemma
        // passes the congruence-closure check inside `assert_euf_lemmas`).
        if !self.derived_reasons.lemma_log_poisoned
            && !self.derived_reasons.theory_lemmas.is_empty()
        {
            let skipped = checker.assert_euf_lemmas(&self.derived_reasons.theory_lemmas, manager);
            #[cfg(feature = "std")]
            if skipped > 0 && std::env::var("NIXIE_CERT_DEBUG").is_ok() {
                eprintln!(
                    "[cert] {} of {} recorded lemmas skipped (outside verifier fragments)",
                    skipped,
                    self.derived_reasons.theory_lemmas.len()
                );
            }
        }
        checker.verify_unsat(&self.certificate_assertions, manager)
    }

    #[cfg(not(feature = "std"))]
    fn certify_unsat(&self, _manager: &mut TermManager) -> Result<(), String> {
        Err("certified Unsat checking requires the std feature".to_string())
    }
}

/// Convert the solver's term-valued model into the exact, deliberately small
/// model format consumed by `nixie-core`'s independent AST validator.
///
/// Unsupported values are omitted rather than guessed. If a reachable
/// assertion needs one, the evaluator reports that it could not completely
/// check the witness and certified mode returns `Unknown`.
fn certificate_model(model: &Model, manager: &TermManager) -> CertificateModel {
    let mut certificate = CertificateModel::new();
    for (&term, &value_term) in model.assignments() {
        let Some(value) = concrete_value(value_term, model, manager) else {
            continue;
        };
        match value {
            ModelValue::Bool(value) => certificate.assign_bool(term, value),
            ModelValue::Int(value) => certificate.assign_int(term, value),
            ModelValue::Real(value) => certificate.assign_real(term, value),
            ModelValue::BitVec { value, width } => {
                certificate.assign_bitvec_big(term, value, width);
            }
            ModelValue::Uninterpreted { sort, id } => {
                certificate.assign_uninterpreted(term, sort, id);
            }
        }
    }
    certificate
}

/// Decode a concrete value term, following model aliases with a hard bound.
fn concrete_value(
    mut value_term: TermId,
    model: &Model,
    manager: &TermManager,
) -> Option<ModelValue> {
    for _ in 0..=model.size() {
        let term = manager.get(value_term)?;
        return match &term.kind {
            TermKind::True => Some(ModelValue::Bool(true)),
            TermKind::False => Some(ModelValue::Bool(false)),
            TermKind::IntConst(value) => Some(ModelValue::Int(value.clone())),
            TermKind::RealConst(value) => Some(ModelValue::Real(BigRational::new(
                BigInt::from(*value.numer()),
                BigInt::from(*value.denom()),
            ))),
            TermKind::BitVecConst { value, width } if *width != 0 => {
                Some(ModelValue::from_bitvec_int(value, *width))
            }
            TermKind::Var(_) => {
                value_term = model.get(value_term)?;
                continue;
            }
            _ => None,
        };
    }
    None
}

/// Small, independent propositional translation and LRAT checking kernel.
///
/// It intentionally does not consume the main SMT encoder's clauses. A bug in
/// that encoder therefore cannot make a raw false-`Unsat` pass this gate. The
/// Boolean structure is explicit and exhaustive below. Any other Boolean term
/// is conservatively abstracted as an independent atom. This is a relaxation:
/// if the abstraction is UNSAT then the original SMT formula is UNSAT too; if
/// theory semantics are needed to derive the contradiction, the abstraction
/// is SAT and the public result fails closed to `Unknown`.
#[cfg(feature = "std")]
struct BooleanLratChecker {
    solver: SatSolver,
    clauses: Vec<Vec<Lit>>,
    encoded: FxHashMap<TermId, Lit>,
}

#[cfg(feature = "std")]
impl BooleanLratChecker {
    fn new() -> Self {
        let config = nixie_sat::SolverConfig {
            enable_inprocessing: false,
            ..nixie_sat::SolverConfig::default()
        };
        let solver = SatSolver::with_config(config);
        Self {
            solver,
            clauses: Vec::new(),
            encoded: FxHashMap::default(),
        }
    }

    fn assert_all(
        &mut self,
        assertions: &[TermId],
        manager: &mut TermManager,
    ) -> Result<(), String> {
        for &assertion in assertions {
            let lit = self.encode(assertion, manager)?;
            self.buffer_clause([lit]);
        }
        Ok(())
    }

    /// Full, polarity-independent Tseitin encoding driven by an explicit heap
    /// stack. Each node is emitted only after all children have their literals.
    fn encode(&mut self, root: TermId, manager: &mut TermManager) -> Result<Lit, String> {
        let mut stack = vec![(root, false)];
        while let Some((term_id, combine)) = stack.pop() {
            if self.encoded.contains_key(&term_id) {
                continue;
            }
            let term = manager
                .get(term_id)
                .ok_or_else(|| format!("missing term {term_id:?} in Boolean certificate"))?;
            if term.sort != manager.sorts.bool_sort {
                return Err(format!(
                    "certified Unsat currently supports propositional formulas; {term_id:?} is not Bool"
                ));
            }

            if !combine {
                stack.push((term_id, true));
                match &term.kind {
                    TermKind::Not(arg) => stack.push((*arg, false)),
                    TermKind::And(args) | TermKind::Or(args) => {
                        for &arg in args.iter().rev() {
                            stack.push((arg, false));
                        }
                    }
                    TermKind::Xor(lhs, rhs) | TermKind::Implies(lhs, rhs) => {
                        stack.push((*rhs, false));
                        stack.push((*lhs, false));
                    }
                    TermKind::Eq(lhs, rhs)
                        if self.is_boolean_term(*lhs, manager)
                            && self.is_boolean_term(*rhs, manager) =>
                    {
                        stack.push((*rhs, false));
                        stack.push((*lhs, false));
                    }
                    TermKind::Ite(condition, then_branch, else_branch) => {
                        stack.push((*else_branch, false));
                        stack.push((*then_branch, false));
                        stack.push((*condition, false));
                    }
                    // Variables and every non-connective Boolean term are
                    // independent atoms in the propositional relaxation.
                    TermKind::True | TermKind::False | TermKind::Var(_) | TermKind::Eq(_, _) => {}
                    _ => {}
                }
                continue;
            }

            // `Distinct` is structural, not an opaque atom: the EUF lemmas'
            // `¬Eq` literals need the link `distinct ⇒ pairwise ¬Eq`, and the
            // pair atoms are the hash-consed `Eq` terms the lemma literals
            // use, so both sides unify on one Tseitin variable.  Forward
            // direction only — sound for UNSAT certification, and exactly
            // what a refutation consumes.  Handled before the general
            // combine match because building the pair atoms interns new
            // terms (needs `&mut manager`, incompatible with the `&Term`
            // borrow inside the match).
            if combine && let TermKind::Distinct(distinct_args) = &term.kind {
                let args: Vec<TermId> = distinct_args.iter().copied().collect();
                let result = Lit::pos(self.solver.new_var());
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        let eq = manager.mk_eq(args[i], args[j]);
                        let eq_lit = self.encode(eq, manager)?;
                        self.buffer_clause([result.negate(), eq_lit.negate()]);
                    }
                }
                self.encoded.insert(term_id, result);
                continue;
            }

            let lit = match &term.kind {
                TermKind::True => {
                    let lit = Lit::pos(self.solver.new_var());
                    self.buffer_clause([lit]);
                    lit
                }
                TermKind::False => {
                    let lit = Lit::pos(self.solver.new_var());
                    self.buffer_clause([lit.negate()]);
                    lit
                }
                TermKind::Var(_) => Lit::pos(self.solver.new_var()),
                TermKind::Not(arg) => self.child(*arg)?.negate(),
                TermKind::And(args) => {
                    let result = Lit::pos(self.solver.new_var());
                    let mut reverse = Vec::with_capacity(args.len() + 1);
                    for &arg in args {
                        let arg = self.child(arg)?;
                        self.buffer_clause([result.negate(), arg]);
                        reverse.push(arg.negate());
                    }
                    reverse.push(result);
                    self.buffer_clause(reverse);
                    result
                }
                TermKind::Or(args) => {
                    let result = Lit::pos(self.solver.new_var());
                    let mut forward = Vec::with_capacity(args.len() + 1);
                    forward.push(result.negate());
                    for &arg in args {
                        let arg = self.child(arg)?;
                        forward.push(arg);
                        self.buffer_clause([arg.negate(), result]);
                    }
                    self.buffer_clause(forward);
                    result
                }
                TermKind::Xor(lhs, rhs) => {
                    let lhs = self.child(*lhs)?;
                    let rhs = self.child(*rhs)?;
                    let result = Lit::pos(self.solver.new_var());
                    self.buffer_clause([result.negate(), lhs, rhs]);
                    self.buffer_clause([result.negate(), lhs.negate(), rhs.negate()]);
                    self.buffer_clause([lhs.negate(), rhs, result]);
                    self.buffer_clause([lhs, rhs.negate(), result]);
                    result
                }
                TermKind::Implies(lhs, rhs) => {
                    let lhs = self.child(*lhs)?;
                    let rhs = self.child(*rhs)?;
                    let result = Lit::pos(self.solver.new_var());
                    self.buffer_clause([result.negate(), lhs.negate(), rhs]);
                    self.buffer_clause([lhs, result]);
                    self.buffer_clause([rhs.negate(), result]);
                    result
                }
                TermKind::Eq(lhs, rhs)
                    if self.is_boolean_term(*lhs, manager)
                        && self.is_boolean_term(*rhs, manager) =>
                {
                    let lhs = self.child(*lhs)?;
                    let rhs = self.child(*rhs)?;
                    let result = Lit::pos(self.solver.new_var());
                    self.buffer_clause([result.negate(), lhs.negate(), rhs]);
                    self.buffer_clause([result.negate(), rhs.negate(), lhs]);
                    self.buffer_clause([lhs, rhs, result]);
                    self.buffer_clause([lhs.negate(), rhs.negate(), result]);
                    result
                }
                TermKind::Ite(condition, then_branch, else_branch) => {
                    let condition = self.child(*condition)?;
                    let then_branch = self.child(*then_branch)?;
                    let else_branch = self.child(*else_branch)?;
                    let result = Lit::pos(self.solver.new_var());
                    self.buffer_clause([condition.negate(), result.negate(), then_branch]);
                    self.buffer_clause([condition.negate(), then_branch.negate(), result]);
                    self.buffer_clause([condition, result.negate(), else_branch]);
                    self.buffer_clause([condition, else_branch.negate(), result]);
                    result
                }
                // An opaque Boolean atom. Assigning it a fresh independent
                // variable removes theory constraints and therefore cannot
                // manufacture an UNSAT result.
                _ => Lit::pos(self.solver.new_var()),
            };
            self.encoded.insert(term_id, lit);
        }
        self.child(root)
    }

    /// Buffer an original clause without letting input-time unit propagation
    /// interleave derived LRAT ids with the original-clause prefix.
    ///
    /// A unit `l` is replaced by `(l or p) and (l or not p)` for a fresh `p`.
    /// The pair is exactly equivalent to `l`, contains no unit clause, and
    /// lets every original be registered before `solve` derives anything.
    fn buffer_clause(&mut self, lits: impl IntoIterator<Item = Lit>) {
        // Dedup literals and drop tautologies, matching what any CNF
        // consumer does: the Tseitin walk emits one entry per *occurrence*,
        // and an `or`/`and` term with a repeated argument term (QG-class
        // inputs have them) otherwise lands duplicate literals in the
        // canonical CNF. A tautology is trivially satisfied — dropping it
        // is sound (it never constrains).
        let mut clause: Vec<Lit> = Vec::new();
        for lit in lits {
            if clause.contains(&lit.negate()) {
                return;
            }
            if !clause.contains(&lit) {
                clause.push(lit);
            }
        }
        if let [lit] = clause.as_slice() {
            let padding = Lit::pos(self.solver.new_var());
            self.clauses.push(vec![*lit, padding]);
            self.clauses.push(vec![*lit, padding.negate()]);
        } else {
            self.clauses.push(clause);
        }
    }

    fn child(&self, term: TermId) -> Result<Lit, String> {
        self.encoded
            .get(&term)
            .copied()
            .ok_or_else(|| format!("Boolean certificate child {term:?} was not encoded"))
    }

    fn is_boolean_term(&self, term: TermId, manager: &TermManager) -> bool {
        manager
            .get(term)
            .is_some_and(|term| term.sort == manager.sorts.bool_sort)
    }

    /// Verify each recorded theory lemma independently (congruence closure
    /// or exact LP, by atom kind) and add the verified ones as clauses
    /// over the lemma atoms' Tseitin literals. Returns the number of
    /// *skipped* lemmas.
    ///
    /// A lemma that fails its verifier is **skipped, not fatal**: the
    /// verified clauses form a subset of the true constraint set, so a
    /// refutation over them is sound regardless — and a refutation the
    /// skipped lemma was needed for simply does not happen (the SAT solve
    /// finds the subset satisfiable and the certification fails closed to
    /// `unknown`). This keeps fragment gaps (disequality literals,
    /// div/mod atoms, mixed lemmas) from rejecting whole certifications
    /// whose other lemmas suffice.
    fn assert_euf_lemmas(
        &mut self,
        lemmas: &[Vec<(TermId, bool)>],
        manager: &mut TermManager,
    ) -> usize {
        let mut skipped = 0usize;
        for lemma in lemmas {
            // Route by atom kind: all-EUF atoms (equalities over
            // non-arith non-Bool operands, Bool-sorted applications) go to
            // the congruence-closure verifier; all-arithmetic atoms
            // (linear (in)equalities over Int/Real) to the LP verifier.
            // Mixed lemmas need interface reasoning (Nelson–Oppen) —
            // declined (fail closed).
            let int_sort = manager.sorts.int_sort;
            let real_sort = manager.sorts.real_sort;
            let mut euf = false;
            let mut arith = false;
            let mut unclassifiable = false;
            for &(atom, _) in lemma {
                match manager.get(atom).map(|t| &t.kind) {
                    Some(TermKind::Lt(_, _))
                    | Some(TermKind::Le(_, _))
                    | Some(TermKind::Gt(_, _))
                    | Some(TermKind::Ge(_, _)) => arith = true,
                    Some(TermKind::Eq(lhs, rhs)) => {
                        let side_arith = |x: &TermId| {
                            manager
                                .get(*x)
                                .is_some_and(|s| s.sort == int_sort || s.sort == real_sort)
                        };
                        if side_arith(lhs) || side_arith(rhs) {
                            arith = true;
                        } else {
                            euf = true;
                        }
                    }
                    Some(TermKind::Apply { .. }) => euf = true,
                    _ => unclassifiable = true,
                }
            }
            let verified = if unclassifiable || (euf && arith) {
                // Mixed lemmas need interface reasoning (Nelson–Oppen) —
                // future work; unclassifiable atoms cannot be decoded —
                // skip either way.
                false
            } else if arith {
                verify_lia_lemma(lemma, manager)
            } else {
                verify_euf_lemma(lemma, manager)
            };
            if !verified {
                skipped += 1;
                #[cfg(feature = "std")]
                if std::env::var("NIXIE_CERT_DEBUG").is_ok() {
                    for &(atom, pol) in lemma {
                        let detail = manager
                            .get(atom)
                            .map(|t| format!("{:?}", &t.kind))
                            .unwrap_or_else(|| "<missing>".to_string());
                        eprintln!("[lemma-skip] atom={atom:?} pol={pol} kind={detail}");
                    }
                }
                continue;
            }
            let mut clause: smallvec::SmallVec<[Lit; 8]> =
                smallvec::SmallVec::with_capacity(lemma.len());
            for &(atom, polarity) in lemma {
                let lit = match self.encode(atom, manager) {
                    Ok(lit) => lit,
                    // A lemma atom the encoder rejects (should not happen:
                    // the recorder only accepts Eq/Apply/comparison atoms)
                    // skips the lemma — same fail-closed semantics as a
                    // failed verification.
                    Err(_) => {
                        skipped += 1;
                        clause.clear();
                        break;
                    }
                };
                clause.push(if polarity { lit } else { lit.negate() });
            }
            if !clause.is_empty() {
                self.buffer_clause(clause);
            }
        }
        skipped
    }

    fn verify_unsat(
        mut self,
        assertions: &[TermId],
        manager: &mut TermManager,
    ) -> Result<(), String> {
        // Phase 1 — verified model blocking. Solve the Boolean
        // abstraction; for each candidate model, hand the model's *true*
        // theory atoms to the independent verifiers (congruence closure
        // / exact LP). An infeasible atom conjunction yields a blocking
        // clause that is valid by exactly that verified infeasibility —
        // the gate never adds a clause it has not itself verified. A
        // theory-consistent model (or the iteration cap) fails closed.
        // Recorded lemmas (all independently verified as well) tighten
        // the loop.
        let mut search_solver = nixie_sat::Solver::with_config(nixie_sat::SolverConfig {
            enable_inprocessing: false,
            ..nixie_sat::SolverConfig::default()
        });
        let mut all_clauses: Vec<Vec<Lit>> = Vec::with_capacity(self.clauses.len());
        for clause in core::mem::take(&mut self.clauses) {
            search_solver.add_clause(clause.iter().copied());
            all_clauses.push(clause);
        }
        let mut iterations = 0u32;
        loop {
            match search_solver.solve() {
                SatResult::Unsat => break,
                SatResult::Sat => {
                    let blocked = match self.block_theory_inconsistent_model(
                        &search_solver,
                        assertions,
                        manager,
                    ) {
                        Some(block) => block,
                        None => {
                            return Err(
                                    "independent checker found a theory-consistent model of the asserted formula"
                                        .to_string(),
                                );
                        }
                    };
                    search_solver.backtrack_to_root();
                    search_solver.add_clause(blocked.iter().copied());
                    all_clauses.push(blocked);
                    iterations += 1;
                    if iterations > 10_000 {
                        return Err("model-blocking iteration cap exceeded; refusing to certify"
                            .to_string());
                    }
                }
                SatResult::Unknown => {
                    return Err("independent propositional checker returned Unknown".to_string());
                }
            }
        }

        // Phase 2 — transcript replay. Every clause (skeleton, verified
        // recorded lemmas, verified blocking clauses) enters a fresh
        // solver as an *original* in order — the LRAT original prefix is
        // sequential, which mid-stream additions after derived clauses
        // cannot be — and the refutation is checked as usual.
        let mut proof_solver = nixie_sat::Solver::with_config(nixie_sat::SolverConfig {
            enable_inprocessing: false,
            ..nixie_sat::SolverConfig::default()
        });
        let transcript = proof_solver.enable_lrat_transcript();
        for clause in &all_clauses {
            if !proof_solver.add_clause(clause.iter().copied()) {
                return Err(
                    "canonical CNF became inconsistent while registering original clauses"
                        .to_string(),
                );
            }
        }
        match proof_solver.solve() {
            SatResult::Unsat => {}
            SatResult::Sat => {
                return Err(
                    "transcript replay disagreed with the blocking search (nondeterminism)"
                        .to_string(),
                );
            }
            SatResult::Unknown => {
                return Err("independent propositional checker returned Unknown".to_string());
            }
        }
        proof_solver.flush_proof();
        let transcript = transcript
            .snapshot()
            .map_err(|error| format!("could not read complete LRAT transcript: {error}"))?;
        // Reproduction aid (env-gated): dump the gate's CNF + proof so the
        // standalone checker and the lrat_file tool can replay exactly what
        // the in-process checker saw.
        #[cfg(feature = "std")]
        if let Ok(dir) = std::env::var("NIXIE_CERT_DUMP")
            && let Err(error) = dump_gate_transcript(&dir, &transcript)
        {
            eprintln!("[cert] transcript dump failed: {error}");
        }
        let report = nixie_proof::lrat_check::check_lrat_proof(
            &transcript.original_clauses,
            &transcript.proof,
        );
        if report.verified {
            Ok(())
        } else {
            Err(format!(
                "LRAT checker rejected the independent refutation: {}",
                report
                    .failure
                    .unwrap_or_else(|| "no rejection reason was provided".to_string())
            ))
        }
    }

    /// Try to refute a candidate model of the Boolean abstraction with
    /// the independent theory verifiers: collect the model's *true*
    /// theory atoms over the assertion DAG, hand the EUF atoms to
    /// congruence closure and the arithmetic atoms to the exact LP
    /// checker. An infeasible conjunction yields the blocking clause
    /// (negations of exactly the witnessed atoms — valid by the verified
    /// infeasibility, and it falsifies the model). `None` when neither
    /// verifier refutes the model (fail closed).
    fn block_theory_inconsistent_model(
        &self,
        solver: &nixie_sat::Solver,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> Option<Vec<Lit>> {
        use nixie_core::ast::traversal::get_children;

        let int_sort = manager.sorts.int_sort;
        let real_sort = manager.sorts.real_sort;
        let bool_sort = manager.sorts.bool_sort;

        // Collect the assertion DAG's theory-atom leaves.
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut euf_true: Vec<(TermId, bool)> = Vec::new();
        let mut arith_true: Vec<(TermId, bool)> = Vec::new();
        let mut euf_lits: Vec<Lit> = Vec::new();
        let mut arith_lits: Vec<Lit> = Vec::new();
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            let Some(term) = manager.get(id) else {
                continue;
            };
            let atom_kind = match &term.kind {
                TermKind::Eq(lhs, rhs) => {
                    let l_arith = manager
                        .get(*lhs)
                        .is_some_and(|t| t.sort == int_sort || t.sort == real_sort);
                    let r_arith = manager
                        .get(*rhs)
                        .is_some_and(|t| t.sort == int_sort || t.sort == real_sort);
                    let l_bool = manager.get(*lhs).is_some_and(|t| t.sort == bool_sort);
                    if l_bool {
                        None // Boolean iff: structural, not a theory atom
                    } else if l_arith || r_arith {
                        Some(true) // arithmetic
                    } else {
                        Some(false) // EUF
                    }
                }
                TermKind::Lt(_, _)
                | TermKind::Le(_, _)
                | TermKind::Gt(_, _)
                | TermKind::Ge(_, _) => Some(true),
                TermKind::Apply { .. } if term.sort == bool_sort => Some(false),
                _ => None,
            };
            if let Some(is_arith) = atom_kind
                && let Some(&lit) = self.encoded.get(&id)
            {
                // The model IS the full atom assignment — both polarities
                // join the check. A TRUE atom is asserted in the
                // conjunction (clause-literal polarity `false` = negative
                // literal, and the blocking clause negates it); a FALSE
                // atom contributes its negation (clause-literal polarity
                // `true` = positive literal, and the blocking clause
                // asserts it). Validity of the blocking clause is exactly
                // the verified infeasibility of this full assignment —
                // including the case where congruence derives an equality
                // the model denies.
                match solver.model_value(lit.var()) {
                    value if value.is_true() => {
                        if is_arith {
                            arith_true.push((id, false));
                            arith_lits.push(lit.negate());
                        } else {
                            euf_true.push((id, false));
                            euf_lits.push(lit.negate());
                        }
                    }
                    value if value.is_false() => {
                        if is_arith {
                            arith_true.push((id, true));
                            arith_lits.push(lit);
                        } else {
                            euf_true.push((id, true));
                            euf_lits.push(lit);
                        }
                    }
                    _ => {}
                }
            }
            for child in get_children(&term.kind) {
                stack.push(child);
            }
        }

        #[cfg(feature = "std")]
        if std::env::var("NIXIE_CERT_DEBUG").is_ok() {
            eprintln!(
                "[block] euf atoms: {} (cc: {}), arith atoms: {} (lp: {})",
                euf_true.len(),
                if euf_true.is_empty() {
                    false
                } else {
                    verify_euf_lemma(&euf_true, manager)
                },
                arith_true.len(),
                if arith_true.is_empty() {
                    false
                } else {
                    verify_lia_lemma(&arith_true, manager)
                },
            );
        }
        if !euf_true.is_empty() && verify_euf_lemma(&euf_true, manager) {
            return Some(minimize_verified_block(
                euf_true,
                euf_lits,
                manager,
                verify_euf_lemma,
            ));
        }
        if !arith_true.is_empty() && verify_lia_lemma(&arith_true, manager) {
            return Some(minimize_verified_block(
                arith_true,
                arith_lits,
                manager,
                verify_lia_lemma,
            ));
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_core::ast::TermKind;

    fn certified_solver() -> Solver {
        Solver::with_config(super::super::types::SolverConfig::balanced().certified())
    }

    #[test]
    fn certified_propositional_sat_checks_model() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let b = manager.mk_var("b", manager.sorts.bool_sort);
        let assertion = manager.mk_or([a, b]);
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Sat);
        assert_eq!(solver.certification_failure(), None);
    }

    #[test]
    fn certified_propositional_unsat_requires_valid_lrat() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let not_a = manager.mk_not(a);
        let assertion = manager.mk_and([a, not_a]);
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        let result = solver.check(&mut manager);
        assert_eq!(
            result,
            SolverResult::Unsat,
            "certification failure: {:?}",
            solver.certification_failure()
        );
        assert_eq!(solver.certification_failure(), None);
    }

    #[test]
    fn certified_false_assertion_has_valid_lrat() {
        let mut manager = TermManager::new();
        let assertion = manager.mk_false();
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
        assert_eq!(solver.certification_failure(), None);
    }

    #[test]
    fn certified_empty_goal_has_a_checked_empty_model() {
        let mut manager = TermManager::new();
        let mut solver = certified_solver();

        assert_eq!(solver.check(&mut manager), SolverResult::Sat);
        assert_eq!(solver.certification_failure(), None);
        assert!(solver.model().is_some());
    }

    #[test]
    fn certified_arithmetic_sat_checks_exact_ground_witness() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let five = manager.mk_int(5);
        let assertion = manager.mk_eq(x, five);
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Sat);
        assert_eq!(solver.certification_failure(), None);
    }

    #[test]
    fn certified_wide_bitvec_sat_checks_exact_witness() {
        let mut manager = TermManager::new();
        let bv128 = manager.sorts.bitvec(128);
        let x = manager.mk_var("x", bv128);
        let one = manager.mk_bitvec(BigInt::from(1), 128);
        let target = manager.mk_bitvec(BigInt::from(1u128 << 64) + BigInt::from(1), 128);
        let sum = manager.mk_bv_add(x, one);
        let assertion = manager.mk_eq(sum, target);
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Sat);
        assert_eq!(solver.certification_failure(), None);
    }

    #[test]
    fn theory_semantic_unsat_fails_closed() {
        // Parity infeasibility — outside the LP fragment (rational-
        // feasible) and invisible to congruence closure. (The linear
        // bound contradiction formerly used here is LP-certifiable since
        // the 2026-09 LIA lemma verifier: `certified_mode_lp_refutable_
        // unsat_accepts` in context.rs pins the accepting side.)
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let z = manager.mk_var("z", manager.sorts.int_sort);
        let two = manager.mk_int(2);
        let one = manager.mk_int(1);
        let two_y = manager.mk_mul([two, y]);
        let e1_body = manager.mk_add([two_y, one]);
        let e1 = manager.intern_term(TermKind::Eq(x, e1_body), manager.sorts.bool_sort);
        let two_z = manager.mk_mul([two, z]);
        let e2 = manager.intern_term(TermKind::Eq(x, two_z), manager.sorts.bool_sort);
        let assertion = manager.mk_and([e1, e2]);
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Unknown);
        assert!(
            solver.certification_failure().is_some(),
            "parity-only refutation must be declined, not accepted"
        );
        assert!(solver.get_unsat_core().is_none());
    }

    #[test]
    fn propositional_contradiction_over_theory_atom_is_certified() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let zero = manager.mk_int(0);
        let atom = manager.intern_term(TermKind::Lt(x, zero), manager.sorts.bool_sort);
        let not_atom = manager.mk_not(atom);
        let assertion = manager.mk_and([atom, not_atom]);
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
        assert_eq!(solver.certification_failure(), None);
    }

    #[test]
    fn untouched_assertion_ledger_tracks_push_and_pop() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let not_a = manager.mk_not(a);
        let mut solver = certified_solver();
        solver.assert(a, &mut manager);
        solver.push();
        solver.assert(not_a, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
        solver.pop();
        assert_eq!(solver.check(&mut manager), SolverResult::Sat);
        assert_eq!(solver.certificate_assertions, vec![a]);
    }

    #[test]
    fn falsified_candidate_model_fails_closed() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let false_term = manager.mk_false();
        let mut solver = certified_solver();
        solver.assert(a, &mut manager);
        let mut wrong_model = Model::new();
        wrong_model.set(a, false_term);
        solver.model = Some(wrong_model);

        assert_eq!(
            solver.certify_result(SolverResult::Sat, &mut manager),
            SolverResult::Unknown
        );
        assert!(
            solver
                .certification_failure()
                .is_some_and(|reason| reason.contains("falsifies"))
        );
        assert!(solver.model().is_none());
    }

    #[test]
    fn sat_certificate_uses_untouched_assertion_not_preprocessed_copy() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let false_term = manager.mk_false();
        let true_term = manager.mk_true();
        let mut solver = certified_solver();
        solver.assert(a, &mut manager);

        // Simulate an unsound preprocessing rewrite.  The independent ledger
        // must still contain `a`, so a model that only satisfies the corrupted
        // search assertion is rejected.
        solver.assertions[0] = true_term;
        let mut wrong_model = Model::new();
        wrong_model.set(a, false_term);
        solver.model = Some(wrong_model);

        assert_eq!(
            solver.certify_result(SolverResult::Sat, &mut manager),
            SolverResult::Unknown
        );
        assert!(
            solver
                .certification_failure()
                .is_some_and(|reason| reason.contains("falsifies"))
        );
    }

    #[test]
    fn false_unsat_candidate_fails_closed() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let mut solver = certified_solver();
        solver.assert(a, &mut manager);

        assert_eq!(
            solver.certify_result(SolverResult::Unsat, &mut manager),
            SolverResult::Unknown
        );
        assert!(
            solver
                .certification_failure()
                .is_some_and(|reason| reason.contains("consistent"))
        );
    }

    #[test]
    fn unsat_certificate_uses_untouched_assertion_not_preprocessed_copy() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let not_a = manager.mk_not(a);
        let corrupted = manager.mk_and([a, not_a]);
        let mut solver = certified_solver();
        solver.assert(a, &mut manager);

        // A contradiction manufactured by a buggy preprocessing pass must not
        // become the LRAT checker's original formula.
        solver.assertions[0] = corrupted;

        assert_eq!(
            solver.certify_result(SolverResult::Unsat, &mut manager),
            SolverResult::Unknown
        );
        assert!(
            solver
                .certification_failure()
                .is_some_and(|reason| reason.contains("consistent"))
        );
    }

    fn check_boolean_truth_case(
        manager: &mut TermManager,
        variables: &[(TermId, bool)],
        formula: TermId,
        expected: bool,
    ) {
        let mut contradictory = Vec::with_capacity(variables.len() + 1);
        for &(variable, value) in variables {
            contradictory.push(if value {
                variable
            } else {
                manager.mk_not(variable)
            });
        }
        contradictory.push(if expected {
            manager.mk_not(formula)
        } else {
            formula
        });

        let mut checker = BooleanLratChecker::new();
        checker
            .assert_all(&contradictory, manager)
            .expect("truth-table case should be in the Boolean fragment");
        checker
            .verify_unsat(&contradictory, manager)
            .expect("opposite of the truth-table value must have an LRAT refutation");

        let mut consistent = Vec::with_capacity(variables.len() + 1);
        for &(variable, value) in variables {
            consistent.push(if value {
                variable
            } else {
                manager.mk_not(variable)
            });
        }
        consistent.push(if expected {
            formula
        } else {
            manager.mk_not(formula)
        });
        let mut checker = BooleanLratChecker::new();
        checker
            .assert_all(&consistent, manager)
            .expect("truth-table case should be in the Boolean fragment");
        assert!(
            checker
                .verify_unsat(&consistent, manager)
                .is_err_and(|reason| reason.contains("consistent")),
            "the consistent truth-table row must remain unrefuted"
        );
    }

    #[test]
    fn boolean_certificate_encoder_matches_truth_tables() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let b = manager.mk_var("b", manager.sorts.bool_sort);
        let c = manager.mk_var("c", manager.sorts.bool_sort);
        let and = manager.mk_and([a, b]);
        let or = manager.mk_or([a, b]);
        let xor = manager.mk_xor(a, b);
        let implies = manager.mk_implies(a, b);
        let eq = manager.mk_eq(a, b);
        let ite = manager.mk_ite(c, a, b);

        for lhs in [false, true] {
            for rhs in [false, true] {
                let values = [(a, lhs), (b, rhs)];
                check_boolean_truth_case(&mut manager, &values, and, lhs && rhs);
                check_boolean_truth_case(&mut manager, &values, or, lhs || rhs);
                check_boolean_truth_case(&mut manager, &values, xor, lhs != rhs);
                check_boolean_truth_case(&mut manager, &values, implies, !lhs || rhs);
                check_boolean_truth_case(&mut manager, &values, eq, lhs == rhs);
                for condition in [false, true] {
                    check_boolean_truth_case(
                        &mut manager,
                        &[(a, lhs), (b, rhs), (c, condition)],
                        ite,
                        if condition { lhs } else { rhs },
                    );
                }
            }
        }
    }
}

// ======== Independent congruence-closure verification of EUF lemmas ========

/// Check that a recorded lemma — a clause whose literals are `(Eq atom,
/// literal polarity)` pairs — is a **valid** EUF consequence, by a fresh,
/// self-contained congruence closure over the lemma's ground subterm
/// closure. The clause is valid iff its negation (the conjunction of the
/// negated literals: a positive clause literal `Eq` becomes a *disequality*,
/// a negative one an *equality*) is EUF-unsatisfiable:
///
/// * equality literals (negated negative clause literals) merge their
///   operands,
/// * disequality literals (negated positive clause literals) become
///   pending,
/// * the closure runs to fixpoint (applications of one function whose
///   arguments are class-equal merge — the congruence axiom schema),
/// * the lemma verifies iff some pending pair ended up merged.
///
/// Congruence closure is complete for ground EUF, so `false` is exactly
/// "this clause is NOT a valid EUF lemma". The verifier shares no state
/// with the solver's own EUF: a bug there can only make a lemma fail
/// here, never pass.
fn verify_euf_lemma(lemma: &[(TermId, bool)], manager: &TermManager) -> bool {
    use nixie_core::ast::traversal::get_children;

    if lemma.is_empty() {
        return false;
    }

    // Ground subterm closure of every atom's operands. `ite`-over-uninterpreted
    // operands and nested applications are walked generically — no
    // assumption that the E-graph ever interned them (the addendum-7
    // candidate-bug class). Bool-sorted `Apply` atoms seed themselves (a
    // `f(x…)` atom is the equality `f(x…) = true/false`).
    let mut terms: Vec<TermId> = Vec::new();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = Vec::new();
    let true_term = manager.mk_true();
    let false_term = manager.mk_false();
    for &(atom, _polarity) in lemma {
        match manager.get(atom).map(|t| &t.kind) {
            Some(TermKind::Eq(lhs, rhs)) => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            Some(TermKind::Apply { .. }) => stack.push(atom),
            _ => return false,
        }
    }
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        let Some(term) = manager.get(id) else {
            return false;
        };
        terms.push(id);
        for child in get_children(&term.kind) {
            stack.push(child);
        }
    }

    // Union-find over the closure (a term absent from the map is its own
    // root).
    let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();
    fn find(parent: &mut FxHashMap<TermId, TermId>, x: TermId) -> TermId {
        let mut root = x;
        while let Some(&p) = parent.get(&root)
            && p != root
        {
            root = p;
        }
        let mut cur = x;
        while let Some(&p) = parent.get(&cur)
            && p != root
        {
            parent.insert(cur, root);
            cur = p;
        }
        root
    }
    fn union(parent: &mut FxHashMap<TermId, TermId>, a: TermId, b: TermId) {
        let (ra, rb) = (find(parent, a), find(parent, b));
        if ra != rb {
            let (keep, redirect) = if ra > rb { (ra, rb) } else { (rb, ra) };
            parent.insert(redirect, keep);
            parent.entry(keep).or_insert(keep);
        }
    }

    let mut pending: Vec<(TermId, TermId)> = Vec::new();
    for &(atom, polarity) in lemma {
        match manager.get(atom).map(|t| &t.kind) {
            // An `Eq` atom: positive clause literal → the negated
            // conjunction asserts the *disequality*; negative → the
            // *equality*.
            Some(TermKind::Eq(lhs, rhs)) => {
                parent.entry(*lhs).or_insert(*lhs);
                parent.entry(*rhs).or_insert(*rhs);
                if polarity {
                    pending.push((*lhs, *rhs));
                } else {
                    union(&mut parent, *lhs, *rhs);
                }
            }
            // A Bool-sorted application: `A` is the equality `A = true`,
            // so a positive clause literal negates to `A = false` (merge
            // with the false constant) and a negative to `A = true`.
            Some(TermKind::Apply { .. }) => {
                parent.entry(atom).or_insert(atom);
                if polarity {
                    union(&mut parent, atom, false_term);
                } else {
                    union(&mut parent, atom, true_term);
                }
            }
            _ => return false,
        }
    }

    // Congruence to fixpoint over the closure's applications.
    let applications: Vec<TermId> = terms
        .iter()
        .copied()
        .filter(|&id| {
            manager
                .get(id)
                .is_some_and(|t| matches!(t.kind, TermKind::Apply { .. }))
        })
        .collect();
    loop {
        let mut changed = false;
        let mut sigs: FxHashMap<
            (nixie_core::interner::Spur, smallvec::SmallVec<[TermId; 4]>),
            TermId,
        > = FxHashMap::default();
        for &app in &applications {
            let Some(TermKind::Apply { func, args }) = manager.get(app).map(|t| &t.kind) else {
                continue;
            };
            let mut key: smallvec::SmallVec<[TermId; 4]> = smallvec::SmallVec::new();
            for &arg in args.iter() {
                key.push(find(&mut parent, arg));
            }
            match sigs.entry((*func, key)) {
                std::collections::hash_map::Entry::Occupied(first) => {
                    let first = *first.get();
                    if find(&mut parent, app) != find(&mut parent, first) {
                        union(&mut parent, app, first);
                        changed = true;
                    }
                }
                std::collections::hash_map::Entry::Vacant(slot) => {
                    slot.insert(app);
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Contradiction = a pending disequality whose sides merged, OR the
    // Boolean constants merged (a Bool-sorted application forced both true
    // and false — the eq_diamond reasoning shape).
    find(&mut parent, true_term) == find(&mut parent, false_term)
        || pending
            .iter()
            .any(|&(a, b)| find(&mut parent, a) == find(&mut parent, b))
}

/// Write the gate's CNF (original clauses, id order) and text LRAT proof
/// under `dir` for offline reproduction (see `NIXIE_CERT_DUMP`).
#[cfg(feature = "std")]
fn dump_gate_transcript(dir: &str, transcript: &nixie_sat::LratTranscript) -> std::io::Result<()> {
    use std::io::Write;
    let _ = std::fs::create_dir_all(dir);
    let max_var = transcript
        .original_clauses
        .iter()
        .flat_map(|c| c.iter().map(|l| l.unsigned_abs()))
        .max()
        .unwrap_or(0);
    let cnf = std::fs::File::create(std::path::Path::new(dir).join("gate.cnf"))?;
    let mut w = std::io::BufWriter::new(cnf);
    writeln!(w, "p cnf {max_var} {}", transcript.original_clauses.len())?;
    for clause in &transcript.original_clauses {
        for lit in clause {
            write!(w, "{lit} ")?;
        }
        writeln!(w, "0")?;
    }
    w.flush()?;
    let lrat = std::fs::File::create(std::path::Path::new(dir).join("gate.lrat"))?;
    let mut w = std::io::BufWriter::new(lrat);
    write!(w, "{}", transcript.proof)?;
    w.flush()?;
    Ok(())
}

// ======== Independent LP verification of arithmetic lemmas ========
//
// The QF_LIA analogue of `verify_euf_lemma`: a recorded lemma whose atoms
// are linear (in)equalities is valid iff its negation — the conjunction
// of the negated literals — is infeasible. Each atom decodes into an
// exact `BigRational` linear constraint over the lemma's own variables;
// strict bounds tighten over integer-valued expressions (`a < b ⟺ a ≤
// b-1`); equalities substitute away; the remaining inequalities go
// through Fourier–Motzkin elimination. A derived constant-only
// contradiction (`0 ≤ k`, `k < 0`) verifies the lemma.
//
// Completeness boundary (documented, fail-closed): rational infeasibility
// only. Integer-only infeasibility (parity/divisibility conflicts) is
// LP-feasible and returns `false` — the certification declines, never a
// wrong verdict. Disequality literals (a positive `Eq` clause literal
// negates to `≠`) make the conjunction disjunctive and are declined in
// this slice.

/// A decoded linear expression: variable coefficients plus a constant,
/// all exact rationals.
#[derive(Default, Clone)]
struct LinExpr {
    coefs: FxHashMap<TermId, BigRational>,
    constant: BigRational,
}

impl LinExpr {
    fn zero() -> Self {
        Self {
            coefs: FxHashMap::default(),
            constant: BigRational::zero(),
        }
    }

    /// Add `factor * term` — false when the term is not linear.
    fn add_term(&mut self, term: TermId, factor: &BigRational, manager: &TermManager) -> bool {
        if factor.is_zero() {
            return true;
        }
        let Some(t) = manager.get(term) else {
            return false;
        };
        match &t.kind {
            TermKind::Var(_) => {
                let slot = self.coefs.entry(term).or_insert_with(BigRational::zero);
                *slot += factor;
                if slot.is_zero() {
                    self.coefs.remove(&term);
                }
                true
            }
            TermKind::IntConst(n) => {
                self.constant += factor * BigRational::from(n.clone());
                true
            }
            TermKind::RealConst(r) => {
                self.constant +=
                    factor * BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()));
                true
            }
            TermKind::Add(args) => args.iter().all(|&a| self.add_term(a, factor, manager)),
            TermKind::Neg(arg) => {
                let neg = -factor.clone();
                self.add_term(*arg, &neg, manager)
            }
            TermKind::Sub(lhs, rhs) => {
                if !self.add_term(*lhs, factor, manager) {
                    return false;
                }
                let neg = -factor.clone();
                self.add_term(*rhs, &neg, manager)
            }
            TermKind::Mul(args) => {
                // Linear only: at most one variable operand.
                let mut const_factor = BigRational::one();
                let mut var_arg: Option<TermId> = None;
                for &arg in args.iter() {
                    let Some(a) = manager.get(arg) else {
                        return false;
                    };
                    match &a.kind {
                        TermKind::IntConst(n) => {
                            const_factor *= BigRational::from(n.clone());
                        }
                        TermKind::RealConst(r) => {
                            const_factor *= BigRational::new(
                                BigInt::from(*r.numer()),
                                BigInt::from(*r.denom()),
                            );
                        }
                        TermKind::Var(_) => {
                            if var_arg.is_some() {
                                return false; // two variables: nonlinear
                            }
                            var_arg = Some(arg);
                        }
                        _ => return false,
                    }
                }
                match var_arg {
                    Some(v) => {
                        let f = factor * &const_factor;
                        self.add_term(v, &f, manager)
                    }
                    None => {
                        self.constant += factor * &const_factor;
                        true
                    }
                }
            }
            _ => false,
        }
    }

    /// Integer-valued: every variable Int-sorted, every coefficient and
    /// the constant integral.
    fn integer_valued(&self, manager: &TermManager) -> bool {
        self.constant.denom().is_one()
            && self.coefs.iter().all(|(&var, coef)| {
                coef.denom().is_one()
                    && manager
                        .get(var)
                        .is_some_and(|t| t.sort == manager.sorts.int_sort)
            })
    }

    /// Substitute `var = rhs` (var absent from `rhs`) into the expression.
    fn substitute(&mut self, var: TermId, rhs: &LinExpr) {
        if let Some(c) = self.coefs.get(&var).cloned() {
            self.coefs.remove(&var);
            self.constant -= &c * &rhs.constant;
            for (&v2, c2) in rhs.coefs.iter() {
                let slot = self.coefs.entry(v2).or_insert_with(BigRational::zero);
                *slot += &c * c2;
                if slot.is_zero() {
                    self.coefs.remove(&v2);
                }
            }
        }
    }
}

/// Inequality direction for the LP verifier's constraints (`E ⋈ 0`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum LiaDir {
    Le,
    Ge,
}

/// Greedy deletion minimization of a verified blocking clause: drop each
/// atom in turn, keeping the drop when the remaining conjunction is still
/// verifier-infeasible. Every intermediate is re-verified, so the final
/// clause is valid by the same evidence; a small core (the transitivity
/// chain, the bound collision) blocks the whole class of models sharing
/// it instead of exactly one assignment. Probe-capped so a pathological
/// model cannot dominate.
fn minimize_verified_block(
    mut atoms: Vec<(TermId, bool)>,
    mut lits: Vec<Lit>,
    manager: &TermManager,
    verify: fn(&[(TermId, bool)], &TermManager) -> bool,
) -> Vec<Lit> {
    const PROBE_CAP: usize = 256;
    let mut probes = 0usize;
    if atoms.len() <= 4 {
        return lits;
    }
    let mut i = 0;
    while i < atoms.len() && probes < PROBE_CAP {
        let removed_atom = atoms.remove(i);
        let removed_lit = lits.remove(i);
        probes += 1;
        if !verify(&atoms, manager) {
            // The atom is load-bearing: restore it.
            atoms.insert(i, removed_atom);
            lits.insert(i, removed_lit);
            i += 1;
        }
        // Dropped: stay at index i (the next candidate shifted in).
    }
    lits
}

/// Verify an arithmetic lemma: the negated conjunction is LP-infeasible.
///
/// Disequality literals (a positive `Eq` clause literal negates to `≠`)
/// split exactly over integer-valued expressions (`t ≠ k ⟺ t ≤ k-1 ∨
/// t ≥ k+1`), so the check branches over every combination and requires
/// **all** branches infeasible (capped at 5 disequalities — 32 branches;
/// beyond that the lemma is declined).
fn verify_lia_lemma(lemma: &[(TermId, bool)], manager: &TermManager) -> bool {
    use num_traits::One;

    let int_sort = manager.sorts.int_sort;
    let real_sort = manager.sorts.real_sort;
    let arith_sort = |t: TermId| -> bool {
        manager
            .get(t)
            .is_some_and(|x| x.sort == int_sort || x.sort == real_sort)
    };

    let mut inequalities: Vec<(LinExpr, LiaDir)> = Vec::new();
    let mut equalities: Vec<LinExpr> = Vec::new();
    let mut disequalities: Vec<LinExpr> = Vec::new();

    for &(atom, polarity) in lemma {
        let Some(term) = manager.get(atom) else {
            return false;
        };
        enum Rel {
            Lt,
            Le,
            Gt,
            Ge,
            Eq,
        }
        let (rel, lhs, rhs) = match &term.kind {
            TermKind::Lt(a, b) => (Rel::Lt, *a, *b),
            TermKind::Le(a, b) => (Rel::Le, *a, *b),
            TermKind::Gt(a, b) => (Rel::Gt, *a, *b),
            TermKind::Ge(a, b) => (Rel::Ge, *a, *b),
            TermKind::Eq(a, b) => (Rel::Eq, *a, *b),
            _ => return false,
        };
        if !matches!(rel, Rel::Eq) && !arith_sort(lhs) && !arith_sort(rhs) {
            return false;
        }
        let mut expr = LinExpr::zero();
        if !expr.add_term(lhs, &BigRational::one(), manager)
            || !expr.add_term(rhs, &BigRational::from(BigInt::from(-1)), manager)
        {
            return false;
        }
        // Relation of the *asserted* literal (clause negation flips it):
        // polarity=false → the atom holds; true → its negation holds.
        let (lia_dir, strict) = match (rel, polarity) {
            (Rel::Lt, false) => (Some(LiaDir::Le), true),
            (Rel::Lt, true) => (Some(LiaDir::Ge), false),
            (Rel::Le, false) => (Some(LiaDir::Le), false),
            (Rel::Le, true) => (Some(LiaDir::Ge), true),
            (Rel::Gt, false) => (Some(LiaDir::Ge), true),
            (Rel::Gt, true) => (Some(LiaDir::Le), false),
            (Rel::Ge, false) => (Some(LiaDir::Ge), false),
            (Rel::Ge, true) => (Some(LiaDir::Le), true),
            (Rel::Eq, false) => (None, false),
            // Negates to a disequality: disjunctive, but over an
            // integer-valued expression it splits exactly into two
            // bounds — handled by branching after the decode.
            (Rel::Eq, true) => {
                if !expr.integer_valued(manager) {
                    return false;
                }
                disequalities.push(expr);
                continue;
            }
        };
        match lia_dir {
            None => equalities.push(expr),
            Some(lia_dir) => {
                if strict {
                    // `expr < 0` / `expr > 0` over an integer-valued
                    // expression tightens to `≤ -1` / `≥ +1`; anything
                    // else needs ε reasoning — decline.
                    if !expr.integer_valued(manager) {
                        return false;
                    }
                    // `E < 0` tightens to `E + 1 ≤ 0` and `E > 0` to
                    // `E - 1 ≥ 0` (the constraint form is `E ⋈ 0`).
                    match lia_dir {
                        LiaDir::Le => expr.constant += BigRational::one(),
                        LiaDir::Ge => expr.constant -= BigRational::one(),
                    }
                }
                inequalities.push((expr, lia_dir));
            }
        }
    }

    // Branch over the disequalities: every branch must be infeasible for
    // the (disjunctive) conjunction to be unsatisfiable. Capped at 5
    // disequalities (32 branches); beyond that the lemma is declined.
    if disequalities.is_empty() {
        return lia_conjunction_infeasible(equalities, inequalities);
    }
    if disequalities.len() > 5 {
        return false;
    }
    let branches = 1usize << disequalities.len();
    for branch in 0..branches {
        let mut ineqs = inequalities.clone();
        for (i, expr) in disequalities.iter().enumerate() {
            let mut e = expr.clone();
            if branch & (1 << i) == 0 {
                // `t ≠ 0` branch low: `t ≤ -1` ⟺ `(t + 1) ≤ 0`.
                e.constant += BigRational::one();
                ineqs.push((e, LiaDir::Le));
            } else {
                // branch high: `t ≥ 1` ⟺ `(t - 1) ≥ 0`.
                e.constant -= BigRational::one();
                ineqs.push((e, LiaDir::Ge));
            }
        }
        if !lia_conjunction_infeasible(equalities.clone(), ineqs) {
            return false; // this branch is feasible → conjunction satisfiable
        }
    }
    true
}

/// Substitutive equality elimination + Fourier–Motzkin over the
/// inequality set; `true` iff a constant-only contradiction is derivable.
fn lia_conjunction_infeasible(
    mut equalities: Vec<LinExpr>,
    mut inequalities: Vec<(LinExpr, LiaDir)>,
) -> bool {
    // Equalities: substitute one variable at a time.
    let mut eq_i = 0;
    while eq_i < equalities.len() {
        let Some((var, coef)) = equalities[eq_i]
            .coefs
            .iter()
            .find(|(_, c)| !c.is_zero())
            .map(|(v, c)| (*v, c.clone()))
        else {
            // Constant equality: `0 = c`.
            if !equalities[eq_i].constant.is_zero() {
                return true;
            }
            equalities.remove(eq_i);
            continue;
        };
        // var = (const - Σ others) / coef
        let mut rhs = equalities[eq_i].clone();
        rhs.coefs.remove(&var);
        rhs.constant = -&rhs.constant;
        rhs.constant /= &coef;
        for c in rhs.coefs.values_mut() {
            *c /= &coef;
        }
        equalities.remove(eq_i);
        for e in equalities.iter_mut() {
            e.substitute(var, &rhs);
        }
        for (e, _) in inequalities.iter_mut() {
            e.substitute(var, &rhs);
        }
        eq_i = 0;
    }

    // Fourier–Motzkin elimination.
    let mut guard = 0usize;
    loop {
        for (e, d) in &inequalities {
            if e.coefs.is_empty() {
                // The constraint is `E ⋈ 0` with E constant: `E ≤ 0` is
                // violated iff E > 0, `E ≥ 0` iff E < 0.
                let violated = match d {
                    LiaDir::Le => {
                        e.constant.numer().sign() == num_bigint::Sign::Plus && !e.constant.is_zero()
                    }
                    LiaDir::Ge => e.constant.numer().sign() == num_bigint::Sign::Minus,
                };
                if violated {
                    return true;
                }
            }
        }
        let Some(&var) = inequalities.iter().find_map(|(e, _)| e.coefs.keys().next()) else {
            return false; // eliminated everything without contradiction
        };
        // Split into explicit bounds `v ≤ U` / `v ≥ L` on the residual
        // (v removed, divided by |c|; the residual sign depends on the
        // arm: E = c·v + R ⋈ 0 with c > 0 gives v ⋈ -R/|c|, so the
        // direction-matching arms negate their residual).
        let negate = |mut e: LinExpr| {
            for c in e.coefs.values_mut() {
                *c = -std::mem::replace(c, BigRational::zero());
            }
            e.constant = -e.constant;
            e
        };
        let mut upper: Vec<LinExpr> = Vec::new();
        let mut lower: Vec<LinExpr> = Vec::new();
        let mut rest: Vec<(LinExpr, LiaDir)> = Vec::new();
        for (mut e, d) in inequalities.drain(..) {
            let Some(c) = e.coefs.remove(&var) else {
                rest.push((e, d));
                continue;
            };
            let abs = if c.numer().sign() == num_bigint::Sign::Minus {
                -c.clone()
            } else {
                c.clone()
            };
            for coef in e.coefs.values_mut() {
                *coef /= &abs;
            }
            e.constant /= &abs;
            let positive = c.numer().sign() == num_bigint::Sign::Plus;
            match (d, positive) {
                (LiaDir::Le, true) => upper.push(negate(e)),
                (LiaDir::Le, false) => lower.push(e),
                (LiaDir::Ge, true) => lower.push(negate(e)),
                (LiaDir::Ge, false) => upper.push(e),
            }
        }
        let mut combined: Vec<(LinExpr, LiaDir)> = rest;
        for u in &upper {
            for l in &lower {
                // `v ≤ U` and `v ≥ L` combine to `L - U ≤ 0`. (Sign errors
                // here make feasible systems derive contradictions — the
                // feasible-pair unit is the regression.)
                let mut e = l.clone();
                e.constant -= &u.constant;
                for (&v2, c2) in u.coefs.iter() {
                    let slot = e.coefs.entry(v2).or_insert_with(BigRational::zero);
                    *slot -= c2;
                    if slot.is_zero() {
                        e.coefs.remove(&v2);
                    }
                }
                combined.push((e, LiaDir::Le));
            }
        }
        inequalities = combined;
        guard += 1;
        if guard > 64 || inequalities.len() > 4096 {
            return false; // blowup guard: fail closed
        }
    }
}

#[cfg(test)]
mod euf_lemma_tests {
    use super::*;
    use nixie_core::ast::TermManager;

    fn setup() -> (TermManager, TermId, TermId, TermId, TermId, TermId) {
        // Sort S; constants a, b, c; f : S -> S.
        let mut manager = TermManager::new();
        let s_name = manager.intern_str("S");
        let s = manager
            .sorts
            .intern(nixie_core::sort::SortKind::Uninterpreted(s_name));
        let a = manager.mk_var("a", s);
        let b = manager.mk_var("b", s);
        let c = manager.mk_var("c", s);
        let f = |m: &mut TermManager, t: TermId| m.mk_apply("f", [t], s);
        let fa = f(&mut manager, a);
        let fb = f(&mut manager, b);
        (manager, a, b, c, fa, fb)
    }

    /// Congruence axiom instance `a ≠ b ∨ f(a) = f(b)` is valid.
    #[test]
    fn congruence_instance_verifies() {
        let (mut manager, a, b, _c, fa, fb) = setup();
        let eq_ab = manager.mk_eq(a, b);
        let eq_fafb = manager.mk_eq(fa, fb);
        // Clause ¬(a=b) ∨ f(a)=f(b): negated conjunction a=b ∧ f(a)≠f(b)
        // — the merge a=b congruence-merges f(a),f(b), violating the
        // pending disequality.
        let lemma = vec![(eq_ab, false), (eq_fafb, true)];
        assert!(verify_euf_lemma(&lemma, &manager));
    }

    /// The converse orientation is the same lemma.
    #[test]
    fn congruence_instance_verifies_flipped() {
        let (mut manager, a, b, _c, fa, fb) = setup();
        let eq_ab = manager.mk_eq(a, b);
        let eq_fafb = manager.mk_eq(fa, fb);
        let lemma = vec![(eq_fafb, true), (eq_ab, false)];
        assert!(verify_euf_lemma(&lemma, &manager));
    }

    /// A NON-valid lemma must be rejected: `a ≠ b ∨ f(a) = f(b)` is not an
    /// EUF consequence (f may collapse).
    #[test]
    fn non_valid_lemma_rejected() {
        let (mut manager, a, b, _c, fa, fb) = setup();
        let eq_ab = manager.mk_eq(a, b);
        let eq_fafb = manager.mk_eq(fa, fb);
        // Clause: ¬(a=b) ∨ f(a)=f(b) — NOT valid (f may collapse a≠b).
        // Negated conjunction a=b ∧ f(a)≠f(b) IS contradictory... via
        // congruence, so the flipped clause IS valid — the NON-valid one
        // is (a=b) ∨ ¬(f(a)=f(b)) without the a=b side... use a genuinely
        // invalid shape: f(a)=f(b) ∨ f(a)≠f(b) is a tautology; instead
        // take (f(a)≠f(b)) alone as a unit — not a consequence.
        let lemma = vec![(eq_fafb, false)];
        assert!(!verify_euf_lemma(&lemma, &manager));
        let _ = eq_ab;
    }

    /// Transitivity + distinct chain: `(a=b) ∨ (b=c) ∨ (a≠c)` is valid.
    #[test]
    fn transitivity_distinct_verifies() {
        let (mut manager, a, b, c, _fa, _fb) = setup();
        let eq_ab = manager.mk_eq(a, b);
        let eq_bc = manager.mk_eq(b, c);
        let eq_ac = manager.mk_eq(a, c);
        let lemma = vec![(eq_ab, false), (eq_bc, false), (eq_ac, true)];
        assert!(verify_euf_lemma(&lemma, &manager));
    }

    /// Deep congruence through an ite-over-uninterpreted-sort operand (the
    /// not-EUF-interned class): `ite(p,a,b) = a ∧ a = b ∨ f(ite) ≠ f(b)` —
    /// building the chain via the ite term.
    #[test]
    fn ite_operand_walks_generically() {
        let (mut manager, a, b, _c, _fa, _fb) = setup();
        let p = manager.mk_var("p", manager.sorts.bool_sort);
        let ite = manager.mk_ite(p, a, b);
        let s = manager_sort_s(&mut manager);
        let f_ite = manager.mk_apply("f", [ite], s);
        let f_b = manager.mk_apply("f", [b], s);
        // Clause ¬(ite=a) ∨ ¬(a=b) ∨ f(ite)≠f(b): the negated
        // conjunction ite=a ∧ a=b ∧ f(ite)≠f(b) is unsat by congruence
        // through the never-interned ite term (ite = a = b, so
        // f(ite) = f(b)).
        let lemma = vec![
            (manager.mk_eq(ite, a), false),
            (manager.mk_eq(a, b), false),
            (manager.mk_eq(f_ite, f_b), true),
        ];
        assert!(verify_euf_lemma(&lemma, &manager));
    }

    /// Bool-sorted applications as lemma atoms: `(S)->Bool` function atoms
    /// are equalities against the Boolean constants — `¬p(a) ∨ ¬p(b) ∨ a≠b`
    /// hmm, directly: clause `p(a) ∨ p(b)` with a=b... the VALID lemma is
    /// `¬p(a) ∨ p(b) ∨ a≠b` (if a=b and p(a) then p(b)). Negated
    /// conjunction: p(a) ∧ ¬p(b) ∧ a=b — congruence merges p(a),p(b), so
    /// p(a)=true and p(b)=false merge the constants.
    #[test]
    fn bool_apply_congruence_verifies() {
        let mut manager = TermManager::new();
        let s_name = manager.intern_str("S");
        let s = manager
            .sorts
            .intern(nixie_core::sort::SortKind::Uninterpreted(s_name));
        let a = manager.mk_var("a", s);
        let b = manager.mk_var("b", s);
        let pa = manager.mk_apply("p", [a], manager.sorts.bool_sort);
        let pb = manager.mk_apply("p", [b], manager.sorts.bool_sort);
        let eq_ab = manager.mk_eq(a, b);
        // Clause: ¬(a=b) ∨ ¬p(a) ∨ p(b) — entries in clause polarity.
        // Negated conjunction: a=b ∧ p(a) ∧ ¬p(b); the merge a=b
        // congruence-merges p(a),p(b), colliding true with false.
        let lemma = vec![(eq_ab, false), (pa, false), (pb, true)];
        assert!(verify_euf_lemma(&lemma, &manager));
    }

    /// Non-valid Bool-Apply lemma: `p(a) ∨ p(b)` alone (nothing forces
    /// either) must be rejected.
    #[test]
    fn bool_apply_non_valid_rejected() {
        let mut manager = TermManager::new();
        let s_name = manager.intern_str("S");
        let s = manager
            .sorts
            .intern(nixie_core::sort::SortKind::Uninterpreted(s_name));
        let a = manager.mk_var("a", s);
        let b = manager.mk_var("b", s);
        let pa = manager.mk_apply("p", [a], manager.sorts.bool_sort);
        let pb = manager.mk_apply("p", [b], manager.sorts.bool_sort);
        let lemma = vec![(pa, true), (pb, true)];
        assert!(!verify_euf_lemma(&lemma, &manager));
    }

    /// LP verifier units (see `verify_lia_lemma`). Entries are (atom,
    /// clause-literal polarity): polarity=false asserts the atom in the
    /// negated conjunction.
    fn lia_setup() -> (TermManager, TermId, TermId, TermId) {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let z = manager.mk_var("z", manager.sorts.int_sort);
        (manager, x, y, z)
    }

    #[test]
    fn lia_equal_constants_contradiction() {
        let (mut m, x, _y, _z) = lia_setup();
        let one = m.mk_int(1);
        let two = m.mk_int(2);
        let e1 = m.mk_eq(x, one);
        let e2 = m.mk_eq(x, two);
        // Clause ¬(x=1) ∨ ¬(x=2): negated conjunction x=1 ∧ x=2
        // (negative clause literals assert their atoms).
        assert!(verify_lia_lemma(&[(e1, false), (e2, false)], &m));
        // Sanity: a positive (x=1) literal negates to a disequality —
        // declined in this slice, which also fails.
        assert!(!verify_lia_lemma(&[(e1, true), (e2, false)], &m));
    }

    #[test]
    fn lia_bound_collision() {
        let (mut m, x, _y, _z) = lia_setup();
        let three = m.mk_int(3);
        let one = m.mk_int(1);
        let ge = m.mk_ge(x, three);
        let le = m.mk_le(x, one);
        // Clause ¬(x≥3) ∨ ¬(x≤1): conjunction x≥3 ∧ x≤1.
        assert!(verify_lia_lemma(&[(ge, false), (le, false)], &m));
    }

    #[test]
    fn lia_strict_integer_tightening() {
        let (mut m, x, _y, _z) = lia_setup();
        let one = m.mk_int(1);
        let lt = m.mk_lt(x, one);
        let ge = m.mk_ge(x, one);
        // Clause ¬(x<1) ∨ ¬(x≥1): conjunction x<1 ∧ x≥1 over
        // integers tightens to x≤0 ∧ x≥1.
        assert!(verify_lia_lemma(&[(lt, false), (ge, false)], &m));
    }

    #[test]
    fn lia_feasible_rejected() {
        let (mut m, x, _y, _z) = lia_setup();
        let zero = m.mk_int(0);
        let five = m.mk_int(5);
        let ge = m.mk_ge(x, zero);
        let le = m.mk_le(x, five);
        // Clause ¬(x≥0) ∨ ¬(x≤5): conjunction feasible.
        assert!(!verify_lia_lemma(&[(ge, false), (le, false)], &m));
    }

    #[test]
    fn lia_parity_boundary_declined() {
        // x = 2y+1 ∧ x = 2z is integer-infeasible but LP-feasible: the
        // documented completeness boundary — must return false (fail
        // closed), never a wrong acceptance.
        let (mut m, x, y, z) = lia_setup();
        let two = m.mk_int(2);
        let one = m.mk_int(1);
        let two_y = m.mk_mul([two, y]);
        let sum1 = m.mk_add([two_y, one]);
        let e1 = m.mk_eq(x, sum1);
        let two_z = m.mk_mul([two, z]);
        let e2 = m.mk_eq(x, two_z);
        assert!(!verify_lia_lemma(&[(e1, false), (e2, false)], &m));
    }

    #[test]
    fn lia_two_var_substitution() {
        // y ≥ x+2 ∧ x ≥ 5 ∧ y ≤ 6: substituting y: x+2 ≤ 6 ∧ x ≥ 5 —
        // feasible (x=5,y=7? y≤6 violated... x+2≤6 → x≤4 ∧ x≥5 —
        // infeasible). Conjunction: y ≥ x+2, x ≥ 5, y ≤ 6.
        let (mut m, x, y, _z) = lia_setup();
        let two2 = m.mk_int(2);
        let x_plus_2 = m.mk_add([x, two2]);
        let ge1 = m.mk_ge(y, x_plus_2);
        let five = m.mk_int(5);
        let six = m.mk_int(6);
        let ge2 = m.mk_ge(x, five);
        let le = m.mk_le(y, six);
        assert!(verify_lia_lemma(
            &[(ge1, false), (ge2, false), (le, false)],
            &m
        ));
    }

    /// Disequality literals: the conjunction `x ≠ 5 ∧ x ≤ 4 ∧ x ≥ 6` is
    /// unsatisfiable on BOTH branches of `x ≠ 5` (low: x ≤ 4 ∧ x ≤ 4;
    /// high: x ≤ 4 ∧ x ≥ 6 — infeasible), so the clause verifies.
    #[test]
    fn lia_disequality_branch_verifies() {
        let (mut m, x, _y, _z) = lia_setup();
        let five = m.mk_int(5);
        let four = m.mk_int(4);
        let six = m.mk_int(6);
        let ne = m.mk_eq(x, five); // clause literal POSITIVE → x ≠ 5
        let le = m.mk_le(x, four); // negative literal → x ≤ 4
        let ge = m.mk_ge(x, six); // negative literal → x ≥ 6
        assert!(verify_lia_lemma(
            &[(ne, true), (le, false), (ge, false)],
            &m
        ));
    }

    /// A disequality that does NOT close both branches: `x ≠ 5 ∧ x ≤ 4`
    /// is satisfiable (x = 4) — rejected.
    #[test]
    fn lia_disequality_open_branch_rejected() {
        let (mut m, x, _y, _z) = lia_setup();
        let five = m.mk_int(5);
        let four = m.mk_int(4);
        let ne = m.mk_eq(x, five);
        let le = m.mk_le(x, four);
        assert!(!verify_lia_lemma(&[(ne, true), (le, false)], &m));
    }

    /// Disequality over a non-integer-valued expression (x/2 ≠ 0) is
    /// declined — no exact integer split.
    #[test]
    fn lia_disequality_non_integral_declined() {
        let (mut m, x, _y, _z) = lia_setup();
        let zero = m.mk_int(0);
        let two = m.mk_int(2);
        let half_x = m.mk_div(x, two);
        let ne = m.mk_eq(half_x, zero);
        // Force infeasibility on both sides via x = 1 (so x/2 = 0.5,
        // satisfying ≠ 0): the lemma (¬(x/2≠0) ∨ ¬(x=1)) is NOT valid, and
        // the conjunction x/2≠0 ∧ x=1 is actually satisfiable — but the
        // disequality is non-integral so the verifier declines regardless.
        let one = m.mk_int(1);
        let e = m.mk_eq(x, one);
        assert!(!verify_lia_lemma(&[(ne, true), (e, false)], &m));
    }

    fn manager_sort_s(manager: &mut TermManager) -> nixie_core::sort::SortId {
        let s_name = manager.intern_str("S");
        manager
            .sorts
            .intern(nixie_core::sort::SortKind::Uninterpreted(s_name))
    }
}
