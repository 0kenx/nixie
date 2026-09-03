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
use num_bigint::BigInt;
use num_rational::BigRational;
use oxiz_core::ast::{
    CachedEvaluator, Model as CertificateModel, ModelValue, TermId, TermKind, TermManager,
};
use oxiz_sat::{Lit, Solver as SatSolver, SolverResult as SatResult};

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
        if std::env::var("OXIZ_CERT_DEBUG").is_ok() {
            for (&term, value) in certificate.assignments() {
                eprintln!(
                    "[cert] {:?} -> {value:?}",
                    manager.get(term).map(|t| &t.kind)
                );
            }
        }
        for (i, &assertion) in self.certificate_assertions.iter().enumerate() {
            #[cfg(feature = "std")]
            if std::env::var("OXIZ_CERT_DEBUG").is_ok() {
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
        use oxiz_core::ast::traversal::get_children;
        use oxiz_core::sort::SortKind;

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
                (oxiz_core::interner::Spur, smallvec::SmallVec<[TermId; 4]>),
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
        use oxiz_core::ast::traversal::get_children;
        use oxiz_core::interner::Spur;

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
    fn certify_unsat(&self, manager: &TermManager) -> Result<(), String> {
        let mut checker = BooleanLratChecker::new();
        checker.assert_all(&self.certificate_assertions, manager)?;
        checker.verify_unsat()
    }

    #[cfg(not(feature = "std"))]
    fn certify_unsat(&self, _manager: &TermManager) -> Result<(), String> {
        Err("certified Unsat checking requires the std feature".to_string())
    }
}

/// Convert the solver's term-valued model into the exact, deliberately small
/// model format consumed by `oxiz-core`'s independent AST validator.
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
        let config = oxiz_sat::SolverConfig {
            enable_inprocessing: false,
            ..oxiz_sat::SolverConfig::default()
        };
        let solver = SatSolver::with_config(config);
        Self {
            solver,
            clauses: Vec::new(),
            encoded: FxHashMap::default(),
        }
    }

    fn assert_all(&mut self, assertions: &[TermId], manager: &TermManager) -> Result<(), String> {
        for &assertion in assertions {
            let lit = self.encode(assertion, manager)?;
            self.buffer_clause([lit]);
        }
        Ok(())
    }

    /// Full, polarity-independent Tseitin encoding driven by an explicit heap
    /// stack. Each node is emitted only after all children have their literals.
    fn encode(&mut self, root: TermId, manager: &TermManager) -> Result<Lit, String> {
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
        let clause: Vec<Lit> = lits.into_iter().collect();
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

    fn verify_unsat(mut self) -> Result<(), String> {
        let transcript = self.solver.enable_lrat_transcript();
        for clause in core::mem::take(&mut self.clauses) {
            if !self.solver.add_clause(clause) {
                return Err(
                    "canonical CNF became inconsistent while registering original clauses"
                        .to_string(),
                );
            }
        }
        match self.solver.solve() {
            SatResult::Unsat => {}
            SatResult::Sat => {
                return Err(
                    "independent propositional checker found the asserted formula satisfiable"
                        .to_string(),
                );
            }
            SatResult::Unknown => {
                return Err("independent propositional checker returned Unknown".to_string());
            }
        }
        self.solver.flush_proof();
        let transcript = transcript
            .snapshot()
            .map_err(|error| format!("could not read complete LRAT transcript: {error}"))?;
        let report = oxiz_proof::lrat_check::check_lrat_proof(
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::ast::TermKind;

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
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let zero = manager.mk_int(0);
        let lt = manager.intern_term(TermKind::Lt(x, zero), manager.sorts.bool_sort);
        let ge = manager.intern_term(TermKind::Ge(x, zero), manager.sorts.bool_sort);
        let assertion = manager.mk_and([lt, ge]);
        let mut solver = certified_solver();
        solver.assert(assertion, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Unknown);
        assert!(
            solver
                .certification_failure()
                .is_some_and(|reason| reason.contains("satisfiable"))
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
                .is_some_and(|reason| reason.contains("satisfiable"))
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
                .is_some_and(|reason| reason.contains("satisfiable"))
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
            .verify_unsat()
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
                .verify_unsat()
                .is_err_and(|reason| reason.contains("satisfiable")),
            "the consistent truth-table row must remain satisfiable"
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
