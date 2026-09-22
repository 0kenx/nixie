//! CP declarations -> independently checked leaves -> canonical CNF -> LRAT.
//! The search engine and its clause log are untrusted proof producers.
use super::*;
use nixie_theories::cp::proof::CpStatement;

/// A finite-graph implication naming an independently supplied graph
/// statement (reachability/acyclicity path, cut or cycle lemma).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphLemma {
    /// Index in the retained graph-statement list, not a statement from
    /// the proof.
    pub declaration: usize,
    /// Signed Boolean conclusion; false represents conflict.
    pub conclusion: TermId,
    /// Signed Boolean antecedents.
    pub premises: Vec<TermId>,
}

/// A finite-domain implication naming an independently supplied CP declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpLemma {
    /// Index in the original declaration list, not a declaration from the proof.
    pub declaration: usize,
    /// Signed Boolean conclusion; false represents conflict.
    pub conclusion: TermId,
    /// Signed Boolean antecedents.
    pub premises: Vec<TermId>,
}

/// Complete CP UNSAT certificate relative to retained original inputs.
///
/// All fields are untrusted. Checking reconstructs the exact CNF from those
/// inputs and verified leaves, then checks the LRAT derivation of false.
/// No callback, SMT search, or SAT search runs in `check`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpProof {
    /// CP explanation clauses (including exactly-one domain reasoning).
    pub lemmas: Vec<CpLemma>,
    /// Graph explanation clauses (path/cut/cycle lemmas over retained
    /// graph statements — plain graph registrations and FSM products).
    pub graph_lemmas: Vec<GraphLemma>,
    /// Additional independently checked EUF/linear-arithmetic clauses.
    pub theory_lemmas: Vec<Vec<(TermId, bool)>>,
    /// Text LRAT, whose input clause IDs refer to the canonical encoding.
    pub lrat: String,
}

impl CpProof {
    /// Export the complete leaf log and LRAT in a versioned text envelope.
    /// Original inputs are deliberately external: a proof cannot choose the
    /// problem it claims to refute. Term IDs refer to that retained problem.
    pub fn to_text(&self) -> String {
        let mut text = String::from("nixie-cp-proof 2\n");
        for lemma in &self.lemmas {
            text.push_str(&format!("cp {} {}", lemma.declaration, lemma.conclusion.0));
            for premise in &lemma.premises {
                text.push_str(&format!(" {}", premise.0));
            }
            text.push('\n');
        }
        for lemma in &self.graph_lemmas {
            text.push_str(&format!(
                "graph {} {}",
                lemma.declaration, lemma.conclusion.0
            ));
            for premise in &lemma.premises {
                text.push_str(&format!(" {}", premise.0));
            }
            text.push('\n');
        }
        for lemma in &self.theory_lemmas {
            text.push_str("smt");
            for (atom, sign) in lemma {
                text.push_str(&format!(" {} {}", atom.0, u8::from(*sign)));
            }
            text.push('\n');
        }
        text.push_str("lrat\n");
        text.push_str(&self.lrat);
        text
    }

    /// Parse an untrusted envelope. Parsing does not verify the proof.
    pub fn from_text(text: &str) -> Result<Self, String> {
        let mut lines = text.split_inclusive('\n');
        // Version 1 predates graph records; version 2 adds them.
        match lines.next() {
            Some("nixie-cp-proof 1\n") | Some("nixie-cp-proof 2\n") => {}
            _ => return Err("unsupported CP proof envelope".to_string()),
        }
        let mut proof = Self {
            lemmas: Vec::new(),
            graph_lemmas: Vec::new(),
            theory_lemmas: Vec::new(),
            lrat: String::new(),
        };
        for line in lines.by_ref() {
            if line == "lrat\n" {
                proof.lrat = lines.collect();
                return Ok(proof);
            }
            let mut words = line.split_whitespace();
            match words.next() {
                Some("cp") => {
                    let declaration = words
                        .next()
                        .ok_or("missing declaration")?
                        .parse()
                        .map_err(|_| "invalid declaration")?;
                    let conclusion = TermId(
                        words
                            .next()
                            .ok_or("missing conclusion")?
                            .parse()
                            .map_err(|_| "invalid conclusion")?,
                    );
                    let mut premises = Vec::new();
                    for word in words {
                        premises.push(TermId(word.parse().map_err(|_| "invalid premise")?));
                    }
                    proof.lemmas.push(CpLemma {
                        declaration,
                        conclusion,
                        premises,
                    });
                }
                Some("graph") => {
                    let declaration = words
                        .next()
                        .ok_or("missing declaration")?
                        .parse()
                        .map_err(|_| "invalid declaration")?;
                    let conclusion = TermId(
                        words
                            .next()
                            .ok_or("missing conclusion")?
                            .parse()
                            .map_err(|_| "invalid conclusion")?,
                    );
                    let mut premises = Vec::new();
                    for word in words {
                        premises.push(TermId(word.parse().map_err(|_| "invalid premise")?));
                    }
                    proof.graph_lemmas.push(GraphLemma {
                        declaration,
                        conclusion,
                        premises,
                    });
                }
                Some("smt") => {
                    let mut lemma = Vec::new();
                    while let Some(atom) = words.next() {
                        let atom = TermId(atom.parse().map_err(|_| "invalid SMT atom")?);
                        let sign = match words.next() {
                            Some("0") => false,
                            Some("1") => true,
                            _ => return Err("invalid SMT polarity".to_string()),
                        };
                        lemma.push((atom, sign));
                    }
                    proof.theory_lemmas.push(lemma);
                }
                _ => return Err("unknown CP proof record".to_string()),
            }
        }
        Err("missing CP LRAT section".to_string())
    }

    fn encoding(
        &self,
        originals: &[CpStatement],
        graph_originals: &[nixie_theories::graph::GraphStatement],
        assertions: &[TermId],
        manager: &mut TermManager,
        mut work_limit: u64,
    ) -> Result<BooleanLratChecker, String> {
        for original in originals {
            original
                .check_encoding(manager)
                .map_err(|e| e.to_string())?;
        }
        let mut checker = BooleanLratChecker::new();
        checker.assert_all(assertions, manager)?;
        for original in originals {
            checker.assert_all(original.assertions(), manager)?;
        }
        for lemma in &self.lemmas {
            let original = originals
                .get(lemma.declaration)
                .ok_or_else(|| "unregistered CP proof declaration".to_string())?;
            original
                .check_lemma(lemma.conclusion, &lemma.premises, &mut work_limit)
                .map_err(|e| e.to_string())?;
            let mut clause = Vec::new();
            for &premise in &lemma.premises {
                clause.push(!checker.encode(premise, manager)?);
            }
            clause.push(checker.encode(lemma.conclusion, manager)?);
            checker.buffer_clause(clause);
        }
        for lemma in &self.graph_lemmas {
            let original = graph_originals
                .get(lemma.declaration)
                .ok_or_else(|| "unregistered graph proof declaration".to_string())?;
            original
                .check_lemma(lemma.conclusion, &lemma.premises)
                .map_err(|e| e.to_string())?;
            let mut clause = Vec::new();
            for &premise in &lemma.premises {
                clause.push(!checker.encode(premise, manager)?);
            }
            clause.push(checker.encode(lemma.conclusion, manager)?);
            checker.buffer_clause(clause);
        }
        if checker.assert_euf_lemmas(&self.theory_lemmas, manager) != 0 {
            return Err("invalid or unsupported SMT leaf in CP proof".to_string());
        }
        Ok(checker)
    }

    /// Verify against independently retained declarations and active assertions.
    /// The term manager must be the one that owns these original inputs.
    pub fn check(
        &self,
        originals: &[CpStatement],
        graph_originals: &[nixie_theories::graph::GraphStatement],
        assertions: &[TermId],
        manager: &mut TermManager,
        work_limit: u64,
    ) -> Result<(), String> {
        let checker = self.encoding(originals, graph_originals, assertions, manager, work_limit)?;
        let clauses = dimacs_clauses(&checker);
        let report = nixie_proof::lrat_check::check_lrat_proof(&clauses, &self.lrat);
        if report.verified {
            Ok(())
        } else {
            Err(report
                .failure
                .unwrap_or_else(|| "CP LRAT refutation rejected".to_string()))
        }
    }

    /// Reconstruct the checked input CNF for an external LRAT checker.
    /// Checking this CNF alone does not establish its connection to CP: retain
    /// the original declarations and run `check` for the complete chain.
    pub fn dimacs(
        &self,
        originals: &[CpStatement],
        graph_originals: &[nixie_theories::graph::GraphStatement],
        assertions: &[TermId],
        manager: &mut TermManager,
        work_limit: u64,
    ) -> Result<String, String> {
        use core::fmt::Write;
        let checker = self.encoding(originals, graph_originals, assertions, manager, work_limit)?;
        let mut output = format!(
            "p cnf {} {}\n",
            checker.solver.num_vars(),
            checker.clauses.len()
        );
        for clause in dimacs_clauses(&checker) {
            for lit in clause {
                write!(output, "{lit} ").map_err(|e| e.to_string())?;
            }
            output.push_str("0\n");
        }
        Ok(output)
    }
}

fn dimacs_clauses(checker: &BooleanLratChecker) -> Vec<Vec<i32>> {
    checker
        .clauses
        .iter()
        .map(|c| c.iter().map(|l| l.to_dimacs()).collect())
        .collect()
}

impl Solver {
    /// Original inputs to `CpProof::check`, kept separately from its untrusted
    /// fields. Capture at the assertion scope being checked (including assumptions).
    pub fn cp_proof_inputs(
        &self,
    ) -> (
        Vec<CpStatement>,
        Vec<nixie_theories::graph::GraphStatement>,
        Vec<TermId>,
    ) {
        (
            self.user_state.cp_originals.clone(),
            self.user_state.graph_statements.clone(),
            self.cp_user_assertions(),
        )
    }

    /// Complete checked CP refutation from the latest proof/certified check.
    /// Invalidated on assertion changes, push/pop, reset, and settings changes.
    pub fn get_cp_proof(&self) -> Option<&CpProof> {
        self.user_state.cp_proof.as_ref()
    }

    fn build_cp_proof(&self, manager: &mut TermManager) -> Result<CpProof, String> {
        let mut proof = CpProof {
            lemmas: Vec::new(),
            graph_lemmas: Vec::new(),
            theory_lemmas: Vec::new(),
            lrat: String::new(),
        };
        let mut budget = 10_000_000;
        for (conclusion, premises) in &self.user_state.proof_lemmas {
            let mut verified = None;
            for (i, original) in self.user_state.cp_originals.iter().enumerate() {
                if original
                    .check_lemma(*conclusion, premises, &mut budget)
                    .is_ok()
                {
                    verified = Some(i);
                    break;
                }
            }
            // Unchecked clauses are not admitted as inputs to LRAT. A missing
            // lemma can only make proof reconstruction fail, never prove false.
            if let Some(declaration) = verified {
                proof.lemmas.push(CpLemma {
                    declaration,
                    conclusion: *conclusion,
                    premises: premises.clone(),
                });
                continue;
            }
            // Graph path/cut/cycle lemmas check against the retained graph
            // statements (explicit closures; the propagator is untrusted).
            let mut graph_verified = None;
            for (i, original) in self.user_state.graph_statements.iter().enumerate() {
                if original.check_lemma(*conclusion, premises).is_ok() {
                    graph_verified = Some(i);
                    break;
                }
            }
            if let Some(declaration) = graph_verified {
                proof.graph_lemmas.push(GraphLemma {
                    declaration,
                    conclusion: *conclusion,
                    premises: premises.clone(),
                });
            }
        }
        if !self.derived_reasons.lemma_log_poisoned {
            for lemma in &self.derived_reasons.theory_lemmas {
                let mut checker = BooleanLratChecker::new();
                if checker.assert_euf_lemmas(core::slice::from_ref(lemma), manager) == 0 {
                    proof.theory_lemmas.push(lemma.clone());
                }
            }
        }
        let checker = proof.encoding(
            &self.user_state.cp_originals,
            &self.user_state.graph_statements,
            &self.cp_user_assertions(),
            manager,
            10_000_000,
        )?;
        // The main search may refute a mixed goal before recording all leaves
        // needed by the independent encoding. Reconstruct only verified missing
        // leaves from models of that encoding; final LRAT uses a fresh prefix.
        self.complete_cp_leaves(&mut proof, checker, manager)?;
        let checker = proof.encoding(
            &self.user_state.cp_originals,
            &self.user_state.graph_statements,
            &self.cp_user_assertions(),
            manager,
            10_000_000,
        )?;
        let expected = dimacs_clauses(&checker);
        let mut solver = SatSolver::with_config(nixie_sat::SolverConfig {
            enable_inprocessing: false,
            ..Default::default()
        });
        solver.set_max_conflicts(Some(100_000));
        let transcript = solver.enable_lrat_transcript();
        for clause in &checker.clauses {
            if !solver.add_clause(clause.iter().copied()) {
                return Err("CP canonical input registration failed".to_string());
            }
        }
        if solver.solve() != SatResult::Unsat {
            return Err("CP leaves did not produce a complete refutation".to_string());
        }
        solver.flush_proof();
        let transcript = transcript.snapshot()?;
        if transcript.original_clauses != expected {
            return Err("CP LRAT input clauses differ from canonical encoding".to_string());
        }
        proof.lrat = transcript.proof;
        proof.check(
            &self.user_state.cp_originals,
            &self.user_state.graph_statements,
            &self.cp_user_assertions(),
            manager,
            10_000_000,
        )?;
        Ok(proof)
    }

    fn complete_cp_leaves(
        &self,
        proof: &mut CpProof,
        mut checker: BooleanLratChecker,
        manager: &mut TermManager,
    ) -> Result<(), String> {
        let mut search = SatSolver::with_config(nixie_sat::SolverConfig {
            enable_inprocessing: false,
            ..Default::default()
        });
        search.set_max_conflicts(Some(100_000));
        for clause in &checker.clauses {
            search.add_clause(clause.iter().copied());
        }
        let mut budget = 10_000_000;
        for _ in 0..10_000 {
            match search.solve() {
                SatResult::Unsat => return Ok(()),
                SatResult::Unknown => return Err("CP reconstruction SAT work limit".to_string()),
                SatResult::Sat => {}
            }
            let old_len = checker.clauses.len();
            let mut cp_block = None;
            for (declaration, original) in self.user_state.cp_originals.iter().enumerate() {
                let mut premises = Vec::new();
                for atom in original.indicators() {
                    let lit = checker.child(atom)?;
                    let value = search.model_value(lit.var());
                    let positive = if value.is_true() {
                        !lit.is_neg()
                    } else if value.is_false() {
                        lit.is_neg()
                    } else {
                        return Err("incomplete CP reconstruction assignment".to_string());
                    };
                    premises.push(if positive { atom } else { manager.mk_not(atom) });
                }
                if original
                    .check_lemma(manager.mk_false(), &premises, &mut budget)
                    .is_ok()
                {
                    cp_block = Some(CpLemma {
                        declaration,
                        conclusion: manager.mk_false(),
                        premises,
                    });
                    break;
                }
            }
            if let Some(lemma) = cp_block {
                let mut clause = Vec::new();
                for &premise in &lemma.premises {
                    clause.push(!checker.encode(premise, manager)?);
                }
                clause.push(checker.encode(lemma.conclusion, manager)?);
                checker.buffer_clause(clause);
                proof.lemmas.push(lemma);
            } else {
                let block = checker
                    .block_theory_inconsistent_model(&search, &self.certification_roots(), manager)
                    .ok_or_else(|| {
                        "CP reconstruction found no checked model blocker".to_string()
                    })?;
                // Recover signed original atoms, not search-specific SAT IDs.
                let mut atoms: Vec<_> = checker.encoded.iter().collect();
                atoms.sort_unstable_by_key(|(term, _)| **term);
                let mut lemma = Vec::new();
                for lit in block {
                    let (term, encoded) = atoms
                        .iter()
                        .copied()
                        .find(|(term, encoded)| {
                            encoded.var() == lit.var()
                                && matches!(
                                    manager.get(**term).map(|t| &t.kind),
                                    Some(
                                        TermKind::Eq(..)
                                            | TermKind::Lt(..)
                                            | TermKind::Le(..)
                                            | TermKind::Gt(..)
                                            | TermKind::Ge(..)
                                            | TermKind::Apply { .. }
                                    )
                                )
                        })
                        .ok_or_else(|| "unmapped SMT reconstruction literal".to_string())?;
                    lemma.push((*term, *encoded == lit));
                }
                // Recheck the reconstructed *term* clause too: wrong polarity
                // or a bad inverse mapping must never acquire axiom authority.
                if checker.assert_euf_lemmas(core::slice::from_ref(&lemma), manager) != 0 {
                    return Err("SMT reconstruction leaf failed verification".to_string());
                }
                proof.theory_lemmas.push(lemma);
            }
            search.backtrack_to_root();
            for clause in &checker.clauses[old_len..] {
                search.add_clause(clause.iter().copied());
            }
        }
        Err("CP reconstruction model limit".to_string())
    }

    pub(in crate::solver) fn certify_cp_result(
        &mut self,
        result: SolverResult,
        manager: &mut TermManager,
    ) -> SolverResult {
        self.user_state.cp_proof = None;
        let checked = if self.user_state.unproved_callbacks != 0 {
            Err("arbitrary user callbacks have no complete proof checker".to_string())
        } else {
            match result {
                SolverResult::Sat => self.certify_sat(manager),
                SolverResult::Unsat => self.build_cp_proof(manager).map(|proof| {
                    self.user_state.cp_proof = Some(proof);
                }),
                SolverResult::Unknown => return result,
            }
        };
        match checked {
            Ok(()) => result,
            Err(reason) => {
                self.certification_failure = Some(reason);
                SolverResult::Unknown
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_theories::cp::CpModel;

    #[test]
    fn reconstructs_without_any_main_search_leaves_and_rejects_false_unsat() {
        for count in [2, 3] {
            let mut tm = TermManager::new();
            let mut cp = CpModel::new(&tm);
            let mut vars = Vec::new();
            for i in 0..count {
                let a = tm.mk_var(&format!("a{i}"), tm.sorts.bool_sort);
                let b = tm.mk_var(&format!("b{i}"), tm.sorts.bool_sort);
                match cp.variable(vec![(0.into(), a), (1.into(), b)], &mut tm) {
                    Ok(v) => vars.push(v),
                    Err(e) => panic!("invalid test input: {e}"),
                }
            }
            assert!(cp.alldifferent(vars).is_ok());
            let mut solver = Solver::new();
            assert!(solver.register_cp(cp, &mut tm).is_ok());
            assert!(solver.user_state.proof_lemmas.is_empty());
            let proof = solver.build_cp_proof(&mut tm);
            assert_eq!(proof.is_ok(), count == 3, "{proof:?}");
            // Even a forged unconditional callback conflict cannot certify the
            // satisfiable case: the finite checker rejects it before LRAT.
            if count == 2 {
                // A corrupted main-encoder ledger entry for a CP domain must
                // not become an original premise of the independent proof.
                solver.certificate_assertions[0] = tm.mk_false();
                assert!(solver.build_cp_proof(&mut tm).is_err());
                solver.user_state.proof_lemmas.push((tm.mk_false(), vec![]));
                assert!(solver.build_cp_proof(&mut tm).is_err());
            }
        }
    }
}
