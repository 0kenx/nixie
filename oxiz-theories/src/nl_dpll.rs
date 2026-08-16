//! DPLL case-splitting over the Boolean structure of nonlinear-integer goals.
//!
//! The conjunction-only CAD/B&B core ([`crate::nlsat::dispatch_nia_constraints`]
//! tail) is strong on pure conjunctions but cannot see disjunctions at all.
//! Industrial QF_NIA (VeryMax ITS transition relations, AProVE termination
//! certificates) is dominated by `(or template₁ template₂ …)` goal shapes,
//! where each *template* is a small conjunction. Z3's `qfnia-nlsat` arm
//! decides exactly these by lazily splitting the disjunctions inside its
//! CDCL loop – visible as dozens of small per-case nlsat runs – and learning
//! blocking lemmas across cases.
//!
//! This module implements the same case-splitting *above* the solver: the
//! assertions' Boolean structure (`or`/`not`/`=>`/`xor`/Boolean `ite`/`=`/
//! free Boolean variables) is split DPLL-style into alternative conjunction
//! cases, and every leaf case is decided by the existing conjunction
//! CAD/B&B core (`solve_conjunction_nia`), with a per-case Gaussian
//! re-simplification pass so each branch sees the strongest linear context.
//!
//! ## Soundness contract
//!
//! * **Sat** is only reported through `solve_conjunction_nia`, which
//!   concretely verifies the witness against the *raw* assertions (with the
//!   branch's Boolean choices substituted in) before answering.
//! * **Unsat** requires *every* explored leaf case to be refuted by a
//!   trustworthy conjunction verdict under the same gates the flat path
//!   applies (complete extraction, no Real-sorted symbols, no array
//!   stores, per-case symbol budget), and the case enumeration to have
//!   covered the whole formula (budget never exhausted, every split total).
//!   A single undecided leaf demotes the whole answer to a fall-through.
//! * Anything the splitter cannot decompose faithfully (quantifiers, other
//!   theories, exotic connectives) makes the driver return `None` – never
//!   a guess.

use crate::nlsat::NlDispatchResult;
use oxiz_core::ast::{TermId, TermKind, TermManager};

/// Maximum number of explored case frames before the driver concedes.
/// Generous against Z3's observed per-goal case counts (≲ 300), small
/// enough that the driver never dominates a timeout budget.
const DPLL_CASE_BUDGET: u32 = 2_000;

/// Per-case symbol ceiling handed down to the conjunction core.
const DPLL_CAD_MAX_SYMBOLS: usize = 150;

/// Arithmetic re-sampling budget per DPLL leaf: enough for a leaf the engine
/// can decide, small enough that an undecidable leaf concedes fast (the
/// default 10 000 otherwise turns every undecided case into a multi-second
/// burn, dominating whole-goal budgets – the ps4/geo timeout regression).
const DPLL_LEAF_RESAMPLE_BUDGET: u32 = 400;

/// One alternative produced by splitting an assertion: replacement
/// assertions plus Boolean-variable choices made on this branch.
struct Alternative {
    /// Assertions replacing the split one.
    assertions: Vec<TermId>,
    /// `(bool var, chosen value)` pairs fixed by this alternative.
    bool_choices: Vec<(TermId, bool)>,
}

/// Result of splitting one structured assertion.
enum Split {
    /// The alternative branches (each must be explored).
    Alternatives(Vec<Alternative>),
    /// The assertion is provably `false`: the whole case is unsat.
    Impossible,
}

/// DPLL driver entry point. See the module docs for the soundness contract.
pub(crate) fn try_dpll_nia_case_split(
    working: &[TermId],
    raw_assertions: &[TermId],
    base_eliminations: &[(TermId, TermId)],
    manager: &mut TermManager,
    integer_mode: bool,
) -> Option<NlDispatchResult> {
    let trace = cfg!(feature = "std") && std::env::var("OXIZ_NIA_TRACE").is_ok();
    let mut budget = DPLL_CASE_BUDGET;
    let mut undecided_leaves = 0;
    let mut explored = 0u32;
    let mut stack = vec![CaseFrame {
        assertions: working.to_vec(),
        bool_choices: Vec::new(),
        eliminations: base_eliminations.to_vec(),
    }];
    let mut all_cases_refuted = true;

    while let Some(frame) = stack.pop() {
        if budget == 0 {
            // Case enumeration incomplete: cannot claim Unsat; a Sat already
            // returned above. Concede honestly.
            if trace {
                eprintln!(
                    "[nia] dpll: budget exhausted after {explored} frames (undecided_leaves={undecided_leaves})"
                );
            }
            return None;
        }
        budget -= 1;
        explored += 1;

        // Substitute the branch's Boolean choices, then re-run the Gaussian
        // preamble on this case: disjunct values often enable further
        // defining-equality eliminations.
        let mut case = frame.assertions.clone();
        if !frame.bool_choices.is_empty() {
            let sub = bool_subst_map(&frame.bool_choices, manager);
            case = case.iter().map(|&a| manager.substitute(a, &sub)).collect();
        }
        let gauss = crate::nl_preprocess::gaussian_eliminate(&case, manager);
        let false_id = manager.mk_false();
        if gauss.conjuncts.contains(&false_id) {
            continue; // branch refuted at level 0
        }
        let mut eliminations = frame.eliminations.clone();
        if gauss.changed {
            case = gauss.conjuncts.clone();
            eliminations.extend(gauss.eliminations.iter().copied());
        }

        // Find the first assertion still carrying Boolean structure.
        let split_idx = case.iter().position(|&a| has_boolean_structure(a, manager));
        let Some(split_idx) = split_idx else {
            // Leaf: a pure conjunction. Hand it to the CAD/B&B core with the
            // per-case trust gates.
            match solve_leaf(
                &case,
                raw_assertions,
                &frame.bool_choices,
                &eliminations,
                manager,
                integer_mode,
            ) {
                LeafVerdict::Sat(result) => return Some(result),
                LeafVerdict::Unsat => continue,
                LeafVerdict::Undecided => {
                    all_cases_refuted = false;
                    undecided_leaves += 1;
                    continue;
                }
            }
        };

        let Some(split_result) = split_assertion(case[split_idx], manager) else {
            // An un-splittable connective keeps the enumeration honest only
            // if we stop claiming full coverage: concede (fall through).
            if trace {
                eprintln!("[nia] dpll: split bail (unhandled connective)");
            }
            return None;
        };
        match split_result {
            Split::Impossible => continue,
            Split::Alternatives(alts) => {
                for alt in alts.into_iter().rev() {
                    let mut next = case.clone();
                    next.remove(split_idx);
                    next.extend(alt.assertions);
                    let mut bool_choices = frame.bool_choices.clone();
                    bool_choices.extend(alt.bool_choices);
                    stack.push(CaseFrame {
                        assertions: next,
                        bool_choices,
                        eliminations: eliminations.clone(),
                    });
                }
            }
        }
    }

    if trace {
        eprintln!(
            "[nia] dpll: done after {explored} frames: all_refuted={all_cases_refuted} undecided_leaves={undecided_leaves}"
        );
    }
    if all_cases_refuted {
        Some(NlDispatchResult::Unsat)
    } else {
        None
    }
}

/// Verdict of one solved leaf case.
enum LeafVerdict {
    Sat(NlDispatchResult),
    Unsat,
    Undecided,
}

/// Solve one conjunction leaf with the flat path's trust gates, applied
/// per-case.
fn solve_leaf(
    case: &[TermId],
    raw_assertions: &[TermId],
    bool_choices: &[(TermId, bool)],
    eliminations: &[(TermId, TermId)],
    manager: &mut TermManager,
    integer_mode: bool,
) -> LeafVerdict {
    // Per-case symbol budget: mirrors the flat path's CAD gate.
    if crate::nlsat::count_arith_symbols_pub(case, manager) > DPLL_CAD_MAX_SYMBOLS {
        return LeafVerdict::Undecided;
    }
    let has_unsupported_ops = case
        .iter()
        .any(|&a| crate::nlsat::contains_non_polynomial_ops_pub(a, manager));
    let has_array_stores = crate::ania_ground::assertions_contain_store(case, manager);
    let has_real_symbols = case
        .iter()
        .any(|&a| crate::nlsat::assertions_have_real_symbols_pub(a, manager));

    // Model verification runs against the raw assertions with this branch's
    // Boolean choices substituted, so free Booleans evaluate under the very
    // values this case fixed.
    let verify_against: Vec<TermId> = if bool_choices.is_empty() {
        raw_assertions.to_vec()
    } else {
        let sub = bool_subst_map(bool_choices, manager);
        raw_assertions
            .iter()
            .map(|&a| manager.substitute(a, &sub))
            .collect()
    };

    let result = crate::nlsat::solve_conjunction_nia_pub(
        case,
        &verify_against,
        eliminations,
        manager,
        integer_mode,
        has_unsupported_ops,
        has_array_stores,
        has_real_symbols,
        DPLL_LEAF_RESAMPLE_BUDGET,
    );
    match result {
        Some(NlDispatchResult::Unsat) => LeafVerdict::Unsat,
        Some(sat @ NlDispatchResult::Sat(_)) => LeafVerdict::Sat(sat),
        None => LeafVerdict::Undecided,
    }
}

/// One DPLL branch: the pending assertion list plus the Boolean choices and
/// Gaussian eliminations accumulated along the path.
struct CaseFrame {
    assertions: Vec<TermId>,
    bool_choices: Vec<(TermId, bool)>,
    eliminations: Vec<(TermId, TermId)>,
}

fn bool_subst_map(
    choices: &[(TermId, bool)],
    manager: &mut TermManager,
) -> rustc_hash::FxHashMap<TermId, TermId> {
    let mut sub = rustc_hash::FxHashMap::default();
    for &(term, value) in choices {
        sub.insert(
            term,
            if value {
                manager.mk_true()
            } else {
                manager.mk_false()
            },
        );
    }
    sub
}

/// Whether the term carries Boolean structure beyond conjunctions (same
/// shape test the dispatcher uses).
fn has_boolean_structure(term: TermId, manager: &TermManager) -> bool {
    crate::nlsat::has_boolean_structure_pub(&[term], manager)
}

/// Split one structured assertion into alternative branches. `None` means
/// the structure is outside the fragment this driver decomposes faithfully.
fn split_assertion(term: TermId, manager: &mut TermManager) -> Option<Split> {
    let node = manager.get(term)?;
    let kind = node.kind.clone();
    let bool_sort = manager.sorts.bool_sort;
    let is_bool = |t: TermId, m: &TermManager| m.get(t).is_some_and(|n| n.sort == bool_sort);
    match &kind {
        TermKind::True => Some(Split::Alternatives(vec![Alternative {
            assertions: vec![],
            bool_choices: vec![],
        }])),
        TermKind::False => Some(Split::Impossible),
        // An asserted Boolean variable is simply TRUE: substitute it.  (The
        // term is an *assertion* here, not an existential choice – offering a
        // `b = false` branch would explore cases the formula does not have,
        // and was the source of the 2^k free-Boolean case explosion on
        // VeryMax goals whose Tseitin spurs survive the Gaussian pass.)
        TermKind::Var(_) if node.sort == bool_sort => {
            Some(Split::Alternatives(vec![Alternative {
                assertions: vec![],
                bool_choices: vec![(term, true)],
            }]))
        }
        TermKind::Or(args) => Some(Split::Alternatives(
            args.iter()
                .map(|&a| Alternative {
                    assertions: vec![a],
                    bool_choices: vec![],
                })
                .collect(),
        )),
        TermKind::And(args) => Some(Split::Alternatives(vec![Alternative {
            assertions: args.to_vec(),
            bool_choices: vec![],
        }])),
        TermKind::Implies(a, b) => Some(Split::Alternatives(vec![
            Alternative {
                assertions: vec![manager.mk_not(*a)],
                bool_choices: vec![],
            },
            Alternative {
                assertions: vec![*b],
                bool_choices: vec![],
            },
        ])),
        TermKind::Ite(c, t, e) if node.sort == bool_sort => Some(Split::Alternatives(vec![
            Alternative {
                assertions: vec![*c, *t],
                bool_choices: vec![],
            },
            Alternative {
                assertions: vec![manager.mk_not(*c), *e],
                bool_choices: vec![],
            },
        ])),
        TermKind::Xor(a, b) => {
            let not_b = manager.mk_not(*b);
            let not_a = manager.mk_not(*a);
            Some(Split::Alternatives(vec![
                Alternative {
                    assertions: vec![*a, not_b],
                    bool_choices: vec![],
                },
                Alternative {
                    assertions: vec![not_a, *b],
                    bool_choices: vec![],
                },
            ]))
        }
        TermKind::Eq(a, b) if is_bool(*a, manager) && is_bool(*b, manager) => {
            let not_a = manager.mk_not(*a);
            let not_b = manager.mk_not(*b);
            Some(Split::Alternatives(vec![
                Alternative {
                    assertions: vec![*a, *b],
                    bool_choices: vec![],
                },
                Alternative {
                    assertions: vec![not_a, not_b],
                    bool_choices: vec![],
                },
            ]))
        }
        // Arithmetic equality without Boolean sides stays a leaf atom.
        TermKind::Eq(..) => None,
        TermKind::Distinct(args) => {
            let all_bool = args.iter().all(|&a| is_bool(a, manager));
            let none_bool = args.iter().all(|&a| !is_bool(a, manager));
            if none_bool && args.len() == 2 {
                // distinct a b ≡ ¬(a = b): a single negated-Eq leaf.
                let eq = manager.mk_eq(args[0], args[1]);
                let not_eq = manager.mk_not(eq);
                Some(Split::Alternatives(vec![Alternative {
                    assertions: vec![not_eq],
                    bool_choices: vec![],
                }]))
            } else if none_bool {
                // Pairwise ¬Eq leaves (a single conjunction alternative).
                let mut leaves = Vec::new();
                for i in 0..args.len() {
                    for j in 0..i {
                        let eq = manager.mk_eq(args[i], args[j]);
                        leaves.push(manager.mk_not(eq));
                    }
                }
                Some(Split::Alternatives(vec![Alternative {
                    assertions: leaves,
                    bool_choices: vec![],
                }]))
            } else if all_bool && args.len() == 2 {
                let not_b = manager.mk_not(args[1]);
                let not_a = manager.mk_not(args[0]);
                Some(Split::Alternatives(vec![
                    Alternative {
                        assertions: vec![args[0], not_b],
                        bool_choices: vec![],
                    },
                    Alternative {
                        assertions: vec![not_a, args[1]],
                        bool_choices: vec![],
                    },
                ]))
            } else {
                // Mixed or >2 Boolean arguments: the partition lattice of
                // "all different" has too many cases to enumerate soundly
                // here; leave it to the CNF engine.
                None
            }
        }
        TermKind::Not(x) => {
            let inner = manager.get(*x)?;
            let inner_kind = inner.kind.clone();
            match &inner_kind {
                TermKind::True => Some(Split::Impossible),
                TermKind::False => Some(Split::Alternatives(vec![Alternative {
                    assertions: vec![],
                    bool_choices: vec![],
                }])),
                TermKind::Var(_) if inner.sort == bool_sort => {
                    Some(Split::Alternatives(vec![Alternative {
                        assertions: vec![],
                        bool_choices: vec![(*x, false)],
                    }]))
                }
                TermKind::And(args) => Some(Split::Alternatives(
                    args.iter()
                        .map(|&a| Alternative {
                            assertions: vec![manager.mk_not(a)],
                            bool_choices: vec![],
                        })
                        .collect(),
                )),
                TermKind::Or(args) => {
                    let all: Vec<TermId> = args.iter().map(|&a| manager.mk_not(a)).collect();
                    Some(Split::Alternatives(vec![Alternative {
                        assertions: all,
                        bool_choices: vec![],
                    }]))
                }
                TermKind::Implies(a, b) => {
                    let not_b = manager.mk_not(*b);
                    Some(Split::Alternatives(vec![Alternative {
                        assertions: vec![*a, not_b],
                        bool_choices: vec![],
                    }]))
                }
                // ¬ite(c,t,e) ≡ (c ∧ ¬t) ∨ (¬c ∧ ¬e)
                TermKind::Ite(c, t, e) if inner.sort == bool_sort => {
                    let not_t = manager.mk_not(*t);
                    let not_c = manager.mk_not(*c);
                    let not_e = manager.mk_not(*e);
                    Some(Split::Alternatives(vec![
                        Alternative {
                            assertions: vec![*c, not_t],
                            bool_choices: vec![],
                        },
                        Alternative {
                            assertions: vec![not_c, not_e],
                            bool_choices: vec![],
                        },
                    ]))
                }
                // ¬(a ⊕ b) ≡ (a ∧ b) ∨ (¬a ∧ ¬b)
                TermKind::Xor(a, b) => {
                    let not_a = manager.mk_not(*a);
                    let not_b = manager.mk_not(*b);
                    Some(Split::Alternatives(vec![
                        Alternative {
                            assertions: vec![*a, *b],
                            bool_choices: vec![],
                        },
                        Alternative {
                            assertions: vec![not_a, not_b],
                            bool_choices: vec![],
                        },
                    ]))
                }
                // ¬(a = b) over Booleans ≡ xor.
                TermKind::Eq(a, b) if is_bool(*a, manager) && is_bool(*b, manager) => {
                    let not_b = manager.mk_not(*b);
                    let not_a = manager.mk_not(*a);
                    Some(Split::Alternatives(vec![
                        Alternative {
                            assertions: vec![*a, not_b],
                            bool_choices: vec![],
                        },
                        Alternative {
                            assertions: vec![not_a, *b],
                            bool_choices: vec![],
                        },
                    ]))
                }
                // ¬(arithmetic comparison / arith equality / distinct-2):
                // already a leaf the conjunction core handles natively.
                TermKind::Lt(..)
                | TermKind::Le(..)
                | TermKind::Gt(..)
                | TermKind::Ge(..)
                | TermKind::Eq(..)
                | TermKind::Distinct(_) => Some(Split::Alternatives(vec![Alternative {
                    assertions: vec![term],
                    bool_choices: vec![],
                }])),
                _ => None,
            }
        }
        // Arithmetic comparison leaves never reach the splitter (they carry
        // no Boolean structure); anything else is outside the fragment.
        _ => None,
    }
}
