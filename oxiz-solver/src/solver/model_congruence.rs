//! Congruence canonicalization of candidate `Sat` models.
//!
//! The final congruence honesty gate (`Solver::model_violates_euf_congruence`)
//! refuses a `Sat` whose model gives one function two applications with
//! model-equal arguments but differing results — such an interpretation
//! cannot exist, whatever the search did.  But many refusable candidate
//! models differ from a **real** model only in inconsequential application
//! results: the search recorded arbitrary results for applications the
//! assertions never constrained, and an arbitrary choice can collide with
//! a congruent twin (measured: `sorted_list_insert_noalloc1` — the two
//! "pinned" results `t.nxt(t.l)=1` vs `t.nxt(i1)=0` at model-equal
//! arguments are both free, verified by z3: `F ∧ (= (t.nxt t.l) (t.nxt
//! i1))` is sat AND `F ∧ distinct(...)` is sat — neither side entailed).
//!
//! [`Solver::canonicalize_model_congruence`] unifies each split group's
//! results to a representative (deterministic: majority, ties by smallest
//! TermId) as a **trial repair**, and the caller post-validates with
//! [`Solver::model_refutes_assertions`] — the same ground evaluator the
//! model-refutation gate uses.  A repair that falsifies a ground assertion
//! is discarded wholesale (original assignments restored).  The gate
//! therefore fires only when **every** congruent choice is inconsistent
//! with the assertions — the genuinely unsat-shaped candidates.

use rustc_hash::{FxHashMap, FxHashSet};

use super::Solver;
use oxiz_core::ast::{TermId, TermKind, TermManager};

/// Exact scalar model value used as a congruence key (the gate's
/// `GroundValue`, shared shape).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum GroundValue {
    Bool(bool),
    Number(num_rational::BigRational),
    BitVec {
        value: num_bigint::BigInt,
        width: u32,
    },
    String(String),
}

impl GroundValue {
    fn from_term(t: &TermKind) -> Option<Self> {
        use num_bigint::BigInt;
        use num_rational::BigRational;
        match t {
            TermKind::True => Some(Self::Bool(true)),
            TermKind::False => Some(Self::Bool(false)),
            TermKind::IntConst(v) => Some(Self::Number(BigRational::from_integer(v.clone()))),
            TermKind::RealConst(v) => Some(Self::Number(BigRational::new(
                BigInt::from(*v.numer()),
                BigInt::from(*v.denom()),
            ))),
            TermKind::BitVecConst { value, width } => Some(Self::BitVec {
                value: value.clone(),
                width: *width,
            }),
            TermKind::StringLit(v) => Some(Self::String(v.clone())),
            _ => None,
        }
    }
}

/// One application occurrence: the app term and its chased result
/// constant term.
struct Occurrence {
    app: TermId,
    result_const: TermId,
}

impl Solver {
    /// Canonicalize the current candidate model's function-application
    /// results under congruence.  Returns `true` when any assignment changed
    /// (the caller re-runs the gate; see the module doc for the contract).
    pub(super) fn canonicalize_model_congruence(&mut self, manager: &TermManager) -> bool {
        let Some(model) = self.model.as_ref() else {
            return false;
        };
        let asg = model.assignments();

        // chase: follow assignment chains to a fixed point (cycle-safe).
        let chase = |mut t: TermId| -> TermId {
            let mut seen: FxHashSet<TermId> = FxHashSet::default();
            while seen.insert(t) {
                match asg.get(&t) {
                    Some(&w) if w != t => t = w,
                    _ => break,
                }
            }
            t
        };
        let ground_of = |t: TermId| -> Option<GroundValue> {
            manager
                .get(t)
                .and_then(|td| GroundValue::from_term(&td.kind))
        };

        // Group occurrences by (function, argument ground values).
        let mut groups: FxHashMap<(u32, Vec<GroundValue>), Vec<Occurrence>> = FxHashMap::default();
        for &assertion in &self.assertions {
            let mut stack = vec![assertion];
            while let Some(st) = stack.pop() {
                let Some(t) = manager.get(st) else { continue };
                if matches!(t.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                    continue; // binder environments are not model-assigned
                }
                stack.extend(oxiz_core::ast::get_children(&t.kind));
                let TermKind::Apply { func, args } = &t.kind else {
                    continue;
                };
                let Some(key_args) = args
                    .iter()
                    .map(|&arg| ground_of(chase(arg)))
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                let chased = chase(st);
                if chased == st {
                    continue; // no recorded result
                }
                if ground_of(chased).is_none() {
                    continue; // result not a concrete constant
                }
                let key = (func.into_inner().get(), key_args);
                groups.entry(key).or_default().push(Occurrence {
                    app: st,
                    result_const: chased,
                });
            }
        }

        // Repair split groups: unify every group's results to a
        // representative (majority, ties by smallest TermId —
        // deterministic).  This is a TRIAL repair: the caller
        // post-validates against the ground assertions and discards it if
        // it falsifies any.  No pin exception: the decisive measurement
        // (sorted_list, z3 cross-check) is that recorded-but-unconstrained
        // results are search-arbitrary choices, and refusing to move them
        // restores exactly the false downgrades this pass exists to fix.
        let mut repairs: FxHashMap<TermId, TermId> = FxHashMap::default();
        for occs in groups.values() {
            if occs.len() < 2 {
                continue;
            }
            let mut counts: FxHashMap<GroundValue, (usize, TermId)> = FxHashMap::default();
            for o in occs {
                let Some(g) = ground_of(o.result_const) else {
                    continue;
                };
                let e = counts.entry(g).or_insert((0, o.result_const));
                e.0 += 1;
            }
            if counts.len() < 2 {
                continue; // already congruent
            }
            let mut winner: Option<(usize, TermId)> = None;
            for (_g, (n, rep)) in &counts {
                let take = match winner {
                    None => true,
                    Some((bw, br)) => *n > bw || (*n == bw && rep.raw() < br.raw()),
                };
                if take {
                    winner = Some((*n, *rep));
                }
            }
            let Some((_, winner_const)) = winner else {
                continue;
            };
            for o in occs {
                if o.result_const != winner_const {
                    repairs.insert(o.app, winner_const);
                }
            }
        }

        if repairs.is_empty() {
            return false;
        }
        let Some(model) = self.model.as_mut() else {
            return false;
        };
        for (app, winner) in repairs {
            model.set(app, winner);
        }
        true
    }
}
