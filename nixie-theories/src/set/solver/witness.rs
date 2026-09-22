//! Boolean-algebra witnesses with cardinality and explicit existential elements.
//! As in CVC5's set model construction, named members are supplemented with
//! fresh distinct elements. One default membership pattern represents the
//! infinitely many unnamed elements of Int/Real universes.
use super::*;
use nixie_sat::{CardinalityEncoder, Lit, Solver, SolverResult, Var};

/// A finite or cofinite set: membership defaults to `default_member`, except
/// on the explicitly listed elements. A cofinite model is never flattened
/// into a fabricated finite member list by `SetSolver::get_model`.
#[derive(Clone, Debug)]
pub struct SetModelValue {
    pub default_member: bool,
    pub exceptions: FxHashSet<u32>,
}

impl SetModelValue {
    pub fn contains(&self, element: u32) -> bool {
        self.default_member ^ self.exceptions.contains(&element)
    }
}

impl SetSolver {
    pub(super) fn search_set_witness(&mut self) -> SetResult<bool> {
        // BvSet and ElementSet do not supply the universe cardinality. Do not
        // invent an infinite supply of distinct elements for those sorts.
        if self
            .vars
            .iter()
            .any(|v| !matches!(v.sort, SetSort::IntSet | SetSort::RealSet))
        {
            return Ok(false);
        }
        let mut named = FxHashSet::default();
        let mut needed = 0i128;
        for v in &self.vars {
            named.extend(v.must_members.iter().copied());
            named.extend(v.must_not_members.iter().copied());
            if let Some(may) = &v.may_members {
                named.extend(may.iter().copied());
            }
            needed += i128::from(v.cardinality_bounds().0.max(0));
        }
        // Strict > i64::MAX cannot be rounded back into a narrow bound.
        if self
            .card_constraints
            .iter()
            .any(|c| c.kind == CardConstraintKind::Gt && c.bound == i64::MAX)
        {
            return Ok(false);
        }
        needed += self
            .relations
            .iter()
            .filter(|r| matches!(r, SetRelation::Subset(_, _, false)))
            .count() as i128;
        let limit = self.config.max_finite_card.unwrap_or(4096).min(4096);
        if needed > limit as i128 || named.len() > limit {
            return Ok(false);
        }
        let mut elements: Vec<_> = named.iter().copied().collect();
        elements.sort_unstable();
        let mut fresh = 0u32;
        let total = elements.len() + needed as usize;
        if self.vars.len().saturating_mul(total + 1) > 100_000 {
            return Ok(false);
        }
        if self.vars.len().saturating_mul(total.saturating_mul(total)) > 2_000_000 {
            return Ok(false);
        }
        while elements.len() < total {
            if !named.contains(&fresh) {
                elements.push(fresh);
            }
            let Some(next) = fresh.checked_add(1) else {
                return Ok(false);
            };
            fresh = next;
        }
        let n = elements.len();
        let mut sat = Solver::new();
        let bits: Vec<Vec<Var>> = self
            .vars
            .iter()
            .map(|_| (0..=n).map(|_| sat.new_var()).collect())
            .collect();
        for (v, row) in self.vars.iter().zip(&bits) {
            let (lo, hi) = v.cardinality_bounds();
            for (i, &element) in elements.iter().enumerate() {
                let positive = v.is_universal || v.must_members.contains(&element);
                let negative = v.is_definitely_empty()
                    || v.must_not_members.contains(&element)
                    || v.may_members
                        .as_ref()
                        .is_some_and(|may| !may.contains(&element));
                if positive {
                    sat.add_clause([Lit::pos(row[i])]);
                }
                if negative {
                    sat.add_clause([Lit::neg(row[i])]);
                }
            }
            if v.is_universal {
                sat.add_clause([Lit::pos(row[n])]);
            }
            if hi.is_some() || v.may_members.is_some() || v.is_definitely_empty() {
                sat.add_clause([Lit::neg(row[n])]);
            }
            let members: Vec<_> = row[..n].iter().map(|&b| Lit::pos(b)).collect();
            if let Some(hi) = hi {
                if hi < 0 {
                    return Err(Self::relation_conflict("negative upper cardinality"));
                }
                if !CardinalityEncoder::encode_at_most_k(
                    &mut sat,
                    &members,
                    usize::try_from(hi).unwrap_or(usize::MAX),
                ) {
                    return Ok(false);
                }
            }
            let lo = usize::try_from(lo.max(0))
                .map_err(|_| Self::relation_conflict("invalid cardinality"))?;
            // A cofinite set satisfies every finite lower bound. Repeated
            // default literals contribute lo true occurrences when selected.
            let mut at_least = members;
            at_least.extend(core::iter::repeat_n(Lit::pos(row[n]), lo));
            if !CardinalityEncoder::encode_at_least_k(&mut sat, &at_least, lo) {
                return Ok(false);
            }
        }
        for relation in self.relations.iter().copied() {
            let vars = relation.vars();
            for &v in &vars {
                self.require_var(v)?;
            }
            if let SetRelation::Subset(a, b, false) = relation {
                let mut witnesses = Vec::new();
                for (&a, &b) in bits[a.0 as usize].iter().zip(&bits[b.0 as usize]) {
                    let w = sat.new_var();
                    sat.add_clause([Lit::neg(w), Lit::pos(a)]);
                    sat.add_clause([Lit::neg(w), Lit::neg(b)]);
                    sat.add_clause([Lit::pos(w), Lit::neg(a), Lit::pos(b)]);
                    witnesses.push(Lit::pos(w));
                }
                sat.add_clause(witnesses);
            } else {
                for mask in 0..(1usize << vars.len()) {
                    let assignment: Vec<_> =
                        (0..vars.len()).map(|i| mask & (1 << i) != 0).collect();
                    if relation.holds(&assignment) {
                        continue;
                    }
                    for (i, _) in elements
                        .iter()
                        .map(Some)
                        .chain(core::iter::once(None))
                        .enumerate()
                    {
                        sat.add_clause(vars.iter().enumerate().map(|(j, v)| {
                            let b = bits[v.0 as usize][i];
                            if assignment[j] {
                                Lit::neg(b)
                            } else {
                                Lit::pos(b)
                            }
                        }));
                    }
                }
            }
        }
        // Cardinality terms denote finite integer sizes. First seek a model
        // where every explicitly cardinality-constrained set is finite. If
        // that restriction fails, recheck the weaker encoding before claiming
        // UNSAT: an infinite-cardinality case is unresolved, not a fabricated
        // integer cardinality or a refutation based only on a finite guess.
        sat.push();
        for c in &self.card_constraints {
            sat.add_clause([Lit::neg(bits[c.set.0 as usize][n])]);
        }
        let result = sat.solve();
        if result == SolverResult::Unsat {
            sat.pop();
            return match sat.solve() {
                SolverResult::Unsat => Err(Self::relation_conflict(
                    "exhausted set membership/cardinality model",
                )),
                SolverResult::Sat | SolverResult::Unknown => Ok(false),
            };
        }
        match result {
            // Small-model bound: keep named elements, lo witnesses for each
            // lower cardinality, and one witness for each negative subset.
            // Removing all other finite elements preserves Boolean relations
            // and upper bounds. Choose any one remaining infinite region as
            // the default; the rest may be made finite. Thus this encoding
            // represents a model whenever the supported input has one.
            SolverResult::Unsat => Ok(false),
            SolverResult::Unknown => Ok(false),
            SolverResult::Sat => {
                let mut values = Vec::new();
                for row in &bits {
                    let read = |b: Var| {
                        sat.model()
                            .get(b.index())
                            .filter(|v| v.is_defined())
                            .map(|v| v.is_true())
                    };
                    let Some(default_member) = read(row[n]) else {
                        return Ok(false);
                    };
                    let mut exceptions = FxHashSet::default();
                    for (i, &element) in elements.iter().enumerate() {
                        let Some(member) = read(row[i]) else {
                            return Ok(false);
                        };
                        if member != default_member {
                            exceptions.insert(element);
                        }
                    }
                    values.push(SetModelValue {
                        default_member,
                        exceptions,
                    });
                }
                if !self.validate_set_witness(&values) {
                    return Ok(false);
                }
                self.model = Some(values);
                Ok(true)
            }
        }
    }

    pub(super) fn validate_set_witness(&self, values: &[SetModelValue]) -> bool {
        if values.len() != self.vars.len() {
            return false;
        }
        let mut elements = FxHashSet::default();
        for (var, value) in self.vars.iter().zip(values) {
            let (lo, hi) = var.cardinality_bounds();
            if value.default_member {
                if hi.is_some() || var.may_members.is_some() || var.is_definitely_empty() {
                    return false;
                }
            } else {
                let Ok(size) = i64::try_from(value.exceptions.len()) else {
                    return false;
                };
                if size < lo || hi.is_some_and(|hi| size > hi) || var.is_universal {
                    return false;
                }
            }
            if var.is_universal && !value.exceptions.is_empty() {
                return false;
            }
            if var.must_members.iter().any(|&e| !value.contains(e))
                || var.must_not_members.iter().any(|&e| value.contains(e))
            {
                return false;
            }
            if var
                .may_members
                .as_ref()
                .is_some_and(|may| !value.exceptions.is_subset(may))
            {
                return false;
            }
            elements.extend(value.exceptions.iter().copied());
        }
        for c in &self.card_constraints {
            let Some(value) = values.get(c.set.0 as usize) else {
                return false;
            };
            if value.default_member {
                return false;
            } else {
                let Ok(size) = i64::try_from(value.exceptions.len()) else {
                    return false;
                };
                if !c.kind.check(size, c.bound) {
                    return false;
                }
            }
        }
        for relation in self.relations.iter().copied() {
            let ids = relation.vars();
            if ids.iter().any(|v| v.0 as usize >= values.len()) {
                return false;
            }
            let defaults: Vec<_> = ids
                .iter()
                .map(|v| values[v.0 as usize].default_member)
                .collect();
            if let SetRelation::Subset(a, b, false) = relation {
                let a = &values[a.0 as usize];
                let b = &values[b.0 as usize];
                let witness = (a.default_member && !b.default_member)
                    || elements.iter().any(|&e| a.contains(e) && !b.contains(e));
                if !witness {
                    return false;
                }
            } else {
                if !relation.holds(&defaults) {
                    return false;
                }
                for &e in &elements {
                    let member: Vec<_> = ids
                        .iter()
                        .map(|v| values[v.0 as usize].contains(e))
                        .collect();
                    if !relation.holds(&member) {
                        return false;
                    }
                }
            }
        }
        for constraint in &self.constraints {
            if let SetConstraint::Member { element, set, sign } = constraint
                && Self::evaluate_membership(set, *element, values) != Some(*sign)
            {
                return false;
            }
        }
        true
    }

    fn evaluate_membership(expr: &SetExpr, element: u32, values: &[SetModelValue]) -> Option<bool> {
        let mut todo = vec![(expr, false)];
        let mut results = Vec::new();
        while let Some((expr, expanded)) = todo.pop() {
            match expr {
                SetExpr::Var(v) => results.push(values.get(v.0 as usize)?.contains(element)),
                SetExpr::Empty => results.push(false),
                SetExpr::Universal => results.push(true),
                SetExpr::Singleton(e) => results.push(*e == element),
                SetExpr::Comprehension { formula, .. } => todo.push((formula, false)),
                SetExpr::Complement(inner) => {
                    if expanded {
                        let bit = results.pop()?;
                        results.push(!bit);
                    } else {
                        todo.push((expr, true));
                        todo.push((inner, false));
                    }
                }
                SetExpr::Union(a, b) | SetExpr::Intersection(a, b) | SetExpr::Difference(a, b) => {
                    if expanded {
                        let right = results.pop()?;
                        let left = results.pop()?;
                        results.push(match expr {
                            SetExpr::Union(..) => left || right,
                            SetExpr::Intersection(..) => left && right,
                            SetExpr::Difference(..) => left && !right,
                            _ => return None,
                        });
                    } else {
                        todo.push((expr, true));
                        todo.push((b, false));
                        todo.push((a, false));
                    }
                }
            }
        }
        if results.len() == 1 {
            results.pop()
        } else {
            None
        }
    }
}
