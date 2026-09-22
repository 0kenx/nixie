//! Persistent set relations and independently validated finite witnesses.
use super::*;

#[derive(Clone, Copy, Debug)]
pub(super) enum SetRelation {
    Subset(SetVarId, SetVarId, bool),
    Disjoint(SetVarId, SetVarId),
    Union(SetVarId, SetVarId, SetVarId),
    Intersection(SetVarId, SetVarId, SetVarId),
    Difference(SetVarId, SetVarId, SetVarId),
    Complement(SetVarId, SetVarId),
}

impl SetRelation {
    fn vars(self) -> Vec<SetVarId> {
        match self {
            Self::Subset(a, b, _) | Self::Disjoint(a, b) | Self::Complement(a, b) => vec![a, b],
            Self::Union(r, a, b) | Self::Intersection(r, a, b) | Self::Difference(r, a, b) => {
                vec![r, a, b]
            }
        }
    }

    /// Pointwise semantics. A negative subset is existential, so it is
    /// checked separately and must not be asserted for every element.
    fn holds(self, bits: &[bool]) -> bool {
        match self {
            Self::Subset(_, _, true) => !bits[0] || bits[1],
            Self::Subset(_, _, false) => true,
            Self::Disjoint(..) => !(bits[0] && bits[1]),
            Self::Union(..) => bits[0] == (bits[1] || bits[2]),
            Self::Intersection(..) => bits[0] == (bits[1] && bits[2]),
            Self::Difference(..) => bits[0] == (bits[1] && !bits[2]),
            Self::Complement(..) => bits[0] != bits[1],
        }
    }
}

impl SetSolver {
    pub(super) fn relation_conflict(reason: &str) -> SetConflict {
        SetConflict {
            literals: Vec::new(),
            reason: reason.into(),
            proof_steps: Vec::new(),
        }
    }

    pub(super) fn require_var(&self, var: SetVarId) -> SetResult<()> {
        if self.get_var(var).is_some() {
            Ok(())
        } else {
            Err(Self::relation_conflict("invalid set variable"))
        }
    }

    fn known_member(var: &SetVar, elem: u32) -> Option<bool> {
        if var.is_universal || var.must_members.contains(&elem) {
            Some(true)
        } else if var.is_definitely_empty()
            || var.must_not_members.contains(&elem)
            || var
                .may_members
                .as_ref()
                .is_some_and(|may| !may.contains(&elem))
            || var.card_bounds.1 == i64::try_from(var.must_members.len()).ok()
        {
            Some(false)
        } else {
            None
        }
    }

    pub(super) fn propagate_relations(&mut self) -> SetResult<()> {
        self.model = None;
        loop {
            let mut elements = FxHashSet::default();
            for var in &self.vars {
                elements.extend(var.must_members.iter().copied());
                elements.extend(var.must_not_members.iter().copied());
                let (lo, hi) = var.cardinality_bounds();
                if hi.is_some_and(|h| lo > h)
                    || !var.must_members.is_disjoint(&var.must_not_members)
                    || (var.is_definitely_empty() && !var.must_members.is_empty())
                    || (var.is_universal && !var.must_not_members.is_empty())
                    || var
                        .may_members
                        .as_ref()
                        .is_some_and(|may| !var.must_members.is_subset(may))
                {
                    return Err(Self::relation_conflict("inconsistent set domain"));
                }
            }
            let mut updates = Vec::new();
            for relation in self.relations.iter().copied() {
                let ids = relation.vars();
                for &id in &ids {
                    self.require_var(id)?;
                }
                if let SetRelation::Subset(a, b, false) = relation {
                    if a == b || self.vars[a.0 as usize].is_definitely_empty() {
                        return Err(Self::relation_conflict(
                            "negative subset has no possible witness",
                        ));
                    }
                    continue;
                }
                for &elem in &elements {
                    self.stats.num_propagations += 1;
                    let known: Vec<_> = ids
                        .iter()
                        .map(|v| Self::known_member(&self.vars[v.0 as usize], elem))
                        .collect();
                    let mut possibilities = Vec::new();
                    // At most three membership bits: exhaustive truth tables
                    // implement the standard pointwise set axioms. Equal IDs
                    // must use the same bit even at different operand positions.
                    for mask in 0..(1usize << ids.len()) {
                        let bits: Vec<_> = (0..ids.len()).map(|i| mask & (1 << i) != 0).collect();
                        let consistent = (0..ids.len()).all(|i| {
                            known[i].is_none_or(|k| k == bits[i])
                                && (0..i).all(|j| ids[i] != ids[j] || bits[i] == bits[j])
                        });
                        if consistent && relation.holds(&bits) {
                            possibilities.push(bits);
                        }
                    }
                    let Some(first) = possibilities.first() else {
                        return Err(Self::relation_conflict(
                            "set relation contradicts known membership",
                        ));
                    };
                    for (i, &var) in ids.iter().enumerate() {
                        if known[i].is_none() && possibilities.iter().all(|p| p[i] == first[i]) {
                            updates.push((var, elem, first[i]));
                        }
                    }
                }
            }
            if updates.is_empty() {
                break;
            }
            for (var, elem, sign) in updates {
                // This helper records every mutation on the existing trail.
                self.add_member_constraint(elem, &SetExpr::Var(var), sign)?;
            }
        }
        self.propagation_queue.clear();
        Ok(())
    }

    pub(super) fn validate_finite_model(&mut self) -> SetResult<bool> {
        // A minimal finite candidate is a witness only after EVERY domain,
        // relation and cardinality has been checked. Failed candidates cost
        // completeness, never justify an unsatisfiable result.
        let values: Vec<_> = self.vars.iter().map(|v| v.must_members.clone()).collect();
        let mut elements = FxHashSet::default();
        for (var, value) in self.vars.iter().zip(&values) {
            if var.is_universal {
                return Ok(false);
            }
            let Ok(size) = i64::try_from(value.len()) else {
                return Ok(false);
            };
            let (lo, hi) = var.cardinality_bounds();
            if size < lo || hi.is_some_and(|h| size > h) {
                return Ok(false);
            }
            elements.extend(value.iter().copied());
        }
        for c in &self.card_constraints {
            self.require_var(c.set)?;
            let Ok(size) = i64::try_from(values[c.set.0 as usize].len()) else {
                return Ok(false);
            };
            if !c.kind.check(size, c.bound) {
                return Ok(false);
            }
        }
        for relation in self.relations.iter().copied() {
            let ids = relation.vars();
            for &id in &ids {
                self.require_var(id)?;
            }
            match relation {
                SetRelation::Subset(a, b, false) => {
                    if values[a.0 as usize].is_subset(&values[b.0 as usize]) {
                        return Ok(false);
                    }
                }
                // The default membership outside these finite sets is false.
                // Complement cannot be satisfied by two finite candidates.
                SetRelation::Complement(..) => return Ok(false),
                _ => {
                    for &elem in &elements {
                        let bits: Vec<_> = ids
                            .iter()
                            .map(|v| values[v.0 as usize].contains(&elem))
                            .collect();
                        if !relation.holds(&bits) {
                            return Ok(false);
                        }
                    }
                }
            }
        }
        self.model = Some(values);
        Ok(true)
    }
}
