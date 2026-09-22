//! Independent finite semantics for CP proof leaves and concrete models.
//!
//! This checker never calls filtering, matching, or a user callback. A lemma
//! is checked by exhausting the remaining assignments of one original global.
//! The caller supplies a deterministic work budget; exhaustion is an error.
use super::*;
#[cfg(not(feature = "std"))]
use alloc::collections::BTreeSet;
#[cfg(feature = "std")]
use std::collections::BTreeSet;

/// Original declarations retained by the caller, outside the proof artifact.
/// Term IDs must belong to the same term manager throughout checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpStatement {
    pub(super) domains: Vec<Arc<Domain>>,
    pub(super) constraints: Vec<Constraint>,
    pub(super) assertions: Vec<TermId>,
    pub(super) bindings: Vec<(CpVar, TermId)>,
    pub(super) presences: Vec<Presence>,
    pub(super) true_term: TermId,
    pub(super) false_term: TermId,
}

fn spend(budget: &mut u64) -> Result<(), CpError> {
    *budget = budget
        .checked_sub(1)
        .ok_or(CpError("CP proof work limit"))?;
    Ok(())
}

impl CpStatement {
    /// Authenticate generated domain/link assertions against the declarations.
    /// This is independent of the input constructor's assertion buffer, so a
    /// missing, extra, or incorrect generated axiom cannot become a proof input.
    pub fn check_encoding(&self, tm: &mut TermManager) -> Result<(), CpError> {
        if self.true_term != tm.mk_true() || self.false_term != tm.mk_false() {
            return Err(CpError("CP Boolean constants do not match original terms"));
        }
        let mut expected = Vec::new();
        let mut indicators = HashSet::new();
        for domain in &self.domains {
            if domain.values.len() != domain.atoms.len()
                || domain.atoms.len() != domain.negations.len()
            {
                return Err(CpError("malformed original CP domain"));
            }
            let mut values = BTreeSet::new();
            for (i, &atom) in domain.atoms.iter().enumerate() {
                if !indicators.insert(atom)
                    || !values.insert(&domain.values[i])
                    || !tm.get(atom).is_some_and(|t| {
                        t.sort == tm.sorts.bool_sort
                            && matches!(t.kind, nixie_core::ast::TermKind::Var(_))
                    })
                    || tm.mk_not(atom) != domain.negations[i]
                {
                    return Err(CpError("invalid original CP indicator meaning"));
                }
            }
            expected.push(tm.mk_or(domain.atoms.iter().copied()));
        }
        for &(var, term) in &self.bindings {
            let domain = self
                .domains
                .get(var.0)
                .ok_or(CpError("invalid original CP binding variable"))?;
            if !tm.get(term).is_some_and(|t| t.sort == tm.sorts.int_sort) {
                return Err(CpError("invalid original CP integer binding"));
            }
            for (value, &atom) in domain.values.iter().zip(&domain.atoms) {
                let constant = tm.mk_int(value.clone());
                let equality = tm.mk_eq(term, constant);
                expected.push(tm.mk_eq(atom, equality));
            }
        }
        let mut conditions = HashSet::new();
        for presence in &self.presences {
            if !conditions.insert(presence.atom)
                || !tm
                    .get(presence.atom)
                    .is_some_and(|t| t.sort == tm.sorts.bool_sort)
                || tm.mk_not(presence.atom) != presence.negation
            {
                return Err(CpError("invalid original CP presence meaning"));
            }
        }
        for constraint in &self.constraints {
            if constraint
                .variables()
                .iter()
                .any(|v| v.0 >= self.domains.len())
            {
                return Err(CpError("invalid original CP variable"));
            }
            if let Constraint::Cumulative(tasks, _) = constraint {
                for scheduled in tasks {
                    if scheduled.task.duration < BigInt::zero()
                        || scheduled.task.demand < BigInt::zero()
                        || scheduled
                            .presence
                            .is_some_and(|(i, _)| i >= self.presences.len())
                    {
                        return Err(CpError("invalid original CP task"));
                    }
                }
            }
        }
        // Variable and binding declarations may be interleaved by the caller.
        // Check the multiset, including duplicates, rather than buffer order.
        expected.sort_unstable();
        let mut actual = self.assertions.clone();
        actual.sort_unstable();
        if actual != expected {
            return Err(CpError("generated CP assertions do not match declarations"));
        }
        Ok(())
    }

    /// Positive value indicators in original domain order.
    pub fn indicators(&self) -> impl Iterator<Item = TermId> + '_ {
        self.domains
            .iter()
            .flat_map(|domain| domain.atoms.iter().copied())
    }

    /// Boolean inputs required for replay and proof reconstruction, including
    /// optional-task presence conditions as well as finite-domain indicators.
    pub fn boolean_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.indicators()
            .chain(self.presences.iter().map(|p| p.atom))
    }

    /// Domain and integer-binding assertions installed with this declaration.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Check `AND(premises) => conclusion` against the original declarations.
    /// Foreign literals are conservatively forgotten, never assumed true as
    /// conclusions. Each global is tried separately; failure proves nothing.
    pub fn check_lemma(
        &self,
        conclusion: TermId,
        premises: &[TermId],
        budget: &mut u64,
    ) -> Result<(), CpError> {
        spend(budget)?;
        if conclusion == self.true_term || premises.contains(&self.false_term) {
            return Ok(());
        }
        let mut remaining = Vec::new();
        for domain in &self.domains {
            let mut choices = Vec::new();
            for i in 0..domain.values.len() {
                let mut possible = true;
                for (&term, truth) in premises
                    .iter()
                    .map(|t| (t, true))
                    .chain(core::iter::once((&conclusion, false)))
                {
                    spend(budget)?;
                    // Exactly one positive indicator: all other positives
                    // are false and all other negative indicators are true.
                    for j in 0..domain.values.len() {
                        spend(budget)?;
                        if (term == domain.atoms[j] && (i == j) != truth)
                            || (term == domain.negations[j] && (i != j) != truth)
                        {
                            possible = false;
                        }
                    }
                }
                if possible {
                    choices.push(i);
                }
            }
            if choices.is_empty() {
                return Ok(());
            }
            remaining.push(choices);
        }
        // Conditions may be formulas or aliases of domain indicators. Treat
        // their Boolean values independently here: this enlarges the support
        // set and can only reject additional lemmas, never certify a bad one.
        // Repeated/complemented uses of one condition share the same digit.
        let mut presence_choices = Vec::new();
        for presence in &self.presences {
            let mut choices = Vec::new();
            for truth in [false, true] {
                let mut possible = !(presence.atom == self.true_term && !truth
                    || presence.atom == self.false_term && truth);
                for (&term, required) in premises
                    .iter()
                    .map(|t| (t, true))
                    .chain(core::iter::once((&conclusion, false)))
                {
                    spend(budget)?;
                    if (term == presence.atom && truth != required)
                        || (term == presence.negation && truth == required)
                    {
                        possible = false;
                    }
                }
                if possible {
                    choices.push(truth);
                }
            }
            if choices.is_empty() {
                return Ok(());
            }
            presence_choices.push(choices);
        }
        // Unsatisfiability of any one original global under the restricted
        // domains suffices. Aliased positions share one enumeration digit.
        for constraint in &self.constraints {
            let mut vars = constraint.variables();
            vars.sort_unstable();
            vars.dedup();
            let mut conditions = match constraint {
                Constraint::Cumulative(tasks, _) => tasks
                    .iter()
                    .filter_map(|t| t.presence.map(|(i, _)| i))
                    .collect::<Vec<_>>(),
                Constraint::AllDifferent(_)
                | Constraint::Table(_)
                | Constraint::Regular(..)
                | Constraint::Circuit(_) => Vec::new(),
            };
            conditions.sort_unstable();
            conditions.dedup();
            let mut digits = vec![0; vars.len() + conditions.len()];
            let mut presence_values = vec![false; self.presences.len()];
            let mut selected = vec![0; self.domains.len()];
            let mut has_support = false;
            loop {
                spend(budget)?;
                for (k, var) in vars.iter().enumerate() {
                    selected[var.0] = remaining[var.0][digits[k]];
                }
                for (k, &index) in conditions.iter().enumerate() {
                    presence_values[index] = presence_choices[index][digits[vars.len() + k]];
                }
                if self.satisfied(constraint, &selected, &presence_values, budget)? {
                    has_support = true;
                    break;
                }
                let mut carry = true;
                for (k, size) in vars
                    .iter()
                    .map(|v| remaining[v.0].len())
                    .chain(conditions.iter().map(|&i| presence_choices[i].len()))
                    .enumerate()
                {
                    digits[k] += 1;
                    if digits[k] < size {
                        carry = false;
                        break;
                    }
                    digits[k] = 0;
                }
                if carry {
                    break;
                }
            }
            if !has_support {
                return Ok(());
            }
        }
        Err(CpError("CP lemma has no checked finite-domain refutation"))
    }

    /// Independently check a complete indicator valuation, including every
    /// exactly-one domain and every original global. Missing values fail.
    pub fn check_model(
        &self,
        mut value: impl FnMut(TermId) -> Option<bool>,
        budget: &mut u64,
    ) -> Result<(), CpError> {
        let mut selected = Vec::new();
        for domain in &self.domains {
            let mut fixed = None;
            for (i, &atom) in domain.atoms.iter().enumerate() {
                spend(budget)?;
                match value(atom) {
                    Some(true) if fixed.is_none() => fixed = Some(i),
                    Some(false) => {}
                    _ => return Err(CpError("invalid or incomplete CP domain model")),
                }
            }
            selected.push(fixed.ok_or(CpError("empty CP domain model"))?);
        }
        let mut presence_values = Vec::new();
        for presence in &self.presences {
            spend(budget)?;
            let truth = if presence.atom == self.true_term {
                true
            } else if presence.atom == self.false_term {
                false
            } else {
                value(presence.atom).ok_or(CpError("incomplete CP presence model"))?
            };
            presence_values.push(truth);
        }
        for constraint in &self.constraints {
            if !self.satisfied(constraint, &selected, &presence_values, budget)? {
                return Err(CpError("model violates an original CP global"));
            }
        }
        Ok(())
    }

    // Exact predicates over complete assignments. Deliberately separate from
    // feasibility.rs: no matching, mandatory parts, or partial-domain tests.
    fn satisfied(
        &self,
        constraint: &Constraint,
        selected: &[usize],
        presences: &[bool],
        budget: &mut u64,
    ) -> Result<bool, CpError> {
        spend(budget)?;
        let value = |v: CpVar| &self.domains[v.0].values[selected[v.0]];
        Ok(match constraint {
            Constraint::AllDifferent(vars) => {
                for (i, &a) in vars.iter().enumerate() {
                    for &b in &vars[..i] {
                        spend(budget)?;
                        if value(a) == value(b) {
                            return Ok(false);
                        }
                    }
                }
                true
            }
            Constraint::Table(table) => {
                for row in table.rows() {
                    spend(budget)?;
                    let mut matches = true;
                    for (&var, entry) in table.variables().iter().zip(row) {
                        spend(budget)?;
                        matches &= value(var) == entry;
                    }
                    if matches {
                        return Ok(true);
                    }
                }
                false
            }
            Constraint::Regular(vars, initial, accepting, edges) => {
                let mut states = BTreeSet::from([*initial]);
                for &var in vars {
                    let mut next = BTreeSet::new();
                    for edge in edges {
                        spend(budget)?;
                        if states.contains(&edge.source) && value(var) == &edge.symbol {
                            next.insert(edge.destination);
                        }
                    }
                    states = next;
                }
                accepting.iter().any(|q| states.contains(q))
            }
            Constraint::Circuit(vars) => {
                if vars.is_empty() {
                    return Ok(true);
                }
                let mut seen = vec![false; vars.len()];
                let mut node = 0;
                for _ in vars {
                    spend(budget)?;
                    if seen[node] {
                        return Ok(false);
                    }
                    seen[node] = true;
                    match value(vars[node]).to_usize() {
                        Some(next) if next < vars.len() => node = next,
                        _ => return Ok(false),
                    }
                }
                node == 0
            }
            Constraint::Cumulative(tasks, capacity) => {
                if *capacity < BigInt::zero() {
                    return Ok(false);
                }
                // A nonnegative piecewise-constant load can increase only at
                // a task start. Evaluate those points with half-open intervals
                // directly, independently of the producer's event sweep.
                let present = |task: &ScheduledTask| -> Result<bool, CpError> {
                    match task.presence {
                        None => Ok(true),
                        Some((i, sign)) => presences
                            .get(i)
                            .map(|&p| p == sign)
                            .ok_or(CpError("missing CP presence valuation")),
                    }
                };
                for task in tasks {
                    spend(budget)?;
                    if !present(task)? {
                        continue;
                    }
                    let time = value(task.task.start);
                    let mut load = BigInt::zero();
                    for other in tasks {
                        spend(budget)?;
                        if !present(other)? {
                            continue;
                        }
                        let start = value(other.task.start);
                        if start <= time && *time < start + &other.task.duration {
                            load += &other.task.demand;
                        }
                    }
                    if load > *capacity {
                        return Ok(false);
                    }
                }
                true
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_axioms_are_checked_against_typed_declarations() {
        let mut tm = TermManager::new();
        let mut cp = CpModel::new(&tm);
        let a = tm.mk_var("a", tm.sorts.bool_sort);
        let b = tm.mk_var("b", tm.sorts.bool_sort);
        let x = match cp.variable(vec![(0.into(), a), (1.into(), b)], &mut tm) {
            Ok(v) => v,
            Err(e) => panic!("{e}"),
        };
        let integer = tm.mk_var("x", tm.sorts.int_sort);
        assert!(cp.bind_integer(x, integer, &mut tm).is_ok());
        // Interleaved declarations and duplicate bindings are legitimate.
        assert!(cp.variable(vec![], &mut tm).is_ok());
        assert!(cp.bind_integer(x, integer, &mut tm).is_ok());
        let original = cp.statement();
        assert!(original.check_encoding(&mut tm).is_ok());
        for mutation in 0..5 {
            let mut bad = original.clone();
            match mutation {
                0 => {
                    bad.assertions.push(tm.mk_false());
                }
                1 => {
                    bad.assertions.remove(0);
                }
                2 => {
                    bad.assertions[0] = tm.mk_and([a, b]);
                }
                3 => {
                    bad.assertions[1] = tm.mk_not(bad.assertions[1]);
                }
                4 => {
                    bad.bindings[0].1 = tm.mk_true();
                }
                _ => unreachable!(),
            }
            assert!(bad.check_encoding(&mut tm).is_err(), "mutation {mutation}");
        }
        let mut bad = original;
        let mut domain = (*bad.domains[0]).clone();
        domain.negations[0] = a;
        bad.domains[0] = Arc::new(domain);
        assert!(bad.check_encoding(&mut tm).is_err());
    }
}
