//! String Theory Quantifier Elimination Plugin.
//!
//! Eliminates quantifiers over string variables using automata-based
//! decision procedures and length constraints.
//!
//! ## Strategy
//!
//! For `∃x:String. φ(x)`:
//! 1. Extract length constraints and word equations
//! 2. Build automaton representing solutions
//! 3. Check if automaton is non-empty
//! 4. Eliminate quantifier based on automaton properties
//!
//! ## References
//!
//! - "Solving String Constraints with Regex-Dependent Functions" (Lin & Barceló, 2016)
//! - Z3's `qe/qe_arith.cpp` (adapted for strings)

#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use crate::{Term, TermId, TermKind};

/// Variable identifier.
pub type VarId = usize;

/// String constraint type.
#[derive(Debug, Clone)]
pub enum StringConstraint {
    /// x = y
    Equality(VarId, VarId),
    /// x = "const"
    ConstantEquality(VarId, String),
    /// x = concat(y, z)
    Concatenation(VarId, VarId, VarId),
    /// contains(x, "pattern")
    Contains(VarId, String),
    /// length(x) op k
    Length(VarId, LengthOp, i64),
    /// x matches regex
    RegexMatch(VarId, String),
}

/// Length comparison operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LengthOp {
    /// ==
    Equal,
    /// <
    Less,
    /// <=
    LessEq,
    /// >
    Greater,
    /// >=
    GreaterEq,
}

/// Configuration for string QE.
#[derive(Debug, Clone)]
pub struct StringQeConfig {
    /// Enable automata-based elimination.
    pub enable_automata: bool,
    /// Enable length-based elimination.
    pub enable_length: bool,
    /// Maximum automaton size.
    pub max_automaton_states: usize,
}

impl Default for StringQeConfig {
    fn default() -> Self {
        Self {
            enable_automata: true,
            enable_length: true,
            max_automaton_states: 10_000,
        }
    }
}

/// Statistics for string QE.
#[derive(Debug, Clone, Default)]
pub struct StringQeStats {
    /// Variables eliminated.
    pub vars_eliminated: u64,
    /// Automata constructed.
    pub automata_constructed: u64,
    /// Length constraints solved.
    pub length_constraints_solved: u64,
    /// Concatenations eliminated.
    pub concatenations_eliminated: u64,
}

/// String QE plugin.
#[derive(Debug)]
pub struct StringQePlugin {
    /// Known string constraints.
    constraints: Vec<StringConstraint>,
    /// Variable dependencies.
    dependencies: FxHashMap<VarId, FxHashSet<VarId>>,
    /// Configuration.
    config: StringQeConfig,
    /// Statistics.
    stats: StringQeStats,
}

impl StringQePlugin {
    /// Create a new string QE plugin.
    pub fn new(config: StringQeConfig) -> Self {
        Self {
            constraints: Vec::new(),
            dependencies: FxHashMap::default(),
            config,
            stats: StringQeStats::default(),
        }
    }

    /// Create with default configuration.
    pub fn default_config() -> Self {
        Self::new(StringQeConfig::default())
    }

    /// Add a string constraint.
    pub fn add_constraint(&mut self, constraint: StringConstraint) {
        // Track dependencies
        match &constraint {
            StringConstraint::Equality(x, y) => {
                self.dependencies.entry(*x).or_default().insert(*y);
                self.dependencies.entry(*y).or_default().insert(*x);
            }
            StringConstraint::Concatenation(x, y, z) => {
                self.dependencies.entry(*x).or_default().insert(*y);
                self.dependencies.entry(*x).or_default().insert(*z);
            }
            _ => {}
        }

        self.constraints.push(constraint);
    }

    /// Eliminate quantifier over a string variable.
    pub fn eliminate(&mut self, var: VarId) -> Option<Term> {
        // Collect constraints mentioning var
        let relevant = self.collect_relevant_constraints(var);

        if relevant.is_empty() {
            // Unconstrained variable - always satisfiable
            self.stats.vars_eliminated += 1;
            return Some(self.create_true());
        }

        // Cache config flags to avoid borrow issues
        let enable_length = self.config.enable_length;
        let enable_automata = self.config.enable_automata;

        // Try length-based elimination first (simpler)
        if enable_length && let Some(result) = self.eliminate_by_length(var, &relevant) {
            self.stats.vars_eliminated += 1;
            self.stats.length_constraints_solved += 1;
            return Some(result);
        }

        // Try automata-based elimination
        if enable_automata && let Some(result) = self.eliminate_by_automaton(var, &relevant) {
            self.stats.vars_eliminated += 1;
            self.stats.automata_constructed += 1;
            return Some(result);
        }

        None
    }

    /// Collect constraints relevant to a variable.
    fn collect_relevant_constraints(&self, var: VarId) -> Vec<&StringConstraint> {
        self.constraints
            .iter()
            .filter(|c| self.mentions_var(c, var))
            .collect()
    }

    /// Check if constraint mentions a variable.
    fn mentions_var(&self, constraint: &StringConstraint, var: VarId) -> bool {
        match constraint {
            StringConstraint::Equality(x, y) => *x == var || *y == var,
            StringConstraint::ConstantEquality(x, _) => *x == var,
            StringConstraint::Concatenation(x, y, z) => *x == var || *y == var || *z == var,
            StringConstraint::Contains(x, _) => *x == var,
            StringConstraint::Length(x, _, _) => *x == var,
            StringConstraint::RegexMatch(x, _) => *x == var,
        }
    }

    /// Eliminate using length constraints.
    ///
    /// Sound only when *every* constraint relevant to `var` is a pure
    /// length constraint (`length(x) op k`); mixed constraint kinds (word
    /// equations, concatenation, `contains`, regex membership) are left to
    /// [`Self::eliminate_by_automaton`] by returning `None` here.
    ///
    /// The relevant constraints form a conjunction of linear bounds and
    /// equalities over the non-negative integer `length(var)`. We solve
    /// that system directly: intersect all bounds and equalities, and the
    /// quantifier is satisfiable (`true`) iff the resulting integer
    /// interval/equality is non-empty, otherwise the constraints are
    /// contradictory and the quantifier is unsatisfiable (`false`). This
    /// mirrors Z3's `qe/qe_arith.cpp` bound-propagation approach, specialized
    /// to a single non-negative variable.
    fn eliminate_by_length(&self, _var: VarId, constraints: &[&StringConstraint]) -> Option<Term> {
        // Check if all constraints are length-based
        let all_length = constraints
            .iter()
            .all(|c| matches!(c, StringConstraint::Length(..)));

        if !all_length {
            return None;
        }

        // String length is always a non-negative integer.
        let mut lower: i64 = 0;
        let mut upper: i64 = i64::MAX;
        let mut equal_to: Option<i64> = None;

        for c in constraints {
            let (op, k) = match c {
                StringConstraint::Length(_, op, k) => (*op, *k),
                // Unreachable: `all_length` guaranteed every entry is
                // `Length`, but stay honest rather than panicking.
                _ => continue,
            };

            match op {
                LengthOp::Equal => match equal_to {
                    Some(existing) if existing != k => {
                        // Two distinct required lengths: contradiction.
                        return Some(self.create_false());
                    }
                    Some(_) => {}
                    None => equal_to = Some(k),
                },
                LengthOp::Less => upper = upper.min(k.saturating_sub(1)),
                LengthOp::LessEq => upper = upper.min(k),
                LengthOp::Greater => lower = lower.max(k.saturating_add(1)),
                LengthOp::GreaterEq => lower = lower.max(k),
            }
        }

        let satisfiable = match equal_to {
            Some(k) => k >= 0 && k >= lower && k <= upper,
            None => lower <= upper,
        };

        Some(if satisfiable {
            self.create_true()
        } else {
            self.create_false()
        })
    }

    /// Eliminate using automaton construction.
    ///
    /// Real automata-based string quantifier elimination (word equations,
    /// concatenation, `contains`, and regex membership) is not yet
    /// implemented. Rather than fabricate a satisfiability result, this
    /// conservatively gives up (`None`) so the caller keeps the quantifier
    /// or falls back to another decision procedure. This must never be
    /// changed to unconditionally return `true`/`false` without an actual
    /// automaton construction and non-emptiness check behind it.
    fn eliminate_by_automaton(
        &self,
        _var: VarId,
        _constraints: &[&StringConstraint],
    ) -> Option<Term> {
        None
    }

    /// Create a "true" term (placeholder).
    fn create_true(&self) -> Term {
        Term {
            id: TermId(0),
            kind: TermKind::True,
            sort: SortId(0),
        }
    }

    /// Create a "false" term (placeholder).
    fn create_false(&self) -> Term {
        Term {
            id: TermId(0),
            kind: TermKind::False,
            sort: SortId(0),
        }
    }

    /// Get statistics.
    pub fn stats(&self) -> &StringQeStats {
        &self.stats
    }

    /// Reset statistics.
    pub fn reset_stats(&mut self) {
        self.stats = StringQeStats::default();
    }
}

impl Default for StringQePlugin {
    fn default() -> Self {
        Self::default_config()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_plugin_creation() {
        let plugin = StringQePlugin::default_config();
        assert_eq!(plugin.stats().vars_eliminated, 0);
    }

    #[test]
    fn test_add_constraint() {
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Equality(0, 1));
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Equal, 5));

        assert_eq!(plugin.constraints.len(), 2);
    }

    #[test]
    fn test_mentions_var() {
        let plugin = StringQePlugin::default_config();

        let eq = StringConstraint::Equality(0, 1);
        assert!(plugin.mentions_var(&eq, 0));
        assert!(plugin.mentions_var(&eq, 1));
        assert!(!plugin.mentions_var(&eq, 2));
    }

    #[test]
    fn test_collect_relevant() {
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Equality(0, 1));
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Equal, 5));
        plugin.add_constraint(StringConstraint::Length(2, LengthOp::Equal, 3));

        let relevant = plugin.collect_relevant_constraints(0);
        assert_eq!(relevant.len(), 2); // Equality and Length for var 0
    }

    #[test]
    fn test_dependencies() {
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Equality(0, 1));

        assert!(plugin.dependencies.contains_key(&0));
        assert!(plugin.dependencies.contains_key(&1));
    }

    #[test]
    fn test_contradictory_length_constraints_yield_false_not_true() {
        // exists x. length(x) = 5 && length(x) = 3 is UNSATISFIABLE.
        // Regression for: plugin used to fabricate `true` for any
        // constrained quantifier, including contradictory ones.
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Equal, 5));
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Equal, 3));

        let result = plugin.eliminate(0).expect("length system is decidable");
        assert_eq!(result.kind, TermKind::False);
    }

    #[test]
    fn test_contradictory_length_bounds_yield_false() {
        // exists x. length(x) > 10 && length(x) < 5 is UNSATISFIABLE.
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Greater, 10));
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Less, 5));

        let result = plugin.eliminate(0).expect("length system is decidable");
        assert_eq!(result.kind, TermKind::False);
    }

    #[test]
    fn test_satisfiable_length_constraints_yield_true() {
        // exists x. length(x) >= 3 && length(x) <= 7 is satisfiable.
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::GreaterEq, 3));
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::LessEq, 7));

        let result = plugin.eliminate(0).expect("length system is decidable");
        assert_eq!(result.kind, TermKind::True);
    }

    #[test]
    fn test_negative_required_length_is_unsatisfiable() {
        // exists x. length(x) = -1 is UNSATISFIABLE (lengths are >= 0).
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Equal, -1));

        let result = plugin.eliminate(0).expect("length system is decidable");
        assert_eq!(result.kind, TermKind::False);
    }

    #[test]
    fn test_mixed_constraints_give_up_honestly_instead_of_fabricating_true() {
        // A word equation combined with a length bound is beyond the
        // pure-length solver and the automaton builder is unimplemented,
        // so eliminate() must honestly give up (`None`), never claim `true`.
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Equality(0, 1));
        plugin.add_constraint(StringConstraint::Length(0, LengthOp::Equal, 5));

        assert!(plugin.eliminate(0).is_none());
        assert_eq!(plugin.stats().vars_eliminated, 0);
    }

    #[test]
    fn test_unconstrained_var_still_eliminates_to_true() {
        // No constraints mention the variable at all: exists x. true.
        let mut plugin = StringQePlugin::default_config();
        plugin.add_constraint(StringConstraint::Length(1, LengthOp::Equal, 5));

        let result = plugin
            .eliminate(0)
            .expect("unconstrained var is trivially true");
        assert_eq!(result.kind, TermKind::True);
    }

    #[test]
    fn test_stats() {
        let mut plugin = StringQePlugin::default_config();
        plugin.stats.vars_eliminated = 10;

        assert_eq!(plugin.stats().vars_eliminated, 10);

        plugin.reset_stats();
        assert_eq!(plugin.stats().vars_eliminated, 0);
    }
}
