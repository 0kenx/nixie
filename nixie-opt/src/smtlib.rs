//! SMT-LIB2 optimization commands.
//!
//! This module implements SMT-LIB2 extensions for optimization:
//! - `(minimize <term>)` - Minimize an objective
//! - `(maximize <term>)` - Maximize an objective
//! - `(assert-soft <term> :weight <num>)` - Soft constraint with weight
//! - `(get-objectives)` - Get objective values
//!
//! Reference: SMT-LIB2 optimization extensions, Z3's `opt/opt_frontend.cpp`

use nixie_core::ast::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;
use rustc_hash::FxHashMap;
use thiserror::Error;

use crate::context::{OptContext, OptResult, SoftConstraintId};
use crate::maxsat::Weight;
use crate::objective::ObjectiveId;

/// Errors that can occur during SMT-LIB2 command execution
#[derive(Error, Debug)]
pub enum SmtLibError {
    /// Invalid command
    #[error("invalid command: {0}")]
    InvalidCommand(String),
    /// Unknown objective
    #[error("unknown objective: {0}")]
    UnknownObjective(String),
    /// Context error
    #[error("context error: {0}")]
    ContextError(String),
}

/// SMT-LIB2 optimization command
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptCommand {
    /// Minimize an objective term
    Minimize {
        /// The term to minimize
        term: TermId,
        /// Optional name for the objective
        name: Option<String>,
    },
    /// Maximize an objective term
    Maximize {
        /// The term to maximize
        term: TermId,
        /// Optional name for the objective
        name: Option<String>,
    },
    /// Add a soft constraint
    AssertSoft {
        /// The constraint term
        term: TermId,
        /// Weight of the constraint
        weight: Weight,
        /// Optional group name
        group: Option<String>,
        /// Optional identifier
        id: Option<String>,
    },
    /// Get objective values
    GetObjectives,
    /// Check optimization result
    CheckSat,
}

/// Result of an optimization command
#[derive(Debug, Clone)]
pub enum CommandResult {
    /// Objective ID assigned
    ObjectiveId(ObjectiveId),
    /// Soft constraint ID assigned
    SoftId(SoftConstraintId),
    /// Optimization result
    Result(OptResult),
    /// Objective values
    Objectives(Vec<ObjectiveValue>),
    /// Success with no specific value
    Success,
}

/// Value of an objective in the solution
#[derive(Debug, Clone)]
pub struct ObjectiveValue {
    /// Objective identifier
    pub id: ObjectiveId,
    /// Name (if provided)
    pub name: Option<String>,
    /// Value in the optimal model
    pub value: ObjectiveValueData,
    /// Whether this is optimal
    pub optimal: bool,
}

/// Data for objective value
#[derive(Debug, Clone)]
pub enum ObjectiveValueData {
    /// Integer value
    Int(BigInt),
    /// Rational value
    Rational(BigRational),
    /// Infinite value (unbounded)
    Infinite,
    /// Unknown (not yet optimized)
    Unknown,
}

/// SMT-LIB2 optimization frontend
pub struct SmtLibOptimizer {
    /// The optimization context
    context: OptContext,
    /// Objective names
    objective_names: FxHashMap<ObjectiveId, String>,
    /// Soft constraint IDs
    soft_ids: FxHashMap<String, SoftConstraintId>,
    /// Result of the most recent `(check-sat)`/`optimize()` call, if any has
    /// run since the optimizer was created (or last reset/mutated). This is
    /// what `get_objectives` consults to report each objective's `optimal`
    /// flag honestly -- `(get-objectives)` reflects the *last proven*
    /// optimization state, not a blanket assumption.
    last_result: Option<OptResult>,
}

impl Default for SmtLibOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtLibOptimizer {
    /// Create a new SMT-LIB2 optimizer
    pub fn new() -> Self {
        Self {
            context: OptContext::new(),
            objective_names: FxHashMap::default(),
            soft_ids: FxHashMap::default(),
            last_result: None,
        }
    }

    /// Execute a command
    pub fn execute(&mut self, cmd: OptCommand) -> Result<CommandResult, SmtLibError> {
        match cmd {
            OptCommand::Minimize { term, name } => {
                let id = self.context.minimize(term);
                if let Some(n) = name {
                    self.objective_names.insert(id, n);
                }
                // A newly added objective invalidates whatever optimality
                // was previously proven: the problem has changed and the
                // old model/bounds no longer necessarily apply to it.
                self.last_result = None;
                Ok(CommandResult::ObjectiveId(id))
            }
            OptCommand::Maximize { term, name } => {
                let id = self.context.maximize(term);
                if let Some(n) = name {
                    self.objective_names.insert(id, n);
                }
                self.last_result = None;
                Ok(CommandResult::ObjectiveId(id))
            }
            OptCommand::AssertSoft {
                term,
                weight,
                group,
                id: soft_id,
            } => {
                let id = self.context.add_soft_grouped(term, weight, group);
                if let Some(sid) = soft_id {
                    self.soft_ids.insert(sid, id);
                }
                self.last_result = None;
                Ok(CommandResult::SoftId(id))
            }
            OptCommand::GetObjectives => {
                let objectives = self.get_objectives();
                Ok(CommandResult::Objectives(objectives))
            }
            OptCommand::CheckSat => {
                let result = self
                    .context
                    .optimize()
                    .map_err(|e| SmtLibError::ContextError(e.to_string()))?;
                self.last_result = Some(result.clone());
                Ok(CommandResult::Result(result))
            }
        }
    }

    /// Get all objective values
    fn get_objectives(&self) -> Vec<ObjectiveValue> {
        let mut result = Vec::new();

        // An objective's value is only certified *optimal* when the most
        // recent `(check-sat)` actually proved optimality
        // (`OptResult::Optimal`). Any other outcome -- no check-sat run
        // yet, `Satisfiable` (optimality unproven), `Unknown`, `Unbounded`,
        // or a check-sat that ran before the objective/soft-constraint set
        // was last mutated -- must not be reported as optimal, since the
        // numeric value (if any is even available) is then only a
        // best-effort bound rather than a certified optimum.
        let proven_optimal = matches!(self.last_result, Some(OptResult::Optimal));

        for i in 0..self.context.num_objectives() {
            let id = ObjectiveId(i as u32);
            let name = self.objective_names.get(&id).cloned();

            let value = if let Some(weight) = self.context.objective_value(id) {
                match weight {
                    Weight::Int(n) => ObjectiveValueData::Int(n.clone()),
                    Weight::Rational(r) => ObjectiveValueData::Rational(r.clone()),
                    Weight::Infinite => ObjectiveValueData::Infinite,
                }
            } else {
                ObjectiveValueData::Unknown
            };

            result.push(ObjectiveValue {
                id,
                name,
                value,
                optimal: proven_optimal,
            });
        }

        result
    }

    /// Get the optimization context
    pub fn context(&self) -> &OptContext {
        &self.context
    }

    /// Get mutable access to the optimization context
    pub fn context_mut(&mut self) -> &mut OptContext {
        &mut self.context
    }

    /// Reset the optimizer
    pub fn reset(&mut self) {
        self.context.reset();
        self.objective_names.clear();
        self.soft_ids.clear();
        self.last_result = None;
    }
}

/// Format objective values as SMT-LIB2 output
pub fn format_objectives(objectives: &[ObjectiveValue]) -> String {
    let mut output = String::from("(objectives\n");

    for obj in objectives {
        let name = obj.name.as_deref().unwrap_or("objective");
        let value_str = match &obj.value {
            ObjectiveValueData::Int(n) => n.to_string(),
            ObjectiveValueData::Rational(r) => {
                format!("(/ {} {})", r.numer(), r.denom())
            }
            ObjectiveValueData::Infinite => "oo".to_string(),
            ObjectiveValueData::Unknown => "?".to_string(),
        };

        output.push_str(&format!("  ({} {})\n", name, value_str));
    }

    output.push(')');
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_smtlib_optimizer_new() {
        let opt = SmtLibOptimizer::new();
        assert_eq!(opt.context.num_objectives(), 0);
        assert_eq!(opt.context.num_soft(), 0);
    }

    #[test]
    fn test_minimize_command() {
        let mut opt = SmtLibOptimizer::new();
        let term = TermId::from(1);

        let cmd = OptCommand::Minimize {
            term,
            name: Some("cost".to_string()),
        };

        let result = opt.execute(cmd);
        assert!(matches!(result, Ok(CommandResult::ObjectiveId(_))));
        assert_eq!(opt.context.num_objectives(), 1);
    }

    #[test]
    fn test_maximize_command() {
        let mut opt = SmtLibOptimizer::new();
        let term = TermId::from(1);

        let cmd = OptCommand::Maximize {
            term,
            name: Some("profit".to_string()),
        };

        let result = opt.execute(cmd);
        assert!(matches!(result, Ok(CommandResult::ObjectiveId(_))));
        assert_eq!(opt.context.num_objectives(), 1);
    }

    #[test]
    fn test_assert_soft_command() {
        let mut opt = SmtLibOptimizer::new();
        let term = TermId::from(1);

        let cmd = OptCommand::AssertSoft {
            term,
            weight: Weight::from(5),
            group: None,
            id: Some("soft1".to_string()),
        };

        let result = opt.execute(cmd);
        assert!(matches!(result, Ok(CommandResult::SoftId(_))));
        assert_eq!(opt.context.num_soft(), 1);
    }

    #[test]
    fn test_get_objectives_empty() {
        let mut opt = SmtLibOptimizer::new();

        let cmd = OptCommand::GetObjectives;
        let result = opt.execute(cmd).expect("test operation should succeed");

        if let CommandResult::Objectives(objs) = result {
            assert_eq!(objs.len(), 0);
        } else {
            panic!("Expected Objectives result");
        }
    }

    #[test]
    fn test_get_objectives_with_values() {
        let mut opt = SmtLibOptimizer::new();

        // Add objectives
        let term1 = TermId::from(1);
        let term2 = TermId::from(2);

        opt.execute(OptCommand::Minimize {
            term: term1,
            name: Some("obj1".to_string()),
        })
        .expect("test operation should succeed");

        opt.execute(OptCommand::Maximize {
            term: term2,
            name: Some("obj2".to_string()),
        })
        .expect("test operation should succeed");

        // Get objectives
        let result = opt
            .execute(OptCommand::GetObjectives)
            .expect("test operation should succeed");

        if let CommandResult::Objectives(objs) = result {
            assert_eq!(objs.len(), 2);
            assert_eq!(objs[0].name, Some("obj1".to_string()));
            assert_eq!(objs[1].name, Some("obj2".to_string()));
        } else {
            panic!("Expected Objectives result");
        }
    }

    #[test]
    fn test_format_objectives() {
        let objectives = vec![
            ObjectiveValue {
                id: ObjectiveId(0),
                name: Some("cost".to_string()),
                value: ObjectiveValueData::Int(BigInt::from(42)),
                optimal: true,
            },
            ObjectiveValue {
                id: ObjectiveId(1),
                name: Some("profit".to_string()),
                value: ObjectiveValueData::Rational(BigRational::new(
                    BigInt::from(3),
                    BigInt::from(2),
                )),
                optimal: true,
            },
        ];

        let output = format_objectives(&objectives);
        assert!(output.contains("cost"));
        assert!(output.contains("profit"));
        assert!(output.contains("42"));
        assert!(output.contains("(/ 3 2)"));
    }

    #[test]
    fn test_reset() {
        let mut opt = SmtLibOptimizer::new();

        opt.execute(OptCommand::Minimize {
            term: TermId::from(1),
            name: Some("obj1".to_string()),
        })
        .expect("test operation should succeed");

        opt.execute(OptCommand::AssertSoft {
            term: TermId::from(2),
            weight: Weight::one(),
            group: None,
            id: None,
        })
        .expect("test operation should succeed");

        assert_eq!(opt.context.num_objectives(), 1);
        assert_eq!(opt.context.num_soft(), 1);

        opt.reset();

        assert_eq!(opt.context.num_objectives(), 0);
        assert_eq!(opt.context.num_soft(), 0);
    }
}
