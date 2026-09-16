//! Standalone row-cover checking for table lemmas.
//!
//! A statement is an immutable original table plus its finite-domain indicator
//! meanings. Each row needs one obstruction under the premises and the negation
//! of the conclusion. This module never calls CP filtering or reads search state.

use super::{CpVar, Domain};
use crate::prelude::*;
use nixie_core::ast::TermId;
use num_bigint::BigInt;

/// Immutable table and indicator meanings, captured at construction time.
///
/// Obtain original statements from `CpModel::table_statements` before consuming
/// the model. A checker must use that original statement, not trust a statement
/// supplied by an untrusted certificate. Term IDs belong to the same term manager.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableStatement(pub(super) Arc<TableData>);

#[derive(Debug, PartialEq, Eq)]
pub(super) struct TableData {
    pub(super) variables: Vec<CpVar>,
    pub(super) rows: Vec<Vec<BigInt>>,
    pub(super) domains: BTreeMap<CpVar, Arc<Domain>>,
    pub(super) false_term: TermId,
}

impl TableStatement {
    /// Column variables, including aliases.
    pub fn variables(&self) -> &[CpVar] {
        &self.0.variables
    }

    /// The original allowed relation, including duplicate rows.
    pub fn rows(&self) -> &[Vec<BigInt>] {
        &self.0.rows
    }

    /// Original values and positive/negative Boolean indicators for a variable.
    pub fn indicators(
        &self,
        var: CpVar,
    ) -> Option<impl Iterator<Item = (&BigInt, TermId, TermId)>> {
        self.0.domains.get(&var).map(|d| {
            d.values
                .iter()
                .zip(&d.atoms)
                .zip(&d.negations)
                .map(|((v, &p), &n)| (v, p, n))
        })
    }
}

/// One locally checkable obstruction for the row at this witness's position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TableRowBlocker {
    /// The row's value is absent from the variable's original domain.
    OutsideDomain {
        /// Index of the obstructed column.
        column: usize,
    },
    /// Two columns name the same variable but have different row values.
    Alias {
        /// First occurrence of the repeated variable.
        first: usize,
        /// Other occurrence with a different row value.
        second: usize,
    },
    /// A stated premise excludes the row value (negative indicator), or fixes
    /// this variable to a different value (positive indicator, exactly-one).
    Premise {
        /// Index of the obstructed column.
        column: usize,
        /// Index into the implication's antecedent literals.
        premise: usize,
    },
    /// Negating the conclusion fixes this variable to a different row value.
    NegatedConclusion {
        /// Column whose row value differs from the assumed conclusion value.
        column: usize,
    },
}

/// A row-cover witness for `premises => conclusion` relative to one table.
///
/// The conclusion must be `false` or a negative indicator of a table variable.
/// Exactly one obstruction is supplied per original row. Public witness data may
/// be untrusted; construction does not validate it. Call [`Self::check`].
#[derive(Debug, Clone)]
pub struct TableCertificate {
    statement: TableStatement,
    /// Row `i` is blocked by `blockers[i]`; no row may be omitted.
    pub blockers: Vec<TableRowBlocker>,
}

/// Rejected table certificate. Malformed indexes never panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TableProofError(pub &'static str);

impl core::fmt::Display for TableProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}
impl core::error::Error for TableProofError {}

impl TableCertificate {
    /// Construct untrusted witness data associated with an original statement.
    pub fn new(statement: TableStatement, blockers: Vec<TableRowBlocker>) -> Self {
        Self {
            statement,
            blockers,
        }
    }

    /// Statement referenced by this certificate; authenticate it before use.
    pub fn statement(&self) -> &TableStatement {
        &self.statement
    }

    /// Whether this references the exact statement registered by the solver.
    /// This identity check prevents a callback substituting a different table.
    pub fn is_for(&self, statement: &TableStatement) -> bool {
        Arc::ptr_eq(&self.statement.0, &statement.0)
    }

    /// Check against an independently retained original statement and the exact
    /// implication being asserted. Unused premises merely weaken the lemma;
    /// their current truth is checked separately by the solver adapter.
    pub fn check(
        &self,
        original: &TableStatement,
        conclusion: TermId,
        premises: &[TermId],
    ) -> Result<(), TableProofError> {
        if original != &self.statement {
            return Err(TableProofError("certificate references a different table"));
        }
        let data = &original.0;
        let assumed = if conclusion == data.false_term {
            None
        } else {
            let Some((var, value)) = data.domains.iter().find_map(|(&var, d)| {
                d.negations
                    .iter()
                    .position(|&n| n == conclusion)
                    .and_then(|i| d.values.get(i).map(|value| (var, value)))
            }) else {
                return Err(TableProofError("unsupported table conclusion"));
            };
            Some((var, value))
        };
        if self.blockers.len() != data.rows.len() {
            return Err(TableProofError("witness does not cover every row"));
        }
        for (row, blocker) in data.rows.iter().zip(&self.blockers) {
            let cell = |column: usize| -> Result<(CpVar, &BigInt, &Domain), TableProofError> {
                let var = *data
                    .variables
                    .get(column)
                    .ok_or(TableProofError("invalid column"))?;
                let value = row
                    .get(column)
                    .ok_or(TableProofError("invalid row arity"))?;
                let domain = data
                    .domains
                    .get(&var)
                    .ok_or(TableProofError("missing domain"))?;
                Ok((var, value, domain))
            };
            let blocked = match *blocker {
                TableRowBlocker::OutsideDomain { column } => {
                    let (_, value, domain) = cell(column)?;
                    !domain.values.contains(value)
                }
                TableRowBlocker::Alias { first, second } => {
                    let (v, value, _) = cell(first)?;
                    let (w, other, _) = cell(second)?;
                    v == w && value != other
                }
                TableRowBlocker::Premise { column, premise } => {
                    let (_, value, domain) = cell(column)?;
                    let literal = premises
                        .get(premise)
                        .ok_or(TableProofError("invalid premise index"))?;
                    domain
                        .values
                        .iter()
                        .zip(&domain.atoms)
                        .zip(&domain.negations)
                        .any(|((v, p), n)| {
                            (literal == n && value == v) || (literal == p && value != v)
                        })
                }
                TableRowBlocker::NegatedConclusion { column } => {
                    let (var, value, _) = cell(column)?;
                    assumed.is_some_and(|(v, forced)| var == v && value != forced)
                }
            };
            if !blocked {
                return Err(TableProofError("row obstruction is not justified"));
            }
        }
        Ok(())
    }
}
