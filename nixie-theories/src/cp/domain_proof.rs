//! Standalone checking of finite-domain exactly-one lemmas.
//!
//! No callback state or filtering code is consulted. The caller must retain and
//! authenticate the original domain, then separately check current premise truth.
use super::Domain;
use crate::prelude::*;
use nixie_core::ast::TermId;
use num_bigint::BigInt;

/// Immutable original domain and its indicator meanings.
/// Obtain it through `CpModel::domain_statements`; term IDs belong to that model's
/// term manager. The statement asserts exactly one indicator, not just at least one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainStatement {
    pub(super) domain: Arc<Domain>,
    pub(super) false_term: TermId,
}
impl DomainStatement {
    /// Original values with their positive and negative indicators.
    pub fn indicators(&self) -> impl Iterator<Item = (&BigInt, TermId, TermId)> {
        self.domain
            .values
            .iter()
            .zip(&self.domain.atoms)
            .zip(&self.domain.negations)
            .map(|((value, &positive), &negative)| (value, positive, negative))
    }
}

/// A local exactly-one rule. All indexes refer to the implication's premises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainRule {
    /// Two different positive indicators of this domain imply false.
    DistinctFixed {
        /// First positive premise.
        first: usize,
        /// Second positive premise.
        second: usize,
    },
    /// One positive indicator excludes a different value of this domain.
    Exclusion {
        /// Positive premise fixing the other value.
        fixed: usize,
    },
    /// Each original value is excluded. Slot `i` indexes the negative premise
    /// for original value `i`; every original value must be covered exactly once.
    Exhausted(Vec<usize>),
}

/// Untrusted witness for `premises => conclusion` relative to one original domain.
#[derive(Debug, Clone)]
pub struct DomainCertificate {
    statement: DomainStatement,
    /// Rule and its witness indexes; construction does not check them.
    pub rule: DomainRule,
}

/// Invalid exactly-one witness; malformed indexes are errors, never panics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DomainProofError(pub &'static str);
impl core::fmt::Display for DomainProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}
impl core::error::Error for DomainProofError {}

impl DomainCertificate {
    /// Construct untrusted witness data; call `check` before accepting it.
    pub fn new(statement: DomainStatement, rule: DomainRule) -> Self {
        Self { statement, rule }
    }
    /// Referenced statement, which a consumer must authenticate independently.
    pub fn statement(&self) -> &DomainStatement {
        &self.statement
    }
    /// Exact identity of a registered domain, preserved across statement clones.
    pub fn is_for(&self, original: &DomainStatement) -> bool {
        self.statement.false_term == original.false_term
            && Arc::ptr_eq(&self.statement.domain, &original.domain)
    }
    /// Check the exact implication against an independently retained original.
    /// Unused premises are harmless weakening; their current truth is separate.
    pub fn check(
        &self,
        original: &DomainStatement,
        conclusion: TermId,
        premises: &[TermId],
    ) -> Result<(), DomainProofError> {
        if original != &self.statement {
            return Err(DomainProofError(
                "certificate references a different domain",
            ));
        }
        let domain = &original.domain;
        let positive = |index: usize| -> Result<usize, DomainProofError> {
            let term = premises
                .get(index)
                .ok_or(DomainProofError("invalid premise index"))?;
            domain
                .atoms
                .iter()
                .position(|p| p == term)
                .ok_or(DomainProofError(
                    "premise is not a positive domain indicator",
                ))
        };
        let valid = match &self.rule {
            DomainRule::DistinctFixed { first, second } => {
                conclusion == original.false_term && positive(*first)? != positive(*second)?
            }
            DomainRule::Exclusion { fixed } => {
                let index = positive(*fixed)?;
                domain
                    .negations
                    .iter()
                    .position(|&n| n == conclusion)
                    .is_some_and(|excluded| excluded != index)
            }
            DomainRule::Exhausted(cover) => {
                conclusion == original.false_term
                    && cover.len() == domain.negations.len()
                    && cover
                        .iter()
                        .zip(&domain.negations)
                        .all(|(&index, negative)| premises.get(index) == Some(negative))
            }
        };
        if valid {
            Ok(())
        } else {
            Err(DomainProofError("domain rule is not justified"))
        }
    }
}
