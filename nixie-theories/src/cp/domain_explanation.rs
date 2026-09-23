//! Witness production, separate from the finite-domain rule checker.
use super::domain_proof::{DomainCertificate, DomainRule, DomainStatement};
#[cfg(not(feature = "std"))]
use crate::prelude::Vec;
use nixie_core::ast::TermId;

impl DomainStatement {
    // The caller supplies an untrusted index from its current snapshot. Keep
    // checking the exact conclusion and premises with the standalone checker.
    pub(super) fn explain_fixed(
        &self,
        conclusion: TermId,
        reasons: &[TermId],
        fixed: usize,
    ) -> Option<DomainCertificate> {
        let certificate = DomainCertificate::new(self.clone(), DomainRule::Exclusion { fixed });
        certificate.check(self, conclusion, reasons).ok()?;
        Some(certificate)
    }

    pub(super) fn explain(
        &self,
        conclusion: TermId,
        reasons: &[TermId],
    ) -> Option<DomainCertificate> {
        let mut positives = reasons
            .iter()
            .enumerate()
            .filter(|(_, term)| self.domain.atoms.contains(term));
        let rule = if conclusion == self.false_term {
            if let Some((first, term)) = positives.next() {
                // Repeated copies of one positive literal cannot form a conflict.
                let (second, _) = positives.find(|(_, other)| *other != term)?;
                DomainRule::DistinctFixed { first, second }
            } else {
                let cover: Option<Vec<_>> = self
                    .domain
                    .negations
                    .iter()
                    .map(|negative| reasons.iter().position(|p| p == negative))
                    .collect();
                DomainRule::Exhausted(cover?)
            }
        } else {
            let excluded = self
                .domain
                .negations
                .iter()
                .position(|&n| n == conclusion)?;
            let (fixed, _) = positives.find(|(_, term)| **term != self.domain.atoms[excluded])?;
            DomainRule::Exclusion { fixed }
        };
        let certificate = DomainCertificate::new(self.clone(), rule);
        certificate.check(self, conclusion, reasons).ok()?;
        Some(certificate)
    }
}
