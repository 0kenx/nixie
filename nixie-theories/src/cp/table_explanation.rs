//! Witness production, kept separate from the standalone table checker.
use super::*;
use table_proof::{TableCertificate, TableRowBlocker, TableStatement};

impl TableStatement {
    pub(super) fn explain(
        &self,
        conclusion: TermId,
        reasons: &[TermId],
    ) -> Option<TableCertificate> {
        let data = &self.0;
        let forced = data.domains.iter().find_map(|(&var, d)| {
            d.negations
                .iter()
                .enumerate()
                .find_map(|(i, &n)| (n == conclusion).then(|| (var, &d.values[i])))
        });
        let mut blockers = Vec::with_capacity(data.rows.len());
        for row in &data.rows {
            let mut obstruction = None;
            for (column, &var) in data.variables.iter().enumerate() {
                let domain = data.domains.get(&var)?;
                let value = row.get(column)?;
                if !domain.values.contains(value) {
                    obstruction = Some(TableRowBlocker::OutsideDomain { column });
                    break;
                }
                if let Some(first) = data.variables[..column]
                    .iter()
                    .enumerate()
                    .find_map(|(i, &v)| (v == var && row[i] != *value).then_some(i))
                {
                    obstruction = Some(TableRowBlocker::Alias {
                        first,
                        second: column,
                    });
                    break;
                }
                if forced.is_some_and(|(v, x)| v == var && x != value) {
                    obstruction = Some(TableRowBlocker::NegatedConclusion { column });
                    break;
                }
                for (index, domain_value) in domain.values.iter().enumerate() {
                    let blocking = if domain_value == value {
                        domain.negations[index]
                    } else {
                        domain.atoms[index]
                    };
                    if let Some(premise) = reasons.iter().position(|&r| r == blocking) {
                        obstruction = Some(TableRowBlocker::Premise { column, premise });
                        break;
                    }
                }
                if obstruction.is_some() {
                    break;
                }
            }
            blockers.push(obstruction?);
        }
        let certificate = TableCertificate::new(self.clone(), blockers);
        // Even internally produced witnesses must pass the independent checker.
        certificate.check(self, conclusion, reasons).ok()?;
        Some(certificate)
    }
}
