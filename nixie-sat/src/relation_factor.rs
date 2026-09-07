//! Exact, opt-in CNF factorization of eight-variable functional relations.
//!
//! This is an offline transformation, never called by ordinary solver paths.
//! All variables retain their meaning. Each replacement is exhaustively
//! checked and carries binary-resolution LRAT steps from original clause IDs.
//! The emitted prefix is a preprocessing certificate, not an UNSAT proof.

use std::collections::BTreeMap;
use std::io::{self, Write};

/// Deterministic resource bounds for the offline transformer.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Maximum number of input clauses inspected.
    pub clauses: usize,
    /// Maximum number of input literals inspected.
    pub literals: usize,
    /// Maximum number of distinct eight-variable supports retained.
    pub groups: usize,
    /// Maximum number of binary-resolution steps retained.
    pub resolutions: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            clauses: 2_000_000,
            literals: 16_000_000,
            groups: 10_000,
            resolutions: 5_000_000,
        }
    }
}

/// Transformation failure. The input is borrowed and is never modified.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactorError {
    /// A deterministic resource cap was exceeded; retain the original CNF.
    Limit,
    /// A literal is zero, unrepresentable, or exceeds the declared variables.
    InvalidLiteral(i32),
    /// A clause ID cannot be represented by LRAT's signed 64-bit IDs.
    IdOverflow,
    /// A candidate's exact equivalence or resolution certificate failed.
    Certificate,
}

impl core::fmt::Display for FactorError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Limit => f.write_str("relation factorization resource limit exceeded"),
            Self::InvalidLiteral(lit) => write!(f, "invalid DIMACS literal {lit}"),
            Self::IdOverflow => f.write_str("relation factorization clause ID overflow"),
            Self::Certificate => f.write_str("relation factorization certificate failed"),
        }
    }
}

impl std::error::Error for FactorError {}

#[derive(Debug)]
struct Resolution {
    id: i64,
    clause: Vec<i32>,
    parents: [i64; 2],
    retained: bool,
}

#[derive(Debug)]
struct Group {
    /// Lowest original clause index for each forbidden assignment.
    rows: [usize; 256],
    originals: Vec<usize>,
}

impl Group {
    fn new() -> Self {
        Self {
            rows: [usize::MAX; 256],
            originals: Vec::new(),
        }
    }
}

/// An equivalent CNF and its preprocessing proof. Constructed only by
/// [`factor_relations`]; callers cannot alter the certified output in place.
#[derive(Debug)]
pub struct Factorization {
    clauses: Vec<Vec<i32>>,
    clause_ids: Vec<i64>,
    steps: Vec<Resolution>,
    deleted: Vec<i64>,
    groups: usize,
    last_id: i64,
}

impl Factorization {
    /// Equivalent clauses, in output order, with unchanged variable IDs.
    #[must_use]
    pub fn clauses(&self) -> &[Vec<i32>] {
        &self.clauses
    }

    /// Proof IDs of output clauses, in the same order as [`Self::clauses`].
    /// Remap a downstream solver's original IDs through this table and assign
    /// its derived IDs above [`Self::last_proof_id`] before appending its proof.
    #[must_use]
    pub fn clause_ids(&self) -> &[i64] {
        &self.clause_ids
    }

    /// Last ID allocated by this prefix (or the original clause count).
    #[must_use]
    pub fn last_proof_id(&self) -> i64 {
        self.last_id
    }

    /// Number of completely replaced relation groups.
    #[must_use]
    pub fn groups(&self) -> usize {
        self.groups
    }

    /// Number of explicitly certified binary-resolution additions.
    #[must_use]
    pub fn resolutions(&self) -> usize {
        self.steps.len()
    }

    /// Write the text LRAT prefix. Original clauses are numbered from one in
    /// their input order. Every addition has two earlier, live parent IDs.
    /// Final deletions leave precisely the exported output clauses active.
    ///
    /// # Errors
    /// Propagates any output error; a partial file is not a certificate.
    pub fn write_lrat_prefix(&self, mut writer: impl Write) -> io::Result<()> {
        for step in &self.steps {
            write!(writer, "{} ", step.id)?;
            for lit in &step.clause {
                write!(writer, "{lit} ")?;
            }
            writeln!(writer, "0 {} {} 0", step.parents[0], step.parents[1])?;
        }
        if !self.deleted.is_empty() {
            write!(writer, "{} d ", self.last_id)?;
            for id in &self.deleted {
                write!(writer, "{id} ")?;
            }
            writeln!(writer, "0")?;
        }
        Ok(())
    }
}

fn clause(vars: &[i32; 8], mask: u8, forbidden: u8) -> Vec<i32> {
    vars.iter()
        .enumerate()
        .filter_map(|(i, &var)| {
            (mask & (1 << i) != 0).then_some(if forbidden & (1 << i) == 0 { var } else { -var })
        })
        .collect()
}

fn basis(allowed: &[u8]) -> Option<u8> {
    // Lexicographic combinations, independent of hash iteration or SAT RNG.
    for a in 0..5 {
        for b in a + 1..6 {
            for c in b + 1..7 {
                for d in c + 1..8 {
                    let mask = (1 << a) | (1 << b) | (1 << c) | (1 << d);
                    let mut seen = [false; 256];
                    if allowed.iter().all(|&row| {
                        let entry = &mut seen[(row & mask) as usize];
                        let fresh = !*entry;
                        *entry = true;
                        fresh
                    }) {
                        return Some(mask);
                    }
                }
            }
        }
    }
    None
}

fn derive(
    result: &mut Factorization,
    vars: &[i32; 8],
    group: &Group,
    mask: u8,
    forbidden: u8,
    limit: usize,
) -> Result<(), FactorError> {
    if result.steps.len().checked_add(7).is_none_or(|n| n > limit) {
        return Err(FactorError::Limit);
    }
    let free: Vec<usize> = (0..8).filter(|&i| mask & (1 << i) == 0).collect();
    if free.len() != 3 {
        return Err(FactorError::Certificate);
    }
    let mut nodes = Vec::with_capacity(8);
    for code in 0..8 {
        let mut row = forbidden & mask;
        for (j, &i) in free.iter().enumerate() {
            if code & (1 << j) != 0 {
                row |= 1 << i;
            }
        }
        let original = group.rows[row as usize];
        if original == usize::MAX {
            return Err(FactorError::Certificate);
        }
        let id = i64::try_from(original).map_err(|_| FactorError::IdOverflow)? + 1;
        nodes.push((row, id));
    }
    let mut live_mask = u8::MAX;
    for pivot in free {
        live_mask &= !(1 << pivot);
        let mut next = Vec::with_capacity(nodes.len() / 2);
        for pair in nodes.chunks_exact(2) {
            if pair[0].0 ^ pair[1].0 != 1 << pivot {
                return Err(FactorError::Certificate);
            }
            let row = pair[0].0 & live_mask;
            result.last_id = result
                .last_id
                .checked_add(1)
                .ok_or(FactorError::IdOverflow)?;
            result.steps.push(Resolution {
                id: result.last_id,
                clause: clause(vars, live_mask, row),
                parents: [pair[0].1, pair[1].1],
                retained: live_mask == mask,
            });
            next.push((row, result.last_id));
        }
        nodes = next;
    }
    if nodes.len() != 1 || live_mask != mask {
        return Err(FactorError::Certificate);
    }
    result.clauses.push(clause(vars, mask, forbidden));
    result.clause_ids.push(result.last_id);
    Ok(())
}

/// Factor fully specified eight-variable relations with sixteen allowed rows
/// and a bijective projection onto four variables. No new variables are used.
/// Unrecognized groups and all other clauses are preserved verbatim. The
/// output places unchanged clauses first, then replacements by sorted support,
/// allowed assignment and output variable. Duplicate source rows retain their
/// first clause as proof provenance; all copies in a replaced group are deleted.
///
/// # Errors
/// Returns [`FactorError::Limit`] on bounded extraction/proof exhaustion; the
/// caller can retain the untouched input. Invalid literals, ID overflow and
/// failed certificates are errors, never partially accepted transformations.
pub fn factor_relations(
    num_vars: usize,
    input: &[Vec<i32>],
    limits: Limits,
) -> Result<Factorization, FactorError> {
    if input.len() > limits.clauses {
        return Err(FactorError::Limit);
    }
    let original_count = i64::try_from(input.len()).map_err(|_| FactorError::IdOverflow)?;
    let mut groups = BTreeMap::<[i32; 8], Group>::new();
    let mut literals = 0usize;
    for (index, lits) in input.iter().enumerate() {
        literals = literals.checked_add(lits.len()).ok_or(FactorError::Limit)?;
        if literals > limits.literals {
            return Err(FactorError::Limit);
        }
        for &lit in lits {
            if lit == 0 || lit == i32::MIN || lit.unsigned_abs() as usize > num_vars {
                return Err(FactorError::InvalidLiteral(lit));
            }
        }
        let Ok(mut sorted) = <[i32; 8]>::try_from(lits.as_slice()) else {
            continue;
        };
        sorted.sort_unstable_by_key(|lit| lit.unsigned_abs());
        if sorted
            .windows(2)
            .any(|p| p[0].unsigned_abs() == p[1].unsigned_abs())
        {
            continue;
        }
        let vars = sorted.map(i32::abs);
        if groups.len() >= limits.groups && !groups.contains_key(&vars) {
            return Err(FactorError::Limit);
        }
        let group = groups.entry(vars).or_insert_with(Group::new);
        let row = sorted
            .iter()
            .enumerate()
            .fold(0usize, |row, (i, lit)| row | (usize::from(*lit < 0) << i));
        if group.rows[row] == usize::MAX {
            group.rows[row] = index;
        }
        group.originals.push(index);
    }
    let mut result = Factorization {
        clauses: Vec::new(),
        clause_ids: Vec::new(),
        steps: Vec::new(),
        deleted: Vec::new(),
        groups: 0,
        last_id: original_count,
    };
    let mut replaced = vec![false; input.len()];
    for (vars, group) in groups {
        let allowed: Vec<u8> = group
            .rows
            .iter()
            .enumerate()
            .filter_map(|(row, &id)| (id == usize::MAX).then_some(row as u8))
            .collect();
        if allowed.len() != 16 {
            continue;
        }
        let Some(inputs) = basis(&allowed) else {
            continue;
        };
        let mut cubes = Vec::with_capacity(64);
        for &row in &allowed {
            for output in 0..8 {
                let bit = 1 << output;
                if inputs & bit != 0 {
                    continue;
                }
                cubes.push((inputs | bit, row ^ bit));
            }
        }
        // Independent local semantic check before generating or deleting any
        // clauses. It proves the reverse implication too, which LRAT additions
        // alone cannot prove (deletion is merely satisfiability preserving).
        for row in 0..256 {
            let satisfies = cubes
                .iter()
                .all(|&(mask, forbidden)| (row as u8 & mask) != (forbidden & mask));
            if satisfies != (group.rows[row] == usize::MAX) {
                return Err(FactorError::Certificate);
            }
        }
        for (mask, forbidden) in cubes {
            derive(
                &mut result,
                &vars,
                &group,
                mask,
                forbidden,
                limits.resolutions,
            )?;
        }
        for index in group.originals {
            replaced[index] = true;
        }
        result.groups += 1;
    }
    let mut unchanged = Vec::with_capacity(input.len());
    let mut unchanged_ids = Vec::with_capacity(input.len());
    for (index, lits) in input.iter().enumerate() {
        let id = i64::try_from(index).map_err(|_| FactorError::IdOverflow)? + 1;
        if replaced[index] {
            result.deleted.push(id);
        } else {
            unchanged.push(lits.clone());
            unchanged_ids.push(id);
        }
    }
    unchanged.append(&mut result.clauses);
    unchanged_ids.append(&mut result.clause_ids);
    result.clauses = unchanged;
    result.clause_ids = unchanged_ids;
    result
        .deleted
        .extend(result.steps.iter().filter(|s| !s.retained).map(|s| s.id));
    Ok(result)
}

#[cfg(test)]
mod tests;
