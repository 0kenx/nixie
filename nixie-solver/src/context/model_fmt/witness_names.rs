//! The `@uc_S_n` witness names of one model rendering, minted without
//! rescanning the declarations for every name.
//!
//! [`Context::build_class_values`] gives every congruence class of an
//! uninterpreted sort a Z3-style abstract witness `@uc_<sort>_<n>`, numbered
//! in declaration order, and steps over the numbers the script itself
//! declared: a user constant named `@uc_U_0` is an ordinary constant, not a
//! reference to the model's first witness.  Each fresh witness used to rescan
//! every declared constant and function name for that collision check, so a
//! model with n unconstrained constants of one sort scanned n² names – 64
//! million for 8,000 constants, and not one of them collided.
//!
//! [`WitnessNames`] collects the declared suffixes once, when a rendering
//! asks for its first witness, and then hands each sort its free numbers
//! through a cursor: a declaration-order pass pays one lookup per witness.
//! The names are the ones the per-witness scan minted, digit for digit –
//! `@uc_U_00` included, which is a user symbol and reserves nothing.  The
//! split of a declared name into sort and suffix is the reader's own
//! (`printed_check::parse_typed_printed_term`, the last underscore): a
//! canonical number holds no underscore, so the two readings agree on every
//! name either one takes for a reservation.
//!
//! Only declarations are read, never the parse-back artifacts a
//! `(get-value)` leaves in the term arena, so repeated `(get-model)` /
//! `(get-value)` calls keep one numbering – and numbering fresh spellings
//! only is what keeps a declared `@uc_U_0` from turning an abstract value
//! into a self-reference.

use std::cmp::Ordering;

use crate::prelude::*;
use nixie_core::sort::SortId;

use super::{Context, published::WITNESS_PLACEHOLDER};

/// The witness names of one model rendering.
#[derive(Default)]
pub(super) struct WitnessNames {
    /// Declared witness suffixes by sort name, ascending – `None` until the
    /// first witness is asked for, so a rendering over no uninterpreted sort
    /// never walks the declarations.
    reserved: Option<FxHashMap<String, Vec<u128>>>,
    /// The sorts asked for so far, and where each one's cursor stands.
    sorts: FxHashMap<SortId, SortWitnesses>,
    /// How many times the declarations were walked (one per rendering).
    #[cfg(test)]
    scans: usize,
}

/// One sort's witnesses: a prefix, the numbers the script declared, and the
/// cursor a declaration-order pass advances.
struct SortWitnesses {
    /// `@uc_<sort>_`, which every witness of the sort starts with.  The bars
    /// of a quoted sort name are removed here and put back by `spell`: a sort
    /// `|W X|` spells its witnesses `|@uc_W X_n|`.
    prefix: String,
    /// The suffixes a declared constant or function of this sort already
    /// holds, ascending and deduplicated.
    reserved: Vec<u128>,
    /// The index of the witness the cursor names next.
    index: usize,
    /// The number that witness takes – the `index`-th free number of the sort.
    number: u128,
    /// How many of `reserved` lie at or below `number`; a forward pass never
    /// revisits them.
    skipped: usize,
}

impl WitnessNames {
    /// The name of the `index`-th witness of `sort` – its `index`-th number
    /// that no declared constant or function holds.
    ///
    /// Indices are counted from zero per sort.  A pass that asks in
    /// declaration order (`0, 1, 2, …`) is served from the cursor; an index
    /// below the cursor – a pass that restarted, as the finite universes do
    /// per size – is counted the plain way.
    pub(super) fn nth(&mut self, ctx: &Context, sort: SortId, index: usize) -> String {
        if self.reserved.is_none() {
            self.reserved = Some(collect_reserved(ctx));
            #[cfg(test)]
            {
                self.scans += 1;
            }
        }
        let reserved = &self.reserved;
        let witnesses = self.sorts.entry(sort).or_insert_with(|| {
            let rendered = ctx.format_sort_name(sort);
            let name = rendered
                .strip_prefix('|')
                .and_then(|name| name.strip_suffix('|'))
                .unwrap_or(&rendered);
            let reserved = reserved
                .as_ref()
                .and_then(|reserved| reserved.get(name))
                .cloned()
                .unwrap_or_default();
            let mut witnesses = SortWitnesses {
                prefix: format!("{WITNESS_PLACEHOLDER}{name}_"),
                reserved,
                index: 0,
                number: 0,
                skipped: 0,
            };
            witnesses.number = witnesses.next_free(0);
            witnesses
        });
        witnesses.nth(index)
    }
}

impl SortWitnesses {
    /// [`WitnessNames::nth`] for a sort whose reserved numbers are known.
    fn nth(&mut self, index: usize) -> String {
        if index < self.index {
            return self.spell(free_by_rank(&self.reserved, index));
        }
        while self.index < index {
            self.number = self.next_free(self.number + 1);
            self.index += 1;
        }
        let number = self.number;
        self.number = self.next_free(self.number + 1);
        self.index += 1;
        self.spell(number)
    }

    /// The first free number at or above `from`, advancing past the reserved
    /// numbers the cursor has caught up with.
    fn next_free(&mut self, from: u128) -> u128 {
        let mut candidate = from;
        while let Some(&reserved) = self.reserved.get(self.skipped) {
            match reserved.cmp(&candidate) {
                Ordering::Less => self.skipped += 1,
                Ordering::Equal => {
                    self.skipped += 1;
                    candidate += 1;
                }
                Ordering::Greater => break,
            }
        }
        candidate
    }

    fn spell(&self, number: u128) -> String {
        nixie_core::smtlib::format_symbol(&format!("{}{number}", self.prefix))
    }
}

/// Every witness-shaped declared name, by sort name: `@uc_<sort>_<n>` with
/// `n` spelled in canonical digits reserves `n` for `<sort>`.
///
/// One walk over the constants and the functions, however many sorts the
/// rendering goes on to name.  A suffix such as `00`, `_7` or `+7` is a user
/// symbol's tail and reserves nothing, as under the per-witness scan.
fn collect_reserved(ctx: &Context) -> FxHashMap<String, Vec<u128>> {
    let mut reserved: FxHashMap<String, Vec<u128>> = FxHashMap::default();
    let names = ctx
        .declared_consts
        .iter()
        .map(|decl| decl.name.as_str())
        .chain(ctx.declared_funs.iter().map(|decl| decl.name.as_str()));
    for symbol in names {
        let Some(rest) = symbol.strip_prefix(WITNESS_PLACEHOLDER) else {
            continue;
        };
        let Some((sort, suffix)) = rest.rsplit_once('_') else {
            continue;
        };
        let Ok(number) = suffix.parse::<u128>() else {
            continue;
        };
        if number.to_string() != suffix {
            continue;
        }
        reserved.entry(sort.to_string()).or_default().push(number);
    }
    for numbers in reserved.values_mut() {
        numbers.sort_unstable();
        numbers.dedup();
    }
    reserved
}

/// The `index`-th number no member of the ascending, deduplicated
/// `reserved` holds: the count the cursor serves without walking.
fn free_by_rank(reserved: &[u128], index: usize) -> u128 {
    let mut candidate = index as u128;
    for &number in reserved {
        if number > candidate {
            break;
        }
        candidate += 1;
    }
    candidate
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The per-witness scan this module replaced, kept as the oracle: every
    /// name minted here must be the name it minted.
    fn scanned(ctx: &Context, sort: SortId, index: usize) -> String {
        let rendered = ctx.format_sort_name(sort);
        let name = rendered
            .strip_prefix('|')
            .and_then(|name| name.strip_suffix('|'))
            .unwrap_or(&rendered);
        let prefix = format!("{WITNESS_PLACEHOLDER}{name}_");
        let mut occupied: Vec<u128> = ctx
            .declared_consts
            .iter()
            .map(|decl| decl.name.as_str())
            .chain(ctx.declared_funs.iter().map(|decl| decl.name.as_str()))
            .filter_map(|symbol| {
                let suffix = symbol.strip_prefix(&prefix)?;
                let number = suffix.parse::<u128>().ok()?;
                (number.to_string() == suffix).then_some(number)
            })
            .collect();
        occupied.sort_unstable();
        occupied.dedup();
        let mut candidate = index as u128;
        for reserved in occupied {
            if reserved > candidate {
                break;
            }
            candidate += 1;
        }
        nixie_core::smtlib::format_symbol(&format!("{prefix}{candidate}"))
    }

    /// Six sorts whose declared names between them spell canonical, non-canonical,
    /// overflowing, quoted and underscore-bearing reservations.
    fn context() -> (Context, [SortId; 6]) {
        let mut ctx = Context::new();
        ctx.execute_script(
            "(declare-sort U 0)
             (declare-sort U_ 0)
             (declare-sort A 0)
             (declare-sort A_1 0)
             (declare-sort |W X| 0)
             (declare-sort V 0)
             (declare-const plain U)
             (declare-const @uc_U_0 U)
             (declare-const @uc_U_00 U)
             (declare-const @uc_U_3 U)
             (declare-const @uc_U_5 U)
             (declare-const @uc_U__7 U)
             (declare-const @uc_U_+9 U)
             (declare-const @uc_U_340282366920938463463374607431768211456 U)
             (declare-fun @uc_U_2 () U)
             (declare-fun f (U) U)
             (declare-const under U_)
             (declare-const @uc_A_1 A)
             (declare-const @uc_A_1_2 A_1)
             (declare-const |@uc_W X_4| |W X|)
             (declare-const |@uc_W X_00| |W X|)
             (declare-const @uc_U A)
             (declare-const @uc_ A)
             (declare-const @uc_V_00 V)
             (declare-const plain_v V)",
        )
        .expect("declarations");
        let sort_of = |name: &str| {
            ctx.declared_consts
                .iter()
                .find(|decl| decl.name == name)
                .expect(name)
                .sort
        };
        let sorts = [
            sort_of("plain"),
            sort_of("under"),
            sort_of("@uc_A_1"),
            sort_of("@uc_A_1_2"),
            sort_of("@uc_W X_4"),
            sort_of("plain_v"),
        ];
        (ctx, sorts)
    }

    /// Every name of a declaration-order pass, of a pass that rewinds, and of
    /// one that skips ahead is the scanned name – on sorts whose declared
    /// names include canonical, non-canonical, overflowing, quoted and
    /// underscore-bearing spellings.
    #[test]
    fn minted_names_are_the_scanned_names() {
        let (ctx, sorts) = context();
        let mut names = WitnessNames::default();
        for &sort in &sorts {
            let sequence = (0..12)
                .chain([3, 0, 9, 1, 12, 13, 4, 20, 19, 21, 2, 22])
                .chain(0..40);
            for index in sequence {
                assert_eq!(
                    names.nth(&ctx, sort, index),
                    scanned(&ctx, sort, index),
                    "sort {:?}, index {index}",
                    ctx.format_sort_name(sort)
                );
            }
        }
    }

    /// The collisions the scan was written for: a declared `@uc_U_0` moves
    /// the first witness to `@uc_U_1`; `@uc_U_00`, `@uc_U_+9` and an
    /// overflowing suffix are user symbols and move nothing; a function name
    /// reserves like a constant's; and a name reserves for the sort its last
    /// underscore leaves (`@uc_U__7` for `U_`, `@uc_A_1_2` for `A_1`).
    #[test]
    fn reserved_spellings_are_stepped_over_and_user_symbols_are_not() {
        let (ctx, [uninterpreted, under, a, a_1, quoted, lookalike]) = context();
        let mut names = WitnessNames::default();
        let nth = |names: &mut WitnessNames, sort, index| names.nth(&ctx, sort, index).to_string();
        // 0, 2 (the function), 3 and 5 are taken.
        assert_eq!(nth(&mut names, uninterpreted, 0), "@uc_U_1");
        assert_eq!(nth(&mut names, uninterpreted, 1), "@uc_U_4");
        assert_eq!(nth(&mut names, uninterpreted, 2), "@uc_U_6");
        assert_eq!(nth(&mut names, uninterpreted, 3), "@uc_U_7");
        assert_eq!(nth(&mut names, under, 0), "@uc_U__0");
        assert_eq!(nth(&mut names, under, 7), "@uc_U__8");
        assert_eq!(nth(&mut names, a, 0), "@uc_A_0");
        assert_eq!(nth(&mut names, a, 1), "@uc_A_2");
        assert_eq!(nth(&mut names, a_1, 0), "@uc_A_1_0");
        assert_eq!(nth(&mut names, a_1, 2), "@uc_A_1_3");
        assert_eq!(nth(&mut names, quoted, 0), "|@uc_W X_0|");
        assert_eq!(nth(&mut names, quoted, 4), "|@uc_W X_5|");
        // `@uc_V_00` alone reserves nothing: `00` is not the spelling of zero.
        assert_eq!(nth(&mut names, lookalike, 0), "@uc_V_0");
        assert_eq!(nth(&mut names, lookalike, 1), "@uc_V_1");
        // A name the cursor has already passed is answered the same way on the way back.
        assert_eq!(nth(&mut names, uninterpreted, 0), "@uc_U_1");
        assert_eq!(nth(&mut names, uninterpreted, 2), "@uc_U_6");
    }

    /// The declarations are walked once per rendering, however many witnesses
    /// and sorts follow.
    #[test]
    fn the_declarations_are_walked_once() {
        let (ctx, sorts) = context();
        let mut names = WitnessNames::default();
        for _ in 0..4 {
            for &sort in &sorts {
                for index in 0..16 {
                    let _ = names.nth(&ctx, sort, index);
                }
            }
        }
        assert_eq!(names.scans, 1);
        // …and not at all for a rendering that names no witness.
        assert_eq!(WitnessNames::default().scans, 0);
    }
}
