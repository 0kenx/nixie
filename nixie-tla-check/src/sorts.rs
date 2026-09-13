//! Turning inferred TLA+ types into SMT sorts.
//!
//! `nixie-tla`'s inferencer says what shape a name has; this says what the
//! solver should call it. The two are deliberately separate: inference is
//! about TLA+, and a type it cannot encode yet is still a correct type.
//!
//! # What is mapped, and what is not
//!
//! The scalar types map directly. Sets go to the solver's finite-set sort,
//! functions to an SMT array, and **tuples and records to single-constructor
//! datatypes** — each field keeping its own sort, which is the whole reason a
//! datatype works where an array does not. A sequence has no sort yet and is
//! declined by name rather than approximated.
//!
//! A type variable inference never constrained becomes an **uninterpreted
//! sort**, not a guess at a concrete one. That is the honest reading: the
//! specification says the values of this name are only ever compared for
//! equality, which is exactly what an uninterpreted sort means. The gradual
//! typing literature would call this `any` and insert a runtime cast; there is
//! no runtime here to check one, so the uninterpreted sort is both the
//! faithful and the only sound choice.

use nixie_core::{SortId, TermManager};
use nixie_tla::Type;

/// Why a type has no SMT sort yet.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0} has no SMT sort yet")]
pub struct NoSort(pub String);

/// The SMT sort for an inferred TLA+ type.
///
/// # Errors
///
/// Returns the shape it cannot map, by name. Never substitutes a different
/// sort: a state variable encoded at the wrong sort is a wrong answer, not a
/// missing feature.
pub fn sort_of(ty: &Type, tm: &mut TermManager) -> Result<SortId, NoSort> {
    match ty {
        Type::Bool => Ok(tm.sorts.bool_sort),
        Type::Int => Ok(tm.sorts.int_sort),
        Type::Str => Ok(tm.sorts.string_sort()),
        // An unconstrained type variable is a value the specification only ever
        // compares for equality. That is an uninterpreted sort, exactly.
        Type::Var(n) => {
            let spur = tm.intern_str(&format!("TlaOpaque{n}"));
            Ok(tm.sorts.intern(nixie_core::SortKind::Uninterpreted(spur)))
        }
        // A TLA+ set maps onto the solver's finite-set sort, which is the one
        // place a *state variable* of set type can live: the arena encoding
        // needs a statically known candidate list, and `s@1` has nowhere to
        // get one from. The theory carries membership, the binary operations,
        // extensional equality and cardinality itself.
        Type::Set(e) => {
            let elem = sort_of(e, tm)?;
            Ok(tm.sorts.set(elem))
        }
        Type::Seq(_) => Err(NoSort("a sequence".into())),
        // A TLA+ function maps onto an SMT array, which is a theory the solver
        // already has. What an array does **not** carry is the domain, and
        // that shows up in two places. Both err in the same direction, which
        // is the one that matters:
        //
        // * `f[x]` outside `DOMAIN f` is *undefined* in TLA+ and gets some
        //   value from the array, admitting behaviours the specification does
        //   not have.
        // * TLA+ function equality compares domains and the values on them;
        //   SMT array equality compares every index. Array equality is
        //   therefore **stricter**. In a positive position that costs nothing —
        //   the out-of-domain entries are free variables, so the solver picks
        //   witnesses that agree — but under a negation it lets two
        //   TLA+-equal functions be told apart.
        //
        // So the encoding can manufacture a counterexample and cannot hide
        // one: `Violation` may be spurious, `NoViolationWithin` stays sound.
        // That is the same asymmetry as a dropped assumption, and it is the
        // right way round. `Encoder::domain_unmodelled` surfaces it.
        Type::Fun(d, r) => {
            let dom = sort_of(d, tm)?;
            let rng = sort_of(r, tm)?;
            Ok(tm.sorts.array(dom, rng))
        }
        // A tuple and a record are **single-constructor datatypes**. The
        // objection that kept them structural was that an SMT array forces one
        // sort across every index, so `<<1, "a">>` could not be array-backed;
        // a datatype has no such problem, because each field carries its own
        // sort. This is how Z3 and CVC5 model them, and it is what a set of
        // tuples or a record-valued state variable needs in order to have a
        // sort at all.
        //
        // Structural values do not go away: the encoder still takes a tuple
        // apart for a literal index and still answers `DOMAIN` exactly. The
        // datatype is what it reifies *into* when a sort is needed.
        Type::Tuple(components) => {
            let mut fields = Vec::with_capacity(components.len());
            for (i, c) in components.iter().enumerate() {
                fields.push((tuple_field(i), sort_of(c, tm)?));
            }
            Ok(declare_struct(&fields, tm))
        }
        // An **open** record is refused. Inference marks one open when it only
        // ever saw field accesses, so the value may carry fields this type does
        // not list; a datatype over the known fields would make two records
        // that differ only in the rest compare *equal*, which hides a
        // counterexample rather than manufacturing one. A record literal closes
        // the row, so the ordinary case is closed.
        Type::Rec { open: true, .. } => Err(NoSort(
            "a record whose full set of fields is not known".into(),
        )),
        Type::Rec {
            fields: known,
            open: false,
        } => {
            // `BTreeMap`, so the field order is the same wherever the type is
            // built — two records written in a different order are one sort.
            let mut fields = Vec::with_capacity(known.len());
            for (name, t) in known {
                fields.push((record_field(name), sort_of(t, tm)?));
            }
            Ok(declare_struct(&fields, tm))
        }
    }
}

/// The selector for component `i` of a tuple, zero-based.
#[must_use]
pub fn tuple_field(i: usize) -> String {
    format!("@t{}", i + 1)
}

/// The selector for a record field.
///
/// Prefixed so that a record whose field is literally called `@t1` cannot
/// collide with a tuple's first component.
#[must_use]
pub fn record_field(name: &str) -> String {
    format!("@f{name}")
}

/// Declare (once) a single-constructor datatype and return its sort.
///
/// The name is a function of the **field names and their sorts**, not of the
/// TLA+ type it came from. That is what lets the encoder rebuild it: the
/// encoder holds values and their sorts, never the inferred type, so a name
/// derived from the type would be one the encoder could not compute. It also
/// makes the sort genuinely structural — two types that map to the same fields
/// are the same datatype, which is what makes two such values comparable.
///
/// Declaring is idempotent: a second caller finds it and takes the sort rather
/// than redefining the name.
pub(crate) fn declare_struct(fields: &[(String, SortId)], tm: &mut TermManager) -> SortId {
    let name = struct_name(fields, tm);
    if let Some(def) = tm.sorts.get_datatype(&name) {
        return def.sort_id;
    }
    let sort = tm.sorts.mk_datatype_sort(&name);
    // The constructor and selector names are interned in the **term**
    // manager's interner, not the sort manager's. `TermManager` and
    // `SortManager` keep separate interners, and the datatype axioms
    // (`nixie_solver::solver::dt_axioms::resolve_decl`) resolve these two
    // fields through the term manager — only `DataTypeDef::name` belongs to
    // the sort manager's own. Interning them in the wrong one does not fail:
    // it resolves to whatever string happens to sit at that index, so the
    // axioms are generated for names no term uses, the reconstruction axiom
    // never fires, and a datatype variable behaves like an opaque constant
    // whose selectors are unrelated to it. That reads as a wrong `sat`, and
    // it is how this comment came to be written.
    let ctor = nixie_core::sort::DataTypeConstructor {
        name: tm.intern_str(&name),
        selectors: fields.iter().map(|(f, s)| (tm.intern_str(f), *s)).collect(),
    };
    tm.sorts.declare_datatype(&name, vec![ctor]);
    sort
}

/// The selectors of a single-constructor datatype sort, in declaration order.
///
/// Resolved through the **term** manager's interner; see [`declare_struct`].
#[must_use]
pub(crate) fn struct_fields(sort: SortId, tm: &TermManager) -> Option<Vec<(String, SortId)>> {
    let name = tm.sorts.datatype_name(sort)?;
    let ctor = tm.sorts.get_datatype(name)?.constructors.first()?;
    Some(
        ctor.selectors
            .iter()
            .map(|(f, s)| (tm.resolve_str(*f).to_string(), *s))
            .collect(),
    )
}

/// The canonical name of a single-constructor datatype over these fields.
pub(crate) fn struct_name(fields: &[(String, SortId)], tm: &TermManager) -> String {
    let mut out = String::from("@tla{");
    for (i, (f, s)) in fields.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(f);
        out.push(':');
        out.push_str(&render_sort(*s, tm));
    }
    out.push('}');
    out
}

/// A sort rendered structurally.
///
/// `SortManager::sort_name` is not usable here: it renders every set as `Set`
/// and every array as `Array`, so `Set(Int)` and `Set(Str)` would name one
/// datatype and two unrelated tuples would share a sort. Written as an
/// explicit stack rather than a recursion because the sort it walks comes from
/// a user-written type.
pub(crate) fn render_sort(sort: SortId, tm: &TermManager) -> String {
    use nixie_core::SortKind;
    /// What to do when the frame comes back up.
    enum Step {
        Emit(SortId),
        Text(&'static str),
    }
    let mut out = String::new();
    let mut stack = vec![Step::Emit(sort)];
    // Bounded: a sort is a finite tree, but a malformed one must not spin.
    let mut budget = 100_000usize;
    while let Some(step) = stack.pop() {
        budget = match budget.checked_sub(1) {
            Some(b) => b,
            None => return out,
        };
        match step {
            Step::Text(t) => out.push_str(t),
            Step::Emit(id) => match tm.sorts.get(id).map(|s| &s.kind) {
                Some(SortKind::Bool) => out.push_str("Bool"),
                Some(SortKind::Int) => out.push_str("Int"),
                Some(SortKind::Real) => out.push_str("Real"),
                Some(SortKind::String) => out.push_str("Str"),
                Some(SortKind::BitVec(w)) => out.push_str(&format!("BV{w}")),
                Some(SortKind::Set(e)) => {
                    out.push_str("Set(");
                    stack.push(Step::Text(")"));
                    stack.push(Step::Emit(*e));
                }
                Some(SortKind::Array { domain, range }) => {
                    out.push_str("Arr(");
                    stack.push(Step::Text(")"));
                    stack.push(Step::Emit(*range));
                    stack.push(Step::Text(","));
                    stack.push(Step::Emit(*domain));
                }
                // The two name kinds live in *different* interners: an
                // uninterpreted sort's name is interned by whoever built it
                // through the term manager (this module included, matching the
                // SMT-LIB parser and printer), a datatype's by the sort
                // manager in `declare_datatype`. Resolving either through the
                // wrong one is an out-of-range index, which panics.
                Some(SortKind::Uninterpreted(spur)) => out.push_str(tm.resolve_str(*spur)),
                Some(SortKind::Datatype(spur)) => out.push_str(tm.sorts.resolve_spur(*spur)),
                // Anything else is named by its id, which is unique within
                // this `TermManager` — unambiguous, if unreadable. Never
                // omitted: two sorts sharing a rendering would share a
                // datatype.
                _ => out.push_str(&format!("S{}", id.0)),
            },
        }
    }
    out
}
