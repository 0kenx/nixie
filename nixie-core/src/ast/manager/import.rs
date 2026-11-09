//! Transfer a DAG between independent arenas without reusing local identifiers.
use super::*;
use crate::error::{NixieError, Result};
use crate::sort::{DataTypeConstructor, SortKind};
use smallvec::SmallVec;

struct Importer<'a> {
    source: &'a TermManager,
    target: &'a mut TermManager,
    terms: FxHashMap<TermId, TermId>,
    sorts: FxHashMap<SortId, SortId>,
}

impl TermManager {
    /// Copy a term DAG, its symbols, sorts, and datatype definitions from an
    /// independent manager. Existing structurally equal target terms are reused.
    ///
    /// # Errors
    /// Rejects missing references, malformed cycles, and conflicting datatype
    /// definitions. Importing may intern terms before an error is discovered.
    pub fn import_term(&mut self, source: &TermManager, root: TermId) -> Result<TermId> {
        let mut importer = Importer {
            source,
            target: self,
            terms: FxHashMap::default(),
            sorts: FxHashMap::default(),
        };
        let mut stack = vec![(root, false)];
        let mut active = FxHashSet::default();
        while let Some((term, finish)) = stack.pop() {
            if importer.terms.contains_key(&term) {
                continue;
            }
            let node = source
                .get(term)
                .ok_or(NixieError::InvalidTermId(term.raw()))?;
            if finish {
                let sort = importer.sort(node.sort)?;
                let mut kind = node.kind.clone();
                importer.remap(&mut kind)?;
                let imported = importer.target.intern_term(kind, sort);
                importer.terms.insert(term, imported);
                active.remove(&term);
            } else {
                if !active.insert(term) {
                    return Err(NixieError::Unsupported("cyclic term DAG in import".into()));
                }
                stack.push((term, true));
                let mut children = get_children(&node.kind);
                if let TermKind::Forall { patterns, .. } | TermKind::Exists { patterns, .. } =
                    &node.kind
                {
                    children.extend(patterns.iter().flatten().copied());
                }
                stack.extend(children.into_iter().rev().map(|child| (child, false)));
            }
        }
        importer.target.rounding_mode_used |= source.rounding_mode_used;
        importer.term(root)
    }
}

impl Importer<'_> {
    fn term(&self, term: TermId) -> Result<TermId> {
        self.terms
            .get(&term)
            .copied()
            .ok_or(NixieError::InvalidTermId(term.raw()))
    }

    fn field(&mut self, field: crate::sort::field::FieldId) -> Result<crate::sort::field::FieldId> {
        let desc = self
            .source
            .sorts
            .field_desc(field)
            .ok_or_else(|| NixieError::Unsupported("missing field in import".into()))?;
        let sort = match desc.binary() {
            Some(binary) => self.target.sorts.binary_field(binary.polynomial().clone()),
            None => self.target.sorts.finite_field(desc.modulus().clone()),
        }
        .map_err(|err| NixieError::Unsupported(err.to_string()))?;
        self.target
            .sorts
            .get(sort)
            .and_then(|s| s.finite_field())
            .ok_or(NixieError::InvalidSortId(sort.raw()))
    }

    fn sort(&mut self, root: SortId) -> Result<SortId> {
        let mut stack = vec![(root, false)];
        let mut datatypes = Vec::new();
        let mut active = FxHashSet::default();
        loop {
            while let Some((sort, finish)) = stack.pop() {
                if self.sorts.contains_key(&sort) {
                    continue;
                }
                let kind = self
                    .source
                    .sorts
                    .get(sort)
                    .ok_or(NixieError::InvalidSortId(sort.raw()))?
                    .kind
                    .clone();
                if let SortKind::Datatype(name) = kind {
                    let name = self.source.sorts.resolve_spur(name).to_string();
                    let decl = self.source.sorts.get_datatype(&name).ok_or_else(|| {
                        NixieError::Unsupported(format!("undefined datatype {name} in import"))
                    })?;
                    let imported = self.target.sorts.mk_datatype_sort(&name);
                    self.sorts.insert(sort, imported);
                    datatypes.push((name, decl.clone()));
                    continue;
                }
                if !finish {
                    if !active.insert(sort) {
                        return Err(NixieError::Unsupported("cyclic sort in import".into()));
                    }
                    stack.push((sort, true));
                    match &kind {
                        SortKind::Set(s) | SortKind::Bag(s) | SortKind::Seq(s) => {
                            stack.push((*s, false))
                        }
                        SortKind::Array { domain, range } => {
                            stack.push((*domain, false));
                            stack.push((*range, false));
                        }
                        SortKind::Parametric { args, .. } => {
                            stack.extend(args.iter().map(|s| (*s, false)))
                        }
                        SortKind::Bool
                        | SortKind::Int
                        | SortKind::Real
                        | SortKind::String
                        | SortKind::BitVec(_)
                        | SortKind::FloatingPoint { .. }
                        | SortKind::RoundingMode
                        | SortKind::Uninterpreted(_)
                        | SortKind::Parameter(_)
                        | SortKind::Datatype(_)
                        | SortKind::FiniteField(_) => {}
                    }
                    continue;
                }
                let mapped = |id: SortId| {
                    self.sorts
                        .get(&id)
                        .copied()
                        .ok_or(NixieError::InvalidSortId(id.raw()))
                };
                let kind = match kind {
                    SortKind::Set(s) => SortKind::Set(mapped(s)?),
                    SortKind::Bag(s) => SortKind::Bag(mapped(s)?),
                    SortKind::Seq(s) => SortKind::Seq(mapped(s)?),
                    SortKind::Array { domain, range } => SortKind::Array {
                        domain: mapped(domain)?,
                        range: mapped(range)?,
                    },
                    SortKind::Parametric { name, args } => {
                        let args = args.into_iter().map(mapped).collect::<Result<_>>()?;
                        let name = self
                            .target
                            .sorts
                            .intern_str(self.source.sorts.resolve_spur(name));
                        SortKind::Parametric { name, args }
                    }
                    SortKind::Uninterpreted(name) => SortKind::Uninterpreted(
                        self.target.intern_str(self.source.resolve_str(name)),
                    ),
                    SortKind::Parameter(name) => SortKind::Parameter(
                        self.target
                            .sorts
                            .intern_str(self.source.sorts.resolve_spur(name)),
                    ),
                    SortKind::FiniteField(field) => SortKind::FiniteField(self.field(field)?),
                    SortKind::Bool
                    | SortKind::Int
                    | SortKind::Real
                    | SortKind::String
                    | SortKind::BitVec(_)
                    | SortKind::FloatingPoint { .. }
                    | SortKind::RoundingMode => kind,
                    SortKind::Datatype(_) => {
                        return Err(NixieError::Unsupported("unresolved datatype import".into()));
                    }
                };
                let imported = self.target.sorts.intern(kind);
                self.sorts.insert(sort, imported);
                active.remove(&sort);
            }
            for (_, decl) in &datatypes {
                for constructor in &decl.constructors {
                    stack.extend(
                        constructor
                            .selectors
                            .iter()
                            .filter(|(_, s)| !self.sorts.contains_key(s))
                            .map(|(_, s)| (*s, false)),
                    );
                }
            }
            if stack.is_empty() {
                break;
            }
        }
        for (name, decl) in datatypes {
            let mut constructors = Vec::new();
            for constructor in decl.constructors {
                let constructor_name = self
                    .target
                    .sorts
                    .intern_str(self.source.sorts.resolve_spur(constructor.name));
                let mut selectors = SmallVec::new();
                for (selector, sort) in constructor.selectors {
                    let selector = self
                        .target
                        .sorts
                        .intern_str(self.source.sorts.resolve_spur(selector));
                    let sort = self
                        .sorts
                        .get(&sort)
                        .copied()
                        .ok_or(NixieError::InvalidSortId(sort.raw()))?;
                    selectors.push((selector, sort));
                }
                constructors.push(DataTypeConstructor {
                    name: constructor_name,
                    selectors,
                });
            }
            if let Some(existing) = self.target.sorts.get_datatype(&name) {
                if existing.constructors.len() != constructors.len()
                    || existing
                        .constructors
                        .iter()
                        .zip(&constructors)
                        .any(|(a, b)| a.name != b.name || a.selectors != b.selectors)
                {
                    return Err(NixieError::Unsupported(format!(
                        "conflicting datatype {name} in import"
                    )));
                }
            } else {
                self.target.sorts.declare_datatype(&name, constructors);
            }
        }
        self.sorts
            .get(&root)
            .copied()
            .ok_or(NixieError::InvalidSortId(root.raw()))
    }

    fn remap(&mut self, kind: &mut TermKind) -> Result<()> {
        match kind {
            TermKind::True => {}
            TermKind::False => {}
            TermKind::IntConst(_) => {}
            TermKind::RealConst(_) => {}
            TermKind::BitVecConst { .. } => {}
            TermKind::Var(f0) => {
                *f0 = self.target.intern_str(self.source.resolve_str(*f0));
            }
            TermKind::Not(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::And(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::Or(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::Xor(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Implies(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Ite(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::Eq(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Distinct(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::Neg(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::Add(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::Sub(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Mul(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::Div(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Mod(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Lt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Le(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Gt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Ge(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Exp(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::Log(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::Sin(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::Cos(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::Atan(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::Sqrt(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::BvConcat(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvExtract { arg, .. } => {
                *arg = self.term(*arg)?;
            }
            TermKind::BvNot(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::BvAnd(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvOr(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvXor(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvAdd(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvSub(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvMul(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvUdiv(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvSdiv(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvUrem(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvSrem(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvShl(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvLshr(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvAshr(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvUlt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvUle(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvSlt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BvSle(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Select(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::Store(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::StringLit(_) => {}
            TermKind::StrConcat(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrLen(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::StrSubstr(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::StrAt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrContains(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrPrefixOf(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrSuffixOf(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrIndexOf(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::StrReplace(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::StrReplaceAll(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::StrReplaceRe(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::StrReplaceReAll(f0, f1, f2) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::StrToInt(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::IntToStr(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::StrInRe(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrLt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrLe(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::StrToCode(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::StrFromCode(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpLit { .. } => {}
            TermKind::FpPlusInfinity { .. } => {}
            TermKind::FpMinusInfinity { .. } => {}
            TermKind::FpPlusZero { .. } => {}
            TermKind::FpMinusZero { .. } => {}
            TermKind::FpNaN { .. } => {}
            TermKind::FpAbs(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpNeg(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpSqrt(_, f1) => {
                *f1 = self.term(*f1)?;
            }
            TermKind::FpRoundToIntegral(_, f1) => {
                *f1 = self.term(*f1)?;
            }
            TermKind::FpAdd(_, f1, f2) => {
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::FpSub(_, f1, f2) => {
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::FpMul(_, f1, f2) => {
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::FpDiv(_, f1, f2) => {
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
            }
            TermKind::FpRem(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpMin(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpMax(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpLeq(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpLt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpGeq(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpGt(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpEq(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::FpFma(_, f1, f2, f3) => {
                *f1 = self.term(*f1)?;
                *f2 = self.term(*f2)?;
                *f3 = self.term(*f3)?;
            }
            TermKind::FpIsNormal(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpIsSubnormal(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpIsZero(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpIsInfinite(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpIsNaN(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpIsNegative(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpIsPositive(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FpToFp { arg, .. } => {
                *arg = self.term(*arg)?;
            }
            TermKind::FpToSBV { arg, .. } => {
                *arg = self.term(*arg)?;
            }
            TermKind::FpToUBV { arg, .. } => {
                *arg = self.term(*arg)?;
            }
            TermKind::FpToReal(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::RealToFp { arg, .. } => {
                *arg = self.term(*arg)?;
            }
            TermKind::SBVToFp { arg, .. } => {
                *arg = self.term(*arg)?;
            }
            TermKind::UBVToFp { arg, .. } => {
                *arg = self.term(*arg)?;
            }
            TermKind::FfConst { field, .. } => {
                *field = self.field(*field)?;
            }
            TermKind::FfAdd(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::FfMul(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::FfNeg(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::FfBitsum(f0) => {
                for value in f0 {
                    *value = self.term(*value)?;
                }
            }
            TermKind::Apply { func, args } => {
                *func = self.target.intern_str(self.source.resolve_str(*func));
                for value in args {
                    *value = self.term(*value)?;
                }
            }
            TermKind::DtConstructor { constructor, args } => {
                *constructor = self
                    .target
                    .intern_str(self.source.resolve_str(*constructor));
                for value in args {
                    *value = self.term(*value)?;
                }
            }
            TermKind::DtTester { constructor, arg } => {
                *constructor = self
                    .target
                    .intern_str(self.source.resolve_str(*constructor));
                *arg = self.term(*arg)?;
            }
            TermKind::DtSelector { selector, arg } => {
                *selector = self.target.intern_str(self.source.resolve_str(*selector));
                *arg = self.term(*arg)?;
            }
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => {
                for (name, sort) in vars {
                    *name = self.target.intern_str(self.source.resolve_str(*name));
                    *sort = self.sort(*sort)?;
                }
                *body = self.term(*body)?;
                for pattern in patterns {
                    for value in pattern {
                        *value = self.term(*value)?;
                    }
                }
            }
            TermKind::Exists {
                vars,
                body,
                patterns,
            } => {
                for (name, sort) in vars {
                    *name = self.target.intern_str(self.source.resolve_str(*name));
                    *sort = self.sort(*sort)?;
                }
                *body = self.term(*body)?;
                for pattern in patterns {
                    for value in pattern {
                        *value = self.term(*value)?;
                    }
                }
            }
            TermKind::Let { bindings, body } => {
                for (name, value) in bindings {
                    *name = self.target.intern_str(self.source.resolve_str(*name));
                    *value = self.term(*value)?;
                }
                *body = self.term(*body)?;
            }
            TermKind::Match { scrutinee, cases } => {
                *scrutinee = self.term(*scrutinee)?;
                for case in cases {
                    if let Some(name) = &mut case.constructor {
                        *name = self.target.intern_str(self.source.resolve_str(*name));
                    }
                    for name in &mut case.bindings {
                        *name = self.target.intern_str(self.source.resolve_str(*name));
                    }
                    case.body = self.term(case.body)?;
                }
            }
            TermKind::SetEmpty(f0) => {
                *f0 = self.sort(*f0)?;
            }
            TermKind::SetSingleton(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::SetUnion(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::SetInter(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::SetMinus(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::SetMember(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::SetSubset(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::SetCard(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::SetComplement(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::SetUniv(f0) => {
                *f0 = self.sort(*f0)?;
            }
            TermKind::SetChoose(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::SetRelJoin(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::SetRelProduct(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::SetRelTranspose(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::SetRelIden(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::BagEmpty(f0) => {
                *f0 = self.sort(*f0)?;
            }
            TermKind::BagMake(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagUnionMax(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagUnionDisjoint(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagInterMin(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagDifferenceSubtract(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagDifferenceRemove(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagMember(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagSubbag(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagCount(f0, f1) => {
                *f0 = self.term(*f0)?;
                *f1 = self.term(*f1)?;
            }
            TermKind::BagCard(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::BagSetof(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::BagChoose(f0) => {
                *f0 = self.term(*f0)?;
            }
            TermKind::BagMap { func, ret, bag } => {
                *func = self.target.intern_str(self.source.resolve_str(*func));
                *ret = self.sort(*ret)?;
                *bag = self.term(*bag)?;
            }
            TermKind::BagFilter { pred, bag } => {
                *pred = self.target.intern_str(self.source.resolve_str(*pred));
                *bag = self.term(*bag)?;
            }
            TermKind::BagFold { func, init, bag } => {
                *func = self.target.intern_str(self.source.resolve_str(*func));
                *init = self.term(*init)?;
                *bag = self.term(*bag)?;
            }
            TermKind::Sequence(f0, f1) => {
                if let crate::ast::sequence::SeqOp::Empty(sort) = f0 {
                    *sort = self.sort(*sort)?;
                }
                for value in f1 {
                    *value = self.term(*value)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbols_and_uninterpreted_sorts_use_the_correct_interner() {
        let mut source = TermManager::new();
        let name = source.intern_str("SourceU");
        let sort = source.sorts.intern(SortKind::Uninterpreted(name));
        let x = source.mk_var("x", sort);
        let f = source.mk_apply("f", [x], sort);
        let mut target = TermManager::new();
        target.intern_str("unrelated");
        target.sorts.intern_str("different-sort-symbol");
        let copied = target.import_term(&source, f).unwrap();
        let node = target.get(copied).unwrap();
        let SortKind::Uninterpreted(name) = target.sorts.get(node.sort).unwrap().kind else {
            panic!("wrong sort");
        };
        assert_eq!(target.resolve_str(name), "SourceU");
        assert_eq!(nixie_printer(&target, copied), "(f x)");
        assert_eq!(target.import_term(&source, f).unwrap(), copied);
    }

    fn nixie_printer(manager: &TermManager, term: TermId) -> String {
        crate::smtlib::Printer::new(manager).print_term(term)
    }

    #[test]
    fn recursive_datatype_fields_and_trigger_only_terms_are_imported() {
        let mut source = TermManager::new();
        let list = source.sorts.mk_datatype_sort("List");
        let array = source.sorts.array(source.sorts.int_sort, list);
        let cons = source.sorts.intern_str("cons");
        let tail = source.sorts.intern_str("tail");
        source.sorts.declare_datatype(
            "List",
            vec![DataTypeConstructor {
                name: cons,
                selectors: smallvec::smallvec![(tail, array)],
            }],
        );
        let x = source.mk_var("x", array);
        let body = source.true_id;
        let term = source.mk_forall_with_patterns([("x", array)], body, [vec![x]]);
        let mut target = TermManager::new();
        target.sorts.bitvec(129);
        let copied = target.import_term(&source, term).unwrap();
        let TermKind::Forall { vars, patterns, .. } = &target.get(copied).unwrap().kind else {
            panic!("binder disappeared");
        };
        assert_eq!(vars[0].1, target.get(patterns[0][0]).unwrap().sort);
        let decl = target.sorts.get_datatype("List").unwrap();
        assert_eq!(decl.constructors[0].selectors[0].1, vars[0].1);
    }

    #[test]
    fn field_ids_and_wide_literals_are_not_copied_as_local_ids() {
        let mut source = TermManager::new();
        let field = source.sorts.finite_field(7u32.into()).unwrap();
        let field_id = source.sorts.get(field).unwrap().finite_field().unwrap();
        let constant = source.intern_term(
            TermKind::FfConst {
                value: 6.into(),
                field: field_id,
            },
            field,
        );
        let mut target = TermManager::new();
        target.sorts.finite_field(5u32.into()).unwrap();
        let copied = target.import_term(&source, constant).unwrap();
        let TermKind::FfConst { field, value } = &target.get(copied).unwrap().kind else {
            panic!("wrong field value");
        };
        assert_eq!(value, &num_bigint::BigInt::from(6));
        assert_eq!(
            target.sorts.field_desc(*field).unwrap().modulus(),
            &num_bigint::BigUint::from(7u32)
        );
        let wide = (num_bigint::BigInt::from(1) << 128usize) + 19;
        let term = source.mk_bitvec(wide, 129);
        let copied = target.import_term(&source, term).unwrap();
        assert_eq!(
            source.get(term).unwrap().kind,
            target.get(copied).unwrap().kind
        );
    }

    #[test]
    fn deep_import_uses_a_heap_stack_and_rejects_missing_references() {
        std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let mut source = TermManager::new();
                let sort = source.sorts.bool_sort;
                let p = source.mk_var("p", sort);
                let mut term = p;
                for _ in 0..20_000 {
                    term = source.intern_term(TermKind::Xor(p, term), sort);
                }
                let mut target = TermManager::new();
                let copied = target.import_term(&source, term).unwrap();
                let mut depth = 0;
                let mut current = copied;
                while let TermKind::Xor(_, next) = target.get(current).unwrap().kind {
                    depth += 1;
                    current = next;
                }
                assert_eq!(depth, 20_000);
                assert!(target.import_term(&source, TermId(u32::MAX)).is_err());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
