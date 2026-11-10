//! The printed model read back as an interpretation — constants **and
//! uninterpreted functions** — and checked against what was asserted
//! (re-fix pass 15: decisions (64), (67), (68)).
//!
//! # Why the functions are read back too (decision (68))
//!
//! The published-model certificate of decision (54)(i) interpreted an
//! uninterpreted function only at the ground applications the assertions
//! spell, and only where their arguments were literals the candidate pinned.
//! An application nested in another (`(f (f 7))`) or read at a bound variable
//! had no reading, so the certificate declined and a model that was correct
//! — `f` constantly `7` — was withheld (recheck 14 measured 95 of 132
//! withheld models correct).  The printed `define-fun` of a function *is* its
//! interpretation: the first entry whose arguments match, else the else
//! value.  Every application is replaced by that table, bottom-up and under
//! binders, so what the certificate checks is exactly the printed model.
//!
//! # The scope of the net (decision (67))
//!
//! The net used to run only where the solver's `has_array_ops` flag was set,
//! and it read the solver's assertions — after Skolemisation, destructive
//! equality resolution and vacuous-binder elimination had removed a
//! quantifier.  A scalar or uninterpreted goal (`q01`, `u04`), and an array
//! goal whose only read sits under a binder that never produced an instance
//! (`n02`), published a model falsifying its own universal.  The goal is now
//! whatever the script asserted: any quantifier in an asserted term puts the
//! `sat` under the certificate, whatever the theory.
//!
//! # The quantifier-free check (decisions (64), (68))
//!
//! A quantifier-free `sat` whose printed model the fresh values of `#P2b-71`
//! changed is evaluated once, exactly, under the printed interpretation: if
//! it makes an assertion false, the fresh values are dropped and the solver's
//! own model is printed (recheck 14's `r03`: a fresh value re-keyed a table
//! and lost an entry — c702310 printed a correct model there).

use super::*;
use crate::prelude::{FxHashMap, FxHashSet};

/// One printed function table: its entries in the order the printed `ite`
/// chain tests them, and the else value.
pub(in crate::context) struct PrintedFunction {
    entries: Vec<(Vec<TermId>, TermId)>,
    else_value: TermId,
    parameters: Vec<TermId>,
}

impl PrintedFunction {
    /// The table applied to `args`: the value of the first entry whose
    /// points equal the arguments, else the else value.
    fn apply(&self, args: &[TermId], terms: &mut nixie_core::ast::TermManager) -> TermId {
        let substitution = self
            .parameters
            .iter()
            .copied()
            .zip(args.iter().copied())
            .collect();
        let mut body = terms.substitute(self.else_value, &substitution);
        for (points, value) in self.entries.iter().rev() {
            if points.len() != args.len() {
                continue;
            }
            let conjuncts: Vec<TermId> = points
                .iter()
                .zip(args)
                .map(
                    |(&point, &arg)| match numeric_literal_equality(arg, point, terms) {
                        // `(f 1)` over a `Real` domain meets the printed point
                        // `1.0`: equal as numbers, whatever the literal's kind.
                        Some(equal) => terms.mk_bool(equal),
                        None => terms.mk_eq(arg, point),
                    },
                )
                .collect();
            let guard = terms.mk_and(conjuncts);
            body = terms.mk_ite(guard, *value, body);
        }
        body
    }
}

/// Whether two numeric literals denote the same number (an `Int` and a
/// `Real` literal compared by value); `None` unless both are numeric
/// literals.
fn numeric_literal_equality(
    a: TermId,
    b: TermId,
    terms: &nixie_core::ast::TermManager,
) -> Option<bool> {
    let value = |term: TermId| -> Option<num_rational::BigRational> {
        match &terms.get(term)?.kind {
            TermKind::IntConst(n) => Some(num_rational::BigRational::from_integer(n.clone())),
            TermKind::RealConst(r) => Some(num_rational::BigRational::new(
                BigInt::from(*r.numer()),
                BigInt::from(*r.denom()),
            )),
            _ => None,
        }
    };
    Some(value(a)? == value(b)?)
}

/// Every printed function table, by the function's name.
pub(in crate::context) type PrintedFunctions = FxHashMap<String, PrintedFunction>;

/// One declared function's printed table, read back
/// (`Context::read_printed_table`).
enum TableReading {
    /// The function prints no table.
    Absent,
    /// The table, parsed back.
    Read(PrintedFunction),
    /// A printed value of the table does not parse back.
    Unreadable,
}

/// The pieces the parse-back of printed values needs, gathered once.
pub(in crate::context) struct ParseBack {
    /// Uninterpreted sorts a witness `@uc_S_n` can belong to, by name.
    pub(in crate::context) sorts: FxHashMap<String, SortId>,
    /// Datatype constructors a printed value can spell, by name.
    pub(in crate::context) constructors: FxHashMap<String, SortId>,
    /// Witness placeholder symbol → the witness constant it stands for.
    pub(in crate::context) witnesses: FxHashMap<TermId, TermId>,
    /// Successful value readings within this fixed sort/constructor context.
    /// Witnesses only accumulate; a hit retains the witness registrations made
    /// by the original reading. This cache never survives a model read.
    values: FxHashMap<String, TermId>,
}

impl Context {
    /// Whether some asserted term — as the script wrote it, before any
    /// quantifier was Skolemised, resolved or dropped — contains a
    /// quantifier (decision (67)).  Assumptions of a `check-sat-assuming`
    /// count too.
    pub(in crate::context) fn goal_is_quantified(&self) -> bool {
        let mut stack: Vec<TermId> = self.certified_goal();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }
            let Some(data) = self.terms.get(current) else {
                continue;
            };
            if matches!(data.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                return true;
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
        false
    }

    /// What a published model must satisfy: every assertion in scope and
    /// every assumption of the last check.
    pub(in crate::context) fn certified_goal(&self) -> Vec<TermId> {
        let mut goal = self.assertions.clone();
        goal.extend(self.last_assumptions.iter().copied());
        goal
    }

    /// Parse one printed value back into a term: witnesses become sorted
    /// constants, constructors constructor terms; `None` when the text does
    /// not parse.
    pub(in crate::context) fn parse_printed_value(
        &mut self,
        text: &str,
        parse: &mut ParseBack,
    ) -> Option<TermId> {
        if let Some(&value) = parse.values.get(text) {
            return Some(value);
        }
        // Resolve witness symbols structurally: replacing text would also
        // corrupt string literals and quoted user symbols containing @uc_.
        let value = self.parse_typed_printed_term(text, parse, Vec::new())?;
        let value = self.resolve_witnesses(value, &parse.sorts, &mut parse.witnesses);
        let value = self.resolve_constructors(value, &parse.constructors);
        let value = self.fold_numeral_value(value);
        parse.values.insert(text.to_string(), value);
        Some(value)
    }

    fn parse_typed_printed_term(
        &mut self,
        text: &str,
        parse: &ParseBack,
        mut declarations: Vec<(String, SortId)>,
    ) -> Option<TermId> {
        // Lex symbols, never string contents: a witness inside a typed array
        // must have its sort before the parser checks the array constructor.
        let mut lexer = nixie_core::smtlib::Lexer::new(text);
        while let Some(token) = lexer.next_token() {
            if matches!(token.kind, nixie_core::smtlib::TokenKind::Eof) {
                break;
            }
            if let nixie_core::smtlib::TokenKind::Symbol(name) = token.kind
                && let Some(rest) = name.strip_prefix(super::published::WITNESS_PLACEHOLDER)
                && let Some((sort, index)) = rest.rsplit_once('_')
                && !index.is_empty()
                && index.bytes().all(|b| b.is_ascii_digit())
                && let Some(&sort) = parse.sorts.get(sort)
            {
                declarations.push((name, sort));
            }
        }
        let mut parser =
            nixie_core::smtlib::Parser::with_context(text, &mut self.terms, declarations);
        for (name, sort) in &parse.constructors {
            parser.seed_datatype_constructor(name.clone(), *sort);
        }
        parser.parse_term().ok()
    }

    /// A printed numeric value as the literal it denotes: the printer spells a
    /// non-integral `Real` as `(/ 37 10)` and a negative one as `(/ -21 10)`
    /// or `(- 2.0)`, which parse back as a division / negation of literals —
    /// terms the exact evaluator reads as `Int` division or leaves open.
    /// Anything else is returned unchanged.
    fn fold_numeral_value(&mut self, value: TermId) -> TermId {
        match crate::solver::array_completion_certify::evaluate_closed_value(
            &self.solver,
            value,
            &mut self.terms,
        ) {
            Some(crate::solver::EvalVal::Num(r))
                if self
                    .terms
                    .get(value)
                    .is_some_and(|t| t.sort == self.terms.sorts.real_sort) =>
            {
                self.terms.mk_real(r)
            }
            Some(crate::solver::EvalVal::Num(r)) if *r.denom() == 1 => {
                self.terms.mk_int(*r.numer())
            }
            Some(crate::solver::EvalVal::NumBig(r)) => {
                if self
                    .terms
                    .get(value)
                    .is_some_and(|t| t.sort == self.terms.sorts.real_sort)
                {
                    let n = self.terms.mk_int(r.numer().clone());
                    let d = self.terms.mk_int(r.denom().clone());
                    self.terms.mk_rdiv(n, d)
                } else if r.is_integer() {
                    self.terms.mk_int(r.to_integer())
                } else {
                    value
                }
            }
            _ => value,
        }
    }

    /// Every declared uninterpreted function's printed table, parsed back.
    /// `Err` names the first function whose table does not parse back into
    /// values; the tables after it are not read (so nothing past it is
    /// interned).
    pub(in crate::context) fn printed_functions(
        &mut self,
        parse: &mut ParseBack,
    ) -> Result<PrintedFunctions, String> {
        let mut out: PrintedFunctions = FxHashMap::default();
        let Some(solver_model) = self.published_model().cloned() else {
            return Ok(out);
        };
        let class_values = self.build_class_values(&solver_model);
        for name in self.uninterpreted_function_names() {
            match self.read_printed_table(&name, &solver_model, &class_values, parse) {
                TableReading::Absent => {}
                TableReading::Read(table) if self.table_is_closed(&table, parse) => {
                    out.insert(name, table);
                }
                TableReading::Read(_) | TableReading::Unreadable => {
                    return Err(format!(
                        "the printed interpretation of {name} does not read back"
                    ));
                }
            }
        }
        self.published.witness_domains.clear();
        for &witness in parse.witnesses.values() {
            if let Some(node) = self.terms.get(witness) {
                let domain = self.published.witness_domains.entry(node.sort).or_default();
                if !domain.contains(&witness) {
                    domain.push(witness);
                }
            }
        }
        for domain in self.published.witness_domains.values_mut() {
            domain.sort_unstable();
        }
        Ok(out)
    }

    /// Every declared uninterpreted function's printed table that parses
    /// back into values closed up to witnesses, and the names of those that
    /// do not — the honesty net's reader (decision (92)(d), re-fix pass 19):
    /// one unreadable table must not switch off the reading of every
    /// assertion, so every other table is still read.  A table counts as
    /// unreadable when a printed value does not parse (a constructor named
    /// `|(a|` prints unquoted as `(a`) or parses into something that is not a
    /// value (a sort named `|W X|` prints its witnesses as `@uc_W X_n`, which
    /// parses by truncation into a free symbol).
    pub(in crate::context) fn printed_functions_readable(
        &mut self,
        parse: &mut ParseBack,
    ) -> (PrintedFunctions, FxHashSet<String>) {
        let mut out: PrintedFunctions = FxHashMap::default();
        let mut unreadable: FxHashSet<String> = FxHashSet::default();
        let Some(solver_model) = self.published_model().cloned() else {
            return (out, unreadable);
        };
        let class_values = self.build_class_values(&solver_model);
        for name in self.uninterpreted_function_names() {
            match self.read_printed_table(&name, &solver_model, &class_values, parse) {
                TableReading::Absent => {}
                TableReading::Read(table) if self.table_is_closed(&table, parse) => {
                    out.insert(name, table);
                }
                TableReading::Read(_) | TableReading::Unreadable => {
                    unreadable.insert(name);
                }
            }
        }
        (out, unreadable)
    }

    /// The names of the declared uninterpreted functions with arguments, in
    /// declaration order.
    fn uninterpreted_function_names(&self) -> Vec<String> {
        self.declared_funs
            .iter()
            .filter(|d| !d.interpreted && !d.arg_sorts.is_empty())
            .map(|d| d.name.clone())
            .collect()
    }

    /// One function's printed table parsed back: its else value first, then
    /// its entries in order, stopping at the first value that does not parse.
    fn read_printed_table(
        &mut self,
        name: &str,
        solver_model: &crate::solver::Model,
        class_values: &super::class_values::ClassValues,
        parse: &mut ParseBack,
    ) -> TableReading {
        // Two entries at one argument tuple with different values (the
        // congruence closure kept two applications apart that the
        // arithmetic valued alike, `#P2b-74`) are read exactly as
        // `(get-model)` prints them — the first entry at a tuple wins —
        // and the certificate judges that function.
        let Some(((entries, else_text, arity), _)) =
            self.func_interp_reading(name, solver_model, class_values, false)
        else {
            return TableReading::Absent;
        };
        let mut parameters = Vec::new();
        let else_value = if self.published.function_overrides.contains_key(name) {
            let Some(decl) = self.declared_funs.iter().find(|d| d.name == name) else {
                return TableReading::Unreadable;
            };
            let declarations: Vec<_> = decl
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, &sort)| (format!("x!{i}"), sort))
                .collect();
            for (name, sort) in &declarations {
                parameters.push(self.terms.mk_var(name, *sort));
            }
            let declarations = declarations
                .into_iter()
                .chain(
                    self.published
                        .witness_symbols
                        .iter()
                        .map(|(n, s)| (n.clone(), *s)),
                )
                .collect();
            let Some(value) = self.parse_typed_printed_term(&else_text, parse, declarations) else {
                return TableReading::Unreadable;
            };
            self.resolve_witnesses(value, &parse.sorts, &mut parse.witnesses)
        } else {
            let Some(value) = self.parse_printed_value(&else_text, parse) else {
                return TableReading::Unreadable;
            };
            value
        };
        let mut table: Vec<(Vec<TermId>, TermId)> = Vec::with_capacity(entries.len());
        for (args, value) in entries {
            if args.len() != arity {
                return TableReading::Unreadable;
            }
            let mut points: Vec<TermId> = Vec::with_capacity(args.len());
            for arg in &args {
                let Some(point) = self.parse_printed_value(arg, parse) else {
                    return TableReading::Unreadable;
                };
                points.push(point);
            }
            let Some(value) = self.parse_printed_value(&value, parse) else {
                return TableReading::Unreadable;
            };
            table.push((points, value));
        }
        TableReading::Read(PrintedFunction {
            entries: table,
            else_value,
            parameters,
        })
    }

    /// Whether every point and value of a parsed table is closed up to the
    /// witnesses the parse resolved.
    fn table_is_closed(&self, table: &PrintedFunction, parse: &ParseBack) -> bool {
        let closed = |term: TermId| {
            self.terms
                .free_vars_including_patterns(term)
                .into_iter()
                .all(|var| parse.witnesses.values().any(|&witness| witness == var))
        };
        self.terms
            .free_vars_including_patterns(table.else_value)
            .into_iter()
            .all(|var| {
                table.parameters.contains(&var) || parse.witnesses.values().any(|&w| w == var)
            })
            && table
                .entries
                .iter()
                .all(|(points, value)| closed(*value) && points.iter().all(|&point| closed(point)))
    }

    /// `term` with every application of a printed function replaced by its
    /// table, bottom-up; under a binder the bound variables stand as fresh
    /// constants while the body is rewritten, so no binder is renamed and no
    /// application is missed.
    pub(in crate::context) fn expand_printed_functions(
        &mut self,
        term: TermId,
        funcs: &PrintedFunctions,
    ) -> TermId {
        if funcs.is_empty() {
            return self.fold_published_zero_division(term);
        }
        enum Frame {
            Expand(TermId),
            Finish {
                term: TermId,
                quantifiers: Vec<TermId>,
                applications: Vec<TermId>,
            },
            Bind {
                original: TermId,
                opened: TermId,
                back: FxHashMap<TermId, TermId>,
                names: Vec<(String, SortId)>,
                universal: bool,
            },
        }
        let mut stack = vec![Frame::Expand(term)];
        let mut done = FxHashMap::default();
        let mut binders = 0u64;
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Expand(current) => {
                    let mut quantifiers = Vec::new();
                    let mut applications = Vec::new();
                    self.collect_rewrite_sites(current, funcs, &mut quantifiers, &mut applications);
                    stack.push(Frame::Finish {
                        term: current,
                        quantifiers: quantifiers.clone(),
                        applications,
                    });
                    let mut pending = Vec::new();
                    for quantifier in quantifiers {
                        let Some(kind) = self.terms.get(quantifier).map(|t| t.kind.clone()) else {
                            return term;
                        };
                        let (vars, body, universal) = match kind {
                            TermKind::Forall { vars, body, .. } => (vars, body, true),
                            TermKind::Exists { vars, body, .. } => (vars, body, false),
                            _ => return term,
                        };
                        let mut to_fresh = FxHashMap::default();
                        let mut back = FxHashMap::default();
                        let mut names = Vec::new();
                        for &(name, sort) in &vars {
                            let text = self.terms.resolve_str(name).to_string();
                            let bound = self.terms.mk_var(&text, sort);
                            binders = match binders.checked_add(1) {
                                Some(n) => n,
                                None => return term,
                            };
                            let fresh = self.terms.mk_var(
                                &nixie_core::reserved::reserved_name("pbv", &binders.to_string()),
                                sort,
                            );
                            to_fresh.insert(bound, fresh);
                            back.insert(fresh, bound);
                            names.push((text, sort));
                        }
                        let opened = self.terms.substitute(body, &to_fresh);
                        pending.push((quantifier, opened, back, names, universal));
                    }
                    for (original, opened, back, names, universal) in pending.into_iter().rev() {
                        stack.push(Frame::Bind {
                            original,
                            opened,
                            back,
                            names,
                            universal,
                        });
                        stack.push(Frame::Expand(opened));
                    }
                }
                Frame::Bind {
                    original,
                    opened,
                    back,
                    names,
                    universal,
                } => {
                    let Some(&rewritten) = done.get(&opened) else {
                        return term;
                    };
                    let result = if rewritten == opened {
                        original
                    } else {
                        let closed = self.terms.substitute(rewritten, &back);
                        let names: Vec<_> = names.iter().map(|(n, s)| (n.as_str(), *s)).collect();
                        if universal {
                            self.terms.mk_forall(names, closed)
                        } else {
                            self.terms.mk_exists(names, closed)
                        }
                    };
                    done.insert(original, result);
                }
                Frame::Finish {
                    term: current,
                    quantifiers,
                    applications,
                } => {
                    let mut map = FxHashMap::default();
                    for q in quantifiers {
                        let Some(&value) = done.get(&q) else {
                            return term;
                        };
                        if value != q {
                            map.insert(q, value);
                        }
                    }
                    for application in applications {
                        let Some(TermKind::Apply { func, args }) =
                            self.terms.get(application).map(|t| t.kind.clone())
                        else {
                            return term;
                        };
                        let Some(table) = funcs.get(self.terms.resolve_str(func)) else {
                            return term;
                        };
                        let args: Vec<_> = args
                            .iter()
                            .map(|&a| self.terms.substitute(a, &map))
                            .collect();
                        map.insert(application, table.apply(&args, &mut self.terms));
                    }
                    let value = if map.is_empty() {
                        current
                    } else {
                        self.terms.substitute(current, &map)
                    };
                    done.insert(current, value);
                }
            }
        }
        let expanded = done.get(&term).copied().unwrap_or(term);
        self.fold_published_zero_division(expanded)
    }

    /// The maximal quantifier nodes of `term` and, outside them, the
    /// applications of printed functions in post-order (arguments first).
    fn collect_rewrite_sites(
        &self,
        term: TermId,
        funcs: &PrintedFunctions,
        quantifiers: &mut Vec<TermId>,
        applications: &mut Vec<TermId>,
    ) {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<(TermId, bool)> = vec![(term, false)];
        while let Some((current, expanded)) = stack.pop() {
            let Some(data) = self.terms.get(current) else {
                continue;
            };
            if expanded {
                if let TermKind::Apply { func, .. } = &data.kind
                    && funcs.contains_key(self.terms.resolve_str(*func))
                {
                    applications.push(current);
                }
                continue;
            }
            if !visited.insert(current) {
                continue;
            }
            if matches!(data.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                quantifiers.push(current);
                continue;
            }
            stack.push((current, true));
            for child in nixie_core::ast::traversal::get_children(&data.kind) {
                stack.push((child, false));
            }
        }
    }

    /// The printed model's reading of every declared constant, parsed back:
    /// `(printed, parse state)`.  A constant whose printed value does not
    /// read back into a term closed up to witnesses prevents certification.
    pub(in crate::context) fn printed_constants(
        &mut self,
    ) -> Option<(FxHashMap<TermId, TermId>, ParseBack)> {
        let rows = self.model_rows()?;
        let decls: Vec<TermId> = self.declared_consts.iter().map(|decl| decl.term).collect();
        if decls.len() != rows.len() {
            return None;
        }
        let mut parse = ParseBack {
            sorts: self.witness_sorts(),
            constructors: self.value_constructors(),
            witnesses: FxHashMap::default(),
            values: FxHashMap::default(),
        };
        let mut printed: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (term, (_, _, text)) in decls.into_iter().zip(rows) {
            let value = self.parse_printed_value(&text, &mut parse)?;
            let closed = self
                .terms
                .free_vars_including_patterns(value)
                .into_iter()
                .all(|var| parse.witnesses.values().any(|&witness| witness == var));
            if !closed {
                return None;
            }
            printed.insert(term, value);
        }
        Some((printed, parse))
    }

    /// The quantifier-free check: the first assertion the printed model —
    /// constants and function tables as `(get-model)` prints them — makes
    /// **definitely** false, quoted; `None` when every assertion is true or
    /// cannot be evaluated exactly.
    pub(in crate::context) fn printed_model_falsifies(&mut self) -> Option<String> {
        let (printed, mut parse) = self.printed_constants()?;
        let funcs = match self.printed_functions(&mut parse) {
            Ok(funcs) => funcs,
            Err(reason) => return Some(reason),
        };
        let witnesses: FxHashSet<TermId> = parse.witnesses.values().copied().collect();
        for (number, assertion) in self.certified_goal().into_iter().enumerate() {
            let expanded = self.expand_printed_functions(assertion, &funcs);
            let closed = self.terms.substitute(expanded, &printed);
            let closed = self.terms.fold_constructor_accessors(closed);
            // Where the exact evaluator is open, comparisons, `ite`s and
            // reads over datatype and uninterpreted-sort values are read by
            // value, interning nothing (decision (79)(a),
            // `printed_eval::ground_values`).
            let holds = crate::solver::array_completion_certify::evaluate_closed(
                &self.solver,
                closed,
                &mut self.terms,
            )
            .or_else(|| self.ground_truth(closed, &witnesses));
            if holds == Some(false) {
                return Some(format!("assertion {} is false", number + 1));
            }
        }
        None
    }

    /// The value `(get-model)`'s printed interpretation gives `term`, as
    /// `(get-value)` prints it (decision (69)(9), (10)): the term with every
    /// printed function applied by its table and every declared constant
    /// replaced by its printed value, folded exactly.  So a compound over an
    /// application (`(+ (f j) 3)`), a comparison of two applications and a
    /// read at an applied index fold to a literal, a constructor is its own
    /// value, and a `Real` keeps its decimal point — the same model the
    /// printed one is, term for term.  `None` for an array- or
    /// uninterpreted-sorted term, or one the evaluator cannot fold (the
    /// ordinary readings then answer).
    pub(in crate::context) fn printed_reading_value(
        &mut self,
        term: TermId,
        reading: &PrintedReading,
    ) -> Option<String> {
        let sort = self.terms.get(term)?.sort;
        let kind = self.terms.sorts.get(sort).map(|s| s.kind.clone())?;
        if matches!(kind, SortKind::Array { .. }) {
            return None;
        }
        let expanded = self.expand_printed_functions(term, &reading.functions);
        let closed = self.terms.substitute(expanded, &reading.constants);
        // `(fst (mk j red))` with `j` printed is the field, not an echo
        // (recheck 15's minor 11).
        let closed = self.terms.fold_constructor_accessors(closed);
        let witnesses = reading.witness_spellings.keys().copied().collect();
        if self
            .terms
            .free_vars_including_patterns(closed)
            .iter()
            .any(|var| !reading.witness_spellings.contains_key(var))
        {
            return None;
        }
        if matches!(kind, SortKind::Uninterpreted(_)) {
            let value = self.ground_witness(closed, &witnesses)?;
            return reading.witness_spellings.get(&value).cloned();
        }
        if kind == SortKind::Bool
            && let Some(value) = self.ground_truth(closed, &witnesses)
        {
            return Some(value.to_string());
        }
        // A read of a datatype-indexed array is decided by value over the
        // printed store chain (`printed_eval::datatype_reads`).
        let closed = self.fold_datatype_reads(closed);
        if matches!(kind, SortKind::Datatype(_)) {
            return super::array_model::is_constructor_value(closed, &self.terms)
                .then(|| nixie_core::smtlib::Printer::new(&self.terms).print_term(closed));
        }
        let value = match crate::solver::array_completion_certify::evaluate_closed_value(
            &self.solver,
            closed,
            &mut self.terms,
        ) {
            Some(value) => value,
            None => {
                // A selector over a constructor value (`(fst (mk 0 red))`) is
                // the rewriter's to fold, not the evaluator's.
                let simplified = self.terms.simplify(closed);
                crate::solver::array_completion_certify::evaluate_closed_value(
                    &self.solver,
                    simplified,
                    &mut self.terms,
                )?
            }
        };
        super::render_eval_value(&value, term, &self.terms)
    }

    /// The printed interpretation `(get-value)` reads, parsed back once per
    /// query; `None` when there is no printed model to read.
    pub(in crate::context) fn printed_reading(&mut self) -> Option<PrintedReading> {
        // An algebraic witness prints as a `root-obj` or a rounded rational
        // no literal reads back exactly; its readings stay the side
        // channel's own.
        if !self.solver.nl_algebraic_values().is_empty() {
            return None;
        }
        let (constants, mut parse) = self.printed_constants()?;
        let functions = self.printed_functions(&mut parse).ok()?;
        let witness_spellings = parse
            .witnesses
            .iter()
            .filter_map(|(&spelling, &value)| {
                let TermKind::Var(name) = self.terms.get(spelling)?.kind else {
                    return None;
                };
                Some((
                    value,
                    nixie_core::smtlib::format_symbol(self.terms.resolve_str(name)),
                ))
            })
            .collect();
        Some(PrintedReading {
            constants,
            functions,
            witness_spellings,
        })
    }
}

/// `(get-model)`'s printed interpretation, parsed back: what
/// [`Context::printed_reading_value`] folds a `(get-value)` term under.
pub(in crate::context) struct PrintedReading {
    witness_spellings: FxHashMap<TermId, String>,
    constants: FxHashMap<TermId, TermId>,
    functions: PrintedFunctions,
}

#[cfg(test)]
mod typed_publication_regressions {
    use super::*;

    #[test]
    fn datatype_array_values_are_typed_before_constructor_validation() {
        let mut ctx = Context::new();
        ctx.execute_script(
            "(declare-datatype E ((ea)(eb)))
            (declare-const a (Array Int E))",
        )
        .expect("declarations");
        let mut parse = ParseBack {
            sorts: ctx.witness_sorts(),
            constructors: ctx.value_constructors(),
            witnesses: FxHashMap::default(),
            values: FxHashMap::default(),
        };
        let base = ctx
            .parse_printed_value("((as const (Array Int E)) ea)", &mut parse)
            .expect("typed const array");
        let stored = ctx
            .parse_printed_value("(store ((as const (Array Int E)) ea) 0 ea)", &mut parse)
            .expect("typed store");
        let equal = ctx.terms.mk_eq(base, stored);
        assert_eq!(ctx.ground_truth(equal, &FxHashSet::default()), Some(true));
        let different = ctx
            .parse_printed_value("(store ((as const (Array Int E)) ea) 0 eb)", &mut parse)
            .expect("typed different store");
        let equal = ctx.terms.mk_eq(base, different);
        assert_eq!(ctx.ground_truth(equal, &FxHashSet::default()), Some(false));
    }

    #[test]
    fn repeated_value_reads_preserve_witnesses_and_do_not_cross_sort_contexts() {
        for sort_name in ["U", "V"] {
            let mut ctx = Context::new();
            ctx.execute_script(&format!(
                "(declare-sort {sort_name} 0)(declare-const a {sort_name})"
            ))
            .expect("sort declaration");
            let mut parse = ParseBack {
                sorts: ctx.witness_sorts(),
                constructors: ctx.value_constructors(),
                witnesses: FxHashMap::default(),
                values: FxHashMap::default(),
            };
            let text = format!("((as const (Array Int {sort_name})) @uc_{sort_name}_17)");
            let first = ctx.parse_printed_value(&text, &mut parse).expect("array");
            let before = parse.witnesses.clone();
            let second = ctx
                .parse_printed_value(&text, &mut parse)
                .expect("same array");
            assert_eq!(first, second);
            assert_eq!(before, parse.witnesses);
            assert!(!before.is_empty());
            let witness_text = format!("@uc_{sort_name}_17");
            let witness = ctx
                .parse_printed_value(&witness_text, &mut parse)
                .expect("witness");
            let zero = ctx.terms.mk_int(0);
            let read = ctx.terms.mk_select(second, zero);
            let equality = ctx.terms.mk_eq(read, witness);
            let witnesses = parse.witnesses.values().copied().collect();
            assert_eq!(ctx.ground_truth(equality, &witnesses), Some(true));
            assert!(
                ctx.parse_printed_value("@uc_missing_17", &mut parse)
                    .is_none()
            );
        }
    }

    #[test]
    fn witnesses_inside_array_values_are_typed_without_touching_strings() {
        let mut ctx = Context::new();
        ctx.execute_script("(declare-sort U 0)(declare-const a (Array Int U))")
            .expect("declarations");
        let mut parse = ParseBack {
            sorts: ctx.witness_sorts(),
            constructors: ctx.value_constructors(),
            witnesses: FxHashMap::default(),
            values: FxHashMap::default(),
        };
        let array = ctx
            .parse_printed_value("((as const (Array Int U)) @uc_U_17)", &mut parse)
            .expect("typed witness");
        let zero = ctx.terms.mk_int(0);
        let read = ctx.terms.mk_select(array, zero);
        let witness = ctx
            .parse_printed_value("@uc_U_17", &mut parse)
            .expect("same witness");
        let equal = ctx.terms.mk_eq(read, witness);
        let witnesses = parse.witnesses.values().copied().collect();
        assert_eq!(ctx.ground_truth(equal, &witnesses), Some(true));
    }
}
