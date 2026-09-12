//! Lowering the surface tree to [`crate::kera`].
//!
//! # Shape of the walk
//!
//! `AGENTS.md` forbids new unbounded native recursion over user-controlled
//! input, and a surface tree parsed from a `.tla` file is exactly that. The
//! walk therefore carries its own stack, with resume state in the frame: a
//! an `Expand` frame pushes one kernel value, a `Build` frame pops the
//! children it asked for and pushes the node built from them, and scope frames
//! bracket the parts of a term where a binder or an inlined parameter is
//! visible.
//!
//! # Inlining
//!
//! Operator applications are inlined by *re-lowering the operator's body* with
//! its parameters bound to the already-lowered arguments, rather than by
//! building a term and substituting afterwards. That keeps one mechanism
//! instead of two, and it is what makes `LET` free: a `LET` definition is just
//! a binding in scope.
//!
//! Every binder is renamed to a unique name on the way down (`x` becomes
//! `x#3`), which removes variable capture as a concern entirely — an inlined
//! argument can mention any name at all and still cannot be captured by a
//! binder in the body it is substituted into.
//!
//! Recursive operators have no finite unfolding, so inlining is bounded and
//! reports [`crate::LowerErrorKind::InlineLimit`] rather than looping.

use crate::error::{LowerError, LowerErrorKind, Result};
use crate::kera::{ArithOp, CmpOp, Kera, KeraRef, Name, SetOp};
use nixie_tla_syntax::Span;
use nixie_tla_syntax::ast::{
    Bound, CaseArm, ExceptSel, Expr, ExprKind, Module, Pattern, QuantKind, Unit, UnitKind,
};
use std::collections::HashMap;
use std::rc::Rc;

/// Default maximum inlining depth.
pub const DEFAULT_MAX_INLINE_DEPTH: usize = 64;
/// Default budget, in steps of the lowering walk.
///
/// Bounds total work rather than nesting: inlining splices a body in at every
/// use, so a term can be enormous without being deep.
///
/// Set to fail *fast*. Inlining is memoised on the identity of an operator's
/// already-lowered arguments, which collapses the common
/// `F(x) == G(x) + G(x)` blowup, but the memo misses when two structurally
/// equal arguments are lowered separately and so are not pointer-identical.
/// A handful of corpus files (`test23.tla` and relatives, ~1.3% of
/// definitions) still exhaust the budget. Hash-consing the kernel would close
/// it properly; until then the budget keeps the failure to a prompt
/// diagnostic instead of an apparent hang.
pub const DEFAULT_STEP_BUDGET: usize = 100_000;

/// A module instantiation: `I == INSTANCE M WITH a <- e`.
///
/// `EXTENDS` makes another module's definitions visible unchanged; `INSTANCE`
/// makes them visible *after substituting* for the declared constants and
/// variables of the instantiated module. That substitution is the whole
/// difference, and it is why an instance member cannot simply be inlined the
/// way an extended one can.
#[derive(Debug, Clone)]
struct Instantiation<'a> {
    module: &'a Module,
    /// Explicit `WITH` replacements, by the instantiated module's name.
    with: Vec<(String, &'a Expr)>,
    /// Parameters of a parameterised instance, `I(p) == INSTANCE M WITH …`.
    params: Vec<String>,
}

/// The instance being looked through while lowering.
///
/// Names inside an instantiated module's definition resolve against *that*
/// module and through *its* substitution, not against the module doing the
/// instantiating.
#[derive(Debug)]
struct InstanceCtx<'a> {
    module: &'a Module,
    subst: HashMap<String, KeraRef>,
}

/// A user operator definition available for inlining.
#[derive(Debug, Clone)]
struct Def<'a> {
    /// Parameter names with their arities. A non-zero arity marks a
    /// *higher-order* parameter: `Op(F(_), x)` takes an operator, not a value,
    /// and the argument has to be bound as an operator to be applied.
    params: Vec<(String, usize)>,
    body: &'a Expr,
    /// Whether the lowered form may be cached and shared.
    ///
    /// True for a module-level definition: TLA+ has no dynamic scoping, so a
    /// top-level body can only mention other top-level names, declared
    /// symbols and its own binders — its lowering does not depend on where it
    /// is used. False for a `LET` definition, whose name is scoped and may be
    /// shadowed.
    cacheable: bool,
}

/// What a name is bound to while lowering.
#[derive(Debug, Clone)]
enum Binding<'a> {
    /// An inlined value: an operator parameter, a `LET` definition, or a
    /// component of a destructured tuple pattern.
    Value(KeraRef),
    /// A renamed bound variable.
    Bound(Name),
    /// An operator passed as an argument — a named definition or a `LAMBDA`.
    /// Bound rather than lowered, because an operator has no value until it is
    /// applied.
    Op {
        /// Its parameters, with arities.
        params: Vec<(String, usize)>,
        /// Its body.
        body: &'a Expr,
    },
}

/// Lowers surface expressions to the kernel.
pub struct Lowerer<'a> {
    defs: HashMap<String, Def<'a>>,
    /// Per-module definitions, so a name inside an instantiated module
    /// resolves against that module rather than against the flat root view.
    module_defs: HashMap<String, HashMap<String, Def<'a>>>,
    /// Named instantiations, `I == INSTANCE M …`.
    instances: HashMap<String, Instantiation<'a>>,
    /// Unnamed `INSTANCE M …`, whose members are visible without a prefix.
    open_instances: Vec<Instantiation<'a>>,
    /// The instance contexts currently being looked through, innermost last.
    ctx: Vec<Rc<InstanceCtx<'a>>>,
    /// Function definitions `f[x \in S] == e`, which denote a *value* rather
    /// than an operator and so are expanded as `[x \in S |-> e]` at use sites.
    funs: HashMap<String, (&'a [Bound], &'a Expr)>,
    scopes: Vec<HashMap<String, Binding<'a>>>,
    /// Binder names chosen during `expand`, keyed by the surface node's start
    /// offset so that `build` can recover them. The walk visits each node's
    /// expand and build exactly once, so one entry per node suffices.
    binder_names: HashMap<u32, Vec<Name>>,
    /// Lowered forms of nullary module-level definitions.
    ///
    /// Inlining re-lowers a body at every use, so `A == B + B` with
    /// `B == C + C` doubles at each level and a chain of a dozen such
    /// definitions is exponential. Sharing the `Rc` collapses that back to
    /// linear, and is sound precisely because a top-level body's meaning does
    /// not depend on where it is used.
    cache: HashMap<String, KeraRef>,
    /// Every loaded module by name, for resolving `INSTANCE`.
    modules: HashMap<String, &'a Module>,
    /// Higher-order arguments resolved by `expand`, keyed by the application's
    /// start offset, waiting for the matching `Inline` frame.
    pending_ops: HashMap<u32, Vec<(String, Binding<'a>)>>,
    fresh: usize,
    inline_depth: usize,
    max_inline_depth: usize,
    step_budget: usize,
}

/// A step of the lowering walk.
enum Frame<'a> {
    Expand(&'a Expr),
    /// Pop `n` kernel values and build this surface node from them.
    Build(&'a Expr, usize),
    PushScope(HashMap<String, Binding<'a>>),
    PopScope,
    /// Bind `@` to the value being replaced, for an `EXCEPT` update. Peeks the
    /// function and index already on the value stack rather than popping them.
    BindExceptAt {
        /// How many index expressions make up the path step.
        path_len: usize,
    },
    /// Inline an operator: pop one value per parameter, bind them, and
    /// continue into `body`.
    Inline {
        name: String,
        params: Vec<(String, usize)>,
        body: &'a Expr,
        span: Span,
        /// Cache the result under this name once the body is lowered.
        cache_as: Option<String>,
    },
    /// Leave an inlined body: drop its scope and the depth it consumed.
    PopInline,
    /// Expand a function definition's `bounds`/`body` as `[x \in S |-> e]`.
    ExpandFun(&'a [Bound], &'a Expr),
    /// Build that function definition from `1 + 1` values (domain, body).
    BuildFun(Name),
    /// Restore operator definitions shadowed by a `LET`.
    PopLetDefs(Vec<(String, Option<Def<'a>>)>),
    /// Push a ready-made kernel value (a record field name in an `EXCEPT`
    /// path, which has no surface expression of its own).
    PushLiteral(KeraRef),
    /// Enter an instance: pop the lowered `WITH` replacements and the member's
    /// arguments, and look through the instantiated module under them.
    PushInstanceCtx {
        module: &'a Module,
        /// Names the popped substitution values belong to, in order.
        subst_names: Vec<String>,
        /// Declared names with no explicit `WITH`, substituted by the
        /// same-named symbol of the instantiating module.
        implicit: Vec<String>,
        /// The member's own parameters, bound to the popped arguments.
        member_params: Vec<(String, usize)>,
    },
    /// Leave an instance.
    PopInstanceCtx,
    /// Remember the lowered form of a nullary module-level definition.
    CacheStore(String),
}

impl<'a> Lowerer<'a> {
    /// A lowerer with no definitions in scope.
    #[must_use]
    pub fn new() -> Self {
        Self {
            defs: HashMap::new(),
            module_defs: HashMap::new(),
            instances: HashMap::new(),
            open_instances: Vec::new(),
            ctx: Vec::new(),
            funs: HashMap::new(),
            scopes: Vec::new(),
            binder_names: HashMap::new(),
            cache: HashMap::new(),
            modules: HashMap::new(),
            pending_ops: HashMap::new(),
            fresh: 0,
            inline_depth: 0,
            max_inline_depth: DEFAULT_MAX_INLINE_DEPTH,
            step_budget: DEFAULT_STEP_BUDGET,
        }
    }

    /// Register every operator definition in `module` for inlining.
    ///
    /// Definitions are registered in source order, so a later definition can
    /// use an earlier one — which is all TLA+ permits anyway.
    pub fn add_module(&mut self, module: &'a Module) {
        self.index_module(module);
        for unit in &module.units {
            self.add_unit(unit);
        }
    }

    /// Index a module without making its definitions visible.
    ///
    /// Visibility is the whole point of the distinction. A module reached only
    /// through `INSTANCE` must **not** contribute to the flat name space: its
    /// definitions mean something only under that instance's substitution, and
    /// letting them resolve directly would silently use the *unsubstituted*
    /// body — reading the wrong module's variables.
    pub fn index_module(&mut self, module: &'a Module) {
        self.modules.insert(module.name.name.clone(), module);
        for unit in &module.units {
            self.add_instance_unit(module, unit);
        }
        // A per-module view, so that a definition reached through an instance
        // resolves its own module's names rather than the root's.
        let mut own: HashMap<String, Def<'a>> = HashMap::new();
        for unit in &module.units {
            if let UnitKind::OpDef {
                name, params, body, ..
            } = &unit.kind
            {
                own.insert(
                    name.name.clone(),
                    Def {
                        params: params
                            .iter()
                            .map(|p| (p.name.name.clone(), p.arity))
                            .collect(),
                        body,
                        cacheable: true,
                    },
                );
            }
        }
        self.module_defs.insert(module.name.name.clone(), own);
    }

    fn add_instance_unit(&mut self, _module: &'a Module, unit: &'a Unit) {
        let (name, params, instance) = match &unit.kind {
            UnitKind::ModuleDef {
                name,
                params,
                instance,
                ..
            } => (
                Some(name.name.clone()),
                params.iter().map(|p| p.name.name.clone()).collect(),
                instance,
            ),
            UnitKind::Instance { instance, .. } => (None, Vec::new(), instance),
            _ => return,
        };
        let Some(target) = self.modules.get(&instance.module.name).copied() else {
            // The instantiated module was not loaded; a use of it will report
            // that by name rather than silently resolving to something else.
            return;
        };
        let inst = Instantiation {
            module: target,
            with: instance
                .substitutions
                .iter()
                .map(|(n, e)| (n.name.clone(), e))
                .collect(),
            params,
        };
        match name {
            Some(n) => {
                self.instances.insert(n, inst);
            }
            None => self.open_instances.push(inst),
        }
    }

    fn add_unit(&mut self, unit: &'a Unit) {
        match &unit.kind {
            UnitKind::OpDef {
                name, params, body, ..
            } => {
                self.defs.insert(
                    name.name.clone(),
                    Def {
                        params: params
                            .iter()
                            .map(|p| (p.name.name.clone(), p.arity))
                            .collect(),
                        body,
                        cacheable: true,
                    },
                );
            }
            // A function definition `f[x \in S] == e` denotes the function
            // itself, not an operator, so it is expanded as `[x \in S |-> e]`
            // wherever `f` is used.
            UnitKind::FnDef {
                name, bounds, body, ..
            } => {
                self.funs
                    .insert(name.name.clone(), (bounds.as_slice(), body));
            }
            UnitKind::ConstantDecl(_)
            | UnitKind::VariableDecl(_)
            | UnitKind::Recursive(_)
            | UnitKind::Extends(_)
            | UnitKind::Instance { .. }
            | UnitKind::ModuleDef { .. }
            | UnitKind::Assume { .. }
            | UnitKind::Theorem { .. }
            | UnitKind::ProofDirective(_)
            | UnitKind::Separator
            | UnitKind::Submodule(_) => {}
        }
    }

    /// Register every module of a loaded spec, dependency-first.
    ///
    /// Without this a spec's imports are invisible and `Sequences`' `\o`,
    /// `TLC`'s `:>` and every operator a module extends fail to lower. The
    /// order matters: `LoadedSpec::modules` is dependency-first, so the root's
    /// own definitions are registered last and shadow anything it extends —
    /// which is what TLA+ means by overriding.
    pub fn add_spec(&mut self, spec: &'a nixie_tla_syntax::LoadedSpec) {
        // Two passes: every module must be findable before any `INSTANCE` is
        // resolved, since a module may instantiate one that appears later.
        for (name, module) in &spec.modules {
            self.modules.insert(name.clone(), module);
        }
        for (_, module) in &spec.modules {
            self.index_module(module);
        }
        // Only the root and what it *extends* contribute visible names.
        // `EXTENDS` re-exports, so the closure is taken transitively; an
        // `INSTANCE` target reached along the way does not join it.
        let mut visible: Vec<&str> = vec![spec.root.as_str()];
        let mut i = 0;
        while i < visible.len() {
            let Some((_, m)) = spec.modules.iter().find(|(n, _)| n == visible[i]) else {
                i += 1;
                continue;
            };
            for dep in m.extends() {
                if !visible.iter().any(|v| *v == dep.name) {
                    visible.push(&dep.name);
                }
            }
            i += 1;
        }
        // Dependency-first, so the root's own definitions are registered last
        // and shadow anything it extends — which is what overriding means.
        for (name, module) in &spec.modules {
            if visible.iter().any(|v| *v == name) {
                for unit in &module.units {
                    self.add_unit(unit);
                }
            }
        }
    }

    /// Lower the body of the named top-level definition.
    ///
    /// # Errors
    ///
    /// Returns [`LowerErrorKind::Unsupported`] if there is no such definition,
    /// or the first lowering error.
    pub fn lower_named(&mut self, module: &'a Module, name: &str) -> Result<KeraRef> {
        let found = module.units.iter().find_map(|u| match &u.kind {
            UnitKind::OpDef { name: n, body, .. } if n.name == name => Some(body),
            _ => None,
        });
        let Some(body) = found else {
            return Err(LowerError::unsupported(
                &format!("`{name}`"),
                "no operator definition with that name in this module",
                nixie_tla_syntax::Span::default(),
            ));
        };
        self.lower(body)
    }

    /// Override the inlining depth budget.
    #[must_use]
    pub fn with_max_inline_depth(mut self, n: usize) -> Self {
        self.max_inline_depth = n;
        self
    }

    /// Override the total work budget, in steps of the lowering walk.
    #[must_use]
    pub fn with_step_budget(mut self, n: usize) -> Self {
        self.step_budget = n;
        self
    }

    fn fresh_name(&mut self, base: &str) -> Name {
        self.fresh += 1;
        Name(format!("{base}#{}", self.fresh))
    }

    /// Read an argument as an *operator*: a defined name, an operator
    /// parameter already in scope, or a `LAMBDA`.
    fn as_operator(&self, arg: &'a Expr) -> Option<Binding<'a>> {
        match &arg.kind {
            ExprKind::Lambda { params, body } => Some(Binding::Op {
                params: params.iter().map(|p| (p.name.clone(), 0)).collect(),
                body,
            }),
            ExprKind::Name(q) if !q.is_qualified() => {
                let id = q.base()?;
                if let Some(b @ Binding::Op { .. }) = self.lookup(&id.name) {
                    return Some(b);
                }
                let def = self.defs.get(&id.name)?;
                Some(Binding::Op {
                    params: def.params.clone(),
                    body: def.body,
                })
            }
            ExprKind::Paren(inner) => self.as_operator(inner),
            _ => None,
        }
    }

    fn lookup(&self, name: &str) -> Option<Binding<'a>> {
        self.scopes.iter().rev().find_map(|s| s.get(name).cloned())
    }

    /// Lower one expression.
    ///
    /// # Errors
    ///
    /// Returns the first [`LowerError`] encountered.
    pub fn lower(&mut self, expr: &'a Expr) -> Result<KeraRef> {
        let mut stack: Vec<Frame<'a>> = vec![Frame::Expand(expr)];
        let mut values: Vec<KeraRef> = Vec::new();
        let mut steps = 0usize;

        while let Some(frame) = stack.pop() {
            // Inlining splices a definition's body in at every use, so a term
            // can be enormous without being deep. The budget bounds total work
            // and exists only to keep a pathological input from exhausting
            // memory.
            steps += 1;
            if steps > self.step_budget {
                return Err(LowerError::new(
                    LowerErrorKind::BudgetExhausted {
                        limit: self.step_budget,
                    },
                    expr.span,
                ));
            }
            match frame {
                Frame::PushScope(s) => self.scopes.push(s),
                Frame::PopScope => {
                    self.scopes.pop();
                }
                Frame::BindExceptAt { path_len } => {
                    // The function is below the path indices on the stack.
                    let n = values.len();
                    let base = n.checked_sub(path_len + 1).and_then(|i| values.get(i));
                    let Some(base) = base.cloned() else {
                        return Err(LowerError::unsupported(
                            "an `EXCEPT` update",
                            "internal: the function being updated was not on the stack",
                            expr.span,
                        ));
                    };
                    let mut at = base;
                    for k in 0..path_len {
                        let Some(idx) = n.checked_sub(path_len - k).and_then(|i| values.get(i))
                        else {
                            break;
                        };
                        at = Kera::FunApp(at, Rc::clone(idx)).rc();
                    }
                    let mut scope = HashMap::new();
                    scope.insert("@".to_string(), Binding::Value(at));
                    self.scopes.push(scope);
                }
                Frame::CacheStore(name) => {
                    if let Some(v) = values.last() {
                        self.cache.insert(name, Rc::clone(v));
                    }
                }
                Frame::Inline {
                    name,
                    params,
                    body,
                    span,
                    cache_as,
                } => {
                    if self.inline_depth >= self.max_inline_depth {
                        return Err(LowerError::new(
                            LowerErrorKind::InlineLimit {
                                name,
                                limit: self.max_inline_depth,
                            },
                            span,
                        ));
                    }
                    let mut scope = HashMap::new();
                    for (p, arity) in params.iter().rev() {
                        if *arity > 0 {
                            // Bound by `expand` as an operator, not a value.
                            continue;
                        }
                        let Some(v) = values.pop() else {
                            return Err(LowerError::new(
                                LowerErrorKind::Arity {
                                    name: name.clone(),
                                    expected: params.len(),
                                    found: 0,
                                },
                                span,
                            ));
                        };
                        scope.insert(p.clone(), Binding::Value(v));
                    }
                    if let Some(extra) = self.pending_ops.remove(&span.start.offset) {
                        for (k, v) in extra {
                            scope.insert(k, v);
                        }
                    }
                    self.inline_depth += 1;
                    self.scopes.push(scope);
                    if let Some(key) = cache_as {
                        stack.push(Frame::CacheStore(key));
                    }
                    stack.push(Frame::PopInline);
                    stack.push(Frame::Expand(body));
                }
                Frame::PopInline => {
                    self.scopes.pop();
                    self.inline_depth = self.inline_depth.saturating_sub(1);
                }
                Frame::PushLiteral(v) => values.push(v),
                Frame::PushInstanceCtx {
                    module,
                    subst_names,
                    implicit,
                    member_params,
                } => {
                    // Arguments were pushed last, so they come off first.
                    let mut scope = HashMap::new();
                    for (p, arity) in member_params.iter().rev() {
                        if *arity > 0 {
                            continue;
                        }
                        let Some(v) = values.pop() else {
                            return Err(LowerError::unsupported(
                                "an instance member application",
                                "internal: missing argument",
                                expr.span,
                            ));
                        };
                        scope.insert(p.clone(), Binding::Value(v));
                    }
                    let mut subst = HashMap::new();
                    for n in subst_names.iter().rev() {
                        let Some(v) = values.pop() else {
                            return Err(LowerError::unsupported(
                                "an `INSTANCE` substitution",
                                "internal: missing replacement",
                                expr.span,
                            ));
                        };
                        subst.insert(n.clone(), v);
                    }
                    // A declared name with no `WITH` clause is substituted by
                    // the same-named symbol of the instantiating module --
                    // resolved through the *enclosing* instance if there is
                    // one, so that nested instantiations compose.
                    for n in implicit {
                        let v = self
                            .ctx
                            .last()
                            .and_then(|c| c.subst.get(&n).cloned())
                            .unwrap_or_else(|| Kera::Var(Name(n.clone())).rc());
                        subst.insert(n, v);
                    }
                    self.ctx.push(Rc::new(InstanceCtx { module, subst }));
                    self.scopes.push(scope);
                }
                Frame::PopInstanceCtx => {
                    self.ctx.pop();
                    self.scopes.pop();
                }
                Frame::PopLetDefs(saved) => {
                    for (name, prev) in saved {
                        match prev {
                            Some(d) => {
                                self.defs.insert(name, d);
                            }
                            None => {
                                self.defs.remove(&name);
                                self.funs.remove(&name);
                            }
                        }
                    }
                }
                Frame::ExpandFun(bounds, body) => {
                    let mut scope = HashMap::new();
                    let mut names = Vec::new();
                    for b in bounds {
                        for p in &b.patterns {
                            names.push(self.bind_pattern(p, &mut scope));
                        }
                    }
                    let Some(first) = names.first().cloned() else {
                        return Err(LowerError::unsupported(
                            "a function definition with no bound variable",
                            "internal",
                            expr.span,
                        ));
                    };
                    if names.len() != 1 {
                        return Err(LowerError::unsupported(
                            "a multi-variable function definition",
                            "`f[x \\in S, y \\in T] == …` is not lowered yet; write it as a \
                             function of one tuple variable",
                            expr.span,
                        ));
                    }
                    stack.push(Frame::BuildFun(first));
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(scope));
                    if let Some(b) = bounds.first() {
                        stack.push(Frame::Expand(&b.domain));
                    }
                }
                Frame::BuildFun(var) => {
                    let (Some(body), Some(set)) = (values.pop(), values.pop()) else {
                        return Err(LowerError::unsupported(
                            "a function definition",
                            "internal: missing children",
                            expr.span,
                        ));
                    };
                    values.push(Kera::FunDef { var, set, body }.rc());
                }
                Frame::Build(e, n) => {
                    let built = self.build(e, &mut values, n)?;
                    values.push(built);
                }
                Frame::Expand(e) => self.expand(e, &mut stack, &mut values)?,
            }
        }

        values.pop().ok_or_else(|| {
            LowerError::unsupported(
                "this expression",
                "internal: lowering produced no value",
                expr.span,
            )
        })
    }
}

impl Default for Lowerer<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// Sort record fields so two records written in different orders compare equal.
fn sort_fields(mut fs: Vec<(String, KeraRef)>) -> Vec<(String, KeraRef)> {
    fs.sort_by(|a, b| a.0.cmp(&b.0));
    fs
}

/// Convert a based numeral to decimal digits.
fn digits_to_decimal(base: nixie_tla_syntax::NumBase, digits: &str) -> Option<String> {
    use nixie_tla_syntax::NumBase;
    let radix = match base {
        NumBase::Decimal => return Some(digits.to_string()),
        NumBase::Binary => 2,
        NumBase::Octal => 8,
        NumBase::Hex => 16,
    };
    // Accumulate in decimal by hand so that a wide literal is exact rather
    // than truncated through `u64` — `AGENTS.md`: wide values stay exact.
    let mut acc: Vec<u8> = vec![0];
    for c in digits.chars() {
        let d = c.to_digit(radix)? as u8;
        let mut carry = u32::from(d);
        for slot in acc.iter_mut() {
            let v = u32::from(*slot) * radix + carry;
            *slot = (v % 10) as u8;
            carry = v / 10;
        }
        while carry > 0 {
            acc.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    let s: String = acc.iter().rev().map(|d| (b'0' + d) as char).collect();
    Some(s.trim_start_matches('0').to_string()).map(|t| if t.is_empty() { "0".into() } else { t })
}

impl<'a> Lowerer<'a> {
    /// Bind one bound group, producing the scope entries and the binder name.
    ///
    /// A plain pattern binds a fresh name directly. A tuple pattern binds one
    /// fresh name and projects the components out of it, which is what keeps
    /// every kernel binder single-variable.
    fn bind_pattern(&mut self, pat: &Pattern, scope: &mut HashMap<String, Binding<'a>>) -> Name {
        match pat {
            Pattern::Name(id) => {
                let fresh = self.fresh_name(&id.name);
                scope.insert(id.name.clone(), Binding::Bound(fresh.clone()));
                fresh
            }
            Pattern::Tuple(ids) => {
                let fresh = self.fresh_name("tuple");
                let tv = Kera::Var(fresh.clone()).rc();
                for (i, id) in ids.iter().enumerate() {
                    let idx = Kera::Int((i + 1).to_string()).rc();
                    scope.insert(
                        id.name.clone(),
                        Binding::Value(Kera::FunApp(Rc::clone(&tv), idx).rc()),
                    );
                }
                fresh
            }
        }
    }

    /// Push the frames for a chain of binders over `bounds`, ending in `body`.
    ///
    /// `make` turns (var, set, body) into the kernel node, so the same
    /// machinery serves `\A`, `\E`, `{x \in S : p}`, `{e : x \in S}` and
    /// `[x \in S |-> e]`.
    fn expand_binder_chain(
        &mut self,
        expr: &'a Expr,
        bounds: &'a [Bound],
        body: &'a Expr,
        stack: &mut Vec<Frame<'a>>,
    ) {
        // Children pushed, in evaluation order: every domain, then the body.
        // `Build` rebuilds the chain from them.
        let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
        let mut scope = HashMap::new();
        let mut names = Vec::with_capacity(total);
        for b in bounds {
            for p in &b.patterns {
                names.push(self.bind_pattern(p, &mut scope));
            }
        }
        self.binder_names.insert(expr.span.start.offset, names);

        stack.push(Frame::Build(expr, total + 1));
        stack.push(Frame::PopScope);
        stack.push(Frame::Expand(body));
        stack.push(Frame::PushScope(scope));
        // Domains are outside the binder's scope.
        for b in bounds.iter().rev() {
            for _ in 0..b.patterns.len() {
                stack.push(Frame::Expand(&b.domain));
            }
        }
    }

    /// Inline a user-defined operator that was written in operator position.
    fn push_symbol_inline(
        &mut self,
        op: &str,
        args: &[&'a Expr],
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let Some(def) = self.defs.get(op).cloned() else {
            return Err(LowerError::unsupported(
                &format!("the operator `{op}`"),
                "internal: it was reported as defined but is not",
                span,
            ));
        };
        if def.params.len() != args.len() {
            return Err(LowerError::new(
                LowerErrorKind::Arity {
                    name: op.to_string(),
                    expected: def.params.len(),
                    found: args.len(),
                },
                span,
            ));
        }
        stack.push(Frame::Inline {
            name: op.to_string(),
            params: def.params.clone(),
            body: def.body,
            span,
            cache_as: None,
        });
        for a in args.iter().rev() {
            stack.push(Frame::Expand(a));
        }
        Ok(())
    }

    /// Push the frames that look through `inst` at its member `member`,
    /// applied to `args`.
    fn push_instance_member(
        &mut self,
        inst_name: &str,
        member: &str,
        args: &[&'a Expr],
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let Some(inst) = self.instances.get(inst_name).cloned() else {
            return Err(LowerError::unsupported(
                &format!("`{inst_name}!{member}`"),
                "no `INSTANCE` with that name is in scope, or the instantiated module was \
                 not found on the search path",
                span,
            ));
        };
        if !inst.params.is_empty() {
            return Err(LowerError::unsupported(
                &format!("`{inst_name}!{member}`"),
                "a parameterised instance must be applied, as `I(e)!Op`",
                span,
            ));
        }
        self.push_instance_body(&inst, member, args, span, stack)
    }

    fn push_instance_body(
        &mut self,
        inst: &Instantiation<'a>,
        member: &str,
        args: &[&'a Expr],
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let target = inst.module;
        let Some(def) = self
            .module_defs
            .get(&target.name.name)
            .and_then(|m| m.get(member))
            .cloned()
        else {
            return Err(LowerError::unsupported(
                &format!("`{member}`"),
                &format!(
                    "module `{}` has no operator definition with that name",
                    target.name.name
                ),
                span,
            ));
        };
        if def.params.len() != args.len() {
            return Err(LowerError::new(
                LowerErrorKind::Arity {
                    name: member.to_string(),
                    expected: def.params.len(),
                    found: args.len(),
                },
                span,
            ));
        }

        // Every constant and variable the instantiated module declares must be
        // substituted: explicitly by `WITH`, or implicitly by the same-named
        // symbol here. Leaving one unsubstituted would silently read the
        // *wrong* module's symbol.
        let declared: Vec<String> = target
            .constants()
            .iter()
            .map(|d| d.name.name.clone())
            .chain(target.variables().iter().map(|v| v.name.clone()))
            .collect();
        let mut subst_names: Vec<String> = Vec::new();
        let mut subst_exprs: Vec<&'a Expr> = Vec::new();
        for (n, e) in &inst.with {
            subst_names.push(n.clone());
            subst_exprs.push(e);
        }
        let implicit: Vec<String> = declared
            .into_iter()
            .filter(|d| !subst_names.iter().any(|s| s == d))
            .collect();

        stack.push(Frame::PopInstanceCtx);
        stack.push(Frame::Expand(def.body));
        stack.push(Frame::PushInstanceCtx {
            module: target,
            subst_names,
            implicit,
            member_params: def.params.clone(),
        });
        // Arguments last so they are on top of the value stack.
        for a in args.iter().rev() {
            stack.push(Frame::Expand(a));
        }
        for e in subst_exprs.into_iter().rev() {
            stack.push(Frame::Expand(e));
        }
        Ok(())
    }

    /// Resolve a bare name through the instance being looked through, if any.
    fn ctx_resolve(&self, name: &str) -> Option<CtxResolution<'a>> {
        let ctx = self.ctx.last()?;
        if let Some(v) = ctx.subst.get(name) {
            return Some(CtxResolution::Value(Rc::clone(v)));
        }
        let def = self.module_defs.get(&ctx.module.name.name)?.get(name)?;
        Some(CtxResolution::Def(def.clone()))
    }

    fn expand(
        &mut self,
        e: &'a Expr,
        stack: &mut Vec<Frame<'a>>,
        values: &mut Vec<KeraRef>,
    ) -> Result<()> {
        let span = e.span;
        match &e.kind {
            ExprKind::Int { base, digits } => {
                let Some(dec) = digits_to_decimal(*base, digits) else {
                    return Err(LowerError::unsupported(
                        "this numeral",
                        "its digits are not valid in the base it was written in",
                        span,
                    ));
                };
                values.push(Kera::Int(dec).rc());
            }
            ExprKind::Str(s) => values.push(Kera::Str(s.clone()).rc()),
            ExprKind::Real(_) => {
                return Err(LowerError::unsupported(
                    "a real literal",
                    "the kernel has no real numbers; use integers, or `Reals` arithmetic \
                     once it is encoded",
                    span,
                ));
            }
            ExprKind::At => match self.lookup("@") {
                Some(Binding::Value(v)) => values.push(v),
                _ => {
                    return Err(LowerError::unsupported(
                        "`@`",
                        "it may only appear inside an `EXCEPT` update",
                        span,
                    ));
                }
            },
            ExprKind::Name(q) => {
                if q.is_qualified() {
                    let names: Vec<&str> = q.path.iter().map(|i| i.name.as_str()).collect();
                    let (Some(inst), Some(member)) = (names.first(), names.get(1)) else {
                        return Err(LowerError::unsupported(
                            "an instance-qualified name",
                            "internal: malformed path",
                            span,
                        ));
                    };
                    if names.len() > 2 {
                        return Err(LowerError::unsupported(
                            &format!("`{}`", names.join("!")),
                            "chained instance qualifiers are not resolved yet",
                            span,
                        ));
                    }
                    return self.push_instance_member(inst, member, &[], span, stack);
                }
                let Some(id) = q.base() else {
                    return Err(LowerError::unsupported("an empty name", "internal", span));
                };
                // Inside an instance, a bare name means the instantiated
                // module's symbol under that instance's substitution -- never
                // the instantiating module's same-named symbol.
                if self.lookup(&id.name).is_none()
                    && let Some(res) = self.ctx_resolve(&id.name)
                {
                    match res {
                        CtxResolution::Value(v) => values.push(v),
                        CtxResolution::Def(def) if def.params.is_empty() => {
                            stack.push(Frame::Inline {
                                name: id.name.clone(),
                                params: Vec::new(),
                                body: def.body,
                                span,
                                cache_as: None,
                            });
                        }
                        CtxResolution::Def(def) => {
                            return Err(LowerError::new(
                                LowerErrorKind::Arity {
                                    name: id.name.clone(),
                                    expected: def.params.len(),
                                    found: 0,
                                },
                                span,
                            ));
                        }
                    }
                    return Ok(());
                }
                match self.lookup(&id.name) {
                    Some(Binding::Value(v)) => values.push(v),
                    Some(Binding::Bound(n)) => values.push(Kera::Var(n).rc()),
                    // An operator parameter has no value of its own; only an
                    // application of it does.
                    Some(Binding::Op { params, .. }) => {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: id.name.clone(),
                                expected: params.len(),
                                found: 0,
                            },
                            span,
                        ));
                    }
                    None => match self.defs.get(&id.name).cloned() {
                        Some(def) if def.params.is_empty() => {
                            // Only a module-level definition may be shared,
                            // and only outside an instance, where the
                            // substitution would change what the body means.
                            let shareable = def.cacheable && self.ctx.is_empty();
                            if shareable && let Some(v) = self.cache.get(&id.name) {
                                values.push(Rc::clone(v));
                                return Ok(());
                            }
                            stack.push(Frame::Inline {
                                name: id.name.clone(),
                                params: Vec::new(),
                                body: def.body,
                                span,
                                cache_as: shareable.then(|| id.name.clone()),
                            });
                        }
                        // An operator named but not applied: it is being
                        // passed to something whose signature we do not know
                        // (an unresolved standard-module operator such as
                        // `ApaFoldSet`). Recorded as a zero-argument opaque
                        // reference so the operator's identity survives; the
                        // encoder must recognise it or decline.
                        Some(_) => {
                            values.push(Kera::Opaque(Name(id.name.clone()), Vec::new()).rc())
                        }
                        None => match self.funs.get(&id.name).cloned() {
                            Some((bounds, body)) => stack.push(Frame::ExpandFun(bounds, body)),
                            None => {
                                // An unnamed `INSTANCE M WITH …` makes M's
                                // members visible without a prefix.
                                let open = self.open_instances.iter().find(|i| {
                                    self.module_defs
                                        .get(&i.module.name.name)
                                        .is_some_and(|d| d.contains_key(&id.name))
                                });
                                match open.cloned() {
                                    Some(inst) => {
                                        self.push_instance_body(&inst, &id.name, &[], span, stack)?;
                                    }
                                    None => values.push(Kera::Var(Name(id.name.clone())).rc()),
                                }
                            }
                        },
                    },
                }
            }
            ExprKind::Apply { head, args } => {
                if head.is_qualified() {
                    let names: Vec<&str> = head.path.iter().map(|i| i.name.as_str()).collect();
                    let (Some(inst), Some(member)) = (names.first(), names.get(1)) else {
                        return Err(LowerError::unsupported(
                            "an instance-qualified application",
                            "internal: malformed path",
                            span,
                        ));
                    };
                    if names.len() > 2 {
                        return Err(LowerError::unsupported(
                            &format!("`{}`", names.join("!")),
                            "chained instance qualifiers are not resolved yet",
                            span,
                        ));
                    }
                    let arg_refs: Vec<&'a Expr> = args.iter().collect();
                    return self.push_instance_member(inst, member, &arg_refs, span, stack);
                }
                let Some(id) = head.base() else {
                    return Err(LowerError::unsupported("an empty name", "internal", span));
                };
                // A parameter bound to a value cannot be applied: higher-order
                // parameters are inlined as values, and applying one needs the
                // operator itself, not its level.
                // Inside an instance, an application resolves against the
                // instantiated module first.
                if self.lookup(&id.name).is_none()
                    && let Some(CtxResolution::Def(def)) = self.ctx_resolve(&id.name)
                    && def.params.len() == args.len()
                {
                    stack.push(Frame::Inline {
                        name: id.name.clone(),
                        params: def.params.clone(),
                        body: def.body,
                        span,
                        cache_as: None,
                    });
                    for a in args.iter().rev() {
                        stack.push(Frame::Expand(a));
                    }
                    return Ok(());
                }
                // An operator *parameter* shadows a global definition.
                let bound_op = match self.lookup(&id.name) {
                    Some(Binding::Op { params, body }) => Some(Def {
                        params,
                        body,
                        cacheable: false,
                    }),
                    _ => None,
                };
                let resolved = bound_op.or_else(|| self.defs.get(&id.name).cloned());
                match resolved {
                    Some(def) if def.params.len() == args.len() => {
                        let mut ops: Vec<(String, Binding<'a>)> = Vec::new();
                        let mut value_args: Vec<&'a Expr> = Vec::new();
                        for ((pname, arity), arg) in def.params.iter().zip(args.iter()) {
                            if *arity == 0 {
                                value_args.push(arg);
                                continue;
                            }
                            let Some(b) = self.as_operator(arg) else {
                                return Err(LowerError::unsupported(
                                    "this higher-order argument",
                                    "a parameter declared as `F(_)` takes an operator: pass a \
                                     defined operator name or a `LAMBDA`",
                                    arg.span,
                                ));
                            };
                            ops.push((pname.clone(), b));
                        }
                        if !ops.is_empty() {
                            self.pending_ops.insert(span.start.offset, ops);
                        }
                        stack.push(Frame::Inline {
                            name: id.name.clone(),
                            params: def.params.clone(),
                            body: def.body,
                            span,
                            cache_as: None,
                        });
                        for a in value_args.into_iter().rev() {
                            stack.push(Frame::Expand(a));
                        }
                    }
                    Some(def) => {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: id.name.clone(),
                                expected: def.params.len(),
                                found: args.len(),
                            },
                            span,
                        ));
                    }
                    None => {
                        stack.push(Frame::Build(e, args.len()));
                        for a in args.iter().rev() {
                            stack.push(Frame::Expand(a));
                        }
                    }
                }
            }
            ExprKind::Quant { kind, bounds, body } => {
                if matches!(kind, QuantKind::TemporalForall | QuantKind::TemporalExists) {
                    return Err(LowerError::unsupported(
                        "a temporal quantifier (`\\AA` / `\\EE`)",
                        "it quantifies over behaviours, which is spec structure rather than \
                         a kernel expression",
                        span,
                    ));
                }
                self.expand_binder_chain(e, bounds, body, stack);
            }
            ExprKind::UnboundedQuant { .. } => {
                return Err(LowerError::unsupported(
                    "an unbounded quantifier",
                    "give the bound variable a set to range over, as `\\A x \\in S : …`",
                    span,
                ));
            }
            ExprKind::Choose {
                pattern,
                domain,
                body,
            } => {
                let mut scope = HashMap::new();
                let Some(domain) = domain else {
                    // `CHOOSE x : P` is legal TLA+ and the standard idiom for
                    // a fresh value (`None == CHOOSE v : v \notin Values`), so
                    // the kernel carries it rather than rejecting it.
                    let name = self.bind_pattern(pattern, &mut scope);
                    self.binder_names.insert(span.start.offset, vec![name]);
                    stack.push(Frame::Build(e, 1));
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(scope));
                    return Ok(());
                };
                let name = self.bind_pattern(pattern, &mut scope);
                self.binder_names.insert(span.start.offset, vec![name]);
                stack.push(Frame::Build(e, 2));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
                stack.push(Frame::Expand(domain));
            }
            ExprKind::SetFilter {
                pattern,
                domain,
                pred,
            } => {
                let mut scope = HashMap::new();
                let name = self.bind_pattern(pattern, &mut scope);
                self.binder_names.insert(span.start.offset, vec![name]);
                stack.push(Frame::Build(e, 2));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(pred));
                stack.push(Frame::PushScope(scope));
                stack.push(Frame::Expand(domain));
            }
            ExprKind::SetMap { expr, bounds } => {
                self.expand_binder_chain(e, bounds, expr, stack);
            }
            ExprKind::FnConstruct { bounds, body } => {
                let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
                if total == 1 {
                    self.expand_binder_chain(e, bounds, body, stack);
                } else {
                    // `[x \in S, y \in T |-> e]` is a function on `S \X T`.
                    // One tuple variable ranges over the product and the
                    // components are projected out of it, which keeps every
                    // kernel binder single-variable.
                    let tv = self.fresh_name("arg");
                    let tvar = Kera::Var(tv.clone()).rc();
                    let mut scope = HashMap::new();
                    let mut i = 0usize;
                    for b in bounds {
                        for p in &b.patterns {
                            i += 1;
                            let proj =
                                Kera::FunApp(Rc::clone(&tvar), Kera::Int(i.to_string()).rc()).rc();
                            match p {
                                Pattern::Name(id) => {
                                    scope.insert(id.name.clone(), Binding::Value(proj));
                                }
                                Pattern::Tuple(ids) => {
                                    for (j, id) in ids.iter().enumerate() {
                                        let inner = Kera::FunApp(
                                            Rc::clone(&proj),
                                            Kera::Int((j + 1).to_string()).rc(),
                                        )
                                        .rc();
                                        scope.insert(id.name.clone(), Binding::Value(inner));
                                    }
                                }
                            }
                        }
                    }
                    self.binder_names.insert(span.start.offset, vec![tv]);
                    stack.push(Frame::Build(e, total + 1));
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(scope));
                    for b in bounds.iter().rev() {
                        for _ in 0..b.patterns.len() {
                            stack.push(Frame::Expand(&b.domain));
                        }
                    }
                }
            }
            ExprKind::Let { defs, body } => {
                let mut saved: Vec<(String, Option<Def<'a>>)> = Vec::new();
                for d in defs {
                    match &d.kind {
                        UnitKind::OpDef {
                            name, params, body, ..
                        } => {
                            let def = Def {
                                params: params
                                    .iter()
                                    .map(|p| (p.name.name.clone(), p.arity))
                                    .collect(),
                                body,
                                cacheable: false,
                            };
                            saved.push((
                                name.name.clone(),
                                self.defs.insert(name.name.clone(), def),
                            ));
                        }
                        UnitKind::FnDef {
                            name, bounds, body, ..
                        } => {
                            self.funs
                                .insert(name.name.clone(), (bounds.as_slice(), body));
                            saved.push((name.name.clone(), None));
                        }
                        UnitKind::Recursive(_) => {
                            return Err(LowerError::unsupported(
                                "`RECURSIVE` inside `LET`",
                                "a recursive operator has no finite unfolding; rewrite it as a \
                                 fold over a finite set, or a function `[x \\in S |-> …]`",
                                d.span,
                            ));
                        }
                        _ => {}
                    }
                }
                stack.push(Frame::PopLetDefs(saved));
                stack.push(Frame::Expand(body));
            }
            ExprKind::Except { base, updates } => {
                // Children, in order: the base, then per update every index
                // expression followed by the replacement value. `@` is bound
                // around each value by a `BindExceptAt` frame.
                let nchildren: usize = 1 + updates
                    .iter()
                    .map(|u| {
                        1 + u
                            .path
                            .iter()
                            .map(|s| match s {
                                ExceptSel::Index(ix) => ix.len(),
                                ExceptSel::Field(_) => 1,
                            })
                            .sum::<usize>()
                    })
                    .sum::<usize>();
                stack.push(Frame::Build(e, nchildren));
                for u in updates.iter().rev() {
                    let path_len: usize = u
                        .path
                        .iter()
                        .map(|s| match s {
                            ExceptSel::Index(ix) => ix.len(),
                            ExceptSel::Field(_) => 1,
                        })
                        .sum();
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(&u.value));
                    stack.push(Frame::BindExceptAt { path_len });
                    for sel in u.path.iter().rev() {
                        match sel {
                            ExceptSel::Index(ix) => {
                                for i in ix.iter().rev() {
                                    stack.push(Frame::Expand(i));
                                }
                            }
                            ExceptSel::Field(f) => {
                                stack.push(Frame::PushLiteral(Kera::Str(f.name.clone()).rc()));
                            }
                        }
                    }
                }
                stack.push(Frame::Expand(base));
            }
            // A user-defined operator symbol: `a \oplus b == …`, `-. z == …`.
            // The definition is registered under its spelling, so it must be
            // consulted before the built-in rules — otherwise every spec that
            // defines an infix operator fails to lower.
            ExprKind::Infix { op, lhs, rhs, .. } if self.defs.contains_key(op.as_str()) => {
                self.push_symbol_inline(op, &[lhs, rhs], span, stack)?;
            }
            ExprKind::Prefix { op, operand, .. } | ExprKind::Postfix { op, operand, .. }
                if self.defs.contains_key(op.as_str()) =>
            {
                self.push_symbol_inline(op, &[operand], span, stack)?;
            }
            // Everything else is "lower the children, then build".
            _ => {
                let kids = surface_children(e);
                stack.push(Frame::Build(e, kids.len()));
                for c in kids.into_iter().rev() {
                    stack.push(Frame::Expand(c));
                }
            }
        }
        Ok(())
    }
}

/// What a bare name means inside an instance.
enum CtxResolution<'a> {
    /// A declared name of the instantiated module, replaced by `WITH`.
    Value(KeraRef),
    /// A definition of the instantiated module, to be looked through as well.
    Def(Def<'a>),
}

/// The children `Frame::Build` will find on the value stack, in order, for the
/// nodes handled by the generic path.
fn surface_children(e: &Expr) -> Vec<&Expr> {
    let mut out: Vec<&Expr> = Vec::new();
    match &e.kind {
        ExprKind::Prefix { operand, .. } | ExprKind::Postfix { operand, .. } => out.push(operand),
        ExprKind::Infix { lhs, rhs, .. } => {
            out.push(lhs);
            out.push(rhs);
        }
        ExprKind::Junction { items, .. } | ExprKind::SetEnum(items) | ExprKind::Tuple(items) => {
            out.extend(items);
        }
        ExprKind::Paren(inner) | ExprKind::Label { body: inner, .. } => out.push(inner),
        ExprKind::Field { record, .. } => out.push(record),
        ExprKind::FnApply { func, args } => {
            out.push(func);
            out.extend(args);
        }
        ExprKind::FnSet { domain, codomain } => {
            out.push(domain);
            out.push(codomain);
        }
        ExprKind::RecordLit(fs) | ExprKind::RecordSet(fs) => {
            out.extend(fs.iter().map(|(_, v)| v));
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            out.push(cond);
            out.push(then_branch);
            out.push(else_branch);
        }
        ExprKind::Case { arms, other } => {
            for a in arms {
                out.push(&a.guard);
                out.push(&a.value);
            }
            out.extend(other.iter().map(AsRef::as_ref));
        }
        ExprKind::Apply { args, .. } => out.extend(args),
        _ => {}
    }
    out
}

impl<'a> Lowerer<'a> {
    /// Build one kernel node from the `n` values its children left on the stack.
    fn build(&mut self, e: &'a Expr, values: &mut Vec<KeraRef>, n: usize) -> Result<KeraRef> {
        let span = e.span;
        let at = values.len().checked_sub(n).ok_or_else(|| {
            LowerError::unsupported("this expression", "internal: value stack underflow", span)
        })?;
        let kids: Vec<KeraRef> = values.split_off(at);
        let take = |i: usize| -> Result<KeraRef> {
            kids.get(i).cloned().ok_or_else(|| {
                LowerError::unsupported("this expression", "internal: missing child", span)
            })
        };

        let built = match &e.kind {
            ExprKind::Paren(_) | ExprKind::Label { .. } => take(0)?,
            ExprKind::Junction { kind, .. } => match kind {
                nixie_tla_syntax::ast::Junct::And => Kera::And(kids).rc(),
                nixie_tla_syntax::ast::Junct::Or => Kera::Or(kids).rc(),
            },
            ExprKind::SetEnum(_) => Kera::SetEnum(kids).rc(),
            ExprKind::Tuple(_) => Kera::Tuple(kids).rc(),
            ExprKind::Field { field, .. } => {
                Kera::FunApp(take(0)?, Kera::Str(field.name.clone()).rc()).rc()
            }
            ExprKind::FnApply { .. } => {
                let f = take(0)?;
                let args: Vec<KeraRef> = kids.iter().skip(1).cloned().collect();
                match args.len() {
                    // `f[a, b]` is `f[<<a, b>>]` in TLA+.
                    0 => {
                        return Err(LowerError::unsupported(
                            "a function application with no argument",
                            "internal",
                            span,
                        ));
                    }
                    1 => Kera::FunApp(f, take(1)?).rc(),
                    _ => Kera::FunApp(f, Kera::Tuple(args).rc()).rc(),
                }
            }
            ExprKind::FnSet { .. } => Kera::FunSet {
                set: take(0)?,
                cod: take(1)?,
            }
            .rc(),
            ExprKind::RecordLit(fs) => {
                let fields = fs
                    .iter()
                    .zip(kids.iter())
                    .map(|((name, _), v)| (name.name.clone(), Rc::clone(v)))
                    .collect();
                Kera::Record(sort_fields(fields)).rc()
            }
            ExprKind::RecordSet(fs) => {
                let fields = fs
                    .iter()
                    .zip(kids.iter())
                    .map(|((name, _), v)| (name.name.clone(), Rc::clone(v)))
                    .collect();
                Kera::RecordSet(sort_fields(fields)).rc()
            }
            ExprKind::If { .. } => Kera::Ite(take(0)?, take(1)?, take(2)?).rc(),
            ExprKind::Case { arms, other } => build_case(arms, other.is_some(), &kids, span)?,
            ExprKind::Apply { head, .. } => {
                let Some(id) = head.base() else {
                    return Err(LowerError::unsupported("an empty name", "internal", span));
                };
                Kera::Opaque(Name(id.name.clone()), kids).rc()
            }
            ExprKind::Prefix { op, .. } => build_prefix(op, take(0)?, span)?,
            ExprKind::Postfix { op, .. } => match op.as_str() {
                "'" => Kera::Prime(take(0)?).rc(),
                other => Kera::Opaque(Name(other.to_string()), vec![take(0)?]).rc(),
            },
            ExprKind::Infix { op, .. } => build_infix(op, take(0)?, take(1)?, span)?,
            ExprKind::Quant { kind, .. } => {
                let names = self.take_binder_names(span);
                let body = kids.last().cloned().ok_or_else(|| {
                    LowerError::unsupported("a quantifier", "internal: no body", span)
                })?;
                let mut acc = body;
                for (i, var) in names.iter().enumerate().rev() {
                    let set = take(i)?;
                    acc = match kind {
                        QuantKind::Forall => Kera::Forall {
                            var: var.clone(),
                            set,
                            body: acc,
                        },
                        _ => Kera::Exists {
                            var: var.clone(),
                            set,
                            body: acc,
                        },
                    }
                    .rc();
                }
                acc
            }
            ExprKind::SetMap { .. } => {
                let names = self.take_binder_names(span);
                let expr = kids.last().cloned().ok_or_else(|| {
                    LowerError::unsupported("a set map", "internal: no body", span)
                })?;
                let mut acc = expr;
                for (i, var) in names.iter().enumerate().rev() {
                    acc = Kera::Map {
                        var: var.clone(),
                        set: take(i)?,
                        expr: acc,
                    }
                    .rc();
                }
                acc
            }
            ExprKind::FnConstruct { .. } => {
                let names = self.take_binder_names(span);
                let Some(var) = names.first().cloned() else {
                    return Err(LowerError::unsupported("a function", "internal", span));
                };
                let body = kids.last().cloned().ok_or_else(|| {
                    LowerError::unsupported("a function", "internal: no body", span)
                })?;
                // One domain, or a product of them for a multi-variable form.
                let ndomains = kids.len().saturating_sub(1);
                let set = if ndomains <= 1 {
                    take(0)?
                } else {
                    let doms: Vec<KeraRef> = kids.iter().take(ndomains).cloned().collect();
                    Kera::Times(doms).rc()
                };
                Kera::FunDef { var, set, body }.rc()
            }
            ExprKind::Choose { domain, .. } => {
                let names = self.take_binder_names(span);
                let Some(var) = names.first().cloned() else {
                    return Err(LowerError::unsupported("a `CHOOSE`", "internal", span));
                };
                if domain.is_some() {
                    Kera::Choose {
                        var,
                        set: take(0)?,
                        body: take(1)?,
                    }
                    .rc()
                } else {
                    Kera::ChooseUnbounded {
                        var,
                        body: take(0)?,
                    }
                    .rc()
                }
            }
            ExprKind::SetFilter { .. } => {
                let names = self.take_binder_names(span);
                let Some(var) = names.first().cloned() else {
                    return Err(LowerError::unsupported("a set filter", "internal", span));
                };
                Kera::Filter {
                    var,
                    set: take(0)?,
                    pred: take(1)?,
                }
                .rc()
            }
            ExprKind::Except { updates, .. } => build_except(updates, &kids, span)?,
            other => {
                return Err(LowerError::unsupported(
                    &format!("{}", DescribeKind(other)),
                    "it has no kernel form",
                    span,
                ));
            }
        };
        Ok(built)
    }

    fn take_binder_names(&mut self, span: Span) -> Vec<Name> {
        self.binder_names
            .remove(&span.start.offset)
            .unwrap_or_default()
    }
}

/// `CASE p -> a [] q -> b [] OTHER -> c` becomes nested `IF`s.
fn build_case(arms: &[CaseArm], has_other: bool, kids: &[KeraRef], span: Span) -> Result<KeraRef> {
    // Children are guard, value, guard, value, …, then the `OTHER` value.
    let mut acc = if has_other {
        kids.last().cloned().ok_or_else(|| {
            LowerError::unsupported("a `CASE`", "internal: missing `OTHER` value", span)
        })?
    } else {
        // TLA+ leaves `CASE` with no matching arm undefined. Marking it
        // explicitly is the honest lowering: a silent default here would be a
        // fabricated value, which `AGENTS.md` forbids outright.
        Kera::Opaque(Name("$CaseNoMatch".to_string()), Vec::new()).rc()
    };
    for i in (0..arms.len()).rev() {
        let guard = kids
            .get(2 * i)
            .cloned()
            .ok_or_else(|| LowerError::unsupported("a `CASE`", "internal: missing guard", span))?;
        let value = kids.get(2 * i + 1).cloned().ok_or_else(|| {
            LowerError::unsupported("a `CASE`", "internal: missing arm value", span)
        })?;
        acc = Kera::Ite(guard, value, acc).rc();
    }
    Ok(acc)
}

/// `[f EXCEPT !p1 = v1, !p2 = v2]` becomes nested single-step updates.
fn build_except(
    updates: &[nixie_tla_syntax::ast::ExceptUpdate],
    kids: &[KeraRef],
    span: Span,
) -> Result<KeraRef> {
    let mut acc = kids
        .first()
        .cloned()
        .ok_or_else(|| LowerError::unsupported("an `EXCEPT`", "internal: no base", span))?;
    let mut at = 1usize;
    for u in updates {
        let path_len: usize = u
            .path
            .iter()
            .map(|s| match s {
                ExceptSel::Index(ix) => ix.len(),
                ExceptSel::Field(_) => 1,
            })
            .sum();
        let path: Vec<KeraRef> = kids
            .get(at..at + path_len)
            .map(<[KeraRef]>::to_vec)
            .ok_or_else(|| {
                LowerError::unsupported("an `EXCEPT`", "internal: missing path", span)
            })?;
        let value = kids.get(at + path_len).cloned().ok_or_else(|| {
            LowerError::unsupported("an `EXCEPT`", "internal: missing value", span)
        })?;
        at += path_len + 1;
        acc = nest_except(acc, &path, value, span)?;
    }
    Ok(acc)
}

/// `[f EXCEPT ![i][j] = v]` is `[f EXCEPT ![i] = [f[i] EXCEPT ![j] = v]]`.
fn nest_except(fun: KeraRef, path: &[KeraRef], value: KeraRef, span: Span) -> Result<KeraRef> {
    let Some((head, rest)) = path.split_first() else {
        return Err(LowerError::unsupported(
            "an `EXCEPT` with an empty path",
            "internal",
            span,
        ));
    };
    if rest.is_empty() {
        return Ok(Kera::Except {
            fun,
            index: Rc::clone(head),
            value,
        }
        .rc());
    }
    let inner_base = Kera::FunApp(Rc::clone(&fun), Rc::clone(head)).rc();
    let inner = nest_except(inner_base, rest, value, span)?;
    Ok(Kera::Except {
        fun,
        index: Rc::clone(head),
        value: inner,
    }
    .rc())
}

fn build_prefix(op: &str, operand: KeraRef, span: Span) -> Result<KeraRef> {
    let k = match op {
        "~" => Kera::Not(operand),
        "-." => Kera::Neg(operand),
        "SUBSET" => Kera::Powerset(operand),
        "UNION" => Kera::BigUnion(operand),
        "DOMAIN" => Kera::Domain(operand),
        "UNCHANGED" => return Ok(unchanged(operand)),
        "[]" | "<>" => {
            return Err(LowerError::unsupported(
                &format!("the temporal operator `{op}`"),
                "temporal operators describe behaviours, not states; they belong to the \
                 spec's structure rather than to a kernel expression",
                span,
            ));
        }
        "ENABLED" => {
            return Err(LowerError::unsupported(
                "`ENABLED`",
                "it quantifies over successor states and needs the transition relation, \
                 which the kernel does not carry",
                span,
            ));
        }
        // A prefix operator from a standard module with no kernel node of its
        // own. Recorded by name rather than rejected: it is a *primitive* the
        // encoder must implement or decline, not something to expand here.
        // This is not a silent default -- nothing is dropped and nothing is
        // invented, the operator is carried through under its own name.
        other => Kera::Opaque(Name(other.to_string()), vec![operand]),
    };
    Ok(k.rc())
}

/// `UNCHANGED e` is `e' = e`, componentwise for a tuple.
fn unchanged(e: KeraRef) -> KeraRef {
    if let Kera::Tuple(items) = e.as_ref() {
        let conjuncts = items
            .iter()
            .map(|i| Kera::Eq(Kera::Prime(Rc::clone(i)).rc(), Rc::clone(i)).rc())
            .collect();
        return Kera::And(conjuncts).rc();
    }
    Kera::Eq(Kera::Prime(Rc::clone(&e)).rc(), e).rc()
}

fn build_infix(op: &str, a: KeraRef, b: KeraRef, span: Span) -> Result<KeraRef> {
    let k = match op {
        "=" => Kera::Eq(a, b),
        "/=" => Kera::Not(Kera::Eq(a, b).rc()),
        "\\in" => Kera::In(a, b),
        "\\notin" => Kera::Not(Kera::In(a, b).rc()),
        "/\\" => Kera::And(vec![a, b]),
        "\\/" => Kera::Or(vec![a, b]),
        "=>" => Kera::Or(vec![Kera::Not(a).rc(), b]),
        "<=>" => Kera::Eq(a, b),
        "\\cup" => Kera::SetBin(SetOp::Union, a, b),
        "\\cap" => Kera::SetBin(SetOp::Intersect, a, b),
        "\\" => Kera::SetBin(SetOp::Difference, a, b),
        "\\subseteq" => {
            // The one set relation without a kernel node: it is a quantifier
            // in every encoding, so expanding it here loses nothing.
            let v = Name("sub#0".to_string());
            Kera::Forall {
                var: v.clone(),
                set: a,
                body: Kera::In(Kera::Var(v).rc(), b).rc(),
            }
        }
        ".." => Kera::Range(a, b),
        "\\X" => Kera::Times(vec![a, b]),
        "+" => Kera::Arith(ArithOp::Add, a, b),
        "-" => Kera::Arith(ArithOp::Sub, a, b),
        "*" => Kera::Arith(ArithOp::Mul, a, b),
        "\\div" => Kera::Arith(ArithOp::Div, a, b),
        "%" => Kera::Arith(ArithOp::Mod, a, b),
        "^" => Kera::Arith(ArithOp::Exp, a, b),
        "<" => Kera::Cmp(CmpOp::Lt, a, b),
        "<=" => Kera::Cmp(CmpOp::Le, a, b),
        ">" => Kera::Cmp(CmpOp::Gt, a, b),
        ">=" => Kera::Cmp(CmpOp::Ge, a, b),
        "~>" | "-+->" | "\\cdot" => {
            return Err(LowerError::unsupported(
                &format!("the operator `{op}`"),
                "it relates behaviours or actions, which is spec structure rather than a \
                 kernel expression",
                span,
            ));
        }
        // An infix operator from a standard module -- `\o` from `Sequences`,
        // `:>` and `@@` from `TLC`, `\oplus` from a user's own module. Carried
        // through by name for the encoder to implement or decline. See the
        // note in `build_prefix`.
        other => Kera::Opaque(Name(other.to_string()), vec![a, b]),
    };
    Ok(k.rc())
}

/// Names a surface node for a diagnostic.
struct DescribeKind<'a>(&'a ExprKind);

impl core::fmt::Display for DescribeKind<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self.0 {
            ExprKind::Action { .. } => "a subscripted action (`[A]_v` / `<<A>>_v`)",
            ExprKind::Fairness { .. } => "a fairness condition (`WF_` / `SF_`)",
            ExprKind::Lambda { .. } => "a bare `LAMBDA`",
            ExprKind::AssumeProve { .. } => "an `ASSUME` … `PROVE` sequent",
            ExprKind::Qualified { .. } => "an instance-qualified expression",
            ExprKind::UnboundedQuant { .. } => "an unbounded quantifier",
            _ => "this construct",
        };
        f.write_str(s)
    }
}
