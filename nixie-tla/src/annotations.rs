//! `@type:` annotations – the Type1 grammar and the seeding of inference.
//!
//! Apalache *requires* annotations on almost every spec it checks, so a
//! drop-in has to read them. The grammar is Apalache's Type1
//! (`DefaultType1Parser.scala`), minus the pieces Nixie's type lattice has
//! no representation for yet (variants are their own sub-issue); what is
//! not representable is a **named refusal**, never a silent ignore.
//!
//! An annotation is *checked, never trusted*: it is unified with what
//! inference derives, and a conflict is the type error it is (exit 120),
//! exactly as Apalache rejects contradictory annotations.

use crate::types::{Inference, Ty, TyId, Type, TypeError};

/// Why an annotation could not be honoured.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AnnotationError {
    /// The annotation text does not parse as Type1.
    #[error("a `@type:` annotation that does not parse: {why}")]
    Parse {
        /// What was wrong, with the text quoted.
        why: String,
    },
    /// A construct of the grammar Nixie has no type for (variants).
    #[error("a `@type:` annotation using `{what}`, which this checker has no type for yet")]
    Unsupported {
        /// The construct, by name.
        what: &'static str,
    },
}

/// One parsed Type1 annotation, ready to seed inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedType(pub Type);

/// One parsed **operator signature** `(a, b) => c`, ready to be checked
/// against the annotated operator's body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedSignature {
    /// The parameter types, in order.
    pub params: Vec<Type>,
    /// The result type.
    pub result: Type,
}

/// Parse an operator-signature annotation, `(a, b) => c` – or the
/// single-parameter form without its parentheses, `P => R`, which is how
/// the corpus writes most of them (`Seq({x: Int, ..}) => Bool`).
///
/// Returns `Ok(None)` when the text is not a signature shape at all (the
/// caller falls back to [`parse_type1`]), and an error when it plainly
/// meant to be one and does not parse.
pub fn parse_signature1(src: &str) -> Result<Option<ParsedSignature>, AnnotationError> {
    let toks = tokenize(src)?;
    let mut p = Parser { toks, at: 0 };
    let params = if p.peek() == Some(&Tok::LParen) {
        p.at += 1;
        // `()` is the empty parameter list, Apalache's `operatorArgs` first
        // form: the signature of a zero-argument operator, which is how the
        // corpus annotates a constant written as a definition (`\* @type:
        // () => Set(Int); Empty == {}`). It is the signature of the body's
        // own type, and it was refused as `RParen where a type was expected`.
        let mut params = Vec::new();
        if p.peek() != Some(&Tok::RParen) {
            params.push(parse_sig_param(&mut p)?);
            while p.peek() == Some(&Tok::Comma) {
                p.at += 1;
                params.push(parse_sig_param(&mut p)?);
            }
        }
        p.expect(&Tok::RParen, "to close a signature's parameter list")?;
        params
    } else {
        // A lone parameter may be written bare. If no arrow follows, this
        // is not a signature at all and the caller's value-type parse owns
        // the text.
        let first = p.parse_fun()?;
        if p.peek() != Some(&Tok::BigArrow) {
            return Ok(None);
        }
        vec![first]
    };
    p.expect(&Tok::BigArrow, "to separate a signature's result")?;
    let result = p.parse_fun()?;
    if p.at < p.toks.len() && !matches!(&p.toks[p.at], Tok::Semi) {
        return Err(AnnotationError::Parse {
            why: format!("trailing input after the type in `{src}`"),
        });
    }
    Ok(Some(ParsedSignature { params, result }))
}

/// One parameter of a signature: an ordinary type, or an **operator
/// parameter** `(A) => B` – the higher-order case, `ChooseOne(S, P(_))`'s
/// `P` – which is a function type at the kernel level (the parameter is
/// applied in the body, and application typing is already `Fun`).
fn parse_sig_param(p: &mut Parser) -> Result<Type, AnnotationError> {
    let first = p.parse_fun()?;
    if p.peek() == Some(&Tok::BigArrow) {
        p.at += 1;
        let result = p.parse_fun()?;
        Ok(Type::Fun(Box::new(first), Box::new(result)))
    } else {
        Ok(first)
    }
}

/// The subset of Type1 this checker reads: Int/Bool/Str, Set(T), Seq(T),
/// right-associative function arrows, tuples, records, and identifiers
/// (lowercase = one type variable, uppercase = an uninterpreted type, or an
/// alias where `@typeAlias` defines that name; `$name` = a reference to the
/// alias `name`, a type constant of its own when no alias defines it).
///
/// Deliberately absent, each a named refusal: variants and operator types
/// (both belong to the variants sub-issue) and real numbers, which the
/// kernel does not have.
pub fn parse_type1(src: &str) -> Result<ParsedType, AnnotationError> {
    let toks = tokenize(src)?;
    let mut p = Parser { toks, at: 0 };
    let ty = p.parse_fun()?;
    let ty = if p.toks.get(p.at) == Some(&Tok::Pipe) {
        // A top-level `|` alternation continues a **variant row** whose
        // first arm `parse_atom` already read (issue #17):
        // `Tag(a) | Tag2(b) | ...` – the `@typeAlias` spelling.
        let mut tags = match &ty {
            Type::Variant { tags, open: false } => tags.clone(),
            _ => {
                return Err(AnnotationError::Parse {
                    why: "a `|` alternation must join `Tag(payload)` arms".to_string(),
                });
            }
        };
        while p.toks.get(p.at) == Some(&Tok::Pipe) {
            p.at += 1;
            let arm = p.parse_fun()?;
            match arm {
                Type::Variant {
                    tags: more,
                    open: false,
                } if more.len() == 1 => {
                    for (k, v) in more {
                        tags.insert(k, v);
                    }
                }
                _ => {
                    return Err(AnnotationError::Parse {
                        why: "a `|` alternation must join `Tag(payload)` arms".to_string(),
                    });
                }
            }
        }
        Type::Variant { tags, open: false }
    } else {
        ty
    };
    // `A => B` at the top level is an operator signature (the paren form
    // lands here too, its group already parsed): named-refused below at the
    // seeding side, which skips signatures with a note.
    if p.toks.get(p.at) == Some(&Tok::BigArrow) {
        return Err(AnnotationError::Unsupported {
            what: "an operator signature (`(a, b) => c`)",
        });
    }
    // Everything after the type is trailing junk – except that the caller
    // strips the `;` Apalache's annotations often end with.
    if p.at < p.toks.len() && !matches!(&p.toks[p.at], Tok::Semi) {
        return Err(AnnotationError::Parse {
            why: format!("trailing input after the type in `{src}`"),
        });
    }
    Ok(ParsedType(ty))
}

/// A token of the annotation grammar.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Arrow,    // ->
    BigArrow, // =>
    LParen,
    RParen,
    LAngle,
    RAngle,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Semi,
    Pipe,
}

fn tokenize(src: &str) -> Result<Vec<Tok>, AnnotationError> {
    let mut out = Vec::new();
    let bytes: Vec<char> = src.chars().collect();
    let mut i = 0usize;
    while i < bytes.len() {
        let c = bytes[i];
        match c {
            ' ' | '\t' | '\n' | '\r' => i += 1,
            // A `//` comment runs to the end of its line, as in Apalache's
            // `Type1Lexer` (`singleComment`): a type spread over several
            // `\*` lines may carry one between its lines
            // (`CommentedTypeAnnotation.tla`).
            '/' if bytes.get(i + 1) == Some(&'/') => {
                while i < bytes.len() && bytes[i] != '\n' {
                    i += 1;
                }
            }
            '-' if bytes.get(i + 1) == Some(&'>') => {
                out.push(Tok::Arrow);
                i += 2;
            }
            '=' if bytes.get(i + 1) == Some(&'>') => {
                out.push(Tok::BigArrow);
                i += 2;
            }
            '(' => {
                out.push(Tok::LParen);
                i += 1;
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
            }
            '<' if bytes.get(i + 1) == Some(&'<') => {
                out.push(Tok::LAngle);
                i += 2;
            }
            '>' if bytes.get(i + 1) == Some(&'>') => {
                out.push(Tok::RAngle);
                i += 2;
            }
            '{' => {
                out.push(Tok::LBrace);
                i += 1;
            }
            '|' => {
                out.push(Tok::Pipe);
                i += 1;
            }
            // A reference to a `@typeAlias`: `$transfer` names the alias
            // `transfer` (Apalache's `aliasReference`, whose `ConstT1`
            // carries the sigil in its name). The sigil stays in the
            // identifier, so the reference is never read as the type variable
            // `transfer`, and when no alias of that name exists it is a type
            // constant of its own, `$transfer`, as it is in Apalache.
            '$' => {
                let start = i + 1;
                let mut j = start;
                while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == '_') {
                    j += 1;
                }
                if j == start {
                    return Err(AnnotationError::Parse {
                        why: format!("`$` must name a type alias (`$name`) in `{src}`"),
                    });
                }
                out.push(Tok::Ident(format!(
                    "${}",
                    bytes[start..j].iter().collect::<String>()
                )));
                i = j;
            }
            '}' => {
                out.push(Tok::RBrace);
                i += 1;
            }
            ',' => {
                out.push(Tok::Comma);
                i += 1;
            }
            ':' => {
                out.push(Tok::Colon);
                i += 1;
            }
            ';' => {
                out.push(Tok::Semi);
                i += 1;
            }
            c if c.is_ascii_alphanumeric() || c == '_' => {
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == '_') {
                    i += 1;
                }
                out.push(Tok::Ident(bytes[start..i].iter().collect::<String>()));
            }
            other => {
                return Err(AnnotationError::Parse {
                    why: format!("`{other}` is not part of a type in `{src}`"),
                });
            }
        }
    }
    Ok(out)
}

/// The parser over those tokens.
struct Parser {
    toks: Vec<Tok>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }

    fn parse_fun(&mut self) -> Result<Type, AnnotationError> {
        // `a -> b -> c` is right-associative.
        let lhs = self.parse_atom()?;
        if self.peek() == Some(&Tok::Arrow) {
            self.at += 1;
            let rhs = self.parse_fun()?;
            return Ok(Type::Fun(Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    fn parse_atom(&mut self) -> Result<Type, AnnotationError> {
        let Some(tok) = self.toks.get(self.at).cloned() else {
            return Err(AnnotationError::Parse {
                why: "the annotation ended where a type was expected".into(),
            });
        };
        self.at += 1;
        match tok {
            Tok::Ident(name) => match name.as_str() {
                "Int" => Ok(Type::Int),
                "Bool" | "BOOLEAN" => Ok(Type::Bool),
                "Str" | "STRING" => Ok(Type::Str),
                "Set" => {
                    self.expect(&Tok::LParen, "after `Set`")?;
                    let e = self.parse_fun()?;
                    self.expect(&Tok::RParen, "after the element type")?;
                    Ok(Type::Set(Box::new(e)))
                }
                "Seq" => {
                    self.expect(&Tok::LParen, "after `Seq`")?;
                    let e = self.parse_fun()?;
                    self.expect(&Tok::RParen, "after the element type")?;
                    Ok(Type::Seq(Box::new(e)))
                }
                // Lowercase: a type variable. Variables are *parametric* –
                // two occurrences of `a` are the same `a` – which the
                // seeding side handles by interning them per name.
                other if other.chars().next().is_some_and(char::is_lowercase) => {
                    Ok(Type::Var(u32::MAX))
                }
                // A **tag arm** of a variant row (issue #17):
                // `RequestVote({ term: Int, from: Str })` – an uppercase
                // identifier applied to one type. The one-tag row it builds
                // is open until the `|` chain at the top level closes it.
                other
                    if self.peek() == Some(&Tok::LParen)
                        && other.chars().next().is_some_and(char::is_uppercase) =>
                {
                    self.at += 1;
                    let payload = self.parse_fun()?;
                    self.expect(&Tok::RParen, "after the tag's payload")?;
                    let mut tags = std::collections::BTreeMap::new();
                    tags.insert(name, payload);
                    Ok(Type::Variant { tags, open: false })
                }
                // Uppercase: an uninterpreted type, its own base. There is
                // no `Type` constructor for it, so it is carried as a
                // zero-field *open record is wrong* – see the seeding side:
                // the name is interned there.
                _ => Ok(Type::Uninterpreted(name)),
            },
            Tok::LAngle => {
                let mut parts = Vec::new();
                if self.peek() != Some(&Tok::RAngle) {
                    loop {
                        parts.push(self.parse_fun()?);
                        if self.peek() == Some(&Tok::Comma) {
                            self.at += 1;
                        } else {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RAngle, "to close the tuple")?;
                Ok(Type::Tuple(parts))
            }
            Tok::LBrace => {
                let mut fields = std::collections::BTreeMap::new();
                // A trailing **bare identifier** is a row variable:
                // `{ from: Str, term: Int, a }` names a record that has
                // these fields and maybe more – Apalache's annotation
                // spelling for an open row (Bug1682's `IsOk` writes it).
                let mut row_tail: Option<String> = None;
                while let Some(Tok::Ident(field)) = self.peek().cloned() {
                    self.at += 1;
                    if self.peek() == Some(&Tok::Colon) {
                        self.at += 1;
                        let ty = self.parse_fun()?;
                        fields.insert(field, ty);
                    } else {
                        // No `:` follows: the row variable, which must be
                        // last.
                        row_tail = Some(field);
                        break;
                    }
                    if self.peek() == Some(&Tok::Comma) {
                        self.at += 1;
                    } else {
                        break;
                    }
                }
                self.expect(&Tok::RBrace, "to close the record")?;
                Ok(Type::Rec {
                    fields,
                    open: row_tail.is_some(),
                })
            }
            Tok::LParen => {
                // `() => T` is an operator signature with no parameters, the
                // same refusal-by-name as `(a, b) => c` below it; a bare `()`
                // is not a type (Apalache's parser rejects it too).
                if self.peek() == Some(&Tok::RParen) {
                    self.at += 1;
                    if self.peek() == Some(&Tok::BigArrow) {
                        return Err(AnnotationError::Unsupported {
                            what: "an operator signature (`(a, b) => c`)",
                        });
                    }
                    return Err(AnnotationError::Parse {
                        why: "`()`: an empty parameter list belongs to an operator signature (`() => T`)".into(),
                    });
                }
                let mut inner = self.parse_fun()?;
                while self.peek() == Some(&Tok::Comma) {
                    // A parameter list: `(A, B) => C`. The parameters are
                    // parsed (so the message can quote the real shape) and
                    // the whole annotation is an operator signature.
                    self.at += 1;
                    inner = self.parse_fun()?;
                }
                if self.peek() == Some(&Tok::BigArrow) {
                    // An operator signature. This checker does not yet
                    // check operator instantiations against annotated
                    // signatures (the remaining piece of the annotations
                    // issue), so the *seeding* side skips it with a note
                    // rather than failing the spec – a wrong annotation on
                    // an operator body is caught by ordinary inference.
                    return Err(AnnotationError::Unsupported {
                        what: "an operator signature (`(a, b) => c`)",
                    });
                }
                self.expect(&Tok::RParen, "to close the group")?;
                Ok(inner)
            }
            other => Err(AnnotationError::Parse {
                why: format!("`{other:?}` where a type was expected"),
            }),
        }
    }

    fn expect(&mut self, t: &Tok, where_: &str) -> Result<(), AnnotationError> {
        if self.toks.get(self.at) == Some(t) {
            self.at += 1;
            Ok(())
        } else {
            Err(AnnotationError::Parse {
                why: format!("expected {t:?} {where_}"),
            })
        }
    }
}

/// Seed inference with one parsed annotation: unify `name`'s type with it.
///
/// Type variables are interned **per name within one annotation**, so
/// `(a, a) => a`-style polymorphism inside a single signature holds, while
/// different annotations do not accidentally share variables. Uninterpreted
/// types intern per name across the whole specification – one `T` is one
/// type and one opaque sort – through the `uninterpreted` table the caller
/// owns and passes in.
///
/// # Errors
///
/// The inference's own unification error on conflict: an annotation that
/// disagrees with what inference derives *is* the type error, reported as
/// such rather than silently overridden.
pub fn assume(
    inf: &mut Inference,
    name: &str,
    ty: &ParsedType,
    uninterpreted: &mut std::collections::HashMap<String, TyId>,
) -> crate::types::Result<()> {
    assume_with_aliases(inf, name, &ty.0, &[], uninterpreted)
}

/// [`assume`] with a `@typeAlias` table (issue #17): an uppercase name that
/// an alias defines resolves to the aliased type, so
/// `@typeAlias: M = R({x: Int});` followed by `@type: Set(M);` seeds the
/// variant row. Aliases resolve recursively, with a depth bound in place of
/// a cycle check – a self-referential alias is a defect in the
/// specification, reported as the parse error it effectively is.
pub fn assume_with_aliases(
    inf: &mut Inference,
    name: &str,
    ty: &Type,
    aliases: &[(String, ParsedType)],
    uninterpreted: &mut std::collections::HashMap<String, TyId>,
) -> crate::types::Result<()> {
    let resolved = resolve_aliases(ty, aliases, 0)?;
    let mut vars: std::collections::HashMap<String, TyId> = std::collections::HashMap::new();
    let tid = intern(inf, &resolved, &mut vars, uninterpreted)?;
    inf.assume(name, tid)
}

/// The alias a name refers to, if any: the name itself, or – with a `$`
/// sigil – the name without it.
fn find_alias<'a>(
    name: &str,
    aliases: &'a [(String, ParsedType)],
) -> Option<&'a (String, ParsedType)> {
    aliases.iter().find(|(k, _)| k == name).or_else(|| {
        name.strip_prefix('$')
            .and_then(|bare| aliases.iter().find(|(k, _)| k == bare))
    })
}

/// [`resolve_aliases`] over a signature: its parameters and its result,
/// each substituted throughout. A signature is checked against its
/// operator's body with its types interned directly, so an alias a
/// parameter names (`$transfer => TX`) has to be resolved before that, or
/// the check compares the body with an opaque `$transfer`.
///
/// # Errors
///
/// The inference's own error on an alias nest deeper than the bound.
pub fn resolve_signature_aliases(
    sig: ParsedSignature,
    aliases: &[(String, ParsedType)],
) -> crate::types::Result<ParsedSignature> {
    let mut params = Vec::with_capacity(sig.params.len());
    for p in &sig.params {
        params.push(resolve_aliases(p, aliases, 0)?);
    }
    let result = resolve_aliases(&sig.result, aliases, 0)?;
    Ok(ParsedSignature { params, result })
}

/// Substitute alias references throughout a type.
///
/// # Errors
///
/// The inference's own error on an alias nest deeper than the bound.
pub fn resolve_aliases(
    ty: &Type,
    aliases: &[(String, ParsedType)],
    depth: usize,
) -> crate::types::Result<Type> {
    use crate::types::TypeError;
    if depth > 8 {
        return Err(TypeError::ArenaFull { limit: 0 });
    }
    let r = |t: &Type| resolve_aliases(t, aliases, depth + 1);
    Ok(match ty {
        Type::Bool | Type::Int | Type::Str | Type::Var(_) => ty.clone(),
        // An uppercase name is an alias when one defines it (Apalache's
        // deprecated all-caps spelling, `@typeAlias: MESSAGE = ...` used as
        // `Set(MESSAGE)`), and a `$name` reference is the camelCase alias
        // `name`. A name no alias defines is a type constant, its own
        // uninterpreted base, sigil included: `$transfer` with no alias is
        // `$transfer`, apart from `transfer` the type variable.
        Type::Uninterpreted(n) => match find_alias(n, aliases) {
            Some((_, parsed)) => r(&parsed.0)?,
            None => ty.clone(),
        },
        Type::Set(e) => Type::Set(Box::new(r(e)?)),
        Type::Seq(e) => Type::Seq(Box::new(r(e)?)),
        Type::Fun(a, b) => Type::Fun(Box::new(r(a)?), Box::new(r(b)?)),
        Type::Tuple(xs) => Type::Tuple(xs.iter().map(r).collect::<crate::types::Result<_>>()?),
        Type::Rec { fields, open } => {
            let mut out = std::collections::BTreeMap::new();
            for (k, v) in fields {
                out.insert(k.clone(), r(v)?);
            }
            Type::Rec {
                fields: out,
                open: *open,
            }
        }
        Type::Variant { tags, open } => {
            let mut out = std::collections::BTreeMap::new();
            for (k, v) in tags {
                out.insert(k.clone(), r(v)?);
            }
            Type::Variant {
                tags: out,
                open: *open,
            }
        }
    })
}

/// Intern one parsed type for the signature check – the same interning
/// [`assume`] does, exposed for a caller that checks an operator's *body*
/// against a signature rather than seeding a name.
///
/// # Errors
/// The inference's own error, on an arena or arity failure.
pub fn intern_for_check(
    inf: &mut Inference,
    ty: &Type,
    vars: &mut std::collections::HashMap<String, TyId>,
    uninterpreted: &mut std::collections::HashMap<String, TyId>,
) -> Result<TyId, TypeError> {
    intern(inf, ty, vars, uninterpreted)
}

/// Intern a parsed type into the inference, with per-name variable interning.
fn intern(
    inf: &mut Inference,
    ty: &Type,
    vars: &mut std::collections::HashMap<String, TyId>,
    uninterpreted: &mut std::collections::HashMap<String, TyId>,
) -> Result<TyId, TypeError> {
    let out: TyId = match ty {
        Type::Bool => inf.bool_ty()?,
        Type::Int => inf.int_ty()?,
        Type::Str => inf.str_ty()?,
        Type::Set(e) => {
            let id = intern(inf, e, vars, uninterpreted)?;
            inf.mk(Ty::Set(id))?
        }
        Type::Seq(e) => {
            let id = intern(inf, e, vars, uninterpreted)?;
            inf.mk(Ty::Seq(id))?
        }
        Type::Fun(a, b) => {
            let d = intern(inf, a, vars, uninterpreted)?;
            let r = intern(inf, b, vars, uninterpreted)?;
            inf.mk(Ty::Fun(d, r))?
        }
        Type::Tuple(parts) => {
            let mut ids = Vec::with_capacity(parts.len());
            for p in parts {
                ids.push(intern(inf, p, vars, uninterpreted)?);
            }
            inf.mk(Ty::Tuple(ids))?
        }
        Type::Rec { fields, .. } => {
            let mut ids = std::collections::BTreeMap::new();
            for (f, t) in fields {
                ids.insert(f.clone(), intern(inf, t, vars, uninterpreted)?);
            }
            // An annotation's record is closed: it is the author's claim
            // about exactly these fields.
            inf.mk(Ty::Rec {
                fields: ids,
                tail: None,
            })?
        }
        Type::Variant { tags, .. } => {
            let mut ids = std::collections::BTreeMap::new();
            for (t, p) in tags {
                ids.insert(t.clone(), intern(inf, p, vars, uninterpreted)?);
            }
            // An annotation's variant row is closed: exactly these tags,
            // the author's claim, the same rule a record annotation follows.
            inf.mk(Ty::Variant {
                tags: ids,
                tail: None,
            })?
        }
        // A type variable: one slot per name within the annotation – the
        // name itself is erased, which is what "parametric within one
        // signature" means.
        Type::Var(_) => {
            let key = "?".to_string();
            if let Some(&id) = vars.get(&key) {
                id
            } else {
                let id = inf.fresh()?;
                vars.insert(key, id);
                id
            }
        }
        Type::Uninterpreted(name) => {
            // An uninterpreted base type: a never-unified inference variable
            // is exactly that – its own opaque sort, distinct from Int and
            // Str – interned per NAME so one `T` is one type everywhere in
            // the specification.
            if let Some(&id) = uninterpreted.get(name) {
                id
            } else {
                let id = inf.fresh()?;
                uninterpreted.insert(name.clone(), id);
                id
            }
        }
    };
    Ok(out)
}
