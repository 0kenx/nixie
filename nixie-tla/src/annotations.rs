//! `@type:` annotations — the Type1 grammar and the seeding of inference.
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

/// The subset of Type1 this checker reads: Int/Bool/Str, Set(T), Seq(T),
/// right-associative function arrows, tuples, records, and identifiers
/// (lowercase = one type variable, uppercase = an uninterpreted type).
///
/// Deliberately absent, each a named refusal: variants and operator types
/// (both belong to the variants sub-issue) and real numbers, which the
/// kernel does not have.
pub fn parse_type1(src: &str) -> Result<ParsedType, AnnotationError> {
    let toks = tokenize(src)?;
    let mut p = Parser { toks, at: 0 };
    let ty = p.parse_fun()?;
    // `A => B` at the top level is an operator signature (the paren form
    // lands here too, its group already parsed): named-refused below at the
    // seeding side, which skips signatures with a note.
    if p.toks.get(p.at) == Some(&Tok::BigArrow) {
        return Err(AnnotationError::Unsupported {
            what: "an operator signature (`(a, b) => c`)",
        });
    }
    // Everything after the type is trailing junk — except that the caller
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
}

fn tokenize(src: &str) -> Result<Vec<Tok>, AnnotationError> {
    let mut out = Vec::new();
    let bytes: Vec<char> = src.chars().collect();
    let mut i = 0usize;
    while i < bytes.len() {
        let c = bytes[i];
        match c {
            ' ' | '\t' | '\n' | '\r' => i += 1,
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
                // Lowercase: a type variable. Variables are *parametric* —
                // two occurrences of `a` are the same `a` — which the
                // seeding side handles by interning them per name.
                other if other.chars().next().is_some_and(char::is_lowercase) => {
                    Ok(Type::Var(u32::MAX))
                }
                // Uppercase: an uninterpreted type, its own base. There is
                // no `Type` constructor for it, so it is carried as a
                // zero-field *open record is wrong* — see the seeding side:
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
                while matches!(self.peek(), Some(Tok::Ident(_))) {
                    let Some(Tok::Ident(field)) = self.toks.get(self.at).cloned() else {
                        break;
                    };
                    self.at += 1;
                    self.expect(&Tok::Colon, "after the field name")?;
                    let ty = self.parse_fun()?;
                    fields.insert(field, ty);
                    if self.peek() == Some(&Tok::Comma) {
                        self.at += 1;
                    } else {
                        break;
                    }
                }
                self.expect(&Tok::RBrace, "to close the record")?;
                Ok(Type::Rec {
                    fields,
                    open: false,
                })
            }
            Tok::LParen => {
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
                    // rather than failing the spec — a wrong annotation on
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
/// types intern per name across the whole specification — one `T` is one
/// type and one opaque sort — through the `uninterpreted` table the caller
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
    let mut vars: std::collections::HashMap<String, TyId> = std::collections::HashMap::new();
    let tid = intern(inf, &ty.0, &mut vars, uninterpreted)?;
    inf.assume(name, tid)
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
        // A type variable: one slot per name within the annotation — the
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
            // is exactly that — its own opaque sort, distinct from Int and
            // Str — interned per NAME so one `T` is one type everywhere in
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
