use {
    anyhow::{anyhow, Result},
    num_bigint::BigInt,
    num_traits::Num,
    std::{
        collections::HashMap,
        fmt,
        ops::{Add, Div, Rem, Sub},
    },
    syn::{
        BinOp, Expr, ExprBinary, ExprLit, ExprPath, ExprUnary, Lit, LitBool, Local, Pat, PatIdent,
        Path, PathArguments, PathSegment, Stmt, UnOp,
    },
};

#[derive(Clone, Debug)]
enum Integer {
    Any(BigInt),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
}

macro_rules! integer_binop {
    ($op:ident, $left:ident, $right:ident) => {
        match ($left, $right) {
            (Integer::Any($left), Integer::Any($right)) => Integer::Any($left.$op($right)),
            (Integer::U8($left), Integer::U8($right)) => Integer::U8($left.$op($right)),
            (Integer::U16($left), Integer::U16($right)) => Integer::U16($left.$op($right)),
            (Integer::U32($left), Integer::U32($right)) => Integer::U32($left.$op($right)),
            (Integer::U64($left), Integer::U64($right)) => Integer::U64($left.$op($right)),
            (Integer::U128($left), Integer::U128($right)) => Integer::U128($left.$op($right)),
            (Integer::I8($left), Integer::I8($right)) => Integer::I8($left.$op($right)),
            (Integer::I16($left), Integer::I16($right)) => Integer::I16($left.$op($right)),
            (Integer::I32($left), Integer::I32($right)) => Integer::I32($left.$op($right)),
            (Integer::I64($left), Integer::I64($right)) => Integer::I64($left.$op($right)),
            (Integer::I128($left), Integer::I128($right)) => Integer::I128($left.$op($right)),

            _ => {
                return Err(anyhow!(
                    "mismatched integer types for {} operation",
                    stringify!($op)
                ))
            }
        }
    };
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Any(value) => write!(f, "{value}"),
            Self::U8(value) => write!(f, "{value}"),
            Self::U16(value) => write!(f, "{value}"),
            Self::U32(value) => write!(f, "{value}"),
            Self::U64(value) => write!(f, "{value}"),
            Self::U128(value) => write!(f, "{value}"),
            Self::I8(value) => write!(f, "{value}"),
            Self::I16(value) => write!(f, "{value}"),
            Self::I32(value) => write!(f, "{value}"),
            Self::I64(value) => write!(f, "{value}"),
            Self::I128(value) => write!(f, "{value}"),
        }
    }
}

#[derive(Clone, Debug)]
enum Term {
    Integer(Integer),
    Boolean(bool),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Integer(value) => write!(f, "{value}"),
            Self::Boolean(value) => write!(f, "{value}"),
        }
    }
}

#[derive(Default)]
struct Scope {
    terms: HashMap<String, Option<Term>>,
}

pub struct Env {
    scopes: Vec<Scope>,
}

impl Env {
    fn inner_scope(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }
}

pub struct Eval {
    term: Option<Term>,
    new_term_bindings: HashMap<String, Option<Term>>,
}

impl fmt::Display for Eval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut need_newline = if let Some(term) = &self.term {
            write!(f, "{term}")?;
            true
        } else {
            false
        };

        for (symbol, term) in &self.new_term_bindings {
            if need_newline {
                write!(f, "\n")?;
            }

            write!(f, "{symbol}")?;

            if let Some(term) = term {
                write!(f, " = {term}")?;
            }

            need_newline = true;
        }

        Ok(())
    }
}

impl Env {
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::default()],
        }
    }

    pub fn eval_line(&mut self, line: &str) -> Result<Eval> {
        let stmt = syn::parse_str::<Stmt>(line)
            .or_else(|_| syn::parse_str::<Stmt>(&format!("{line};")))
            .or_else(|_| syn::parse_str::<Expr>(line).map(Stmt::Expr))?;

        println!("{stmt:#?}");

        self.eval_stmt(&stmt)
    }

    fn eval_stmt(&mut self, stmt: &Stmt) -> Result<Eval> {
        let mut result = Eval {
            term: None,
            new_term_bindings: HashMap::new(),
        };

        match stmt {
            Stmt::Local(Local {
                pat, init, attrs, ..
            }) => {
                if !attrs.is_empty() {
                    return Err(anyhow!("attributes not yet supported"));
                } else {
                    match pat {
                        Pat::Ident(PatIdent {
                            ident,
                            by_ref,
                            mutability,
                            ..
                        }) => {
                            if by_ref.is_some() {
                                return Err(anyhow!("ref patterns not yet supported"));
                            } else if mutability.is_some() {
                                return Err(anyhow!("mut patterns not yet supported"));
                            } else {
                                let symbol = ident.to_string();
                                let term = init
                                    .as_ref()
                                    .map(|(_, expr)| self.eval_expr(expr))
                                    .transpose()?;

                                result
                                    .new_term_bindings
                                    .insert(symbol.clone(), term.clone());

                                self.inner_scope().terms.insert(symbol, term);
                            }
                        }

                        _ => return Err(anyhow!("pattern not yet supported: {pat:?}")),
                    }
                }
            }

            Stmt::Semi(expr, _) => result.term = Some(self.eval_expr(expr)?),

            _ => return Err(anyhow!("stmt not yet supported: {stmt:?}")),
        }

        Ok(result)
    }

    fn eval_expr(&mut self, expr: &Expr) -> Result<Term> {
        match expr {
            Expr::Lit(ExprLit { lit, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    match lit {
                        Lit::Int(lit) => Ok(Term::Integer(match lit.suffix() {
                            "" => Integer::Any(BigInt::from_str_radix(lit.base10_digits(), 10)?),

                            _ => {
                                return Err(anyhow!(
                                    "unexpected integer literal suffix: {}",
                                    lit.suffix()
                                ))
                            }
                        })),

                        Lit::Bool(LitBool { value, .. }) => Ok(Term::Boolean(*value)),

                        _ => Err(anyhow!("literal not yet supported: {lit:?}")),
                    }
                }
            }

            Expr::Unary(ExprUnary { op, expr, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    let term = self.eval_expr(expr)?;

                    match (op, &term) {
                        (UnOp::Neg(_), Term::Integer(value)) => Ok(Term::Integer(match value {
                            Integer::Any(value) => Integer::Any(-value),
                            Integer::I8(value) => Integer::I8(-value),
                            Integer::I16(value) => Integer::I16(-value),
                            Integer::I32(value) => Integer::I32(-value),
                            Integer::I64(value) => Integer::I64(-value),
                            Integer::I128(value) => Integer::I128(-value),

                            _ => {
                                return Err(anyhow!(
                                    "operation {op:?} not supported for term {}",
                                    term
                                ))
                            }
                        })),
                        (UnOp::Not(_), Term::Boolean(value)) => Ok(Term::Boolean(!value)),

                        (UnOp::Deref(_), _) => Err(anyhow!("operation not yet supported: {op:?}")),

                        (op, term) => {
                            Err(anyhow!("operation {op:?} not supported for term {}", term))
                        }
                    }
                }
            }

            Expr::Binary(ExprBinary {
                op,
                left,
                right,
                attrs,
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    let left = self.eval_expr(left)?;

                    match (op, &left) {
                        (BinOp::And(_), Term::Boolean(left)) => {
                            return if *left {
                                match self.eval_expr(right)? {
                                    Term::Boolean(value) => Ok(Term::Boolean(value)),
                                    right => Err(anyhow!("expected boolean, got: {right:?}")),
                                }
                            } else {
                                Ok(Term::Boolean(false))
                            }
                        }

                        (BinOp::Or(_), Term::Boolean(left)) => {
                            return if !left {
                                match self.eval_expr(right)? {
                                    Term::Boolean(value) => Ok(Term::Boolean(value)),
                                    right => Err(anyhow!("expected boolean, got: {right:?}")),
                                }
                            } else {
                                Ok(Term::Boolean(true))
                            }
                        }

                        _ => (),
                    }

                    let right = self.eval_expr(right)?;

                    match (op, left, right) {
                        (BinOp::Add(_), Term::Integer(left), Term::Integer(right)) => {
                            Ok(Term::Integer(integer_binop!(add, left, right)))
                        }

                        (BinOp::Sub(_), Term::Integer(left), Term::Integer(right)) => {
                            Ok(Term::Integer(integer_binop!(sub, left, right)))
                        }

                        (BinOp::Mul(_), Term::Integer(left), Term::Integer(right)) => {
                            Ok(Term::Integer(integer_binop!(div, left, right)))
                        }

                        (BinOp::Rem(_), Term::Integer(left), Term::Integer(right)) => {
                            Ok(Term::Integer(integer_binop!(rem, left, right)))
                        }

                        _ => Err(anyhow!("operation not yet supported: {op:?}")),
                    }
                }
            }

            Expr::Path(ExprPath {
                path:
                    Path {
                        leading_colon,
                        segments,
                    },
                qself,
                attrs,
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if qself.is_some() {
                    Err(anyhow!("qualified paths not yet supported"))
                } else if leading_colon.is_some() {
                    Err(anyhow!("absolute paths not yet supported"))
                } else if segments.len() != 1 {
                    Err(anyhow!("qualified paths not yet supported"))
                } else if let Some(PathSegment { ident, arguments }) = segments.last() {
                    if let PathArguments::None = arguments {
                        let ident = ident.to_string();

                        if let Some(term) = self.find_term(&ident) {
                            if let Some(term) = term {
                                Ok(term.clone())
                            } else {
                                Err(anyhow!("use of uninitialized variable: {ident}"))
                            }
                        } else {
                            Err(anyhow!("symbol not found: {ident}"))
                        }
                    } else {
                        Err(anyhow!("path arguments not yet supported"))
                    }
                } else {
                    Err(anyhow!("unexpected empty path"))
                }
            }

            _ => Err(anyhow!("expr not yet supported: {expr:?}")),
        }
    }

    fn find_term(&self, symbol: &str) -> Option<Option<&Term>> {
        for scope in &self.scopes {
            if let Some(term) = scope.terms.get(symbol) {
                return Some(term.as_ref());
            }
        }

        None
    }

    pub fn eval_file(&mut self, _file: &str) -> Result<Eval> {
        todo!()
    }
}
