use {
    anyhow::{anyhow, Context, Result},
    std::{collections::HashMap, fmt},
    syn::{Expr, ExprLit, Lit, Local, Pat, PatIdent, Stmt},
};

#[derive(Copy, Clone)]
enum Type {
    Integer,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Integer => write!(f, "{{integer}}"),
        }
    }
}

#[derive(Clone)]
enum Value {
    Literal(String),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Literal(literal) => write!(f, "{literal}"),
        }
    }
}

#[derive(Clone)]
struct Term {
    ty: Type,
    value: Value,
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
            write!(f, " => {} as {}", term.value, term.ty)?;
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
                write!(f, ": {} = {}", term.ty, term.value)?;
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

        self.eval_stmt(&stmt).with_context(|| format!("{stmt:#?}"))
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
                        Lit::Int(lit) => Ok(Term {
                            ty: Type::Integer,
                            value: Value::Literal(lit.base10_digits().to_owned()),
                        }),

                        _ => Err(anyhow!("pattern not yet supported: {lit:?}")),
                    }
                }
            }

            _ => Err(anyhow!("expr not yet supported: {expr:?}")),
        }
    }

    pub fn eval_file(&mut self, _file: &str) -> Result<Eval> {
        todo!()
    }
}
