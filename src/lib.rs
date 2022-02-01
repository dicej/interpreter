use {
    anyhow::{anyhow, Result},
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

#[derive(Clone, Copy, Debug)]
enum Integer {
    Unknown,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

#[derive(Clone, Copy, Debug)]
enum Float {
    F32,
    F64,
}

#[derive(Clone, Copy, Debug)]
struct Identifier(usize);

#[derive(Clone, Copy, Debug)]
struct Lifetime(Identifier);

#[derive(Clone, Debug)]
struct Trait(Identifier, Rc<[Type]>, Rc<[Lifetime]>);

// enum Bound {
//     Lifetime { long: Lifetime, short: Lifetime },
//     Trait(Type, Trait),
// }

#[derive(Clone, Debug)]
enum Type {
    Never,
    Unit,
    Boolean,
    Character,
    Integer(Integer),
    Float(Float),
    Array(Rc<Type>),
    Tuple(Rc<[Type]>),
    Pointer(Rc<Type>),
    Reference(Rc<Type>, Lifetime),
    Slice(Rc<Type>, Lifetime),
    Str(Lifetime),
    Function {
        parameters: Rc<[Type]>,
        ret: Rc<Type>,
    },
    Nominal(Identifier, Rc<[Type]>, Rc<[Lifetime]>),
}

#[derive(Clone)]
struct Literal {
    value: Rc<dyn Any>,
    r#type: Type,
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.r#type {
            Type::Integer(integer) => match integer {
                Integer::Unknown => write!(f, "{}", self.value.downcast_ref::<String>()),
                Integer::U8 => write!(f, "{}_u8", self.value.downcast_ref::<u8>()),
                Integer::U16 => write!(f, "{}_u16", self.value.downcast_ref::<u16>()),
                Integer::U32 => write!(f, "{}_u32", self.value.downcast_ref::<u32>()),
                Integer::U64 => write!(f, "{}_u64", self.value.downcast_ref::<u64>()),
                Integer::U128 => write!(f, "{}_u128", self.value.downcast_ref::<u128>()),
                Integer::Usize => write!(f, "{}_usize", self.value.downcast_ref::<usize>()),
                Integer::I8 => write!(f, "{}_i8", self.value.downcast_ref::<i8>()),
                Integer::I16 => write!(f, "{}_i16", self.value.downcast_ref::<i16>()),
                Integer::I32 => write!(f, "{}_i32", self.value.downcast_ref::<i32>()),
                Integer::I64 => write!(f, "{}_i64", self.value.downcast_ref::<i64>()),
                Integer::I128 => write!(f, "{}_i128", self.value.downcast_ref::<i128>()),
                Integer::Isize => write!(f, "{}_isize", self.value.downcast_ref::<isize>()),
            },

            Type::Boolean => write!(f, "{}", self.value.downcast_ref::<bool>()),

            _ => write!(f, "TODO: Debug for {}", self.r#type),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum UnaryOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, Debug)]
enum BinaryOp {
    And,
    Or,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Clone, Debug)]
struct Abstraction {
    // TODO: what about type parameters?  Or will this always be monomorphized?  If the latter, we may want to
    // reference the polymorphic version, if any.
    parameters: Rc<[(Identifier, Type)]>,
    r#return: Type,
    body: Rc<TypedTerm>,
}

#[derive(Clone, Debug)]
enum TypedTerm {
    Block(Rc<[TypedTerm]>),
    Literal(Literal),
    Parameter {
        index: usize,
        r#type: Type,
    },
    Application {
        abstraction: Abstraction,
        arguments: Rc<[TypedTerm]>,
    },
    Abstraction(Abstraction),
    And(Rc<TypedTerm>, Rc<TypedTerm>),
    Or(Rc<TypedTerm>, Rc<TypedTerm>),
    UnaryOp(UnaryOp, Rc<TypedTerm>),
    BinaryOp(BinaryOp, Rc<TypedTerm>, Rc<TypedTerm>),
    If {
        predicate: TypedTerm,
        then: Rc<TypedTerm>,
        r#else: Rc<TypedTerm>,
    },
    Loop {
        label: Option<Identifier>,
        body: Rc<TypedTerm>,
    },
    Continue(Option<Identifier>),
    Break {
        label: Option<Identifier>,
        term: Rc<TypedTerm>,
    },
    Return {
        term: Rc<TypedTerm>,
    },
    Cast {
        term: Rc<TypedTerm>,
        r#type: Type,
    },
}

impl TypedTerm {
    fn r#type(&self) -> Type {
        match self {
            Self::Block(terms) => terms.last().map(|term| term.r#type()).unwrap_or(Type::Unit),
            Self::Literal(literal) => literal.r#type,
            // TODO: the return type of an abstraction may be a function of its type parameters
            Self::Application {
                abstraction: Abstraction { ret, .. },
                ..
            } => r#return,
            Self::And { .. } | Self::Or { .. } => Type::Boolean,
            Self::If { then, .. } => then.r#type(),
            _ => todo!(),
        }
    }
}

#[derive(Clone, Debug)]
enum Term {
    Block(Rc<[Term]>),
    Literal(Literal),
    Variable(Identifier),
    Application {
        abstraction: Rc<Term>,
        arguments: Rc<[Term]>,
    },
    Abstraction {
        // TODO: what about type parameters?
        parameters: Rc<[Type]>,
        r#return: Type,
        body: Rc<Term>,
    },
    UnaryOp {
        op: UnaryOp,
        term: Rc<Term>,
    },
    BinaryOp {
        op: BinaryOp,
        left: Rc<Term>,
        right: Rc<Term>,
    },
    If {
        predicate: Term,
        then: Rc<Term>,
        r#else: Rc<Term>,
    },
    Loop {
        label: Option<Identifier>,
        body: Rc<Term>,
    },
    Continue(Option<Identifier>),
    Break {
        label: Option<Identifier>,
        term: Rc<Term>,
    },
    Return {
        term: Rc<Term>,
    },
    Cast {
        term: Rc<Term>,
        r#type: Type,
    },
}

#[derive(Clone, Debug)]
struct TypedTerm {
    term: Term,
    r#type: Type,
}

#[derive(Default)]
struct Scope {
    terms: HashMap<Identifier, Option<Term>>,
}

pub struct Env {
    ids_to_names: Vec<Rc<str>>,
    names_to_ids: HashMap<Rc<str>, usize>,
    scopes: Vec<Scope>,
    parameters: Vec<Literal>,
}

impl Env {
    fn inner_scope(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }
}

pub struct Eval {
    value: Option<Literal>,
    new_term_bindings: HashMap<Rc<str>, Option<Term>>,
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

        // TODO: convert stmt to a term (if it's an expression), then typecheck it, then lower it to something
        // MIR-like, then borrow-check it, then evaluate it.
        //
        // If it's not an expression (i.e. it's an item), update the relevant symbol tables.  If it's an item with
        // code inside (e.g. an impl block or fn) do all of the above except evaluation.

        let mut new_term_bindings = HashSet::new();

        let value = self.eval_term(
            &self.type_check(&self.stmt_to_term(&stmt, &mut new_term_bindings)?, None)?,
        )?;

        Ok(Eval {
            value: Some(value),
            new_term_bindings: new_term_bindings
                .into_iter()
                .filter_map(|id| {
                    self.find_term(id)
                        .map(|term| (self.unintern(id).clone(), term))
                })
                .collect()?,
        })
    }

    fn eval_term(&mut self, term: &TypedTerm) -> Result<Literal> {
        match term {
            TypedTerm::Literal(literal) => literal.clone(),

            TypedTerm::Application {
                abstraction: Abstraction { body, .. },
                arguments,
            } => {
                let mut parameters = arguments
                    .iter()
                    .map(|term| self.eval_term(term)?)
                    .collect::<Result<_>>()?;

                mem::swap(&mut self.parameters, &mut parameters);

                let result = self.eval_term(body);

                mem::swap(&mut self.parameters, &mut parameters);

                result
            }

            TypedTerm::And(left, right) => {
                if *self.eval_term(left)?.value.downcast_ref::<bool>() {
                    self.eval_term(right)
                } else {
                    Ok(Literal {
                        value: Rc::new(false),
                        r#type: Type::Boolean,
                    })
                }
            }

            TypedTerm::Or(left, right) => {
                if !*self.eval_term(left)?.value.downcast_ref::<bool>() {
                    self.eval_term(right)
                } else {
                    Ok(Literal {
                        value: Rc::new(true),
                        r#type: Type::Boolean,
                    })
                }
            }

            _ => Err(anyhow!("evaluation not yet supported for term {term:?}")),
        }
    }

    fn type_check(&mut self, term: &Term, expected_type: Option<&Type>) -> Result<TypedTerm> {
        match term {
            Term::Literal(Literal { value, r#type }) => {
                let literal = if let Type::Integer(Integer::Unknown) = r#type {
                    match expected_type
                        .cloned()
                        .unwrap_or(Type::Integer(Integer::I32))
                    {
                        Type::Integer(integer_type) => Literal {
                            value: Rc::new(Integer::parse(
                                value.downcast_ref::<String>().unwrap(),
                            )?),
                            r#type: Type::Integer(integer_type),
                        },

                        _ => Literal {
                            value: Rc::new(value.downcast_ref::<String>().unwrap().parse::<I32>()?),
                            r#type: Type::Integer(Integer::I32),
                        },
                    }
                };

                Ok(TypedTerm {
                    term: Term::Literal(literal),
                    r#type: literal.r#type,
                })
            }

            Term::UnaryOp { op, term } => {
                let term = self.type_check(&term, expected_type)?;

                let (r#trait, function) = match op {
                    UnaryOp::Neg => (self.traits.neg, self.names.neg),
                    UnaryOp::Not => (self.traits.not, self.names.not),
                };

                let r#impl = self.get_impl(term.r#type(), r#trait).unwrap_or_else(|| {
                    anyhow!("type {r#type} is not compatible with unary operator {op}")
                })?;

                let r#type = term.r#type();

                Ok(match (op, r#type) {
                    (UnaryOp::Neg, Type::Integer(_)) | (UnaryOp::Not, Type::Boolean) => {
                        TypedTerm::UnaryOp(op, term)
                    }
                    _ => TypedTerm::Application {
                        abstraction: self.get_associated_function(r#impl, function),
                        arguments: Rc::new([term]),
                    },
                })
            }

            Term::BinaryOp { op, left, right } => {
                let left = self.type_check(&left, expected_type)?;

                let (expected_type, r#impl) = match op {
                    BinaryOp::And | BinaryOp::Or => (Type::Boolean, None),
                    _ => {
                        let r#impl = self
                            .get_impl(
                                r#type,
                                match op {
                                    BinaryOp::Add => self.traits.add,
                                    BinaryOp::Sub => self.traits.sub,
                                    BinaryOp::Mul => self.traits.mul,
                                    BinaryOp::Div => self.traits.div,
                                    BinaryOp::Rem => self.traits.rem,
                                    _ => unreachable!(),
                                },
                            )
                            .unwrap_or_else(|| {
                                anyhow!("type {r#type} is not compatible with binary operator {op}")
                            })?;

                        (self.get_argument_type(r#impl, 0).unwrap(), Some(r#impl))
                    }
                };

                let right = self.type_check(&right, Some(&expected_type))?;

                if expected_type != right.r#type() {
                    Err(anyhow!("expected {expected_type}, got {right_type}"))
                } else {
                    let r#type = left.r#type();

                    Ok(match (op, r#type) {
                        (BinaryOp::And, _) => TypedTerm::And(Rc::new(left), Rc::new(right)),

                        (BinaryOp::Or, _) => TypedTerm::Or(Rc::new(left), Rc::new(right)),

                        (BinaryOp::Add, Type::Integer(_))
                        | (BinaryOp::Sub, Type::Integer(_))
                        | (BinaryOp::Mul, Type::Integer(_))
                        | (BinaryOp::Div, Type::Integer(_))
                        | (BinaryOp::Rem, Type::Integer(_)) => {
                            TypedTerm::BinaryOp(op, Rc::new(left), Rc::new(right))
                        }

                        _ => TypedTerm::Application {
                            abstraction: self.get_associated_function(r#impl.unwrap(), function),
                            arguments: Rc::new([left, right]),
                        },
                    })
                }
            }

            Term::Variable(identifier) => match self.inner_scope().terms.get(identifier) {
                Some(Some(term)) => self.type_check(term, expected_type),

                // TODO: will need to do some control/data flow analysis to support uninitialized lets
                Some(None) => Err(anyhow!(
                    "use of uninitialized symbol: {}",
                    self.unintern(identifier)
                )),

                None => Err(anyhow!("symbol not found: {}", self.unintern(identifier))),
            },

            _ => Err(anyhow!("type checking not yet supported for term {term:?}")),
        }
    }

    fn stmt_to_term(
        &mut self,
        stmt: &Stmt,
        new_term_bindings: &mut HashSet<Indentifier>,
    ) -> Result<Term> {
        match stmt {
            Stmt::Local(Local {
                pat, init, attrs, ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"));
                } else {
                    match pat {
                        Pat::Ident(PatIdent {
                            ident,
                            by_ref,
                            mutability,
                            ..
                        }) => {
                            if by_ref.is_some() {
                                Err(anyhow!("ref patterns not yet supported"));
                            } else if mutability.is_some() {
                                Err(anyhow!("mut patterns not yet supported"));
                            } else {
                                self.scopes.push(Scope::default());

                                let identifier = self.intern(&ident.to_string());

                                new_term_bindings.insert(identifier);

                                let value = init
                                    .as_ref()
                                    .map(|(_, expr)| self.expr_to_term(expr))
                                    .transpose()?;

                                self.inner_scope().insert(identifier, value);

                                Ok(Term::Literal(Literal {
                                    value: Rc::new(()),
                                    r#type: Type::Unit,
                                }))
                            }
                        }

                        _ => Err(anyhow!("pattern not yet supported: {pat:?}")),
                    }
                }
            }

            Stmt::Semi(expr, _) => self.expr_to_term(expr)?,

            _ => Err(anyhow!("stmt not yet supported: {stmt:?}")),
        }
    }

    fn expr_to_term(&mut self, expr: &Expr) -> Result<Term> {
        match expr {
            Expr::Lit(ExprLit { lit, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    match lit {
                        Lit::Int(lit) => match lit.suffix() {
                            "" => Ok(Term::Literal {
                                value: Rc::new(lit.base10_digits().to_owned()),
                                r#type: Type::Integer(Integer::Unknown),
                            }),

                            "u8" => Ok(Term::Literal {
                                value: Rc::new(lit.base10_digits().parse::<u8>()?),
                                r#type: Type::Integer(Integer::U8),
                            }),

                            "u16" => Ok(Term::Literal {
                                value: Rc::new(lit.base10_digits().parse::<u16>()?),
                                r#type: Type::Integer(Integer::U16),
                            }),

                            "u32" => Ok(Term::Literal {
                                value: Rc::new(lit.base10_digits().parse::<u32>()?),
                                r#type: Type::Integer(Integer::U32),
                            }),

                            "u64" => Ok(Term::Literal {
                                value: Rc::new(lit.base10_digits().parse::<u64>()?),
                                r#type: Type::Integer(Integer::U64),
                            }),

                            "u128" => Ok(Term::Literal {
                                value: Rc::new(lit.base10_digits().parse::<u128>()?),
                                r#type: Type::Integer(Integer::U128),
                            }),

                            _ => Err(anyhow!(
                                "unexpected integer literal suffix: {}",
                                lit.suffix()
                            )),
                        },

                        Lit::Bool(LitBool { value, .. }) => Ok(Term::Literal {
                            value: Rc::new(*value),
                            r#type: Type::Boolean,
                        }),

                        _ => Err(anyhow!("literal not yet supported: {lit:?}")),
                    }
                }
            }

            Expr::Unary(ExprUnary { op, expr, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    let term = self.expr_to_term(expr)?;

                    Ok(Term::UnaryOp {
                        op: match op {
                            UnOp::Neg(_) => UnaryOp::Neg,
                            UnOp::Not(_) => UnaryOp::Not,
                            _ => return Err(anyhow!("operation not yet supported: {op:?}")),
                        },
                        term,
                    })
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
                    let left = self.expr_to_term(left)?;
                    let right = self.expr_to_term(right)?;

                    Ok(Term::BinaryOp {
                        op: match op {
                            BinOp::And(_) => BinaryOp::And,
                            BinOp::Or(_) => BinaryOp::Or,
                            BinOp::Add(_) => BinaryOp::Add,
                            BinOp::Sub(_) => BinaryOp::Sub,
                            BinOp::Mul(_) => BinaryOp::Mul,
                            BinOp::Div(_) => BinaryOp::Div,
                            BinOp::Rem(_) => BinaryOp::Rem,
                            _ => return Err(anyhow!("operation not yet supported: {op:?}")),
                        },
                        left,
                        right,
                    })
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
                        Ok(Term::Variable(self.intern(ident.to_string())?))
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

    pub fn eval_file(&mut self, _file: &str) -> Result<Eval> {
        todo!()
    }
}
