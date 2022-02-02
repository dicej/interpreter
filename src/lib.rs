use {
    anyhow::{anyhow, Result},
    maplit::hashmap,
    std::{
        any::Any,
        collections::{HashMap, HashSet},
        fmt, mem,
        ops::{Add, Div, Mul, Rem, Sub},
        rc::Rc,
    },
    syn::{
        BinOp, Block, Expr, ExprBinary, ExprBlock, ExprIf, ExprLit, ExprParen, ExprPath, ExprUnary,
        Lit, LitBool, Local, Pat, PatIdent, Path, PathArguments, PathSegment, Stmt, UnOp,
    },
};

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug)]
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

impl Integer {
    fn parse(self, value: &str) -> Result<Rc<dyn Any>> {
        Ok(match self {
            Integer::Unknown => unreachable!(),
            Integer::U8 => Rc::new(value.parse::<u8>()?),
            Integer::U16 => Rc::new(value.parse::<u16>()?),
            Integer::U32 => Rc::new(value.parse::<u32>()?),
            Integer::U64 => Rc::new(value.parse::<u64>()?),
            Integer::U128 => Rc::new(value.parse::<u128>()?),
            Integer::Usize => Rc::new(value.parse::<usize>()?),
            Integer::I8 => Rc::new(value.parse::<i8>()?),
            Integer::I16 => Rc::new(value.parse::<i16>()?),
            Integer::I32 => Rc::new(value.parse::<i32>()?),
            Integer::I64 => Rc::new(value.parse::<i64>()?),
            Integer::I128 => Rc::new(value.parse::<i128>()?),
            Integer::Isize => Rc::new(value.parse::<isize>()?),
        })
    }
}

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug)]
enum Float {
    F32,
    F64,
}

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug)]
struct Identifier(usize);

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug)]
struct Lifetime(Identifier);

// TODO: will need more fields here for associated types, functions, etc.
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
struct Trait(Identifier, Rc<[Type]>);

#[derive(Clone, Debug)]
struct Impl {
    arguments: Rc<[Type]>,
    functions: Rc<HashMap<Identifier, Abstraction>>,
}

// enum Bound {
//     Lifetime { long: Lifetime, short: Lifetime },
//     Trait(Type, Trait),
// }

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
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
    type_: Type,
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.type_ {
            Type::Integer(integer) => match integer {
                Integer::Unknown => write!(f, "{}", self.value.downcast_ref::<String>().unwrap()),
                Integer::U8 => write!(f, "{}_u8", self.value.downcast_ref::<u8>().unwrap()),
                Integer::U16 => write!(f, "{}_u16", self.value.downcast_ref::<u16>().unwrap()),
                Integer::U32 => write!(f, "{}_u32", self.value.downcast_ref::<u32>().unwrap()),
                Integer::U64 => write!(f, "{}_u64", self.value.downcast_ref::<u64>().unwrap()),
                Integer::U128 => write!(f, "{}_u128", self.value.downcast_ref::<u128>().unwrap()),
                Integer::Usize => {
                    write!(f, "{}_usize", self.value.downcast_ref::<usize>().unwrap())
                }
                Integer::I8 => write!(f, "{}_i8", self.value.downcast_ref::<i8>().unwrap()),
                Integer::I16 => write!(f, "{}_i16", self.value.downcast_ref::<i16>().unwrap()),
                Integer::I32 => write!(f, "{}_i32", self.value.downcast_ref::<i32>().unwrap()),
                Integer::I64 => write!(f, "{}_i64", self.value.downcast_ref::<i64>().unwrap()),
                Integer::I128 => write!(f, "{}_i128", self.value.downcast_ref::<i128>().unwrap()),
                Integer::Isize => {
                    write!(f, "{}_isize", self.value.downcast_ref::<isize>().unwrap())
                }
            },

            Type::Boolean => write!(f, "{}", self.value.downcast_ref::<bool>().unwrap()),

            Type::Unit => write!(f, "()"),

            _ => write!(f, "TODO: Debug for {:?}", self.type_),
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
    // TODO: this seems redundant given that `body` should have a type:
    return_: Type,
    body: Rc<TypedTerm>,
}

#[derive(Clone, Debug)]
enum TypedTerm {
    Block(Rc<[TypedTerm]>),
    Literal(Literal),
    Parameter {
        index: usize,
        type_: Type,
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
        predicate: Rc<TypedTerm>,
        then: Rc<TypedTerm>,
        else_: Rc<TypedTerm>,
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
        type_: Type,
    },
}

impl TypedTerm {
    fn type_(&self) -> Type {
        match self {
            Self::Block(terms) => terms.last().map(|term| term.type_()).unwrap_or(Type::Unit),
            Self::Literal(literal) => literal.type_.clone(),
            // TODO: the return type of an abstraction may be a function of its type parameters unless it's already
            // been monomorphized
            Self::Application {
                abstraction: Abstraction { return_, .. },
                ..
            } => return_.clone(),
            Self::And { .. } | Self::Or { .. } => Type::Boolean,
            Self::If { then, .. } => then.type_(),
            Self::UnaryOp(_, term) => term.type_(),
            Self::BinaryOp(_, term, _) => term.type_(),
            _ => todo!("{self:?}"),
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
        return_: Type,
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
        predicate: Rc<Term>,
        then: Rc<Term>,
        else_: Rc<Term>,
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
        type_: Type,
    },
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
    traits: HashMap<Identifier, Trait>,
    impls: HashMap<(Type, Trait), Option<Impl>>,
    unit: Literal,
}

pub struct Eval {
    value: Option<Literal>,
    new_term_bindings: HashMap<Rc<str>, Option<Term>>,
}

impl fmt::Display for Eval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut need_newline = if let Some(value) = &self.value {
            write!(f, "{value}")?;
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
                write!(f, " = {term:?}")?;
            }

            need_newline = true;
        }

        Ok(())
    }
}

impl Env {
    pub fn new() -> Self {
        let mut env = Self {
            ids_to_names: Vec::new(),
            names_to_ids: HashMap::new(),
            scopes: vec![Scope::default()],
            parameters: Vec::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
            unit: Literal {
                value: Rc::new(()),
                type_: Type::Unit,
            },
        };

        // TODO: should load traits and impls from core/std source files

        let self_ = env.intern("self");
        let other = env.intern("other");

        // These functions won't ever be called at runtime, so just use an empty body:
        let empty = Rc::new(TypedTerm::Block(Rc::new([])));

        let signed = [
            Integer::I8,
            Integer::I16,
            Integer::I32,
            Integer::I64,
            Integer::I128,
            Integer::Isize,
        ]
        .into_iter()
        .map(Type::Integer)
        .collect::<Vec<_>>();

        let unaries = &[
            ("Neg", "neg", &signed as &[Type]),
            ("Not", "not", &[Type::Boolean]),
        ];

        for (name, function, types) in unaries {
            let name = env.intern(name);
            let function = env.intern(function);
            let trait_ = Trait(name, Rc::new([]));

            env.traits.insert(name, trait_.clone());

            for type_ in *types {
                env.impls.insert(
                    (type_.clone(), trait_.clone()),
                    Some(Impl {
                        arguments: Rc::new([]),
                        functions: Rc::new(hashmap! {
                            function => Abstraction {
                                parameters: Rc::new([(self_, type_.clone())]),
                                return_: type_.clone(),
                                body: empty.clone()
                            }
                        }),
                    }),
                );
            }
        }

        let integers = [
            Integer::I8,
            Integer::I16,
            Integer::I32,
            Integer::I64,
            Integer::I128,
            Integer::Isize,
            Integer::U8,
            Integer::U16,
            Integer::U32,
            Integer::U64,
            Integer::U128,
            Integer::Usize,
        ]
        .into_iter()
        .map(Type::Integer)
        .collect::<Vec<_>>();

        let binaries = &[
            ("Add", "add", &integers),
            ("Sub", "sub", &integers),
            ("Mul", "mul", &integers),
            ("Div", "div", &integers),
            ("Rem", "rem", &integers),
        ];

        for (name, function, types) in binaries {
            let name = env.intern(name);
            let function = env.intern(function);
            let trait_ = Trait(name, Rc::new([]));

            env.traits.insert(name, trait_.clone());

            for type_ in *types {
                env.impls.insert(
                    (type_.clone(), trait_.clone()),
                    Some(Impl {
                        arguments: Rc::new([type_.clone()]),
                        functions: Rc::new(hashmap![function => Abstraction {
                            parameters: Rc::new([(self_, type_.clone()), (other, type_.clone())]),
                            return_: type_.clone(),
                            body: empty.clone()
                        }]),
                    }),
                );
            }
        }

        env
    }

    fn inner_scope(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    fn find_term(&self, id: Identifier) -> Option<Option<Term>> {
        for scope in self.scopes.iter().rev() {
            if let Some(term) = scope.terms.get(&id) {
                return Some(term.clone());
            }
        }

        None
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

        let term = &self.stmt_to_term(&stmt, &mut new_term_bindings)?;

        let term = &self.type_check(term, None)?;

        let value = self.eval_term(term)?;

        Ok(Eval {
            value: Some(value),
            new_term_bindings: new_term_bindings
                .into_iter()
                .filter_map(|id| {
                    self.find_term(id)
                        .map(|term| (self.unintern(id).clone(), term))
                })
                .collect(),
        })
    }

    fn intern(&mut self, name: &str) -> Identifier {
        if let Some(&id) = self.names_to_ids.get(name) {
            Identifier(id)
        } else {
            let name = Rc::<str>::from(name);
            let id = self.ids_to_names.len();
            self.ids_to_names.push(name.clone());
            self.names_to_ids.insert(name, id);
            Identifier(id)
        }
    }

    fn unintern(&mut self, Identifier(id): Identifier) -> Rc<str> {
        self.ids_to_names[id].clone()
    }

    fn get_impl(&mut self, type_: &Type, trait_: &Trait) -> Option<Impl> {
        if let Some(result) = self.impls.get(&(type_.clone(), trait_.clone())) {
            result.clone()
        } else {
            // TODO: any exact-match impls should already be in impls, so if we reach here then either the type
            // doesn't implement the trait or there's a matching polymorphic impl we need to find, monomorphize,
            // and add to impls.

            self.impls.insert((type_.clone(), trait_.clone()), None);

            None
        }
    }

    fn eval_term(&mut self, term: &TypedTerm) -> Result<Literal> {
        match term {
            TypedTerm::Literal(literal) => Ok(literal.clone()),

            TypedTerm::Application {
                abstraction: Abstraction { body, .. },
                arguments,
            } => {
                let mut parameters = arguments
                    .iter()
                    .map(|term| self.eval_term(term))
                    .collect::<Result<_>>()?;

                mem::swap(&mut self.parameters, &mut parameters);

                let result = self.eval_term(body);

                mem::swap(&mut self.parameters, &mut parameters);

                result
            }

            TypedTerm::And(left, right) => {
                if *self.eval_term(left)?.value.downcast_ref::<bool>().unwrap() {
                    self.eval_term(right)
                } else {
                    Ok(Literal {
                        value: Rc::new(false),
                        type_: Type::Boolean,
                    })
                }
            }

            TypedTerm::Or(left, right) => {
                if !*self.eval_term(left)?.value.downcast_ref::<bool>().unwrap() {
                    self.eval_term(right)
                } else {
                    Ok(Literal {
                        value: Rc::new(true),
                        type_: Type::Boolean,
                    })
                }
            }

            TypedTerm::UnaryOp(op, term) => {
                let result = self.eval_term(term)?;

                match op {
                    UnaryOp::Neg => match result.type_ {
                        Type::Integer(integer_type) => Ok(Literal {
                            type_: Type::Integer(integer_type),
                            value: match integer_type {
                                Integer::I8 => {
                                    Rc::new(-*result.value.downcast_ref::<i8>().unwrap())
                                }
                                Integer::I16 => {
                                    Rc::new(-*result.value.downcast_ref::<i16>().unwrap())
                                }
                                Integer::I32 => {
                                    Rc::new(-*result.value.downcast_ref::<i32>().unwrap())
                                }
                                Integer::I64 => {
                                    Rc::new(-*result.value.downcast_ref::<i64>().unwrap())
                                }
                                Integer::I128 => {
                                    Rc::new(-*result.value.downcast_ref::<i128>().unwrap())
                                }
                                Integer::Isize => {
                                    Rc::new(-*result.value.downcast_ref::<isize>().unwrap())
                                }
                                _ => unreachable!(),
                            },
                        }),

                        _ => unreachable!(),
                    },

                    UnaryOp::Not => Ok(Literal {
                        type_: Type::Boolean,
                        value: Rc::new(!*result.value.downcast_ref::<bool>().unwrap()),
                    }),
                }
            }

            TypedTerm::BinaryOp(op, left, right) => {
                let left = self.eval_term(left)?;
                let right = self.eval_term(right)?;

                macro_rules! integer_binary_op {
                    ($op:ident, $type:ident, $left:ident, $right:ident) => {
                        match $type {
                            Integer::U8 => Rc::new(
                                left.value
                                    .downcast_ref::<u8>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<u8>().unwrap()),
                            ),
                            Integer::U16 => Rc::new(
                                left.value
                                    .downcast_ref::<u16>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<u16>().unwrap()),
                            ),
                            Integer::U32 => Rc::new(
                                left.value
                                    .downcast_ref::<u32>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<u32>().unwrap()),
                            ),
                            Integer::U64 => Rc::new(
                                left.value
                                    .downcast_ref::<u64>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<u64>().unwrap()),
                            ),
                            Integer::U128 => Rc::new(
                                left.value
                                    .downcast_ref::<u128>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<u128>().unwrap()),
                            ),
                            Integer::Usize => Rc::new(
                                left.value
                                    .downcast_ref::<usize>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<usize>().unwrap()),
                            ),
                            Integer::I8 => Rc::new(
                                left.value
                                    .downcast_ref::<i8>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<i8>().unwrap()),
                            ),
                            Integer::I16 => Rc::new(
                                left.value
                                    .downcast_ref::<i16>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<i16>().unwrap()),
                            ),
                            Integer::I32 => Rc::new(
                                left.value
                                    .downcast_ref::<i32>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<i32>().unwrap()),
                            ),
                            Integer::I64 => Rc::new(
                                left.value
                                    .downcast_ref::<i64>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<i64>().unwrap()),
                            ),
                            Integer::I128 => Rc::new(
                                left.value
                                    .downcast_ref::<i128>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<i128>().unwrap()),
                            ),
                            Integer::Isize => Rc::new(
                                left.value
                                    .downcast_ref::<isize>()
                                    .unwrap()
                                    .$op(right.value.downcast_ref::<isize>().unwrap()),
                            ),
                            _ => unreachable!(),
                        }
                    };
                }

                match left.type_ {
                    Type::Integer(integer_type) => Ok(Literal {
                        type_: Type::Integer(integer_type),
                        value: match op {
                            BinaryOp::Add => integer_binary_op!(add, integer_type, left, right),
                            BinaryOp::Sub => integer_binary_op!(sub, integer_type, left, right),
                            BinaryOp::Mul => integer_binary_op!(mul, integer_type, left, right),
                            BinaryOp::Div => integer_binary_op!(div, integer_type, left, right),
                            BinaryOp::Rem => integer_binary_op!(rem, integer_type, left, right),
                            _ => unreachable!(),
                        },
                    }),
                    _ => unreachable!(),
                }
            }

            _ => Err(anyhow!("evaluation not yet supported for term {term:?}")),
        }
    }

    fn type_check(&mut self, term: &Term, expected_type: Option<&Type>) -> Result<TypedTerm> {
        match term {
            Term::Literal(Literal { value, type_ }) => {
                let literal = if let Type::Integer(Integer::Unknown) = type_ {
                    match expected_type
                        .cloned()
                        .unwrap_or(Type::Integer(Integer::I32))
                    {
                        Type::Integer(integer_type) => Literal {
                            value: integer_type.parse(value.downcast_ref::<String>().unwrap())?,
                            type_: Type::Integer(integer_type),
                        },

                        _ => Literal {
                            value: Rc::new(value.downcast_ref::<String>().unwrap().parse::<i32>()?),
                            type_: Type::Integer(Integer::I32),
                        },
                    }
                } else {
                    Literal {
                        value: value.clone(),
                        type_: type_.clone(),
                    }
                };

                Ok(TypedTerm::Literal(literal))
            }

            Term::UnaryOp { op, term } => {
                let term = self.type_check(&term, expected_type)?;

                let (trait_, function) = match op {
                    UnaryOp::Neg => ("Neg", "neg"),
                    UnaryOp::Not => ("Not", "not"),
                };

                let trait_ = self.intern(trait_);
                let trait_ = self.traits.get(&trait_).unwrap().clone();
                let function = self.intern(function);

                let type_ = term.type_();

                let impl_ = self.get_impl(&type_, &trait_).ok_or_else(|| {
                    anyhow!("type {type_:?} is not compatible with unary operator {op:?}")
                })?;

                let type_ = term.type_();

                Ok(match (op, type_) {
                    (UnaryOp::Neg, Type::Integer(_)) | (UnaryOp::Not, Type::Boolean) => {
                        TypedTerm::UnaryOp(*op, Rc::new(term))
                    }
                    _ => TypedTerm::Application {
                        abstraction: impl_.functions.get(&function).unwrap().clone(),
                        arguments: Rc::new([term]),
                    },
                })
            }

            Term::BinaryOp { op, left, right } => {
                let left = self.type_check(&left, expected_type)?;

                let (expected_type, impl_and_function) = match op {
                    BinaryOp::And | BinaryOp::Or => (Type::Boolean, None),

                    _ => {
                        let (trait_, function) = match op {
                            BinaryOp::Add => ("Add", "add"),
                            BinaryOp::Sub => ("Sub", "sub"),
                            BinaryOp::Mul => ("Mul", "mul"),
                            BinaryOp::Div => ("Div", "div"),
                            BinaryOp::Rem => ("Rem", "rem"),
                            _ => unreachable!(),
                        };

                        let trait_ = self.intern(trait_);
                        let trait_ = self.traits.get(&trait_).unwrap().clone();
                        let function = self.intern(function);

                        let left_type = left.type_();

                        let impl_ = self.get_impl(&left_type, &trait_).ok_or_else(|| {
                            anyhow!(
                                "type {left_type:?} is not compatible with binary operator {op:?}"
                            )
                        })?;

                        (impl_.arguments[0].clone(), Some((impl_, function)))
                    }
                };

                let right = self.type_check(&right, Some(&expected_type))?;

                let right_type = right.type_();

                if expected_type != right_type {
                    Err(anyhow!("expected {expected_type:?}, got {right_type:?}"))
                } else {
                    let type_ = left.type_();

                    Ok(match (op, type_) {
                        (BinaryOp::And, _) => TypedTerm::And(Rc::new(left), Rc::new(right)),

                        (BinaryOp::Or, _) => TypedTerm::Or(Rc::new(left), Rc::new(right)),

                        (
                            BinaryOp::Add
                            | BinaryOp::Sub
                            | BinaryOp::Mul
                            | BinaryOp::Div
                            | BinaryOp::Rem,
                            Type::Integer(_),
                        ) => TypedTerm::BinaryOp(*op, Rc::new(left), Rc::new(right)),

                        _ => {
                            let (impl_, function) = impl_and_function.unwrap();

                            TypedTerm::Application {
                                abstraction: impl_.functions.get(&function).unwrap().clone(),
                                arguments: Rc::new([left, right]),
                            }
                        }
                    })
                }
            }

            Term::Variable(identifier) => match self.inner_scope().terms.get(identifier).cloned() {
                Some(Some(term)) => self.type_check(&term, expected_type),

                // TODO: will need to do some control/data flow analysis to support uninitialized lets
                Some(None) => Err(anyhow!(
                    "use of uninitialized symbol: {}",
                    self.unintern(*identifier)
                )),

                None => Err(anyhow!("symbol not found: {}", self.unintern(*identifier))),
            },

            _ => Err(anyhow!("type checking not yet supported for term {term:?}")),
        }
    }

    fn stmt_to_term(
        &mut self,
        stmt: &Stmt,
        new_term_bindings: &mut HashSet<Identifier>,
    ) -> Result<Term> {
        match stmt {
            Stmt::Local(Local {
                pat, init, attrs, ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    match pat {
                        Pat::Ident(PatIdent {
                            ident,
                            by_ref,
                            mutability,
                            ..
                        }) => {
                            if by_ref.is_some() {
                                Err(anyhow!("ref patterns not yet supported"))
                            } else if mutability.is_some() {
                                Err(anyhow!("mut patterns not yet supported"))
                            } else {
                                // TODO: if we're pushing a new scope for each new binding, each scope only needs
                                // to hold at most a single binding, so perhaps use an Option<(Identifier, Term)>
                                // instead of a HashMap.  Also, if we use a singly-linked list of those to
                                // represent a spaghetti stack of scopes, we could get rid of new_term_bindings;
                                // instead, the caller can just diff the before and after scope stack versions to
                                // identify new bindings.
                                self.scopes.push(Scope::default());

                                let identifier = self.intern(&ident.to_string());

                                new_term_bindings.insert(identifier);

                                let value = init
                                    .as_ref()
                                    .map(|(_, expr)| self.expr_to_term(expr))
                                    .transpose()?;

                                self.inner_scope().terms.insert(identifier, value);

                                Ok(Term::Literal(self.unit.clone()))
                            }
                        }

                        _ => Err(anyhow!("pattern not yet supported: {pat:?}")),
                    }
                }
            }

            Stmt::Semi(expr, _) | Stmt::Expr(expr) => self.expr_to_term(expr),

            _ => Err(anyhow!("stmt not yet supported: {stmt:?}")),
        }
    }

    fn expr_to_term(&mut self, expr: &Expr) -> Result<Term> {
        match expr {
            Expr::Lit(ExprLit { lit, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::Literal(match lit {
                        Lit::Int(lit) => match lit.suffix() {
                            "" => Literal {
                                value: Rc::new(lit.base10_digits().to_owned()),
                                type_: Type::Integer(Integer::Unknown),
                            },

                            "u8" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<u8>()?),
                                type_: Type::Integer(Integer::U8),
                            },

                            "u16" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<u16>()?),
                                type_: Type::Integer(Integer::U16),
                            },

                            "u32" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<u32>()?),
                                type_: Type::Integer(Integer::U32),
                            },

                            "u64" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<u64>()?),
                                type_: Type::Integer(Integer::U64),
                            },

                            "u128" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<u128>()?),
                                type_: Type::Integer(Integer::U128),
                            },

                            "usize" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<usize>()?),
                                type_: Type::Integer(Integer::Usize),
                            },

                            "i8" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<i8>()?),
                                type_: Type::Integer(Integer::I8),
                            },

                            "i16" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<i16>()?),
                                type_: Type::Integer(Integer::I16),
                            },

                            "i32" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<i32>()?),
                                type_: Type::Integer(Integer::I32),
                            },

                            "i64" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<i64>()?),
                                type_: Type::Integer(Integer::I64),
                            },

                            "i128" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<i128>()?),
                                type_: Type::Integer(Integer::I128),
                            },

                            "isize" => Literal {
                                value: Rc::new(lit.base10_digits().parse::<isize>()?),
                                type_: Type::Integer(Integer::Isize),
                            },

                            _ => {
                                return Err(anyhow!(
                                    "unexpected integer literal suffix: {}",
                                    lit.suffix()
                                ))
                            }
                        },

                        Lit::Bool(LitBool { value, .. }) => Literal {
                            value: Rc::new(*value),
                            type_: Type::Boolean,
                        },

                        _ => return Err(anyhow!("literal not yet supported: {lit:?}")),
                    }))
                }
            }

            Expr::Unary(ExprUnary { op, expr, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    let term = Rc::new(self.expr_to_term(expr)?);

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
                    let left = Rc::new(self.expr_to_term(left)?);
                    let right = Rc::new(self.expr_to_term(right)?);

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
                        // TODO: save a reference to the scope so we can use it during resolution and type checking
                        Ok(Term::Variable(self.intern(&ident.to_string())))
                    } else {
                        Err(anyhow!("path arguments not yet supported"))
                    }
                } else {
                    Err(anyhow!("unexpected empty path"))
                }
            }

            Expr::Paren(ExprParen { expr, attrs, .. }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    self.expr_to_term(expr)
                }
            }

            Expr::If(ExprIf {
                cond,
                then_branch: Block { stmts, .. },
                else_branch,
                attrs,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::If {
                        predicate: Rc::new(self.expr_to_term(cond)?),
                        then: Rc::new(self.block_to_term(stmts)?),
                        else_: Rc::new(
                            else_branch
                                .as_ref()
                                .map(|(_, expr)| self.expr_to_term(&expr))
                                .transpose()?
                                .unwrap_or_else(|| Term::Literal(self.unit.clone())),
                        ),
                    })
                }
            }

            Expr::Block(ExprBlock {
                block: Block { stmts, .. },
                attrs,
                label,
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if label.is_some() {
                    Err(anyhow!("block labels not yet supported"))
                } else {
                    self.block_to_term(stmts)
                }
            }

            _ => Err(anyhow!("expr not yet supported: {expr:?}")),
        }
    }

    fn block_to_term(&mut self, stmts: &[Stmt]) -> Result<Term> {
        let scope_count = self.scopes.len();

        let mut dummy = HashSet::new();

        let result = stmts
            .iter()
            .map(|stmt| self.stmt_to_term(stmt, &mut dummy))
            .collect::<Result<Vec<_>>>()
            .map(|terms| match &terms[..] {
                [] => Term::Literal(self.unit.clone()),

                [term] => term.clone(),

                terms => Term::Block(Rc::from(terms)),
            });

        self.scopes.truncate(scope_count);

        result
    }

    pub fn eval_file(&mut self, _file: &str) -> Result<Eval> {
        todo!()
    }
}
