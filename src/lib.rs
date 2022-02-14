#![deny(warnings)]
#![allow(dead_code)] // temporary

use {
    anyhow::{anyhow, Result},
    log::info,
    maplit::hashmap,
    std::{
        any::Any,
        cell::RefCell,
        cmp::Ordering,
        collections::HashMap,
        convert::identity,
        fmt, mem,
        ops::{Add, Deref, Div, Mul, Rem, Sub},
        rc::Rc,
    },
    syn::{
        BinOp, Block, Expr, ExprAssign, ExprAssignOp, ExprBinary, ExprBlock, ExprBreak, ExprIf,
        ExprLit, ExprLoop, ExprParen, ExprPath, ExprUnary, Lit, LitBool, Local, Pat, PatIdent,
        Path, PathArguments, PathSegment, Stmt, UnOp,
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
    Reference {
        // TODO: add lifetime field
        unique: bool,
        type_: Rc<Type>,
    },
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
    Deref,
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
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
    Eq,
    Ge,
    Gt,
    Le,
    Lt,
}

#[derive(Clone, Debug)]
struct Parameter {
    name: Identifier,
    mutable: bool,
    type_: Type,
}

#[derive(Clone, Debug)]
struct Abstraction {
    // TODO: support type and lifetime parameters.
    parameters: Rc<[Parameter]>,
    body: Rc<Term>,
}

#[derive(Clone, Debug)]
enum Pattern {
    Literal(Literal),
    // TODO: support other patterns
}

#[derive(Clone, Debug)]
struct MatchArm {
    pattern: Pattern,
    guard: Option<Term>,
    body: Term,
}

#[derive(Clone, Debug)]
enum Term {
    Block(Rc<[Term]>),
    Literal(Literal),
    Reference {
        // TODO: add lifetime field
        unique: bool,
        term: Rc<Term>,
    },
    Let {
        name: Identifier,
        mutable: bool,
        index: usize,
        term: Option<Rc<RefCell<BindingTerm>>>,
    },
    Phi(Rc<[Option<Rc<RefCell<BindingTerm>>>]>),
    Variable {
        index: usize,
        type_: Type,
    },
    Assignment {
        left: Rc<Term>,
        right: Rc<Term>,
    },
    Application {
        // TODO: support type and lifetime arguments.
        abstraction: Abstraction,
        arguments: Rc<[Term]>,
    },
    Abstraction(Abstraction),
    And(Rc<Term>, Rc<Term>),
    Or(Rc<Term>, Rc<Term>),
    UnaryOp(UnaryOp, Rc<Term>),
    BinaryOp(BinaryOp, Rc<Term>, Rc<Term>),
    Match {
        scrutinee: Rc<Term>,
        arms: Rc<[MatchArm]>,
    },
    Loop {
        label: Option<Identifier>,
        body: Rc<Term>,
        type_: Type,
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

impl Term {
    fn type_(&self) -> Type {
        match self {
            Self::Block(terms) => terms.last().map(|term| term.type_()).unwrap_or(Type::Unit),
            Self::Literal(literal) => literal.type_.clone(),
            // TODO: the return type of an abstraction may be a function of its type parameters
            Self::Application {
                abstraction: Abstraction { body, .. },
                ..
            } => body.type_(),
            Self::And { .. } | Self::Or { .. } => Type::Boolean,
            Self::UnaryOp(_, term) => term.type_(),
            Self::BinaryOp(op, term, _) => match op {
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem => {
                    term.type_()
                }
                BinaryOp::Eq | BinaryOp::Ge | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Lt => {
                    Type::Boolean
                }
                _ => unreachable!(),
            },
            Self::Variable { type_, .. } => type_.clone(),
            Self::Assignment { .. } => Type::Unit,
            Self::Match { arms, .. } => arms[0].body.type_(),
            Self::Break { .. } | Self::Return { .. } => Type::Never,
            Self::Phi(terms) => {
                RefCell::borrow(terms.iter().find_map(|term| term.as_ref()).unwrap())
                    .term
                    .type_()
            }
            _ => todo!("Term::type_ for {self:?}"),
        }
    }
}

struct Loop {
    label: Option<Identifier>,
    expected_type: Option<Type>,
    break_terms: Vec<Term>,
    branch_context: BranchContext,
}

#[derive(Clone, Copy, Debug)]
enum BindingStatus {
    Untyped,
    Typed,
    Evaluated,
}

#[derive(Clone, Debug)]
struct BindingTerm {
    status: BindingStatus,
    term: Term,
}

#[derive(Clone, Debug)]
struct Binding {
    name: Identifier,
    mutable: bool,
    term: Option<Rc<RefCell<BindingTerm>>>,
}

struct BranchContext {
    indexes: Box<[usize]>,
    terms: Vec<Option<Rc<RefCell<BindingTerm>>>>,
}

impl BranchContext {
    fn new(bindings: &[Binding]) -> Self {
        Self {
            indexes: bindings
                .iter()
                .enumerate()
                .filter_map(|(index, binding)| {
                    if binding.term.is_none() {
                        Some(index)
                    } else {
                        None
                    }
                })
                .collect(),
            terms: Vec::new(),
        }
    }

    fn reset(&self, bindings: &mut [Binding]) {
        for &index in self.indexes.iter() {
            bindings[index].term = None;
        }
    }

    fn record_and_reset(&mut self, bindings: &mut [Binding]) {
        self.terms.extend(
            self.indexes
                .iter()
                .map(|&index| bindings[index].term.clone()),
        );

        self.reset(bindings);
    }

    fn make_phi_nodes(&mut self, bindings: &mut [Binding]) {
        for (my_index, &binding_index) in self.indexes.iter().enumerate() {
            let terms = self
                .terms
                .iter()
                .skip(my_index)
                .step_by(self.indexes.len())
                .cloned()
                .collect::<Rc<[_]>>();

            bindings[binding_index].term = if terms.iter().all(|term| term.is_none()) {
                None
            } else {
                Some(Rc::new(RefCell::new(BindingTerm {
                    status: BindingStatus::Untyped,
                    term: Term::Phi(terms),
                })))
            }
        }
    }
}

#[derive(Debug)]
enum EvalException {
    Break {
        label: Option<Identifier>,
        result: Literal,
    },
    Return {
        result: Literal,
    },
}

macro_rules! integer_binary_op {
    ($op:ident, $type:ident, $left:ident, $right:ident, $wrap:path) => {
        match $type {
            Integer::U8 => $wrap(
                $left
                    .value
                    .downcast_ref::<u8>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<u8>().unwrap()),
            ),
            Integer::U16 => $wrap(
                $left
                    .value
                    .downcast_ref::<u16>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<u16>().unwrap()),
            ),
            Integer::U32 => $wrap(
                $left
                    .value
                    .downcast_ref::<u32>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<u32>().unwrap()),
            ),
            Integer::U64 => $wrap(
                $left
                    .value
                    .downcast_ref::<u64>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<u64>().unwrap()),
            ),
            Integer::U128 => $wrap(
                $left
                    .value
                    .downcast_ref::<u128>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<u128>().unwrap()),
            ),
            Integer::Usize => $wrap(
                $left
                    .value
                    .downcast_ref::<usize>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<usize>().unwrap()),
            ),
            Integer::I8 => $wrap(
                $left
                    .value
                    .downcast_ref::<i8>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<i8>().unwrap()),
            ),
            Integer::I16 => $wrap(
                $left
                    .value
                    .downcast_ref::<i16>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<i16>().unwrap()),
            ),
            Integer::I32 => $wrap(
                $left
                    .value
                    .downcast_ref::<i32>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<i32>().unwrap()),
            ),
            Integer::I64 => $wrap(
                $left
                    .value
                    .downcast_ref::<i64>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<i64>().unwrap()),
            ),
            Integer::I128 => $wrap(
                $left
                    .value
                    .downcast_ref::<i128>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<i128>().unwrap()),
            ),
            Integer::Isize => $wrap(
                $left
                    .value
                    .downcast_ref::<isize>()
                    .unwrap()
                    .$op($right.value.downcast_ref::<isize>().unwrap()),
            ),
            _ => unreachable!(),
        }
    };
}

pub struct Eval {
    value: Literal,
    new_term_bindings: HashMap<Rc<str>, Option<Term>>,
}

impl fmt::Display for Eval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut need_newline = match &self.value.type_ {
            Type::Unit => false,
            _ => {
                write!(f, "{}", self.value)?;
                true
            }
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

fn match_types(expected: &Type, actual: &Type) -> Result<()> {
    // TODO: this will need to be refined once we start doing unification, and we'll probably need to move this
    // function into Env's impl

    if expected != &Type::Never && actual != &Type::Never && expected != actual {
        Err(anyhow!(
            "type mismatch: expected {expected:?}, got {actual:?}"
        ))
    } else {
        Ok(())
    }
}

pub struct Env {
    ids_to_names: Vec<Rc<str>>,
    names_to_ids: HashMap<Rc<str>, usize>,
    bindings: Vec<Binding>,
    loops: Vec<Loop>,
    traits: HashMap<Identifier, Trait>,
    impls: HashMap<(Type, Trait), Option<Impl>>,
    unit: Literal,
    true_: Literal,
    false_: Literal,
}

impl Env {
    pub fn new() -> Self {
        let mut env = Self {
            ids_to_names: Vec::new(),
            names_to_ids: HashMap::new(),
            bindings: Vec::new(),
            loops: Vec::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
            unit: Literal {
                value: Rc::new(()),
                type_: Type::Unit,
            },
            true_: Literal {
                value: Rc::new(true),
                type_: Type::Boolean,
            },
            false_: Literal {
                value: Rc::new(false),
                type_: Type::Boolean,
            },
        };

        // TODO: should load traits and impls from core/std source files

        let self_ = env.intern("self");
        let other = env.intern("other");

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
            (UnaryOp::Neg, "Neg", "neg", &signed as &[Type]),
            (UnaryOp::Not, "Not", "not", &[Type::Boolean]),
        ];

        for (op, name, function, types) in unaries {
            let name = env.intern(name);
            let function = env.intern(function);
            let trait_ = Trait(name, Rc::new([]));

            env.traits.insert(name, trait_.clone());

            for type_ in *types {
                let abstraction = Abstraction {
                    parameters: Rc::new([Parameter {
                        name: self_,
                        mutable: false,
                        type_: type_.clone(),
                    }]),
                    body: Rc::new(Term::UnaryOp(
                        *op,
                        Rc::new(Term::Variable {
                            index: 0,
                            type_: type_.clone(),
                        }),
                    )),
                };

                env.impls.insert(
                    (type_.clone(), trait_.clone()),
                    Some(Impl {
                        arguments: Rc::new([]),
                        functions: Rc::new(hashmap![function => abstraction]),
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
            (BinaryOp::Add, "Add", "add", &integers),
            (BinaryOp::Sub, "Sub", "sub", &integers),
            (BinaryOp::Mul, "Mul", "mul", &integers),
            (BinaryOp::Div, "Div", "div", &integers),
            (BinaryOp::Rem, "Rem", "rem", &integers),
        ];

        for (op, name, function, types) in binaries {
            let name = env.intern(name);
            let function = env.intern(function);
            let trait_ = Trait(name, Rc::new([]));

            env.traits.insert(name, trait_.clone());

            for type_ in *types {
                let abstraction = Abstraction {
                    parameters: Rc::new([
                        Parameter {
                            name: self_,
                            mutable: false,
                            type_: type_.clone(),
                        },
                        Parameter {
                            name: other,
                            mutable: false,
                            type_: type_.clone(),
                        },
                    ]),
                    body: Rc::new(Term::BinaryOp(
                        *op,
                        Rc::new(Term::Variable {
                            index: 0,
                            type_: type_.clone(),
                        }),
                        Rc::new(Term::Variable {
                            index: 1,
                            type_: type_.clone(),
                        }),
                    )),
                };

                env.impls.insert(
                    (type_.clone(), trait_.clone()),
                    Some(Impl {
                        arguments: Rc::new([type_.clone()]),
                        functions: Rc::new(hashmap![function => abstraction]),
                    }),
                );
            }
        }

        let assignments = &[
            (BinaryOp::AddAssign, "AddAssign", "add_assign", &integers),
            (BinaryOp::SubAssign, "SubAssign", "sub_assign", &integers),
            (BinaryOp::MulAssign, "MulAssign", "mul_assign", &integers),
            (BinaryOp::DivAssign, "DivAssign", "div_assign", &integers),
            (BinaryOp::RemAssign, "RemAssign", "rem_assign", &integers),
        ];

        for (op, name, function, types) in assignments {
            let name = env.intern(name);
            let function = env.intern(function);
            let trait_ = Trait(name, Rc::new([]));

            env.traits.insert(name, trait_.clone());

            for type_ in *types {
                let self_type = Type::Reference {
                    unique: true,
                    type_: Rc::new(type_.clone()),
                };

                let abstraction = Abstraction {
                    parameters: Rc::new([
                        Parameter {
                            name: self_,
                            mutable: false,
                            type_: self_type.clone(),
                        },
                        Parameter {
                            name: other,
                            mutable: false,
                            type_: type_.clone(),
                        },
                    ]),
                    body: Rc::new(Term::Assignment {
                        left: Rc::new(Term::UnaryOp(
                            UnaryOp::Deref,
                            Rc::new(Term::Variable {
                                index: 0,
                                type_: self_type.clone(),
                            }),
                        )),
                        right: Rc::new(Term::BinaryOp(
                            *op,
                            Rc::new(Term::UnaryOp(
                                UnaryOp::Deref,
                                Rc::new(Term::Variable {
                                    index: 0,
                                    type_: self_type.clone(),
                                }),
                            )),
                            Rc::new(Term::Variable {
                                index: 1,
                                type_: type_.clone(),
                            }),
                        )),
                    }),
                };

                env.impls.insert(
                    (type_.clone(), trait_.clone()),
                    Some(Impl {
                        arguments: Rc::new([type_.clone()]),
                        functions: Rc::new(hashmap![function => abstraction]),
                    }),
                );
            }
        }

        let comparisons = &[
            ("PartialEq", &[(BinaryOp::Eq, "eq")] as &[_], &integers),
            (
                "PartialOrd",
                &[
                    (BinaryOp::Ge, "ge"),
                    (BinaryOp::Gt, "gt"),
                    (BinaryOp::Le, "le"),
                    (BinaryOp::Lt, "lt"),
                ],
                &integers,
            ),
        ];

        for (name, ops_and_functions, types) in comparisons {
            let name = env.intern(name);
            let trait_ = Trait(name, Rc::new([]));

            env.traits.insert(name, trait_.clone());

            for type_ in *types {
                let ref_type = Type::Reference {
                    unique: false,
                    type_: Rc::new(type_.clone()),
                };

                let functions = ops_and_functions
                    .iter()
                    .map(|(op, function)| {
                        (
                            env.intern(function),
                            Abstraction {
                                parameters: Rc::new([
                                    Parameter {
                                        name: self_,
                                        mutable: false,
                                        type_: ref_type.clone(),
                                    },
                                    Parameter {
                                        name: other,
                                        mutable: false,
                                        type_: ref_type.clone(),
                                    },
                                ]),
                                body: Rc::new(Term::BinaryOp(
                                    *op,
                                    Rc::new(Term::UnaryOp(
                                        UnaryOp::Deref,
                                        Rc::new(Term::Variable {
                                            index: 0,
                                            type_: ref_type.clone(),
                                        }),
                                    )),
                                    Rc::new(Term::UnaryOp(
                                        UnaryOp::Deref,
                                        Rc::new(Term::Variable {
                                            index: 1,
                                            type_: ref_type.clone(),
                                        }),
                                    )),
                                )),
                            },
                        )
                    })
                    .collect();

                env.impls.insert(
                    (type_.clone(), trait_.clone()),
                    Some(Impl {
                        arguments: Rc::new([type_.clone()]),
                        functions: Rc::new(functions),
                    }),
                );
            }
        }

        env
    }

    fn find_term(&self, id: Identifier) -> Option<usize> {
        self.bindings
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, binding)| {
                if binding.name == id {
                    Some(index)
                } else {
                    None
                }
            })
    }

    pub fn eval_line(&mut self, line: &str) -> Result<Eval> {
        let stmt = syn::parse_str::<Stmt>(line)
            .or_else(|_| syn::parse_str::<Stmt>(&format!("{line};")))
            .or_else(|_| syn::parse_str::<Expr>(line).map(Stmt::Expr))?;

        info!("{stmt:#?}");

        // TODO: convert stmt to a term (if it's an expression), then typecheck it, then lower it to something
        // MIR-like, then borrow-check it, then evaluate it.
        //
        // If it's not an expression (i.e. it's an item), update the relevant symbol tables.  If it's an item with
        // code inside (e.g. an impl block or fn) do all of the above except evaluation.

        let binding_count = self.bindings.len();

        let term = &self.stmt_to_term(&stmt)?;

        let term = &self.type_check(term, None)?;

        self.type_check_bindings(0)?;

        let value = match self.eval_term(term) {
            Ok(value) => value,
            Err(EvalException::Return { result }) => {
                self.bindings.clear();
                result
            }
            _ => unreachable!(),
        };

        Ok(Eval {
            value,
            new_term_bindings: self.bindings[binding_count..]
                .iter()
                .map(|binding| {
                    (
                        self.unintern(binding.name).clone(),
                        binding
                            .term
                            .as_ref()
                            .map(|term| RefCell::borrow(term).term.clone()),
                    )
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

    fn unintern(&self, Identifier(id): Identifier) -> Rc<str> {
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

    fn eval_term(&mut self, term: &Term) -> Result<Literal, EvalException> {
        match term {
            Term::Let {
                name,
                mutable,
                index,
                term,
            } => {
                match index.cmp(&self.bindings.len()) {
                    Ordering::Less => (),
                    Ordering::Equal => self.bindings.push(Binding {
                        name: *name,
                        mutable: *mutable,
                        term: term.clone(),
                    }),
                    Ordering::Greater => unreachable!(),
                }

                if let Some(term) = term {
                    let mut term = RefCell::borrow_mut(term);

                    *term = BindingTerm {
                        status: BindingStatus::Evaluated,
                        term: Term::Literal(match term.status {
                            BindingStatus::Typed => self.eval_term(&term.term)?,
                            _ => unreachable!(),
                        }),
                    };
                }

                Ok(self.unit.clone())
            }

            Term::Variable { index, .. } => {
                let term = RefCell::borrow(self.bindings[*index].term.as_ref().unwrap());

                if let (BindingStatus::Evaluated, Term::Literal(literal)) =
                    (term.status, &term.term)
                {
                    Ok(literal.clone())
                } else {
                    panic!("unexpected binding status: {term:?}")
                }
            }

            Term::Literal(literal) => Ok(literal.clone()),

            Term::Application {
                abstraction:
                    Abstraction {
                        body, parameters, ..
                    },
                arguments,
            } => {
                let mut parameters = arguments
                    .iter()
                    .zip(parameters.iter())
                    .map(|(term, Parameter { name, mutable, .. })| {
                        Ok(Binding {
                            name: *name,
                            mutable: *mutable,
                            term: Some(Rc::new(RefCell::new(BindingTerm {
                                status: BindingStatus::Evaluated,
                                term: Term::Literal(self.eval_term(term)?),
                            }))),
                        })
                    })
                    .collect::<Result<Vec<_>, EvalException>>()?;

                mem::swap(&mut parameters, &mut self.bindings);

                let result = self.eval_term(body);

                mem::swap(&mut parameters, &mut self.bindings);

                result
            }

            Term::And(left, right) => {
                if *self.eval_term(left)?.value.downcast_ref::<bool>().unwrap() {
                    self.eval_term(right)
                } else {
                    Ok(Literal {
                        value: Rc::new(false),
                        type_: Type::Boolean,
                    })
                }
            }

            Term::Or(left, right) => {
                if !*self.eval_term(left)?.value.downcast_ref::<bool>().unwrap() {
                    self.eval_term(right)
                } else {
                    Ok(Literal {
                        value: Rc::new(true),
                        type_: Type::Boolean,
                    })
                }
            }

            Term::UnaryOp(op, term) => {
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

                    UnaryOp::Deref => todo!(),
                }
            }

            Term::BinaryOp(op, left, right) => {
                let left = self.eval_term(left)?;
                let right = self.eval_term(right)?;

                match left.type_ {
                    Type::Integer(integer_type) => Ok(match op {
                        BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Rem => Literal {
                            type_: Type::Integer(integer_type),
                            value: match op {
                                BinaryOp::Add => {
                                    integer_binary_op!(add, integer_type, left, right, Rc::new)
                                }
                                BinaryOp::Sub => {
                                    integer_binary_op!(sub, integer_type, left, right, Rc::new)
                                }
                                BinaryOp::Mul => {
                                    integer_binary_op!(mul, integer_type, left, right, Rc::new)
                                }
                                BinaryOp::Div => {
                                    integer_binary_op!(div, integer_type, left, right, Rc::new)
                                }
                                BinaryOp::Rem => {
                                    integer_binary_op!(rem, integer_type, left, right, Rc::new)
                                }
                                _ => unreachable!(),
                            },
                        },

                        BinaryOp::Eq
                        | BinaryOp::Ge
                        | BinaryOp::Gt
                        | BinaryOp::Le
                        | BinaryOp::Lt => Literal {
                            type_: Type::Boolean,
                            value: Rc::new(match op {
                                BinaryOp::Eq => {
                                    integer_binary_op!(eq, integer_type, left, right, identity)
                                }
                                BinaryOp::Ge => {
                                    integer_binary_op!(ge, integer_type, left, right, identity)
                                }
                                BinaryOp::Gt => {
                                    integer_binary_op!(gt, integer_type, left, right, identity)
                                }
                                BinaryOp::Le => {
                                    integer_binary_op!(le, integer_type, left, right, identity)
                                }
                                BinaryOp::Lt => {
                                    integer_binary_op!(lt, integer_type, left, right, identity)
                                }
                                _ => unreachable!(),
                            }),
                        },
                        _ => unreachable!(),
                    }),
                    _ => unreachable!(),
                }
            }

            Term::Match { scrutinee, arms } => {
                let scrutinee = self.eval_term(scrutinee)?;

                for arm in arms.iter() {
                    if self.match_pattern(&arm.pattern, &scrutinee) {
                        // TODO: push and pop pattern bindings

                        let match_guard = if let Some(guard) = &arm.guard {
                            *self
                                .eval_term(&guard)?
                                .value
                                .downcast_ref::<bool>()
                                .unwrap()
                        } else {
                            true
                        };

                        if match_guard {
                            return self.eval_term(&arm.body);
                        }
                    }
                }

                unreachable!(
                    "exhaustiveness checking during type checking should prevent reaching this point"
                )
            }

            Term::Assignment { left, right } => {
                if let Term::Variable { index, .. } = left.deref() {
                    let right = self.eval_term(right)?;

                    self.bindings[*index].term = Some(Rc::new(RefCell::new(BindingTerm {
                        status: BindingStatus::Evaluated,
                        term: Term::Literal(right),
                    })));

                    Ok(self.unit.clone())
                } else {
                    todo!("assignment to {left:?}")
                }
            }

            Term::Block(terms) => {
                let binding_count = self.bindings.len();

                let terms = terms
                    .iter()
                    .map(|term| self.eval_term(term))
                    .collect::<Result<Vec<_>, EvalException>>();

                self.bindings.truncate(binding_count);

                Ok(terms?.into_iter().last().unwrap())
            }

            Term::Loop { label, body, .. } => loop {
                match self.eval_term(body) {
                    Ok(_) => (),

                    Err(EvalException::Break {
                        label: break_label,
                        result,
                    }) if break_label.is_none() || break_label == *label => break Ok(result),

                    err => break err,
                }
            },

            Term::Break { label, term } => Err(EvalException::Break {
                label: *label,
                result: self.eval_term(term)?,
            }),

            Term::Return { term } => Err(EvalException::Return {
                result: self.eval_term(term)?,
            }),

            _ => todo!("evaluation not yet supported for term {term:?}"),
        }
    }

    // Does this need to be a method of Env, or can we move it to Pattern?
    fn match_pattern(&mut self, pattern: &Pattern, scrutinee: &Literal) -> bool {
        match pattern {
            Pattern::Literal(literal) => match &scrutinee.type_ {
                Type::Boolean => {
                    *literal.value.downcast_ref::<bool>().unwrap()
                        == *scrutinee.value.downcast_ref::<bool>().unwrap()
                }

                Type::Integer(integer_type) => {
                    integer_binary_op!(eq, integer_type, literal, scrutinee, identity)
                }

                _ => todo!("literal match for {:?}", scrutinee.type_),
            },
        }
    }

    fn type_check(&mut self, term: &Term, expected_type: Option<&Type>) -> Result<Term> {
        match term {
            Term::Let {
                name,
                mutable,
                index,
                term: binding_term,
            } => {
                match index.cmp(&self.bindings.len()) {
                    Ordering::Less => (),
                    Ordering::Equal => self.bindings.push(Binding {
                        name: *name,
                        mutable: *mutable,
                        term: binding_term.clone(),
                    }),
                    Ordering::Greater => unreachable!(),
                }

                Ok(term.clone())
            }

            Term::Variable { index, .. } => {
                let index = *index;

                let term = {
                    let binding = &self.bindings[index];

                    let error = || {
                        Err(anyhow!(
                            "use of uninitialized variable: {}",
                            self.unintern(binding.name)
                        ))
                    };

                    if let Some(term) = &binding.term {
                        if let Term::Phi(terms) = &RefCell::borrow(term).term {
                            if terms.iter().any(|term| term.is_none()) {
                                return error();
                            }
                        }

                        term.clone()
                    } else {
                        return error();
                    }
                };

                Ok(Term::Variable {
                    index,
                    type_: self.type_check_binding(&term, expected_type)?,
                })
            }

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

                Ok(Term::Literal(literal))
            }

            Term::UnaryOp(op, term) => {
                let term = self.type_check(&term, expected_type)?;

                let (trait_, function) = match op {
                    UnaryOp::Neg => ("Neg", "neg"),
                    UnaryOp::Not => ("Not", "not"),
                    UnaryOp::Deref => todo!(),
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
                        Term::UnaryOp(*op, Rc::new(term))
                    }

                    (UnaryOp::Deref, _) => todo!(),

                    _ => Term::Application {
                        abstraction: impl_.functions.get(&function).unwrap().clone(),
                        arguments: Rc::new([term]),
                    },
                })
            }

            Term::BinaryOp(op, left, right) => {
                let left = self.type_check(left, expected_type)?;

                let (expected_type, impl_and_function) = match op {
                    BinaryOp::And | BinaryOp::Or => (Type::Boolean, None),

                    _ => {
                        let (trait_, function) = match op {
                            BinaryOp::Add => ("Add", "add"),
                            BinaryOp::Sub => ("Sub", "sub"),
                            BinaryOp::Mul => ("Mul", "mul"),
                            BinaryOp::Div => ("Div", "div"),
                            BinaryOp::Rem => ("Rem", "rem"),
                            BinaryOp::AddAssign => ("AddAssign", "add_assign"),
                            BinaryOp::SubAssign => ("SubAssign", "sub_assign"),
                            BinaryOp::MulAssign => ("MulAssign", "mul_assign"),
                            BinaryOp::DivAssign => ("DivAssign", "div_assign"),
                            BinaryOp::RemAssign => ("RemAssign", "rem_assign"),
                            BinaryOp::Eq => ("PartialEq", "eq"),
                            BinaryOp::Ge => ("PartialOrd", "ge"),
                            BinaryOp::Gt => ("PartialOrd", "gt"),
                            BinaryOp::Le => ("PartialOrd", "le"),
                            BinaryOp::Lt => ("PartialOrd", "lt"),
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

                let branch_context = if let BinaryOp::And | BinaryOp::Or = op {
                    Some(BranchContext::new(&self.bindings))
                } else {
                    None
                };

                let right = self.type_check(right, Some(&expected_type))?;

                if let Some(branch_context) = branch_context {
                    branch_context.reset(&mut self.bindings);
                }

                let right_type = right.type_();

                match_types(&expected_type, &right_type)?;

                let type_ = left.type_();

                Ok(match (op, type_) {
                    (BinaryOp::And, _) => Term::And(Rc::new(left), Rc::new(right)),

                    (BinaryOp::Or, _) => Term::Or(Rc::new(left), Rc::new(right)),

                    (
                        BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Rem
                        | BinaryOp::Eq
                        | BinaryOp::Ge
                        | BinaryOp::Gt
                        | BinaryOp::Le
                        | BinaryOp::Lt,
                        Type::Integer(_),
                    ) => Term::BinaryOp(*op, Rc::new(left), Rc::new(right)),

                    (
                        BinaryOp::AddAssign
                        | BinaryOp::SubAssign
                        | BinaryOp::MulAssign
                        | BinaryOp::DivAssign
                        | BinaryOp::RemAssign,
                        Type::Integer(_),
                    ) => Term::Assignment {
                        left: Rc::new(left.clone()),
                        right: Rc::new(Term::BinaryOp(
                            match op {
                                BinaryOp::AddAssign => BinaryOp::Add,
                                BinaryOp::SubAssign => BinaryOp::Sub,
                                BinaryOp::MulAssign => BinaryOp::Mul,
                                BinaryOp::DivAssign => BinaryOp::Div,
                                BinaryOp::RemAssign => BinaryOp::Rem,
                                _ => unreachable!(),
                            },
                            Rc::new(left),
                            Rc::new(right),
                        )),
                    },

                    (
                        BinaryOp::AddAssign
                        | BinaryOp::SubAssign
                        | BinaryOp::MulAssign
                        | BinaryOp::DivAssign
                        | BinaryOp::RemAssign,
                        _,
                    ) => {
                        let (impl_, function) = impl_and_function.unwrap();

                        Term::Application {
                            abstraction: impl_.functions.get(&function).unwrap().clone(),
                            arguments: Rc::new([
                                Term::Reference {
                                    unique: true,
                                    term: Rc::new(left),
                                },
                                right,
                            ]),
                        }
                    }

                    (
                        BinaryOp::Eq | BinaryOp::Ge | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Lt,
                        _,
                    ) => {
                        let (impl_, function) = impl_and_function.unwrap();

                        Term::Application {
                            abstraction: impl_.functions.get(&function).unwrap().clone(),
                            arguments: Rc::new([
                                Term::Reference {
                                    unique: false,
                                    term: Rc::new(left),
                                },
                                Term::Reference {
                                    unique: false,
                                    term: Rc::new(right),
                                },
                            ]),
                        }
                    }

                    _ => {
                        let (impl_, function) = impl_and_function.unwrap();

                        Term::Application {
                            abstraction: impl_.functions.get(&function).unwrap().clone(),
                            arguments: Rc::new([left, right]),
                        }
                    }
                })
            }

            Term::Match { scrutinee, arms } => {
                let scrutinee = self.type_check(scrutinee, None)?;

                let scrutinee_type = scrutinee.type_();

                let mut my_expected_type = None;

                let mut branch_context = BranchContext::new(&self.bindings);

                let mut typed_arms = Vec::with_capacity(arms.len());

                // TODO: exhaustiveness check

                for arm in arms.iter() {
                    self.type_check_pattern(&arm.pattern, &scrutinee_type)?;

                    // TODO: push and pop pattern bindings

                    let guard = if let Some(guard) = &arm.guard {
                        let guard = self.type_check(guard, Some(&Type::Boolean))?;

                        let guard_type = guard.type_();

                        match_types(&Type::Boolean, &guard_type)?;

                        Some(guard)
                    } else {
                        None
                    };

                    let body =
                        self.type_check(&arm.body, my_expected_type.as_ref().or(expected_type));

                    branch_context.record_and_reset(&mut self.bindings);

                    let body = body?;

                    let body_type = body.type_();

                    if let Some(expected_type) = my_expected_type.as_ref() {
                        match_types(expected_type, &body_type)?
                    }

                    my_expected_type.get_or_insert(body_type);

                    typed_arms.push(MatchArm {
                        pattern: arm.pattern.clone(),
                        guard,
                        body,
                    });
                }

                branch_context.make_phi_nodes(&mut self.bindings);

                Ok(Term::Match {
                    scrutinee: Rc::new(scrutinee),
                    arms: typed_arms.into_iter().collect(),
                })
            }

            Term::Assignment { left, right } => {
                if let Term::Variable { index, .. } = left.deref() {
                    let index = *index;

                    let expected_type = self.type_check_binding_index(index, None)?;

                    if expected_type.is_some() && !self.bindings[index].mutable {
                        return Err(anyhow!("invalid assignment to immutable variable"));
                    }

                    let right = self.type_check(right, expected_type.as_ref())?;

                    let right_type = right.type_();

                    // TODO: check binding type ascription, if present

                    if let Some(expected_type) = expected_type {
                        match_types(&expected_type, &right_type)?;
                    }

                    self.bindings[index].term = Some(Rc::new(RefCell::new(BindingTerm {
                        status: BindingStatus::Typed,
                        term: right.clone(),
                    })));

                    Ok(Term::Assignment {
                        left: Rc::new(Term::Variable {
                            index,
                            type_: right_type,
                        }),
                        right: Rc::new(right),
                    })
                } else {
                    todo!("assignment to {left:?}")
                }
            }

            Term::Block(terms) => {
                let binding_count = self.bindings.len();

                let terms = terms
                    .iter()
                    .map(|term| self.type_check(term, None))
                    .collect::<Result<_>>();

                let binding_check = if terms.is_ok() {
                    self.type_check_bindings(binding_count)
                } else {
                    Ok(())
                };

                // TODO: check for bound values which implement Drop and insert the appropriate calls

                self.bindings.truncate(binding_count);

                binding_check?;

                Ok(Term::Block(terms?))
            }

            Term::Phi(terms) => {
                self.type_check_phi(terms, expected_type)?;

                Ok(Term::Phi(terms.clone()))
            }

            Term::Loop { label, body, .. } => {
                let label = *label;

                self.loops.push(Loop {
                    label,
                    expected_type: expected_type.cloned(),
                    break_terms: Vec::new(),
                    branch_context: BranchContext::new(&self.bindings),
                });

                let body = self.type_check(body, None);

                let mut loop_ = self.loops.pop().unwrap();

                loop_.branch_context.make_phi_nodes(&mut self.bindings);

                Ok(Term::Loop {
                    label,
                    body: Rc::new(body?),
                    type_: loop_
                        .break_terms
                        .iter()
                        .find_map(|term| match term.type_() {
                            Type::Never => None,
                            type_ => Some(type_.clone()),
                        })
                        .unwrap_or(Type::Never),
                })
            }

            Term::Break { label, term } => {
                let label = *label;

                if let Some((index, expected_type)) =
                    self.loops
                        .iter()
                        .enumerate()
                        .rev()
                        .find_map(|(index, loop_)| {
                            if label.is_none() || loop_.label == label {
                                Some((index, loop_.expected_type.clone()))
                            } else {
                                None
                            }
                        })
                {
                    let term = self.type_check(term, expected_type.as_ref());

                    let loop_ = &mut self.loops[index];

                    loop_.branch_context.record_and_reset(&mut self.bindings);

                    let term = term?;

                    if let Some(expected_type) =
                        loop_
                            .break_terms
                            .iter()
                            .find_map(|term| match term.type_() {
                                Type::Never => None,
                                type_ => Some(type_.clone()),
                            })
                    {
                        match_types(&expected_type, &term.type_())?;
                    }

                    loop_.break_terms.push(term.clone());

                    Ok(Term::Break {
                        label,
                        term: Rc::new(term),
                    })
                } else {
                    Err(anyhow!(
                        "break without matching loop{}",
                        if let Some(label) = label {
                            format!(" (label: {})", self.unintern(label))
                        } else {
                            String::new()
                        }
                    ))
                }
            }

            Term::Return { .. } => {
                todo!()
            }

            _ => Err(anyhow!("type checking not yet supported for term {term:?}")),
        }
    }

    fn type_check_phi(
        &mut self,
        terms: &[Option<Rc<RefCell<BindingTerm>>>],
        expected_type: Option<&Type>,
    ) -> Result<Option<Type>> {
        let mut my_expected_type = None;

        for term in terms.iter().filter_map(|term| term.as_ref()) {
            let type_ =
                self.type_check_binding(term, my_expected_type.as_ref().or(expected_type))?;

            if let Some(expected_type) = my_expected_type.as_ref() {
                match_types(expected_type, &type_)?;
            }

            my_expected_type.get_or_insert(type_);
        }

        Ok(my_expected_type)
    }

    fn type_check_binding_index(
        &mut self,
        index: usize,
        expected_type: Option<&Type>,
    ) -> Result<Option<Type>> {
        Ok(if let Some(term) = self.bindings[index].term.clone() {
            Some(self.type_check_binding(&term, expected_type)?)
        } else {
            None
        })
    }

    fn type_check_binding(
        &mut self,
        term: &RefCell<BindingTerm>,
        expected_type: Option<&Type>,
    ) -> Result<Type> {
        {
            let term = RefCell::borrow(term);

            match term.status {
                BindingStatus::Untyped => (),
                BindingStatus::Typed | BindingStatus::Evaluated => return Ok(term.term.type_()),
            }
        }

        let typed = self.type_check(&RefCell::borrow(term).term, expected_type)?;

        let type_ = typed.type_();

        *RefCell::borrow_mut(term) = BindingTerm {
            status: BindingStatus::Typed,
            term: typed,
        };

        Ok(type_)
    }

    fn type_check_bindings(&mut self, offset: usize) -> Result<()> {
        let indexes = self
            .bindings
            .iter()
            .enumerate()
            .skip(offset)
            .filter_map(|(index, binding)| {
                binding.term.as_ref().and_then(|term| {
                    if let BindingStatus::Untyped = term.borrow().status {
                        Some(index)
                    } else {
                        None
                    }
                })
            })
            .collect::<Vec<_>>();

        indexes
            .into_iter()
            .map(|index| {
                self.type_check(
                    &Term::Variable {
                        index,
                        type_: Type::Never,
                    },
                    None,
                )
                .map(drop)
            })
            .collect::<Result<()>>()
    }

    // Does this need to be a method of Env, or can we move it to Pattern?
    fn type_check_pattern(&mut self, pattern: &Pattern, expected_type: &Type) -> Result<()> {
        match_types(
            expected_type,
            match pattern {
                Pattern::Literal(literal) => &literal.type_,
            },
        )
    }

    fn stmt_to_term(&mut self, stmt: &Stmt) -> Result<Term> {
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
                            } else {
                                let name = self.intern(&ident.to_string());

                                let term = init
                                    .as_ref()
                                    .map(|(_, expr)| self.expr_to_term(expr))
                                    .transpose()?
                                    .map(|term| {
                                        Rc::new(RefCell::new(BindingTerm {
                                            status: BindingStatus::Untyped,
                                            term,
                                        }))
                                    });

                                self.bindings.push(Binding {
                                    name,
                                    mutable: mutability.is_some(),
                                    term: term.clone(),
                                });

                                Ok(Term::Let {
                                    name,
                                    mutable: mutability.is_some(),
                                    index: self.bindings.len() - 1,
                                    term,
                                })
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

                    Ok(Term::UnaryOp(
                        match op {
                            UnOp::Neg(_) => UnaryOp::Neg,
                            UnOp::Not(_) => UnaryOp::Not,
                            _ => return Err(anyhow!("operation not yet supported: {op:?}")),
                        },
                        term,
                    ))
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

                    Ok(Term::BinaryOp(
                        match op {
                            BinOp::And(_) => BinaryOp::And,
                            BinOp::Or(_) => BinaryOp::Or,
                            BinOp::Add(_) => BinaryOp::Add,
                            BinOp::Sub(_) => BinaryOp::Sub,
                            BinOp::Mul(_) => BinaryOp::Mul,
                            BinOp::Div(_) => BinaryOp::Div,
                            BinOp::Rem(_) => BinaryOp::Rem,
                            BinOp::Eq(_) => BinaryOp::Eq,
                            BinOp::Ge(_) => BinaryOp::Ge,
                            BinOp::Gt(_) => BinaryOp::Gt,
                            BinOp::Le(_) => BinaryOp::Le,
                            BinOp::Lt(_) => BinaryOp::Lt,
                            _ => return Err(anyhow!("operation not yet supported: {op:?}")),
                        },
                        left,
                        right,
                    ))
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
                        let name_string = ident.to_string();
                        let name = self.intern(&name_string);

                        Ok(Term::Variable {
                            index: self
                                .find_term(name)
                                .ok_or_else(|| anyhow!("symbol not found: {name_string}"))?,
                            type_: Type::Never,
                        })
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
                    let scrutinee = Rc::new(self.expr_to_term(cond)?);

                    let then = MatchArm {
                        pattern: Pattern::Literal(self.true_.clone()),
                        guard: None,
                        body: self.block_to_term(stmts)?,
                    };

                    let else_ = MatchArm {
                        pattern: Pattern::Literal(self.false_.clone()),
                        guard: None,
                        body: else_branch
                            .as_ref()
                            .map(|(_, expr)| self.expr_to_term(&expr))
                            .transpose()?
                            .unwrap_or_else(|| Term::Literal(self.unit.clone())),
                    };

                    Ok(Term::Match {
                        scrutinee,
                        arms: Rc::new([then, else_]),
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

            Expr::Assign(ExprAssign {
                left, right, attrs, ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::Assignment {
                        left: Rc::new(self.expr_to_term(left)?),
                        right: Rc::new(self.expr_to_term(right)?),
                    })
                }
            }

            Expr::AssignOp(ExprAssignOp {
                left,
                op,
                right,
                attrs,
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::BinaryOp(
                        match op {
                            BinOp::AddEq(_) => BinaryOp::AddAssign,
                            BinOp::SubEq(_) => BinaryOp::SubAssign,
                            BinOp::MulEq(_) => BinaryOp::MulAssign,
                            BinOp::DivEq(_) => BinaryOp::DivAssign,
                            BinOp::RemEq(_) => BinaryOp::RemAssign,
                            _ => return Err(anyhow!("operation not yet supported: {op:?}")),
                        },
                        Rc::new(self.expr_to_term(left)?),
                        Rc::new(self.expr_to_term(right)?),
                    ))
                }
            }

            Expr::Loop(ExprLoop {
                label,
                body: Block { stmts, .. },
                attrs,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::Loop {
                        label: label
                            .as_ref()
                            .map(|label| self.intern(&label.name.ident.to_string())),
                        body: Rc::new(self.block_to_term(stmts)?),
                        type_: Type::Never,
                    })
                }
            }

            Expr::Break(ExprBreak {
                label, expr, attrs, ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::Break {
                        label: label
                            .as_ref()
                            .map(|label| self.intern(&label.ident.to_string())),
                        term: Rc::new(
                            expr.as_ref()
                                .map(|expr| self.expr_to_term(&expr))
                                .transpose()?
                                .unwrap_or_else(|| Term::Literal(self.unit.clone())),
                        ),
                    })
                }
            }

            _ => Err(anyhow!("expr not yet supported: {expr:?}")),
        }
    }

    fn block_to_term(&mut self, stmts: &[Stmt]) -> Result<Term> {
        let binding_count = self.bindings.len();

        let result = stmts
            .iter()
            .map(|stmt| self.stmt_to_term(stmt))
            .collect::<Result<Vec<_>>>()
            .map(|terms| match &terms[..] {
                [] => Term::Literal(self.unit.clone()),

                terms => Term::Block(Rc::from(terms)),
            });

        self.bindings.truncate(binding_count);

        result
    }

    pub fn eval_file(&mut self, _file: &str) -> Result<Eval> {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use {super::*, std::sync::Once};

    fn eval<T: Copy + 'static>(line: &str) -> Result<T> {
        {
            static ONCE: Once = Once::new();

            ONCE.call_once(pretty_env_logger::init_timed);
        }

        Ok(*Env::new()
            .eval_line(line)?
            .value
            .value
            .downcast_ref::<T>()
            .unwrap())
    }

    #[test]
    fn int_literal() {
        assert_eq!(42_i32, eval("42").unwrap())
    }

    #[test]
    fn bool_literal() {
        assert!(eval::<bool>("true").unwrap())
    }

    #[test]
    fn if_expression() {
        assert_eq!(
            77_i32,
            eval("{ let x = false; if x { 27 } else { 77 } }").unwrap()
        )
    }

    #[test]
    fn bad_if_expression() {
        assert!(eval::<()>("{ let x = false; if x { 27 } else { true } }").is_err())
    }

    #[test]
    fn conditional_initialization() {
        assert_eq!(
            27_i32,
            eval("{ let x; if true { x = 27 } else { x = 77 } x }").unwrap()
        )
    }

    #[test]
    fn bad_conditional_initialization() {
        assert!(eval::<()>("{ let x; if true { x = 27 } else { x = true } x }").is_err())
    }

    #[test]
    fn assignment_to_mutable() {
        assert_eq!(7_i32, eval("{ let mut x = 27; x = 7; x }").unwrap())
    }

    #[test]
    fn conditional_assignment_to_mutable() {
        assert_eq!(
            7_i32,
            eval("{ let mut x; if true { x = 27 } x = 7; x }").unwrap()
        )
    }

    #[test]
    fn bad_assignment_to_immutable() {
        assert!(eval::<()>("{ let x = 27; x = 7; x }").is_err())
    }

    #[test]
    fn bad_conditional_assignment_to_immutable() {
        assert!(eval::<()>("{ let x; if true { x = 27 } x = 7; x }").is_err())
    }

    #[test]
    fn minimal_loop() {
        assert_eq!(9_i32, eval("loop { break 9 }").unwrap())
    }

    #[test]
    fn conditional_break() {
        assert_eq!(
            9_i32,
            eval("loop { if true { break 9 } else { break 7 } }").unwrap()
        )
    }

    #[test]
    fn bad_conditional_break() {
        assert!(eval::<()>("loop { if true { break 9 } else { break false } }").is_err())
    }

    #[test]
    fn loop_initialization() {
        assert_eq!(81_i32, eval("{ let x; loop { x = 81; break } x }").unwrap())
    }

    #[test]
    fn bad_loop_initialization() {
        assert!(eval::<()>("{ let x; loop { break; x = 81 } x }").is_err())
    }

    #[test]
    fn loop_a_few_times() {
        assert_eq!(
            11_i32,
            eval("{ let mut x = 0; loop { if x > 10 { break } x += 1; } x }").unwrap()
        )
    }
}
