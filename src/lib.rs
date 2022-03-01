#![deny(warnings)]
#![allow(dead_code)] // temporary

use {
    crate::allocator::Allocator,
    anyhow::{anyhow, Result},
    log::info,
    maplit::hashmap,
    std::{
        any,
        cell::RefCell,
        cmp::Ordering,
        collections::HashMap,
        error,
        fmt::{self, Display},
        mem,
        ops::{Add, Deref, Div, Mul, Neg, Rem, Sub},
        rc::{Rc, Weak},
        str,
        str::FromStr,
    },
    syn::{
        BinOp, Block, Expr, ExprAssign, ExprAssignOp, ExprBinary, ExprBlock, ExprBreak, ExprField,
        ExprIf, ExprLit, ExprLoop, ExprParen, ExprPath, ExprReference, ExprStruct, ExprUnary,
        Fields, FieldsNamed, FieldsUnnamed, Generics, ItemStruct, Lit, LitBool, Local, Member, Pat,
        PatIdent, Path, PathArguments, PathSegment, Stmt, TypePath, UnOp, Visibility,
    },
};

mod allocator;

trait FromBytes {
    fn from_bytes(bytes: &[u8]) -> Self;
}

impl FromBytes for () {
    fn from_bytes(bytes: &[u8]) -> Self {
        assert!(bytes.is_empty());
    }
}

macro_rules! integer_from_bytes {
    ($($type:ident),+) => {
        $(impl FromBytes for $type {
            fn from_bytes(bytes: &[u8]) -> Self {
                Self::from_ne_bytes(bytes.try_into().unwrap())
            }
        })+
    }
}

integer_from_bytes!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl FromBytes for bool {
    fn from_bytes(bytes: &[u8]) -> Self {
        u8::from_ne_bytes(bytes.try_into().unwrap()) != 0
    }
}

trait ToBytes: Sized {
    type Bytes: AsRef<[u8]>;

    fn to_bytes(self) -> Self::Bytes;
}

macro_rules! integer_to_bytes {
    ($($type:ident),+) => {
        $(impl ToBytes for $type {
            type Bytes = [u8; mem::size_of::<Self>()];

            fn to_bytes(self) -> Self::Bytes {
                self.to_ne_bytes()
            }
        })+
    }
}

integer_to_bytes!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

macro_rules! integer_op_cases {
    ($fn:ident, $discriminator:expr, $arg:expr, $($pattern:pat, $type:path),+) => {
        match $discriminator {
            $($pattern => $fn::<$type>($arg)),+,
            _ => unreachable!(),
        }
    }
}

macro_rules! integer_op {
    ($fn:ident, $discriminator:expr, $arg:expr) => {
        integer_op_cases!(
            $fn,
            $discriminator,
            $arg,
            Integer::U8,
            u8,
            Integer::U16,
            u16,
            Integer::U32,
            u32,
            Integer::U64,
            u64,
            Integer::U128,
            u128,
            Integer::Usize,
            usize,
            Integer::I8,
            i8,
            Integer::I16,
            i16,
            Integer::I32,
            i32,
            Integer::I64,
            i64,
            Integer::I128,
            i128,
            Integer::Isize,
            isize
        )
    };
}

macro_rules! integer_signed_op {
    ($fn:ident, $discriminator:expr, $arg:expr) => {
        integer_op_cases!(
            $fn,
            $discriminator,
            $arg,
            Integer::I8,
            i8,
            Integer::I16,
            i16,
            Integer::I32,
            i32,
            Integer::I64,
            i64,
            Integer::I128,
            i128,
            Integer::Isize,
            isize
        )
    };
}

fn add<T: FromBytes + ToBytes + Add<T, Output = T>>(env: &mut Env) {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a + b);
}

fn sub<T: FromBytes + ToBytes + Sub<T, Output = T>>(env: &mut Env) {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a - b);
}

fn mul<T: FromBytes + ToBytes + Mul<T, Output = T>>(env: &mut Env) {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a * b);
}

fn div<T: FromBytes + ToBytes + Div<T, Output = T>>(env: &mut Env) {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a / b);
}

fn rem<T: FromBytes + ToBytes + Rem<T, Output = T>>(env: &mut Env) {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a % b);
}

macro_rules! integer_binary_ops_cases {
    ($op_discriminator:expr, $type_discriminator:expr, $left:expr, $right:expr, $($pattern:pat, $fn:ident),+) => {
        match $op_discriminator {
            $($pattern => integer_op!($fn, $type_discriminator, ($left, $right))),+,
            _ => unreachable!(),
        }
    }
}

macro_rules! integer_binary_ops {
    ($op_discriminator:expr, $type_discriminator:expr, $left:expr, $right:expr) => {
        integer_binary_ops_cases!(
            $op_discriminator,
            $type_discriminator,
            $left,
            $right,
            BinaryOp::Add,
            add,
            BinaryOp::Sub,
            sub,
            BinaryOp::Mul,
            mul,
            BinaryOp::Div,
            div,
            BinaryOp::Rem,
            rem
        )
    };
}

fn eq<T: FromBytes + ToBytes + PartialEq<T>>((a, b): (&[u8], &[u8])) -> bool {
    T::from_bytes(a).eq(&T::from_bytes(b))
}

fn ge<T: FromBytes + ToBytes + PartialOrd<T>>((a, b): (&[u8], &[u8])) -> bool {
    T::from_bytes(a).ge(&T::from_bytes(b))
}

fn gt<T: FromBytes + ToBytes + PartialOrd<T>>((a, b): (&[u8], &[u8])) -> bool {
    T::from_bytes(a).gt(&T::from_bytes(b))
}

fn le<T: FromBytes + ToBytes + PartialOrd<T>>((a, b): (&[u8], &[u8])) -> bool {
    T::from_bytes(a).le(&T::from_bytes(b))
}

fn lt<T: FromBytes + ToBytes + PartialOrd<T>>((a, b): (&[u8], &[u8])) -> bool {
    T::from_bytes(a).lt(&T::from_bytes(b))
}

macro_rules! integer_comparison_ops_cases {
    ($op_discriminator:expr, $type_discriminator:expr, $left:expr, $right:expr, $($pattern:pat, $fn:ident),+) => {
        match $op_discriminator {
            $($pattern => integer_op!($fn, $type_discriminator, ($left, $right))),+,
            _ => unreachable!(),
        }
    }
}

macro_rules! integer_comparison_ops {
    ($op_discriminator:expr, $type_discriminator:expr, $left:expr, $right:expr) => {
        integer_comparison_ops_cases!(
            $op_discriminator,
            $type_discriminator,
            $left,
            $right,
            BinaryOp::Eq,
            eq,
            BinaryOp::Ge,
            ge,
            BinaryOp::Gt,
            gt,
            BinaryOp::Le,
            le,
            BinaryOp::Lt,
            lt
        )
    };
}

macro_rules! integer_suffix_op_cases {
    ($fn:ident, $discriminator:expr, $arg:expr, $($pattern:pat, $variant:expr, $type:path),+) => {
        match $discriminator {
            $($pattern => $fn::<$type>($arg, $variant)),+,
            _ => unreachable!(),
        }
    }
}

macro_rules! integer_suffix_op {
    ($fn:ident, $discriminator:expr, $arg:expr) => {
        integer_suffix_op_cases!(
            $fn,
            $discriminator,
            $arg,
            "u8",
            Integer::U8,
            u8,
            "u16",
            Integer::U16,
            u16,
            "u32",
            Integer::U32,
            u32,
            "u64",
            Integer::U64,
            u64,
            "u128",
            Integer::U128,
            u128,
            "usize",
            Integer::Usize,
            usize,
            "i8",
            Integer::I8,
            i8,
            "i16",
            Integer::I16,
            i16,
            "i32",
            Integer::I32,
            i32,
            "i64",
            Integer::I64,
            i64,
            "i128",
            Integer::I128,
            i128,
            "isize",
            Integer::Isize,
            isize
        )
    };
}

impl ToBytes for () {
    type Bytes = [u8; 0];

    fn to_bytes(self) -> Self::Bytes {
        []
    }
}

impl ToBytes for bool {
    type Bytes = [u8; 1];

    fn to_bytes(self) -> Self::Bytes {
        [if self { 1 } else { 0 }]
    }
}

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
    fn parse(self, value: &str) -> Result<Rc<[u8]>> {
        fn parse<T: ToBytes + FromStr>(value: &str) -> Result<Rc<[u8]>>
        where
            <T as FromStr>::Err: error::Error + Send + Sync + 'static,
        {
            Ok(value.parse::<T>()?.to_rc())
        }

        integer_op!(parse, self, value)
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

// todo: will need more fields here for associated types, functions, etc.
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
struct Trait {
    name: Identifier,
    parameters: Rc<[Type]>,
}

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
        // todo: add lifetime field
        unique: bool,
        type_: Rc<Type>,
    },
    Slice(Rc<Type>, Lifetime),
    Str(Lifetime),
    Function {
        parameters: Rc<[Type]>,
        ret: Rc<Type>,
    },
    Nominal {
        // todo: add lifetime arguments
        definition: Weak<RefCell<Item>>,
        arguments: Rc<[Type]>,
    },
    Unresolved(Identifier),
}

impl Type {
    fn size(&self) -> usize {
        match self {
            Type::Unit => 0,
            Type::Boolean => 1,
            Type::Integer(type_) => match type_ {
                Integer::U8 | Integer::I8 => 1,
                Integer::U16 | Integer::I16 => 2,
                Integer::U32 | Integer::I32 => 4,
                Integer::U64 | Integer::I64 => 8,
                Integer::Usize | Integer::Isize => mem::size_of::<usize>(),
                Integer::U128 | Integer::I128 => 16,
            },
            Type::Nominal { definition, .. } => {
                if let Item::Struct { fields, .. } =
                    RefCell::borrow(&definition.upgrade().unwrap()).deref()
                {
                    // todo: precalculate and store this during typechecking (and be sure to detect and flag infinite types)
                    fields
                        .values()
                        .max_by(|a, b| a.offset.cmp(&b.offset))
                        .map(|max| max.offset + max.type_.size())
                        .unwrap_or(0)
                } else {
                    todo!("size for {self:?}")
                }
            }
            _ => todo!("size for {self:?}"),
        }
    }
}

#[derive(Clone, Debug)]
struct Literal {
    offset: usize,
    type_: Type,
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
    // todo: support type and lifetime parameters.
    parameters: Rc<[Parameter]>,
    body: Rc<Term>,
}

#[derive(Clone, Debug)]
enum Pattern {
    Literal(Literal),
    // todo: support other patterns
}

#[derive(Clone, Debug)]
struct MatchArm {
    pattern: Pattern,
    guard: Option<Term>,
    body: Term,
}

#[derive(Clone, Debug)]
struct Reference {
    // todo: add lifetime field
    unique: bool,
    term: Term,
}

impl Reference {
    fn deref_type(&self) -> Type {
        self.term.type_()
    }

    fn type_(&self) -> Type {
        Type::Reference {
            unique: self.unique,
            type_: Rc::new(self.deref_type()),
        }
    }
}

#[derive(Clone, Debug)]
enum Term {
    Block {
        scope: Scope,
        terms: Rc<[Term]>,
    },
    Literal(Literal),
    Reference(Rc<Reference>),
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
        // todo: support type and lifetime arguments.
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
    Struct {
        type_: Type,
        arguments: Rc<HashMap<Identifier, Term>>,
    },
    Field {
        base: Rc<Term>,
        name: Identifier,
    },
}

impl Term {
    fn type_(&self) -> Type {
        match self {
            Self::Block { terms, .. } => {
                terms.last().map(|term| term.type_()).unwrap_or(Type::Unit)
            }
            Self::Literal(literal) => literal.type_.clone(),
            // todo: the return type of an abstraction may be a function of its type parameters
            Self::Application {
                abstraction: Abstraction { body, .. },
                ..
            } => body.type_(),
            Self::And { .. } | Self::Or { .. } => Type::Boolean,
            Self::UnaryOp(op, term) => match op {
                UnaryOp::Neg | UnaryOp::Not => term.type_(),
                UnaryOp::Deref => match term.type_() {
                    Type::Reference { type_, .. } => type_.deref().clone(),
                    type_ => unreachable!("expected reference to deref, got {:?}", type_),
                },
            },
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
                RefCell::borrow(terms.iter().find_map(|term| term.as_ref()).unwrap()).type_()
            }
            Self::Reference(reference) => reference.type_(),
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

#[derive(Clone, Debug)]
enum BindingTerm {
    Reserved(Literal),
    Typed(Term),
    Untyped(Term),
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
                Some(Rc::new(RefCell::new(BindingTerm::Untyped(Term::Phi(
                    terms,
                )))))
            }
        }
    }
}

#[derive(Debug)]
enum EvalException {
    Break { label: Option<Identifier> },
    Return,
    Overflow,
}

pub struct Eval {
    value: EvalTerm,
    new_term_bindings: HashMap<Rc<str>, Option<Rc<RefCell<BindingTerm>>>>,
}

impl fmt::Display for Eval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut need_newline = match &self.value.type_() {
            Type::Unit => false,
            _ => {
                self.value.fmt(f)?;
                true
            }
        };

        for (symbol, term) in &self.new_term_bindings {
            if need_newline {
                writeln!(f)?;
            }

            symbol.fmt(f)?;

            if let Some(term) = term {
                match RefCell::borrow(term).deref() {
                    BindingTerm::Evaluated(term) => write!(f, " = {term}"),
                    BindingTerm::Typed(term) | BindingTerm::Untyped(term) => {
                        write!(f, " = {term:?}")
                    }
                }?;
            }

            need_newline = true;
        }

        Ok(())
    }
}

fn match_types(expected: &Type, actual: &Type) -> Result<()> {
    // todo: this will need to be refined once we start doing unification, and we'll probably need to move this
    // function into Env's impl

    if expected != &Type::Never && actual != &Type::Never && expected != actual {
        Err(anyhow!(
            "type mismatch: expected {expected:?}, got {actual:?}"
        ))
    } else {
        Ok(())
    }
}

struct Field {
    type_: Type,
    offset: usize,
}

enum Item {
    Struct {
        parameters: Rc<[Type]>,
        fields: Rc<HashMap<Identifier, Field>>,
        methods: Rc<[Abstraction]>,
    },
    Type(Type),
}

struct Scope {
    items: HashMap<Identifier, Rc<RefCell<Item>>>,
}

impl Scope {
    fn new() -> Self {
        Self {
            items: HashMap::new(),
        }
    }
}

impl Default for Scope {
    fn default() -> Self {
        Self::new()
    }
}

struct StackData {
    bottom: usize,
    top: usize,
    offset: usize,
}

pub struct Env {
    heap: Box<[u8]>,
    allocator: Allocator,
    stack: StackData,
    ids_to_names: Vec<Rc<str>>,
    names_to_ids: HashMap<Rc<str>, usize>,
    scopes: Vec<Scope>,
    bindings: Vec<Binding>,
    loops: Vec<Loop>,
    traits: HashMap<Identifier, Trait>,
    impls: HashMap<(Type, Trait), Option<Impl>>,
    unit: Literal,
    true_: Literal,
    false_: Literal,
}

const DEFAULT_HEAP_SIZE: usize = 1024 * 1024;
const DEFAULT_STACK_SIZE: usize = DEFAULT_HEAP_SIZE / 2;

impl Default for Env {
    fn default() -> Self {
        Self::try_new(DEFAULT_HEAP_SIZE, DEFAULT_STACK_SIZE).unwrap()
    }
}

impl Env {
    pub fn try_new(heap_size: usize, stack_size: usize) -> Result<Self> {
        let mut allocator = Allocator::new(heap_size);

        // allocate dummy region so that we know no real object will ever be allocated at offset zero
        let padding = 8;

        allocator
            .allocate(padding)
            .ok_or_else(|| anyhow!("heap size must be at least {padding}"));

        let bottom = allocator.allocate(stack_size).ok_or_else(|| {
            anyhow!("stack size must be less than or equal to heap size + {padding}")
        });

        let stack = StackData {
            bottom,
            top: bottom + stack_size,
            offset: bottom,
        };

        let mut heap = vec![0; heap_size].into_boxed_slice();

        let true_offset = 4;
        heap[true_offset] = 1;

        let false_offset = 5;

        let mut env = Self {
            heap,
            allocator,
            stack,
            ids_to_names: Vec::new(),
            names_to_ids: HashMap::new(),
            scopes: vec![Scope::new(), Scope::new()],
            bindings: Vec::new(),
            loops: Vec::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
            unit: Literal {
                offset: allocator.allocate(0),
                type_: Type::Unit,
            },
            true_: Literal {
                true_offset,
                type_: Type::Boolean,
            },
            false_: Literal {
                false_offset,
                type_: Type::Boolean,
            },
        };

        // todo: should load types, traits and impls from core/std source files (lazily if appropriate)

        env.scopes[0].items = [
            ("()", Type::Unit),
            ("bool", Type::Boolean),
            ("u8", Type::Integer(Integer::U8)),
            ("u16", Type::Integer(Integer::U16)),
            ("u32", Type::Integer(Integer::U32)),
            ("u64", Type::Integer(Integer::U64)),
            ("u128", Type::Integer(Integer::U128)),
            ("usize", Type::Integer(Integer::Usize)),
            ("i8", Type::Integer(Integer::I8)),
            ("i16", Type::Integer(Integer::I16)),
            ("i32", Type::Integer(Integer::I32)),
            ("i64", Type::Integer(Integer::I64)),
            ("i128", Type::Integer(Integer::I128)),
            ("isize", Type::Integer(Integer::Isize)),
        ]
        .into_iter()
        .map(|(name, type_)| (env.intern(name), Rc::new(RefCell::new(Item::Type(type_)))))
        .collect();

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
            (UnaryOp::Not, "Deref", "deref", &[]),
            (UnaryOp::Not, "DerefMut", "deref_mut", &[]),
        ];

        for (op, name, function, types) in unaries {
            let name = env.intern(name);
            let function = env.intern(function);
            let trait_ = Trait {
                name,
                parameters: Rc::new([]),
            };

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
            let trait_ = Trait {
                name,
                parameters: Rc::new([]),
            };

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
            let trait_ = Trait {
                name,
                parameters: Rc::new([]),
            };

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
            let trait_ = Trait {
                name,
                parameters: Rc::new([]),
            };

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

        Ok(env)
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

        // todo: convert stmt to a term (if it's an expression), then typecheck it, then lower it to something
        // MIR-like, then borrow-check it, then evaluate it.
        //
        // If it's not an expression (i.e. it's an item), update the relevant symbol tables.  If it's an item with
        // code inside (e.g. an impl block or fn) do all of the above except evaluation.

        let binding_count = self.bindings.len();

        let term = &self.stmt_to_term(&stmt)?;

        self.type_check_scope(0)?;

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
                .map(|binding| (self.unintern(binding.name), binding.term.clone()))
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

    fn intern_member(&mut self, member: &Member) -> Identifier {
        self.intern(&match member {
            Member::Named(ident) => ident.to_string(),
            Member::Unnamed(index) => index.index.to_string(),
        })
    }

    fn unintern(&self, Identifier(id): Identifier) -> Rc<str> {
        self.ids_to_names[id].clone()
    }

    fn get_impl(&mut self, type_: &Type, trait_: &Trait) -> Option<Impl> {
        if let Some(result) = self.impls.get(&(type_.clone(), trait_.clone())) {
            result.clone()
        } else {
            let impl_ = self.get_blanket_impl(type_, trait_);

            self.impls
                .insert((type_.clone(), trait_.clone()), impl_.clone());

            impl_
        }
    }

    fn get_blanket_impl(&mut self, type_: &Type, trait_: &Trait) -> Option<Impl> {
        if let Type::Reference { unique, .. } = type_ {
            if trait_.name == self.intern("Deref") {
                let self_type = Type::Reference {
                    unique: false,
                    type_: Rc::new(type_.clone()),
                };

                let function = self.intern("deref");

                let abstraction = Abstraction {
                    parameters: Rc::new([Parameter {
                        name: self.intern("self"),
                        mutable: false,
                        type_: self_type.clone(),
                    }]),
                    body: Rc::new(Term::Variable {
                        index: 0,
                        type_: self_type,
                    }),
                };

                return Some(Impl {
                    arguments: Rc::new([]),
                    functions: Rc::new(hashmap![function => abstraction]),
                });
            } else if *unique && trait_.name == self.intern("DerefMut") {
                let self_type = Type::Reference {
                    unique: true,
                    type_: Rc::new(type_.clone()),
                };

                let function = self.intern("deref_mut");

                let abstraction = Abstraction {
                    parameters: Rc::new([Parameter {
                        name: self.intern("self"),
                        mutable: false,
                        type_: self_type.clone(),
                    }]),
                    body: Rc::new(Term::Variable {
                        index: 0,
                        type_: self_type,
                    }),
                };

                return Some(Impl {
                    arguments: Rc::new([]),
                    functions: Rc::new(hashmap![function => abstraction]),
                });
            }
        }

        // todo: search for matching blanket impl and, if found, monomophize it and return the result.
        None
    }

    fn eval_term(&mut self, term: &Term) -> Result<(), EvalException> {
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

                    *term = BindingTerm::Reserved(match term.deref() {
                        BindingTerm::Typed(term) => {
                            let offset = self.stack.offset;

                            self.eval_term(term)?;

                            Literal {
                                offset,
                                type_: term.type_(),
                            }
                        }
                        _ => unreachable!(),
                    });
                }

                Ok(EvalTerm::Value(self.unit.clone()))
            }

            Term::Variable { index, .. } => {
                if let BindingTerm::Reserved(term) =
                    RefCell::borrow(self.bindings[*index].term.as_ref().unwrap()).deref()
                {
                    let src = term.offset;
                    let size = term.type_().size();
                    let dest = self.stack.offset;

                    self.reserve(size);

                    self.heap.copy_within(src..(src + size), dest);
                } else {
                    panic!("unexpected binding term variant: {term:?}")
                }
            }

            Term::Literal(term) => {
                let src = term.offset;
                let size = term.type_().size();
                let dest = self.stack.offset;

                self.reserve(size);

                self.heap.copy_within(src..(src + size), dest);
            }

            Term::Application {
                abstraction:
                    Abstraction {
                        body, parameters, ..
                    },
                arguments,
            } => {
                let offset = self.stack.offset;

                let mut parameters = arguments
                    .iter()
                    .zip(parameters.iter())
                    .map(|(term, Parameter { name, mutable, .. })| {
                        let offset = self.stack.offset;

                        self.eval_term(term)?;

                        Ok(Binding {
                            name: *name,
                            mutable: *mutable,
                            term: Some(Rc::new(RefCell::new(BindingTerm::Reserved(Literal {
                                type_: term.type_(),
                                offset,
                            })))),
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                mem::swap(&mut parameters, &mut self.bindings);

                let result = self.eval_term(body);

                mem::swap(&mut parameters, &mut self.bindings);

                self.stack.offset = offset;

                return result;
            }

            Term::And(left, right) => {
                self.eval_term(left)?;

                if !self.pop::<bool>() {
                    return self.eval_term(right);
                } else {
                    self.push(false);
                }
            }

            Term::Or(left, right) => {
                self.eval_term(left)?;

                if self.pop::<bool>() {
                    return self.eval_term(right);
                } else {
                    self.push(true);
                }
            }

            Term::UnaryOp(op, term) => {
                fn neg<T: FromBytes + ToBytes + Neg<Output = T>>(env: &mut Env) {
                    let tmp = env.pop::<T>();
                    env.push(-tmp);
                }

                self.eval_term(term)?;

                match op {
                    UnaryOp::Neg => match term.type_() {
                        Type::Integer(integer_type) => integer_signed_op!(neg, integer_type, self),

                        _ => unreachable!(),
                    },

                    UnaryOp::Not => {
                        let tmp = self.pop::<bool>();
                        self.push(!tmp);
                    }

                    UnaryOp::Deref => {
                        if let Term::Reference(reference) = term {
                            let src = self.pop::<usize>();
                            let size = reference.deref_type().size();
                            let dest = self.stack.offset;

                            self.reserve(size);

                            self.heap.copy_within(src..(src + size), dest);
                        } else {
                            unreachable!()
                        }
                    }
                }
            }

            Term::BinaryOp(op, left, right) => {
                self.eval_term(left)?;
                self.eval_term(right)?;

                match left.type_ {
                    Type::Integer(integer_type) => match op {
                        BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Rem => integer_binary_ops!(op, integer_type, self),

                        BinaryOp::Eq
                        | BinaryOp::Ge
                        | BinaryOp::Gt
                        | BinaryOp::Le
                        | BinaryOp::Lt => integer_comparison_ops!(op, integer_type, self),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            }

            Term::Match { scrutinee, arms } => {
                self.eval_term(scrutinee)?;

                for arm in arms.iter() {
                    if self.match_pattern(&arm.pattern) {
                        // todo: push and pop pattern bindings

                        let match_guard = if let Some(guard) = &arm.guard {
                            self.eval_term(guard)?;

                            self.pop::<bool>()
                        } else {
                            true
                        };

                        if match_guard {
                            self.eval_term(&arm.body);

                            return Ok(());
                        }
                    }
                }

                unreachable!(
                    "exhaustiveness checking during type checking should prevent reaching this point"
                )
            }

            Term::Assignment { left, right } => {
                let base = self.stack.offset;

                self.eval_term(right)?;

                let offset = match left.deref() {
                    Term::Variable { index, .. } => {
                        if let BindingTerm::Reserved(value) =
                            RefCell::borrow(&self.bindings[*index].term).deref()
                        {
                            value.offset
                        } else {
                            unreachable!()
                        }
                    }

                    Term::UnaryOp(UnaryOp::Deref, left) => self.offset_of(left),

                    _ => todo!("assignment to {left:?}"),
                };

                let size = right.type_.size();

                self.reserve(size)?;

                self.heap.copy_within(base..(base + size), offset);

                self.stack.offset = limit;
            }

            Term::Block { terms, .. } => {
                let binding_count = self.bindings.len();

                let offset = self.stack.offset;

                let terms = terms.iter().try_for_each(|term| {
                    let result = self.eval_term(term);

                    self.stack.offset = offset;

                    result
                });

                self.bindings.truncate(binding_count);

                Ok(terms?.into_iter().last().unwrap())
            }

            Term::Loop { label, body, .. } => loop {
                match self.eval_term(body) {
                    Ok(_) => (),

                    Err(EvalException::Break { label: break_label })
                        if break_label.is_none() || break_label == *label =>
                    {
                        break
                    }

                    err => return err,
                }
            },

            Term::Break { label, term } => {
                return Err(EvalException::Break {
                    label: *label,
                    result: self.eval_term(term)?,
                })
            }

            Term::Return { term } => {
                return Err(EvalException::Return {
                    result: self.eval_term(term)?,
                })
            }

            Term::Reference(Reference { unique, term, path }) => {
                self.push(self.offset_of(term))?;
            }

            Term::Struct { type_, arguments } => {
                let fields = if let Type::Nominal { definition, .. } = &type_ {
                    if let Item::Struct { fields, .. } =
                        RefCell::borrow(&definition.upgrade().unwrap()).deref()
                    {
                        fields
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                };

                let base = self.stack.offset;

                let size = type_.size();

                self.reserve(size)?;

                let offset = self.stack.offset;

                for (name, term) in arguments.deref() {
                    let field = fields.get(name).unwrap();

                    self.eval_term(term)?;

                    self.heap.copy_within(
                        offset..offset + field.type_.size(),
                        base_offset + field.offset,
                    );

                    self.stack.offset = offset;
                }
            }

            Term::Field { base, name } => {
                let field = if let Type::Nominal { definition, .. } = &base.type_() {
                    if let Item::Struct { fields, .. } =
                        RefCell::borrow(&definition.upgrade().unwrap()).deref()
                    {
                        fields.get(name).unwrap()
                    } else {
                        unreachable!()
                    }
                } else {
                    todo!("field access through references, smart pointers, etc.")
                };

                self.eval_term(base)?;

                let base_offset = self.stack.offset - base.type_().size();

                let field_offset = base_offset + field.offset;

                self.heap.copy_within(
                    field_offset..(field_offset + field.type_.size()),
                    base_offset,
                );
                self.stack.offset = base_offset;
            }

            _ => todo!("evaluation not yet supported for term {term:?}"),
        }

        Ok(())
    }

    // Does this need to be a method of Env, or can we move it to Pattern?
    fn match_pattern(&mut self, pattern: &Pattern, scrutinee: &EvalTerm) -> bool {
        match scrutinee {
            EvalTerm::Value(scrutinee) => match pattern {
                Pattern::Literal(literal) => match &scrutinee.type_ {
                    Type::Boolean => {
                        u8::from_ne_bytes(literal.value.deref().try_into().unwrap())
                            == u8::from_ne_bytes(scrutinee.value.deref().try_into().unwrap())
                    }

                    Type::Integer(integer_type) => {
                        integer_op!(eq, integer_type, (&literal.value, &scrutinee.value))
                    }

                    _ => todo!("literal match for {:?}", scrutinee.type_),
                },
            },

            _ => todo!("match for {:?}", scrutinee),
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
                        if let BindingTerm::Typed(Term::Phi(terms)) = RefCell::borrow(term).deref()
                        {
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
                    type_: self.type_check_binding(&term, expected_type)?.type_(),
                })
            }

            Term::Literal(Literal { offset, type_ }) => {
                let offset = *offset;

                let literal = if let Type::Integer(Integer::Unknown) = type_ {
                    let string = str::from_utf8(self.load_slice(offset)).unwrap().to_owned();

                    match expected_type.cloned() {
                        Some(Type::Integer(integer_type)) => Literal {
                            value: self.store(integer_type.parse(&string)?),
                            type_: Type::Integer(integer_type),
                        },

                        _ => Literal {
                            value: self.store(string.parse::<i32>()?),
                            type_: Type::Integer(Integer::I32),
                        },
                    }
                } else {
                    Literal {
                        offset,
                        type_: type_.clone(),
                    }
                };

                Ok(Term::Literal(literal))
            }

            Term::UnaryOp(op, term) => {
                let term = self.type_check(term, expected_type)?;

                let (trait_, function) = match op {
                    UnaryOp::Neg => ("Neg", "neg"),
                    UnaryOp::Not => ("Not", "not"),
                    UnaryOp::Deref => ("Deref", "deref"),
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
                    (UnaryOp::Neg, Type::Integer(_))
                    | (UnaryOp::Not, Type::Boolean)
                    | (UnaryOp::Deref, Type::Reference { .. }) => Term::UnaryOp(*op, Rc::new(term)),

                    (UnaryOp::Deref, _) => Term::UnaryOp(
                        *op,
                        Rc::new(Term::Application {
                            abstraction: impl_.functions.get(&function).unwrap().clone(),
                            arguments: Rc::new([self.shared_reference(&term)?]),
                        }),
                    ),

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
                            arguments: Rc::new([self.unique_reference(&left)?, right]),
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
                                self.shared_reference(&left)?,
                                self.shared_reference(&right)?,
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

                // todo: exhaustiveness check

                for arm in arms.iter() {
                    self.type_check_pattern(&arm.pattern, &scrutinee_type)?;

                    // todo: push and pop pattern bindings

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
                let right = self.type_check(right, expected_type)?;

                let right_type = right.type_();

                if let Term::Variable { index, .. } = left.deref() {
                    let index = *index;

                    let expected_type = self.type_check_binding_index(index, None)?;

                    if expected_type.is_some() && !self.bindings[index].mutable {
                        return Err(anyhow!("invalid assignment to immutable variable"));
                    }

                    // todo: check binding type ascription, if present

                    if let Some(expected_type) = expected_type {
                        match_types(&expected_type, &right_type)?;
                    }

                    self.bindings[index].term =
                        Some(Rc::new(RefCell::new(BindingTerm::Typed(right.clone()))));

                    Ok(Term::Assignment {
                        left: Rc::new(Term::Variable {
                            index,
                            type_: right_type,
                        }),
                        right: Rc::new(right),
                    })
                } else if let Term::UnaryOp(UnaryOp::Deref, left) = self.type_check(left, None)? {
                    if let Type::Reference {
                        unique,
                        type_: expected_type,
                    } = left.type_()
                    {
                        if unique {
                            match_types(&expected_type, &right_type)?;

                            Ok(Term::Assignment {
                                left: Rc::new(Term::UnaryOp(UnaryOp::Deref, left)),
                                right: Rc::new(right),
                            })
                        } else {
                            Err(anyhow!("cannot assign to shared reference"))
                        }
                    } else {
                        unreachable!()
                    }
                } else {
                    todo!("assignment to {left:?}")
                }
            }

            Term::Block { scope, terms } => {
                let binding_count = self.bindings.len();
                let scope_count = self.scopes.len();

                self.scopes.push(scope);

                let scope_check = self.type_check_scope(scope_count);

                let terms = if scope_check.is_ok() {
                    terms
                        .iter()
                        .map(|term| self.type_check(term, None))
                        .collect::<Result<_>>()
                } else {
                    Ok(Rc::from(&[] as &[_]))
                };

                let binding_check = if scope_check.is_ok() && terms.is_ok() {
                    self.type_check_bindings(binding_count)
                } else {
                    Ok(())
                };

                let scope = self.scopes.pop().unwrap();

                // todo: check for bound values which implement Drop and insert the appropriate calls

                self.bindings.truncate(binding_count);

                scope_check?;
                binding_check?;

                Ok(Term::Block {
                    scope,
                    terms: terms?,
                })
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
                            type_ => Some(type_),
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
                                type_ => Some(type_),
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

            // todo: convert temporaries to bindings and variables as needed to ensure all references are to either
            // variables or field access chains to variables.
            Term::Reference(Reference { unique, term, .. }) => Ok(Term::Reference(Reference {
                unique: *unique,
                term: self.type_check(
                    term,
                    expected_type.and_then(|expected| {
                        if let Type::Reference { type_, .. } = expected {
                            Some(type_.deref())
                        } else {
                            None
                        }
                    }),
                )?,
            })),

            Term::Struct { type_, arguments } => {
                let mut type_ = type_.clone();

                let name = if let Type::Unresolved(name) = &type_ {
                    *name
                } else {
                    unreachable!()
                };

                self.resolve_type(&mut type_, None)?;

                if let Type::Nominal { definition, .. } = &type_ {
                    if let Item::Struct { fields, .. } =
                        RefCell::borrow(&definition.upgrade().unwrap()).deref()
                    {
                        return if !fields.keys().all(|name| arguments.contains_key(name)) {
                            Err(anyhow!("fields missing in struct initializer"))
                        } else {
                            Ok(Term::Struct {
                                type_,
                                arguments: Rc::new(
                                    arguments
                                        .iter()
                                        .map(|(name, term)| {
                                            if let Some(Field {
                                                type_: expected_type,
                                                ..
                                            }) = fields.get(name)
                                            {
                                                let term =
                                                    self.type_check(term, Some(expected_type))?;

                                                match_types(expected_type, &term.type_())?;

                                                Ok((*name, term))
                                            } else {
                                                Err(anyhow!(
                                                    "no such field: {}",
                                                    self.unintern(*name)
                                                ))
                                            }
                                        })
                                        .collect::<Result<_>>()?,
                                ),
                            })
                        };
                    }
                }

                Err(anyhow!(
                    "attempt to initialize non-struct {} as a struct",
                    self.unintern(name)
                ))
            }

            Term::Field { base, name } => {
                let base = self.type_check(base, None)?;

                if let Type::Nominal { definition, .. } = &base.type_() {
                    if let Item::Struct { fields, .. } =
                        RefCell::borrow(&definition.upgrade().unwrap()).deref()
                    {
                        return if fields.contains_key(name) {
                            Ok(Term::Field {
                                base: Rc::new(base),
                                name: *name,
                            })
                        } else {
                            Err(anyhow!("no such field: {}", self.unintern(*name)))
                        };
                    }
                }

                // todo: field access through references, smart pointers, etc.
                Err(anyhow!("attempt to resolve a field of non-struct value"))
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
            let type_ = self
                .type_check_binding(term, my_expected_type.as_ref().or(expected_type))?
                .type_();

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
            Some(self.type_check_binding(&term, expected_type)?.type_())
        } else {
            None
        })
    }

    fn type_check_binding(
        &mut self,
        term: &RefCell<BindingTerm>,
        expected_type: Option<&Type>,
    ) -> Result<Term> {
        let untyped = match RefCell::borrow(term).deref() {
            BindingTerm::Untyped(term) => term.clone(),
            BindingTerm::Typed(term) => return Ok(term.clone()),
            BindingTerm::Evaluated(_) => unreachable!(),
        };

        let typed = self.type_check(&untyped, expected_type)?;

        *RefCell::borrow_mut(term) = BindingTerm::Typed(typed.clone());

        Ok(typed)
    }

    #[allow(clippy::needless_collect)]
    fn type_check_bindings(&mut self, offset: usize) -> Result<()> {
        let indexes = self
            .bindings
            .iter()
            .enumerate()
            .skip(offset)
            .filter_map(|(index, binding)| {
                binding.term.as_ref().and_then(|term| {
                    if let BindingTerm::Untyped(_) = RefCell::borrow(term).deref() {
                        Some(index)
                    } else {
                        None
                    }
                })
            })
            .collect::<Vec<_>>();

        indexes.into_iter().try_for_each(|index| {
            self.type_check(
                &Term::Variable {
                    index,
                    type_: Type::Never,
                },
                None,
            )
            .map(drop)
        })
    }

    fn type_check_scope(&mut self, index: usize) -> Result<()> {
        // todo: type check method bodies

        for item in self.scopes[index].items.values() {
            match RefCell::borrow_mut(item).deref() {
                Item::Struct { fields, .. } => {
                    let mut my_offset = 0;

                    // Note that we use the arbitrary HashMap iteration order to order fields, which would not be
                    // ideal if we cared about alignment and efficiency.
                    for Field { type_, offset } in fields.deref_mut() {
                        self.resolve_type(type_, Some(item))?;

                        *offset = my_offset;

                        my_offset += type_.size();
                    }
                }
            }
        }
    }

    fn resolve_type(&self, type_: &mut Type, self_item: Option<&Rc<RefCell<Item>>>) -> Result<()> {
        if let Type::Unresolved(name) = type_ {
            if let Some(found) = self
                .scopes
                .iter()
                .rev()
                .find_map(|scope| {
                    scope.items.get(name).map(|item| {
                        if let Ok(borrowed) = RefCell::try_borrow(item) {
                            Some(match borrowed {
                                Item::Type(type_) => type_,
                                Item::Struct { .. } => Type::Nominal {
                                    definition: Rc::downgrade(item),
                                    arguments: Rc::new([]),
                                },
                            })
                        } else {
                            assert!(Rc::ptr_eq(self_item.unwrap(), item));

                            None
                        }
                    })
                })
                .transpose()?
            {
                *type_ = found.unwrap_or_else(|| Type::Nominal {
                    definition: Rc::downgrade(self_item.unwrap()),
                    arguments: Rc::new([]),
                });
            } else {
                return Err(anyhow!("type not found: {}", self.unintern(name)));
            }
        }

        Ok(())
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
                                    .map(|term| Rc::new(RefCell::new(BindingTerm::Untyped(term))));

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

                        _ => Err(anyhow!("pattern not yet supported: {pat:#?}")),
                    }
                }
            }

            Stmt::Semi(expr, _) | Stmt::Expr(expr) => self.expr_to_term(expr),

            Stmt::Item(syn::Item::Struct(ItemStruct {
                ident,
                generics:
                    Generics {
                        params,
                        where_clause,
                        ..
                    },
                fields,
                vis,
                attrs,
                ..
            })) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if !params.is_empty() {
                    Err(anyhow!("generic parameters not yet supported"))
                } else if where_clause.is_some() {
                    Err(anyhow!("where clauses not yet supported"))
                } else if vis != Visibility::Inherited {
                    Err(anyhow!("visibility not yet supported"))
                } else {
                    let name = self.intern(&ident.to_string());

                    let fields = match fields {
                        Fields::Named(FieldsNamed { fields, .. }) => fields,
                        Fields::Unnamed(FieldsUnnamed { fields, .. }) => fields,
                    };

                    let fields = fields
                        .iter()
                        .enumerate()
                        .map(
                            |(
                                index,
                                syn::Field {
                                    ident,
                                    ty,
                                    vis,
                                    attrs,
                                    ..
                                },
                            )| {
                                if !attrs.is_empty() {
                                    Err(anyhow!("attributes not yet supported"))
                                } else if vis != Visibility::Inherited {
                                    Err(anyhow!("visibility not yet supported"))
                                } else {
                                    Ok((
                                        self.intern(
                                            &ident
                                                .map(|ident| ident.to_string())
                                                .unwrap_or_else(index.to_string()),
                                        ),
                                        Field {
                                            type_: self.type_to_type(ty)?,
                                            offset: 0,
                                        },
                                    ))
                                }
                            },
                        )
                        .collect::<Result<_>>();

                    let items = &mut self.scopes.last_mut().unwrap().items;

                    if items.contains_key(&name) {
                        Err(anyhow!("duplicate item identifier: {}", ident.to_string()))
                    } else {
                        items.insert(
                            name,
                            Item::Struct {
                                parameters: Rc::new([]),
                                fields,
                                methods: Rc::new([]),
                            },
                        );

                        Ok(Term::Literal(self.unit.clone()))
                    }
                }
            }

            _ => Err(anyhow!("stmt not yet supported: {stmt:#?}")),
        }
    }

    fn expr_to_term(&mut self, expr: &Expr) -> Result<Term> {
        fn parse<T: ToBytes + FromStr>(value: &str, variant: Integer) -> Result<Term>
        where
            <T as FromStr>::Err: error::Error + Send + Sync + 'static,
        {
            Ok(Term::Literal(Literal {
                offset: self.store(value.parse::<T>()?)?,
                type_: Type::Integer(variant),
            }))
        }

        match expr {
            Expr::Lit(ExprLit { lit, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    match lit {
                        Lit::Int(lit) => match lit.suffix() {
                            "" => Ok(Term::Literal(Literal {
                                offset: self.store(lit.base10_digits().as_bytes())?,
                                type_: Type::Integer(Integer::Unknown),
                            })),

                            suffix => integer_suffix_op!(parse, suffix, lit.base10_digits()),
                        },

                        Lit::Bool(LitBool { value, .. }) => Ok(Term::Literal(Literal {
                            offset: self.store(*value)?,
                            type_: Type::Boolean,
                        })),

                        _ => Err(anyhow!("literal not yet supported: {lit:?}")),
                    }
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
                            UnOp::Deref(_) => UnaryOp::Deref,
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
                            .map(|(_, expr)| self.expr_to_term(expr))
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
                                .map(|expr| self.expr_to_term(expr))
                                .transpose()?
                                .unwrap_or_else(|| Term::Literal(self.unit.clone())),
                        ),
                    })
                }
            }

            Expr::Reference(ExprReference {
                mutability,
                expr,
                attrs,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::Reference(Reference {
                        unique: mutability.is_some(),
                        term: self.expr_to_term(expr)?,
                    }))
                }
            }

            Expr::Struct(ExprStruct {
                path:
                    Path {
                        leading_colon,
                        segments,
                    },
                fields,
                attrs,
                rest,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if rest.is_some() {
                    Err(anyhow!("move initialization not yet supported"))
                } else if leading_colon.is_some() {
                    Err(anyhow!("absolute paths not yet supported"))
                } else if segments.len() != 1 {
                    Err(anyhow!("qualified paths not yet supported"))
                } else if let Some(PathSegment { ident, arguments }) = segments.last() {
                    if let PathArguments::None = arguments {
                        let type_ = Type::Unresolved(self.intern(&ident.to_string()));

                        let mut arguments = HashMap::new();

                        for syn::FieldValue {
                            member,
                            expr,
                            attrs,
                            ..
                        } in fields
                        {
                            if !attrs.is_empty() {
                                return Err(anyhow!("attributes not yet supported"));
                            } else {
                                let name = self.intern_member(member);

                                if arguments.contains_key(&name) {
                                    return Err(anyhow!(
                                        "duplicate field in struct initializer: {}",
                                        self.unintern(name)
                                    ));
                                } else {
                                    arguments.insert(name, self.expr_to_term(expr)?);
                                }
                            }
                        }

                        Ok(Term::Struct {
                            type_,
                            arguments: Rc::new(arguments),
                        })
                    } else {
                        Err(anyhow!("path arguments not yet supported"))
                    }
                } else {
                    Err(anyhow!("unexpected empty path"))
                }
            }

            Expr::Field(ExprField {
                base,
                member,
                attrs,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::Field {
                        base: self.expr_to_term(base)?,
                        name: self.intern_member(member),
                    })
                }
            }

            _ => Err(anyhow!("expr not yet supported: {expr:#?}")),
        }
    }

    fn block_to_term(&mut self, stmts: &[Stmt]) -> Result<Term> {
        let binding_count = self.bindings.len();

        self.scopes.push(Scope::new());

        let result = stmts
            .iter()
            .map(|stmt| self.stmt_to_term(stmt))
            .collect::<Result<Vec<_>>>()
            .map(|terms| match &terms[..] {
                [] => {
                    self.scopes.pop();
                    Term::Literal(self.unit.clone())
                }

                terms => Term::Block {
                    scope: self.scopes.pop().unwrap(),
                    terms: Rc::from(terms),
                },
            })
            .map_err(|error| {
                self.scopes.pop();
                error
            });

        self.bindings.truncate(binding_count);

        result
    }

    fn type_to_type(&mut self, type_: &syn::Type) -> Result<Type> {
        match type_ {
            syn::Type::Path(TypePath {
                path:
                    Path {
                        leading_colon,
                        segments,
                    },
                qself,
            }) => {
                if qself.is_some() {
                    Err(anyhow!("qualified paths not yet supported"))
                } else if leading_colon.is_some() {
                    Err(anyhow!("absolute paths not yet supported"))
                } else if segments.len() != 1 {
                    Err(anyhow!("qualified paths not yet supported"))
                } else if let Some(PathSegment { ident, arguments }) = segments.last() {
                    if let PathArguments::None = arguments {
                        Ok(Type::Unresolved(self.intern(&ident.to_string())))
                    } else {
                        Err(anyhow!("path arguments not yet supported"))
                    }
                } else {
                    Err(anyhow!("unexpected empty path"))
                }
            }

            _ => Err(anyhow!("type_ not yet supported: {type_:#?}")),
        }
    }

    pub fn eval_file(&mut self, _file: &str) -> Result<Eval> {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use {super::*, std::sync::Once};

    fn eval<T: FromBytes>(line: &str) -> Result<T> {
        {
            static ONCE: Once = Once::new();

            ONCE.call_once(pretty_env_logger::init_timed);
        }

        Ok(T::from_bytes(
            &Env::new().eval_line(line)?.value.rvalue().value,
        ))
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

    #[test]
    fn shared_reference() {
        assert_eq!(4_i32, eval("*&4").unwrap())
    }

    #[test]
    fn unique_reference() {
        assert_eq!(
            46_i32,
            eval("{ let mut x = 0; ({ let y = &mut x; *y = 23; *y }) + x }").unwrap()
        )
    }

    #[test]
    fn struct_field_access() {
        assert_eq!(
            7_i64,
            eval("{ struct Foo { x: i64, y: i64 } let f = Foo { x: 7, y: 14 }; f.x }").unwrap()
        )
    }

    #[test]
    fn struct_field_mutation() {
        assert_eq!(
            56_i64,
            eval("{ struct Foo { x: i64, y: i64 } let mut f = Foo { x: 7, y: 14 }; f.y = 49; f.x + f.y }").unwrap()
        )
    }

    #[test]
    fn struct_field_shared_reference() {
        assert_eq!(
            14_i64,
            eval("{ struct Foo { x: i64, y: i64 } let f = Foo { x: 7, y: 14 }; let y = &f.y; *y }")
                .unwrap()
        )
    }

    #[test]
    fn struct_field_unique_reference() {
        assert_eq!(
            44_i64,
            eval(
                "{ struct Foo { x: i64, y: i64 } \
                  let mut f = Foo { x: 7, y: 14 }; \
                  let y = &mut f.y; \
                  *y = 22;\
                  f.y * *y }"
            )
            .unwrap()
        )
    }
}
