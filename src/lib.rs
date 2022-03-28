#![deny(warnings)]
#![allow(dead_code)] // temporary

use {
    crate::allocator::Allocator,
    anyhow::{anyhow, Error, Result},
    log::info,
    maplit::hashmap,
    std::{
        any,
        cell::RefCell,
        collections::{hash_map::Entry, BTreeMap, HashMap},
        error,
        fmt::{self, Display},
        iter, mem,
        num::ParseIntError,
        ops::{Add, Deref, DerefMut, Div, Mul, Neg, Rem, Sub},
        rc::Rc,
        str,
        str::FromStr,
    },
    syn::{
        punctuated::Punctuated, AngleBracketedGenericArguments, Arm, BinOp, Block, Expr,
        ExprAssign, ExprAssignOp, ExprBinary, ExprBlock, ExprBreak, ExprCall, ExprField, ExprIf,
        ExprLit, ExprLoop, ExprMatch, ExprParen, ExprPath, ExprReference, ExprStruct, ExprTuple,
        ExprUnary, FieldPat, Fields, FieldsNamed, FieldsUnnamed, GenericArgument, GenericParam,
        Generics, ItemEnum, ItemStruct, Lit, LitBool, Local, Member, Pat, PatIdent, PatLit,
        PatPath, PatReference, PatRest, PatStruct, PatTuple, PatTupleStruct, PatWild,
        PathArguments, PathSegment, Stmt, TypePath, TypeReference, UnOp, Visibility,
    },
};

mod allocator;

trait FromBytes: Sized {
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

fn add<T: FromBytes + ToBytes + Add<T, Output = T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a + b)
}

fn sub<T: FromBytes + ToBytes + Sub<T, Output = T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a - b)
}

fn mul<T: FromBytes + ToBytes + Mul<T, Output = T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a * b)
}

fn div<T: FromBytes + ToBytes + Div<T, Output = T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a / b)
}

fn rem<T: FromBytes + ToBytes + Rem<T, Output = T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a % b)
}

macro_rules! integer_binary_ops_cases {
    ($op_discriminator:expr, $type_discriminator:expr, $env:expr, $($pattern:pat, $fn:ident),+) => {
        match $op_discriminator {
            $($pattern => integer_op!($fn, $type_discriminator, $env)),+,
            _ => unreachable!(),
        }
    }
}

macro_rules! integer_binary_ops {
    ($op_discriminator:expr, $type_discriminator:expr, $env:expr) => {
        integer_binary_ops_cases!(
            $op_discriminator,
            $type_discriminator,
            $env,
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

fn eq<T: FromBytes + ToBytes + PartialEq<T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a == b)
}

fn ge<T: FromBytes + ToBytes + PartialOrd<T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a >= b)
}

fn gt<T: FromBytes + ToBytes + PartialOrd<T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a > b)
}

fn le<T: FromBytes + ToBytes + PartialOrd<T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a <= b)
}

fn lt<T: FromBytes + ToBytes + PartialOrd<T>>(env: &mut Env) -> Result<(), EvalException> {
    let b = env.pop::<T>();
    let a = env.pop::<T>();
    env.push(a < b)
}

macro_rules! integer_comparison_ops_cases {
    ($op_discriminator:expr, $type_discriminator:expr, $env:expr, $($pattern:pat, $fn:ident),+) => {
        match $op_discriminator {
            $($pattern => integer_op!($fn, $type_discriminator, $env)),+,
            _ => unreachable!(),
        }
    }
}

macro_rules! integer_comparison_ops {
    ($op_discriminator:expr, $type_discriminator:expr, $env:expr) => {
        integer_comparison_ops_cases!(
            $op_discriminator,
            $type_discriminator,
            $env,
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
    ($fn:ident, $discriminator:expr, $env:expr, $arg:expr, $($pattern:pat, $variant:expr, $type:path),+) => {
        match $discriminator {
            $($pattern => $fn::<$type>($env, $arg, $variant)),+,
            _ => unreachable!(),
        }
    }
}

macro_rules! integer_suffix_op {
    ($fn:ident, $discriminator:expr, $env:expr, $arg:expr) => {
        integer_suffix_op_cases!(
            $fn,
            $discriminator,
            $env,
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
    fn parse(self, env: &mut Env, value: &str) -> Result<usize> {
        fn parse<T: ToBytes + FromStr>((env, value): (&mut Env, &str)) -> Result<usize>
        where
            <T as FromStr>::Err: error::Error + Send + Sync + 'static,
        {
            env.store(value.parse::<T>()?)
        }

        integer_op!(parse, self, (env, value))
    }

    fn load_i128(self, env: &Env, offset: usize) -> i128 {
        fn load_i128<T: TryInto<i128> + FromBytes>((env, offset): (&Env, usize)) -> i128
        where
            <T as TryInto<i128>>::Error: std::fmt::Debug,
        {
            env.load::<T>(offset).try_into().unwrap()
        }

        integer_op!(load_i128, self, (env, offset))
    }

    fn pop_as_i128(self, env: &mut Env) -> i128 {
        fn pop_as_i128<T: TryInto<i128> + FromBytes>(env: &mut Env) -> i128
        where
            <T as TryInto<i128>>::Error: std::fmt::Debug,
        {
            env.pop::<T>().try_into().unwrap()
        }

        integer_op!(pop_as_i128, self, env)
    }

    fn store_from_i128(self, env: &mut Env, offset: usize, value: i128) {
        fn store_from_i128<T: TryFrom<i128> + ToBytes>(
            (env, offset, value): (&mut Env, usize, i128),
        ) where
            <T as TryFrom<i128>>::Error: std::fmt::Debug,
        {
            env.store_at(offset, T::try_from(value).unwrap())
        }

        integer_op!(store_from_i128, self, (env, offset, value))
    }
}

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug)]
enum Float {
    F32,
    F64,
}

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug, Ord, PartialOrd)]
struct NameId(usize);

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug)]
struct ItemId(usize);

#[derive(Clone, Hash, Eq, PartialEq, Copy, Debug)]
struct Lifetime(NameId);

// todo: will need more fields here for associated types, functions, etc.
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
struct Trait {
    name: NameId,
    parameters: Rc<[Type]>,
}

#[derive(Clone, Debug)]
struct Impl {
    arguments: Rc<[Type]>,
    functions: Rc<HashMap<NameId, Abstraction>>,
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
        item: ItemId,
        size: usize,
        arguments: Rc<[Type]>,
    },
    Unresolved(Path),
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
                Integer::Unknown => unreachable!(),
            },
            Type::Nominal { size, .. } => *size,
            Type::Reference { .. } => mem::size_of::<usize>(),
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
    name: NameId,
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
    Unresolved {
        path: Path,
        parameters: Rc<HashMap<NameId, Pattern>>,
        complete: bool,
    },
    Literal {
        required: Term,
        actual: Term,
    },
    Variant {
        type_: Type,
        required_discriminant: i128,
        actual_discriminant: Term,
        parameters: Rc<[Pattern]>,
    },
    Binding {
        binding_mode: Option<BindingMode>,
        name: NameId,
        subpattern: Option<Rc<Pattern>>,
        term: Rc<RefCell<BindingTerm>>,
    },
    Reference {
        unique: bool,
        pattern: Rc<Pattern>,
    },
    Wildcard,
    Rest,
}

impl Pattern {
    fn type_(&self) -> Type {
        match self {
            Pattern::Literal { required, .. } => required.type_(),
            Pattern::Variant { type_, .. } => type_.clone(),
            Pattern::Binding {
                binding_mode, term, ..
            } => {
                let term_type = term.borrow().type_();

                match binding_mode.unwrap() {
                    BindingMode::Move | BindingMode::MoveMut => term_type,
                    BindingMode::Ref | BindingMode::RefMut => {
                        if let Type::Reference { type_, .. } = term_type {
                            type_.deref().clone()
                        } else {
                            unreachable!()
                        }
                    }
                }
            }
            Pattern::Wildcard => Type::Never,
            _ => todo!("Pattern::type_ for {self:?}"),
        }
    }
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
enum Lens {
    Unresolved,
    Field(Field),
    Reference(Rc<Lens>),
}

impl Lens {
    fn type_(&self) -> Type {
        match self {
            Self::Unresolved => unreachable!(),
            Self::Field(Field { type_, .. }) => type_.clone(),
            Self::Reference(lens) => lens.type_(),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Path {
    absolute: bool,
    segments: Rc<[NameId]>,
}

#[derive(Clone, Debug)]
enum Term {
    Block {
        scope: Rc<RefCell<Scope>>,
        terms: Rc<[Term]>,
    },
    Sequence(Rc<[Term]>),
    Literal(Literal),
    Reference(Rc<Reference>),
    Let {
        name: NameId,
        mutable: bool,
        index: usize,
        term: Rc<RefCell<BindingTerm>>,
    },
    Phi(Rc<[Rc<RefCell<BindingTerm>>]>),
    Variable {
        index: usize,
        type_: Type,
    },
    Assignment {
        left: Rc<Term>,
        right: Rc<Term>,
    },
    Application {
        abstraction: Rc<Term>,
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
        label: Option<NameId>,
        body: Rc<Term>,
        type_: Type,
    },
    Continue(Option<NameId>),
    Break {
        label: Option<NameId>,
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
        arguments: Rc<HashMap<NameId, Term>>,
    },
    Variant {
        type_: Type,
        name: NameId,
        arguments: Rc<HashMap<NameId, Term>>,
    },
    Field {
        base: Rc<Term>,
        name: NameId,
        lens: Lens,
    },
    Unresolved(Path),
}

impl Term {
    fn type_(&self) -> Type {
        match self {
            Self::Block { terms, .. } => {
                terms.last().map(|term| term.type_()).unwrap_or(Type::Unit)
            }
            Self::Sequence(terms) => terms.last().map(|term| term.type_()).unwrap_or(Type::Unit),
            Self::Literal(literal) => literal.type_.clone(),
            // todo: the return type of an abstraction may be a function of its type parameters
            Self::Application { abstraction, .. } => {
                if let Self::Abstraction(Abstraction { body, .. }) = abstraction.deref() {
                    body.type_()
                } else {
                    unreachable!()
                }
            }
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
            Self::Phi(terms) => terms
                .iter()
                .find_map(|term| match term.borrow().deref() {
                    BindingTerm::Initialized(literal) | BindingTerm::Uninitialized(literal) => {
                        Some(literal.type_.clone())
                    }
                    BindingTerm::Typed(term) => Some(term.type_()),
                    _ => None,
                })
                .unwrap(),
            Self::Reference(reference) => reference.type_(),
            Self::Loop { type_, .. } => type_.clone(),
            Self::Struct { type_, .. } => type_.clone(),
            Self::Variant { type_, .. } => type_.clone(),
            Self::Field { lens, .. } => lens.type_(),
            _ => todo!("Term::type_ for {self:?}"),
        }
    }

    fn temporary_needs_binding(&self) -> bool {
        match self {
            Term::Variable { .. } => false,
            Term::Field { base, .. } => base.temporary_needs_binding(),
            Term::Literal(_) => false,
            Term::UnaryOp(UnaryOp::Deref, term) => term.temporary_needs_binding(),
            // todo: there may be other cases, e.g. global variables, for which we should return false
            _ => true,
        }
    }
}

struct Loop {
    label: Option<NameId>,
    expected_type: Option<Type>,
    break_terms: Vec<Term>,
    branch_context: BranchContext,
}

#[derive(Clone, Debug)]
enum BindingTerm {
    Initialized(Literal),
    Uninitialized(Literal),
    Typed(Term),
    Untyped(Term),
    UntypedAndUninitialized,
}

impl BindingTerm {
    fn type_(&self) -> Type {
        match self {
            BindingTerm::Initialized(literal) | BindingTerm::Uninitialized(literal) => {
                literal.type_.clone()
            }
            BindingTerm::Typed(term) => term.type_(),
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
struct Binding {
    name: NameId,
    mutable: bool,
    term: Rc<RefCell<BindingTerm>>,
}

#[derive(Copy, Clone, Debug)]
enum BindingMode {
    Move,
    MoveMut,
    Ref,
    RefMut,
}

struct BranchContext {
    originals: Box<[(usize, Rc<RefCell<BindingTerm>>)]>,
    terms: Vec<Rc<RefCell<BindingTerm>>>,
}

impl BranchContext {
    fn new(bindings: &[Binding]) -> Self {
        Self {
            originals: bindings
                .iter()
                .enumerate()
                .filter_map(|(index, binding)| {
                    if matches!(
                        binding.term.borrow().deref(),
                        BindingTerm::UntypedAndUninitialized
                    ) {
                        Some((index, binding.term.clone()))
                    } else {
                        None
                    }
                })
                .collect(),
            terms: Vec::new(),
        }
    }

    fn reset(&self, bindings: &mut [Binding]) {
        for (index, original) in self.originals.iter() {
            bindings[*index].term = original.clone();
        }
    }

    fn record_and_reset(&mut self, bindings: &mut [Binding]) {
        self.terms.extend(
            self.originals
                .iter()
                .map(|(index, _)| bindings[*index].term.clone()),
        );

        self.reset(bindings);
    }

    fn make_phi_nodes(&mut self, bindings: &mut [Binding]) {
        for (my_index, (binding_index, original)) in self.originals.iter().enumerate() {
            let terms = self.terms[my_index..]
                .iter()
                .step_by(self.originals.len())
                .cloned()
                .collect::<Rc<[_]>>();

            if terms
                .iter()
                .all(|term| matches!(term.borrow().deref(), BindingTerm::UntypedAndUninitialized))
            {
                bindings[*binding_index].term = original.clone();
            } else {
                let phi = Term::Phi(terms);

                *original.borrow_mut() = BindingTerm::Uninitialized(Literal {
                    offset: 0,
                    type_: phi.type_(),
                });

                bindings[*binding_index].term = Rc::new(RefCell::new(BindingTerm::Untyped(phi)))
            }
        }
    }
}

#[derive(Debug)]
enum EvalException {
    Break { label: Option<NameId>, term: Term },
    Return { term: Term },
    Overflow,
}

#[derive(Clone)]
pub struct EvalResult {
    value: Rc<[u8]>,
    type_: Type,
}

impl fmt::Debug for EvalResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for EvalResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.type_ {
            Type::Integer(integer) => match integer {
                Integer::Unknown => str::from_utf8(&self.value).unwrap().fmt(f),
                _ => {
                    fn fmt<T: FromBytes + Display>(
                        (f, value): (&mut fmt::Formatter<'_>, &[u8]),
                    ) -> fmt::Result {
                        write!(f, "{}_{}", T::from_bytes(value), any::type_name::<T>())
                    }

                    integer_op!(fmt, integer, (f, &self.value))
                }
            },

            Type::Boolean => bool::from_bytes(&self.value).fmt(f),

            Type::Unit => write!(f, "()"),

            Type::Reference { type_, unique } => write!(
                f,
                "&{}{}",
                if *unique { "mut " } else { "" },
                EvalResult {
                    value: self.value.clone(),
                    type_: type_.deref().clone()
                }
            ),

            _ => write!(f, "todo: Debug for {:?}", self.type_),
        }
    }
}

pub enum Eval {
    Result(EvalResult),
    Bindings(HashMap<Rc<str>, EvalResult>),
}

impl fmt::Display for Eval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Result(result) => match result.type_ {
                Type::Unit => (),
                _ => result.fmt(f)?,
            },

            Self::Bindings(bindings) => {
                let mut need_newline = false;
                for (symbol, binding) in bindings {
                    if need_newline {
                        writeln!(f)?;
                    }

                    write!(f, "{symbol} = {binding}")?;

                    need_newline = true;
                }
            }
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

fn match_types_for_pattern(mut scrutinee_type: &Type, pattern_type: &Type) -> Result<()> {
    // todo: see todo in `match_types`

    let orig_scrutinee_type = scrutinee_type;

    while scrutinee_type != &Type::Never
        && pattern_type != &Type::Never
        && scrutinee_type != pattern_type
    {
        if let Type::Reference { type_, .. } = scrutinee_type {
            scrutinee_type = type_.deref();
        } else {
            return Err(anyhow!(
                "pattern type mismatch: expected {orig_scrutinee_type:?}, got {pattern_type:?}"
            ));
        }
    }

    Ok(())
}

#[derive(Clone, Debug)]
struct Field {
    type_: Type,
    offset: usize,
}

fn fields_size(fields: &HashMap<NameId, Field>, default: usize) -> usize {
    fields
        .values()
        .max_by(|a, b| a.offset.cmp(&b.offset))
        .map(|max| max.offset + max.type_.size())
        .unwrap_or(default)
}

#[derive(Clone, Debug)]
struct Variant {
    item: ItemId,
    fields: Rc<HashMap<NameId, Field>>,
    discriminant: i128,
}

#[derive(Clone, Debug)]
enum Item {
    Unavailable,
    Unresolved(Rc<Item>),
    Struct {
        parameters: Rc<[Type]>,
        fields: Rc<HashMap<NameId, Field>>,
        methods: Rc<[Abstraction]>,
    },
    Enum {
        parameters: Rc<[Type]>,
        discriminant_type: Option<Integer>,
        variants: Rc<HashMap<NameId, Variant>>,
        methods: Rc<[Abstraction]>,
    },
    Variant {
        item: ItemId,
        name: NameId,
    },
    Type(Type),
}

#[derive(Debug)]
struct Scope {
    items: HashMap<NameId, ItemId>,
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
    items: Vec<Item>,
    scopes: Vec<Rc<RefCell<Scope>>>,
    bindings: Vec<Binding>,
    loops: Vec<Loop>,
    traits: HashMap<NameId, Trait>,
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
            .ok_or_else(|| anyhow!("heap size must be at least {padding}"))?;

        let bottom = allocator.allocate(stack_size).ok_or_else(|| {
            anyhow!("stack size must be less than or equal to heap size + {padding}")
        })?;

        let stack = StackData {
            bottom,
            top: bottom + stack_size,
            offset: bottom,
        };

        let mut heap = vec![0; heap_size].into_boxed_slice();

        let true_offset = 4;
        heap[true_offset] = 1;

        let false_offset = 5;

        let unit_offset = allocator.allocate(0).unwrap();

        let mut env = Self {
            heap,
            allocator,
            stack,
            ids_to_names: Vec::new(),
            names_to_ids: HashMap::new(),
            items: Vec::new(),
            scopes: vec![
                Rc::new(RefCell::new(Scope::new())),
                Rc::new(RefCell::new(Scope::new())),
            ],
            bindings: Vec::new(),
            loops: Vec::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
            unit: Literal {
                offset: unit_offset,
                type_: Type::Unit,
            },
            true_: Literal {
                offset: true_offset,
                type_: Type::Boolean,
            },
            false_: Literal {
                offset: false_offset,
                type_: Type::Boolean,
            },
        };

        // todo: should load types, traits and impls from core/std source files (lazily if appropriate)

        env.scopes[0].borrow_mut().items = [
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
        .map(|(name, type_)| (env.intern(name), env.add_item(Item::Type(type_))))
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

    fn find_binding(&self, id: NameId) -> Option<usize> {
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

        let uninitialized_bindings = self.bindings[binding_count..].iter().any(|binding| {
            matches!(
                binding.term.borrow().deref(),
                BindingTerm::UntypedAndUninitialized
            )
        });

        if uninitialized_bindings {
            return Err(anyhow!("top-level let bindings must be initialized"));
        }

        self.resolve_scope()?;

        info!("{term:#?}");

        self.type_check_bindings(binding_count)?;

        self.bindings.truncate(binding_count);

        let term = self.type_check(term, None)?;

        self.bindings.truncate(binding_count);

        info!("{term:#?}");

        match self.eval_term(&term) {
            Ok(_) => (),
            Err(exception) => match exception {
                EvalException::Return { .. } => todo!(),
                EvalException::Overflow => return Err(anyhow!("stack overflow")),
                _ => unreachable!(),
            },
        };

        let type_ = term.type_();

        self.stack.offset -= type_.size();

        let result = self.to_result(&Literal {
            type_,
            offset: self.stack.offset,
        });

        Ok(if let Type::Unit = &result.type_ {
            Eval::Bindings(
                self.bindings[binding_count..]
                    .iter()
                    .map(|binding| {
                        (
                            self.unintern(binding.name),
                            match binding.term.borrow().deref() {
                                BindingTerm::Initialized(literal) => self.to_result(literal),
                                _ => unreachable!(),
                            },
                        )
                    })
                    .collect(),
            )
        } else {
            Eval::Result(result)
        })
    }

    fn intern(&mut self, name: &str) -> NameId {
        if let Some(&id) = self.names_to_ids.get(name) {
            NameId(id)
        } else {
            let name = Rc::<str>::from(name);
            let id = self.ids_to_names.len();
            self.ids_to_names.push(name.clone());
            self.names_to_ids.insert(name, id);
            NameId(id)
        }
    }

    fn intern_member(&mut self, member: &Member) -> NameId {
        self.intern(&match member {
            Member::Named(ident) => ident.to_string(),
            Member::Unnamed(index) => index.index.to_string(),
        })
    }

    fn unintern(&self, NameId(id): NameId) -> Rc<str> {
        self.ids_to_names[id].clone()
    }

    fn unintern_path(&self, Path { absolute, segments }: &Path) -> String {
        format!(
            "{}{}",
            if *absolute { "::" } else { "" },
            segments
                .iter()
                .map(|&segment| self.unintern(segment))
                .collect::<Vec<_>>()
                .join("::")
        )
    }

    fn add_item(&mut self, item: Item) -> ItemId {
        let index = self.items.len();

        self.items.push(item);

        ItemId(index)
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
                {
                    let mut term = term.borrow_mut();

                    *term = match term.deref() {
                        BindingTerm::Typed(term) => {
                            let offset = self.stack.offset;

                            self.eval_term(term)?;

                            BindingTerm::Initialized(Literal {
                                offset,
                                type_: term.type_(),
                            })
                        }

                        BindingTerm::Uninitialized(Literal { type_, .. }) => {
                            BindingTerm::Uninitialized(Literal {
                                offset: self.push_uninitialized(type_.size())?,
                                type_: type_.clone(),
                            })
                        }

                        _ => unreachable!("{:?}", term.deref()),
                    };
                }

                assert_eq!(*index, self.bindings.len());

                self.bindings.push(Binding {
                    name: *name,
                    mutable: *mutable,
                    term: term.clone(),
                });
            }

            Term::Variable { index, .. } => {
                let literal = if let BindingTerm::Initialized(literal) =
                    self.bindings[*index].term.borrow().deref()
                {
                    literal.clone()
                } else {
                    panic!(
                        "unexpected binding term variant: {:?}",
                        self.bindings[*index].term.borrow().deref()
                    )
                };

                self.push_literal(&literal)?;
            }

            Term::Literal(literal) => self.push_literal(literal)?,

            Term::Application {
                abstraction,
                arguments,
            } => {
                // todo: do we need to eval `abstraction` first?
                if let Term::Abstraction(Abstraction {
                    body, parameters, ..
                }) = abstraction.deref()
                {
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
                                term: Rc::new(RefCell::new(BindingTerm::Initialized(Literal {
                                    type_: term.type_(),
                                    offset,
                                }))),
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;

                    mem::swap(&mut parameters, &mut self.bindings);

                    let result = self.eval_term(body);

                    mem::swap(&mut parameters, &mut self.bindings);

                    self.stack.offset = offset;

                    return result;
                } else {
                    unreachable!()
                }
            }

            Term::And(left, right) => {
                self.eval_term(left)?;

                if !self.pop::<bool>() {
                    self.eval_term(right)?;
                } else {
                    self.push(false)?;
                }
            }

            Term::Or(left, right) => {
                self.eval_term(left)?;

                if self.pop::<bool>() {
                    self.eval_term(right)?;
                } else {
                    self.push(true)?;
                }
            }

            Term::UnaryOp(op, term) => {
                fn neg<T: FromBytes + ToBytes + Neg<Output = T>>(
                    env: &mut Env,
                ) -> Result<(), EvalException> {
                    let tmp = env.pop::<T>();
                    env.push(-tmp)
                }

                self.eval_term(term)?;

                match op {
                    UnaryOp::Neg => match term.type_() {
                        Type::Integer(integer_type) => integer_signed_op!(neg, integer_type, self)?,

                        _ => unreachable!(),
                    },

                    UnaryOp::Not => {
                        let tmp = self.pop::<bool>();
                        self.push(!tmp)?;
                    }

                    UnaryOp::Deref => {
                        if let Type::Reference { type_, .. } = &term.type_() {
                            let offset = self.pop::<usize>();
                            dbg!(offset);
                            self.push_copy(type_, offset)?;
                        } else {
                            unreachable!("{:?}", term.type_())
                        }
                    }
                }
            }

            Term::BinaryOp(op, left, right) => {
                self.eval_term(left)?;
                self.eval_term(right)?;

                match left.type_() {
                    Type::Integer(integer_type) => match op {
                        BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Rem => integer_binary_ops!(op, integer_type, self)?,

                        BinaryOp::Eq
                        | BinaryOp::Ge
                        | BinaryOp::Gt
                        | BinaryOp::Le
                        | BinaryOp::Lt => integer_comparison_ops!(op, integer_type, self)?,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            }

            Term::Match { arms, .. } => {
                let base = self.stack.offset;

                let binding_count = self.bindings.len();

                for arm in arms.iter() {
                    let matched = if self.match_pattern(&arm.pattern)? {
                        if let Some(guard) = &arm.guard {
                            self.eval_term(guard)?;

                            self.pop::<bool>()
                        } else {
                            true
                        }
                    } else {
                        false
                    };

                    if matched {
                        self.eval_term(&arm.body)?;
                    }

                    self.bindings.truncate(binding_count);

                    if matched {
                        let size = arm.body.type_().size();

                        let src = self.stack.offset - size;

                        self.heap.copy_within(src..(src + size), base);

                        self.stack.offset = base + size;

                        return Ok(());
                    }
                }

                unreachable!(
                    "exhaustiveness checking during type checking should prevent reaching this point"
                )
            }

            Term::Assignment { left, right } => {
                let src = self.stack.offset;

                self.eval_term(right)?;

                let dst = match left.deref() {
                    Term::Variable { index, .. } => {
                        let literal = match self.bindings[*index].term.borrow().deref() {
                            BindingTerm::Initialized(literal)
                            | BindingTerm::Uninitialized(literal) => literal.clone(),
                            _ => unreachable!(),
                        };

                        let offset = literal.offset;

                        self.bindings[*index].term =
                            Rc::new(RefCell::new(BindingTerm::Initialized(literal)));

                        offset
                    }

                    Term::UnaryOp(UnaryOp::Deref, left) => {
                        self.eval_term(left)?;

                        self.pop()
                    }

                    Term::Field { base, lens, .. } => {
                        self.offset_of_lens(lens, self.offset_of(base))
                    }

                    _ => todo!("assignment to {left:?}"),
                };

                self.heap
                    .copy_within(src..(src + right.type_().size()), dst);

                self.stack.offset = src;
            }

            Term::Block { terms, .. } => {
                let binding_count = self.bindings.len();

                let offset = self.stack.offset;

                let result = terms.iter().try_for_each(|term| self.eval_term(term));

                if result.is_ok() {
                    let size = terms.last().unwrap().type_().size();

                    self.heap
                        .copy_within((self.stack.offset - size)..self.stack.offset, offset);

                    self.stack.offset = offset + size;
                }

                self.bindings.truncate(binding_count);

                return result;
            }

            Term::Sequence(terms) => return terms.iter().try_for_each(|term| self.eval_term(term)),

            Term::Loop { label, body, .. } => {
                let offset = self.stack.offset;

                loop {
                    match self.eval_term(body) {
                        Ok(_) => {
                            self.stack.offset = offset;
                        }

                        Err(EvalException::Break {
                            label: break_label,
                            term,
                        }) if break_label.is_none() || break_label == *label => {
                            let size = term.type_().size();

                            self.heap
                                .copy_within((self.stack.offset - size)..self.stack.offset, offset);

                            self.stack.offset = offset + size;

                            break;
                        }

                        err => return err,
                    }
                }
            }

            Term::Break { label, term } => {
                self.eval_term(term)?;

                return Err(EvalException::Break {
                    label: *label,
                    term: term.deref().clone(),
                });
            }

            Term::Return { term } => {
                self.eval_term(term)?;

                return Err(EvalException::Return {
                    term: term.deref().clone(),
                });
            }

            Term::Reference(reference) => {
                self.push(self.offset_of(&reference.term))?;
            }

            Term::Struct { type_, arguments } => {
                let fields = if let Type::Nominal { item, .. } = &type_ {
                    if let Item::Struct { fields, .. } = &self.items[item.0] {
                        fields.clone()
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                };

                let size = type_.size();

                let base = self.push_uninitialized(size)?;

                let offset = self.stack.offset;

                // todo: eval arguments in program order since they may have side-effects

                for (name, term) in arguments.deref() {
                    let field = fields.get(name).unwrap();

                    self.eval_term(term)?;

                    self.heap
                        .copy_within(offset..offset + field.type_.size(), base + field.offset);

                    self.stack.offset = offset;
                }
            }

            Term::Field { base, lens, .. } => {
                self.eval_term(base)?;

                let dst = self.stack.offset - base.type_().size();

                let src = self.offset_of_lens(lens, dst);

                let type_ = lens.type_();

                self.heap.copy_within(src..(src + type_.size()), dst);

                self.stack.offset = dst + type_.size();
            }

            Term::Variant {
                type_,
                name,
                arguments,
            } => {
                let (discriminant_type, variant) = if let Type::Nominal { item, .. } = &type_ {
                    if let Item::Enum {
                        variants,
                        discriminant_type,
                        ..
                    } = &self.items[item.0]
                    {
                        (*discriminant_type, variants.get(name).unwrap().clone())
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                };

                let size = type_.size();

                let base = self.push_uninitialized(size)?;

                if let Some(discriminant_type) = discriminant_type {
                    discriminant_type.store_from_i128(self, base, variant.discriminant);
                }

                let offset = self.stack.offset;

                // todo: eval arguments in program order since they may have side-effects

                for (name, term) in arguments.deref() {
                    let field = variant.fields.get(name).unwrap();

                    self.eval_term(term)?;

                    self.heap
                        .copy_within(offset..offset + field.type_.size(), base + field.offset);

                    self.stack.offset = offset;
                }
            }

            _ => todo!("evaluation not yet supported for term {term:?}"),
        }

        Ok(())
    }

    fn to_result(&self, literal: &Literal) -> EvalResult {
        let mut type_ = &literal.type_;
        let mut offset = literal.offset;
        while let Type::Reference {
            type_: deref_type, ..
        } = type_
        {
            offset = self.load(offset);
            type_ = deref_type.deref();
        }

        let size = type_.size();
        let value = Rc::from(&self.heap[offset..(offset + size)]);

        EvalResult {
            value,
            type_: type_.clone(),
        }
    }

    fn load<T: FromBytes>(&self, offset: usize) -> T {
        assert!(offset != 0);

        T::from_bytes(&self.heap[offset..(offset + mem::size_of::<T>())])
    }

    fn peek<T: FromBytes>(&self) -> T {
        assert!(self.stack.offset >= self.stack.bottom + mem::size_of::<T>());

        self.load(self.stack.offset - mem::size_of::<T>())
    }

    fn pop<T: FromBytes>(&mut self) -> T {
        assert!(self.stack.offset >= self.stack.bottom + mem::size_of::<T>());

        self.stack.offset -= mem::size_of::<T>();

        self.load(self.stack.offset)
    }

    fn push<T: ToBytes>(&mut self, value: T) -> Result<(), EvalException> {
        let base = self.push_uninitialized(mem::size_of::<T>())?;

        self.heap[base..(base + mem::size_of::<T>())].copy_from_slice(value.to_bytes().as_ref());

        Ok(())
    }

    fn push_copy(&mut self, type_: &Type, src: usize) -> Result<(), EvalException> {
        let size = type_.size();
        let dest = self.push_uninitialized(size)?;

        self.heap.copy_within(src..(src + size), dest);

        Ok(())
    }

    fn push_uninitialized(&mut self, size: usize) -> Result<usize, EvalException> {
        if self.stack.offset + size > self.stack.top {
            Err(EvalException::Overflow)
        } else {
            let base = self.stack.offset;

            self.stack.offset += size;

            Ok(base)
        }
    }

    fn push_literal(&mut self, term: &Literal) -> Result<(), EvalException> {
        self.push_copy(&term.type_, term.offset)
    }

    fn allocate(&mut self, size: usize) -> Result<usize> {
        self.allocator
            .allocate(size)
            .ok_or_else(|| anyhow!("out of memory"))
    }

    fn store_slice(&mut self, value: &[u8]) -> Result<usize> {
        let offset = self.allocate(mem::size_of::<usize>() + value.len())?;

        self.heap[offset..offset + mem::size_of::<usize>()]
            .copy_from_slice(value.len().to_bytes().as_ref());

        let body_offset = offset + mem::size_of::<usize>();

        self.heap[body_offset..(body_offset + value.len())].copy_from_slice(value);

        Ok(offset)
    }

    fn load_slice(&self, offset: usize) -> &[u8] {
        let body_offset = offset + mem::size_of::<usize>();

        &self.heap[body_offset..(body_offset + self.load::<usize>(offset))]
    }

    fn store<T: ToBytes>(&mut self, value: T) -> Result<usize> {
        let offset = self.allocate(mem::size_of::<T>())?;

        self.store_at(offset, value);

        Ok(offset)
    }

    fn store_at<T: ToBytes>(&mut self, offset: usize, value: T) {
        self.heap[offset..(offset + mem::size_of::<T>())]
            .copy_from_slice(value.to_bytes().as_ref());
    }

    fn offset_of(&self, term: &Term) -> usize {
        match term {
            Term::Variable { index, .. } => match self.bindings[*index].term.borrow().deref() {
                BindingTerm::Initialized(literal) | BindingTerm::Uninitialized(literal) => {
                    literal.offset
                }
                _ => unreachable!(),
            },

            Term::Field { base, lens, .. } => self.offset_of_lens(lens, self.offset_of(base)),

            Term::Literal(Literal { offset, .. }) => *offset,

            Term::UnaryOp(UnaryOp::Deref, term) => self.load::<usize>(self.offset_of(term)),

            // At this point any references to temporaries should have been transformed into one of the above
            _ => unreachable!("{:?}", term),
        }
    }

    fn offset_of_lens(&self, lens: &Lens, base: usize) -> usize {
        match lens {
            Lens::Unresolved => unreachable!(),
            Lens::Field(field) => base + field.offset,
            Lens::Reference(lens) => self.offset_of_lens(lens, self.load::<usize>(base)),
        }
    }

    fn match_pattern(&mut self, pattern: &Pattern) -> Result<bool, EvalException> {
        Ok(match pattern {
            Pattern::Literal { required, actual } => {
                self.eval_term(required)?;
                self.eval_term(actual)?;

                match required.type_() {
                    Type::Boolean => {
                        let a = self.pop::<bool>();
                        let b = self.pop::<bool>();
                        a == b
                    }

                    Type::Integer(integer_type) => {
                        fn pattern_eq<T: FromBytes + PartialEq<T>>(env: &mut Env) -> bool {
                            let b = env.pop::<T>();
                            let a = env.pop::<T>();
                            a == b
                        }

                        integer_op!(pattern_eq, integer_type, self)
                    }

                    _ => todo!("match pattern {pattern:?}"),
                }
            }

            Pattern::Variant {
                required_discriminant,
                actual_discriminant,
                parameters,
                ..
            } => {
                self.eval_term(actual_discriminant)?;

                let discriminant_type =
                    if let Type::Integer(integer_type) = actual_discriminant.type_() {
                        integer_type
                    } else {
                        unreachable!()
                    };

                if *required_discriminant == discriminant_type.pop_as_i128(self) {
                    for pattern in parameters.iter() {
                        if !self.match_pattern(pattern)? {
                            return Ok(false);
                        }
                    }

                    true
                } else {
                    false
                }
            }

            Pattern::Binding {
                binding_mode,
                name,
                subpattern,
                term,
            } => {
                let scrutinee = if let BindingTerm::Typed(term) = term.borrow().deref() {
                    term.clone()
                } else {
                    unreachable!()
                };

                if let Some(subpattern) = subpattern.as_ref() {
                    if !self.match_pattern(subpattern)? {
                        return Ok(false);
                    }
                }

                self.eval_term(&scrutinee)?;

                let type_ = scrutinee.type_();

                *term.borrow_mut() = BindingTerm::Initialized(Literal {
                    offset: self.stack.offset - type_.size(),
                    type_,
                });

                self.bindings.push(Binding {
                    name: *name,
                    mutable: matches!(binding_mode.unwrap(), BindingMode::MoveMut),
                    term: term.clone(),
                });

                true
            }

            Pattern::Wildcard => true,

            _ => todo!("match pattern {pattern:?}"),
        })
    }

    fn type_check(&mut self, term: &Term, expected_type: Option<&Type>) -> Result<Term> {
        match term {
            Term::Let {
                name,
                mutable,
                index,
                term: binding_term,
            } => {
                assert_eq!(*index, self.bindings.len());

                self.bindings.push(Binding {
                    name: *name,
                    mutable: *mutable,
                    term: binding_term.clone(),
                });

                Ok(term.clone())
            }

            Term::Variable { index, .. } => {
                let index = *index;

                let term = {
                    let binding = &self.bindings[index];

                    let error = || {
                        Err(anyhow!(
                            "use of or assignment to possibly-uninitialized variable: {}",
                            self.unintern(binding.name)
                        ))
                    };

                    match binding.term.borrow().deref() {
                        BindingTerm::Typed(Term::Phi(terms)) => {
                            if terms.iter().any(|term| {
                                matches!(
                                    term.borrow().deref(),
                                    BindingTerm::Uninitialized(_)
                                        | BindingTerm::UntypedAndUninitialized
                                )
                            }) {
                                return error();
                            }
                        }

                        BindingTerm::Uninitialized(_) | BindingTerm::UntypedAndUninitialized => {
                            return error()
                        }

                        _ => (),
                    }

                    binding.term.clone()
                };

                let type_ = self.type_check_binding(&term, expected_type)?.type_();

                Ok(Term::Variable { index, type_ })
            }

            Term::Literal(literal) => {
                Ok(Term::Literal(self.typed_literal(literal, expected_type)?))
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
                            abstraction: Rc::new(Term::Abstraction(
                                impl_.functions.get(&function).unwrap().clone(),
                            )),
                            arguments: Rc::new([Term::Reference(Rc::new(Reference {
                                unique: false,
                                term,
                            }))]),
                        }),
                    ),

                    _ => Term::Application {
                        abstraction: Rc::new(Term::Abstraction(
                            impl_.functions.get(&function).unwrap().clone(),
                        )),
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
                            abstraction: Rc::new(Term::Abstraction(
                                impl_.functions.get(&function).unwrap().clone(),
                            )),
                            arguments: Rc::new([
                                Term::Reference(Rc::new(Reference {
                                    unique: true,
                                    term: left,
                                })),
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
                            abstraction: Rc::new(Term::Abstraction(
                                impl_.functions.get(&function).unwrap().clone(),
                            )),
                            arguments: Rc::new([
                                Term::Reference(Rc::new(Reference {
                                    unique: false,
                                    term: left,
                                })),
                                Term::Reference(Rc::new(Reference {
                                    unique: false,
                                    term: right,
                                })),
                            ]),
                        }
                    }

                    _ => {
                        let (impl_, function) = impl_and_function.unwrap();

                        Term::Application {
                            abstraction: Rc::new(Term::Abstraction(
                                impl_.functions.get(&function).unwrap().clone(),
                            )),
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

                let binding_count = self.bindings.len();

                // todo: exhaustiveness check

                for arm in arms.iter() {
                    let pattern =
                        self.type_check_pattern(&arm.pattern, &scrutinee, BindingMode::Move)?;

                    match_types_for_pattern(&scrutinee_type, &pattern.type_())?;

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
                        self.type_check(&arm.body, my_expected_type.as_ref().or(expected_type))?;

                    branch_context.record_and_reset(&mut self.bindings);

                    let body_type = body.type_();

                    if let Some(expected_type) = my_expected_type.as_ref() {
                        match_types(expected_type, &body_type)?
                    }

                    my_expected_type.get_or_insert(body_type);

                    typed_arms.push(MatchArm {
                        pattern,
                        guard,
                        body,
                    });

                    self.bindings.truncate(binding_count);
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

                    // todo: check binding type ascription, if present

                    let expected_type = match self.bindings[index].term.borrow().deref() {
                        BindingTerm::Typed(term) => Some(term.type_()),
                        _ => None,
                    };

                    let right = self.type_check(right, expected_type.as_ref())?;

                    let right_type = right.type_();

                    match_types(&self.type_check_binding_index(index, None)?, &right_type)?;

                    match self.bindings[index].term.borrow_mut().deref_mut() {
                        BindingTerm::Uninitialized(literal) => {
                            if right_type != Type::Never {
                                literal.type_ = right_type.clone();
                            }
                        }

                        BindingTerm::UntypedAndUninitialized => (),

                        _ => {
                            if !self.bindings[index].mutable {
                                return Err(anyhow!("invalid assignment to immutable variable"));
                            }
                        }
                    }

                    self.bindings[index].term =
                        Rc::new(RefCell::new(BindingTerm::Typed(right.clone())));

                    Ok(Term::Assignment {
                        left: Rc::new(Term::Variable {
                            index,
                            type_: right_type,
                        }),
                        right: Rc::new(right),
                    })
                } else {
                    let left = self.type_check(left, None)?;

                    if !self.is_mutable(&left) {
                        return Err(anyhow!("invalid assignment to immutable term"));
                    }

                    let left_type = left.type_();

                    let right = self.type_check(right, Some(&left_type))?;

                    let right_type = right.type_();

                    match_types(&left_type, &right_type)?;

                    Ok(Term::Assignment {
                        left: Rc::new(left),
                        right: Rc::new(right),
                    })
                }
            }

            Term::Block { scope, terms } => {
                let binding_count = self.bindings.len();
                let scope_count = self.scopes.len();

                self.scopes.push(scope.clone());

                self.resolve_scope()?;

                let terms = terms
                    .iter()
                    .map(|term| self.type_check(term, None))
                    .collect::<Result<_>>()?;

                self.type_check_bindings(binding_count)?;

                let scope = self.scopes.pop().unwrap();

                assert_eq!(scope_count, self.scopes.len());

                // todo: check for bound values which implement Drop and insert the appropriate calls

                self.bindings.truncate(binding_count);

                Ok(Term::Block { scope, terms })
            }

            Term::Sequence(terms) => Ok(Term::Sequence(
                terms
                    .iter()
                    .map(|term| self.type_check(term, None))
                    .collect::<Result<_>>()?,
            )),

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
            Term::Reference(reference) => {
                let term = self.type_check(
                    &reference.term,
                    expected_type.and_then(|expected| {
                        if let Type::Reference { type_, .. } = expected {
                            Some(type_.deref())
                        } else {
                            None
                        }
                    }),
                )?;

                if reference.unique && !self.is_mutable(&term) {
                    Err(anyhow!("invalid unique reference to immutable term"))
                } else {
                    Ok(Term::Reference(Rc::new(Reference {
                        unique: reference.unique,
                        term,
                    })))
                }
            }

            Term::Struct { type_, arguments } => {
                if let Type::Unresolved(path) = type_.deref() {
                    self.resolve_term(path, arguments.clone(), expected_type)
                } else {
                    let error = || Err(anyhow!("attempt to initialize non-struct as a struct"));

                    let fields = if let Type::Nominal { item, .. } = &type_ {
                        if let Item::Struct { fields, .. } = &self.items[item.0] {
                            if !fields.keys().all(|name| arguments.contains_key(name)) {
                                return Err(anyhow!("fields missing in struct initializer"));
                            } else {
                                fields.clone()
                            }
                        } else {
                            return error();
                        }
                    } else {
                        return error();
                    };

                    Ok(Term::Struct {
                        type_: type_.clone(),
                        arguments: Rc::new(self.type_check_arguments(&fields, arguments)?),
                    })
                }
            }

            Term::Variant {
                type_,
                name,
                arguments,
            } => {
                let type_ = self.resolve_type(type_)?;

                let error = || Err(anyhow!("attempt to initialize non-enum as an enum"));

                let fields = if let Type::Nominal { item, .. } = &type_ {
                    if let Item::Enum { variants, .. } = &self.items[item.0] {
                        variants
                            .get(name)
                            .ok_or_else(|| {
                                anyhow!("variant {} not present in enum", self.unintern(*name))
                            })?
                            .fields
                            .clone()
                    } else {
                        return error();
                    }
                } else {
                    return error();
                };

                Ok(Term::Variant {
                    type_,
                    name: *name,
                    arguments: Rc::new(self.type_check_arguments(&fields, arguments)?),
                })
            }

            Term::Field { base, name, .. } => {
                let base = self.type_check(base, None)?;

                let lens = self.resolve_field(&base.type_(), *name)?;

                Ok(Term::Field {
                    base: Rc::new(base),
                    name: *name,
                    lens,
                })
            }

            Term::Unresolved(path) => {
                self.resolve_term(path, Rc::new(HashMap::new()), expected_type)
            }

            Term::Application {
                abstraction,
                arguments,
            } => {
                if let Term::Unresolved(path) = abstraction.deref() {
                    let arguments = Rc::new(
                        arguments
                            .iter()
                            .enumerate()
                            .map(|(index, term)| (self.intern(&index.to_string()), term.clone()))
                            .collect(),
                    );

                    self.resolve_term(path, arguments, expected_type)
                } else {
                    Err(anyhow!(
                        "application not yet supported for term {abstraction:?}"
                    ))
                }
            }

            _ => Err(anyhow!("type checking not yet supported for term {term:?}")),
        }
    }

    fn resolve_term(
        &mut self,
        path: &Path,
        arguments: Rc<HashMap<NameId, Term>>,
        expected_type: Option<&Type>,
    ) -> Result<Term> {
        let item = self.find_item(path)?;

        let term = match &self.items[item.0] {
            Item::Variant { item, name } => Term::Variant {
                type_: self.type_for_item(*item),
                name: *name,
                arguments,
            },

            Item::Struct { .. } => Term::Struct {
                type_: self.type_for_item(item),
                arguments,
            },

            _ => {
                return Err(anyhow!(
                    "cannot resolve {} as an expression",
                    self.unintern_path(path)
                ))
            }
        };

        self.type_check(&term, expected_type)
    }

    fn type_check_arguments(
        &mut self,
        fields: &HashMap<NameId, Field>,
        arguments: &HashMap<NameId, Term>,
    ) -> Result<HashMap<NameId, Term>> {
        arguments
            .iter()
            .map(|(name, term)| {
                if let Some(Field {
                    type_: expected_type,
                    ..
                }) = fields.get(name)
                {
                    let term = self.type_check(term, Some(expected_type))?;

                    match_types(expected_type, &term.type_())?;

                    Ok((*name, term))
                } else {
                    Err(anyhow!("no such field: {}", self.unintern(*name)))
                }
            })
            .collect::<Result<_>>()
    }

    fn resolve_known_field(&self, type_: &Type, field: &Field) -> Result<Lens> {
        match type_ {
            Type::Nominal { .. } => Ok(Lens::Field(field.clone())),

            Type::Reference { type_, .. } => self
                .resolve_known_field(type_, field)
                .map(|lens| Lens::Reference(Rc::new(lens))),

            // todo: field access through smart pointers (via Deref trait), etc.
            _ => Err(anyhow!("attempt to resolve a field of non-struct value")),
        }
    }

    fn resolve_field(&self, type_: &Type, name: NameId) -> Result<Lens> {
        match type_ {
            Type::Nominal { item, .. } => {
                if let Item::Struct { fields, .. } = &self.items[item.0] {
                    if let Some(field) = fields.get(&name) {
                        Ok(Lens::Field(field.clone()))
                    } else {
                        Err(anyhow!("no such field: {}", self.unintern(name)))
                    }
                } else {
                    Err(anyhow!(
                        "attempt to resolve a field of non-struct value: {:?}",
                        self.items[item.0]
                    ))
                }
            }

            Type::Reference { type_, .. } => self
                .resolve_field(type_, name)
                .map(|lens| Lens::Reference(Rc::new(lens))),

            // todo: field access through smart pointers (via Deref trait), etc.
            _ => Err(anyhow!("attempt to resolve a field of non-struct value")),
        }
    }

    fn is_mutable(&self, term: &Term) -> bool {
        match term {
            Term::UnaryOp(UnaryOp::Deref, term) => {
                if let Type::Reference { unique, .. } = term.type_() {
                    unique
                } else {
                    unreachable!()
                }
            }

            Term::Field { base, .. } => self.is_mutable(base),

            Term::Variable { index, .. } => self.bindings[*index].mutable,

            _ => todo!("mutability of {term:?}"),
        }
    }

    fn type_check_phi(
        &mut self,
        terms: &[Rc<RefCell<BindingTerm>>],
        expected_type: Option<&Type>,
    ) -> Result<Option<Type>> {
        let mut my_expected_type = None;

        for term in terms.iter() {
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
    ) -> Result<Type> {
        let term = self.bindings[index].term.clone();

        Ok(self.type_check_binding(&term, expected_type)?.type_())
    }

    fn type_check_binding(
        &mut self,
        term: &RefCell<BindingTerm>,
        expected_type: Option<&Type>,
    ) -> Result<Term> {
        let untyped = match term.borrow().deref() {
            BindingTerm::Uninitialized(literal) => return Ok(Term::Literal(literal.clone())),
            BindingTerm::UntypedAndUninitialized => {
                return Ok(Term::Literal(Literal {
                    offset: 0,
                    type_: Type::Never,
                }))
            }
            BindingTerm::Untyped(term) => term.clone(),
            BindingTerm::Typed(term) => return Ok(term.clone()),
            _ => unreachable!(),
        };

        let typed = self.type_check(&untyped, expected_type)?;

        *term.borrow_mut() = BindingTerm::Typed(typed.clone());

        Ok(typed)
    }

    #[allow(clippy::needless_collect)]
    fn type_check_bindings(&mut self, offset: usize) -> Result<()> {
        let indexes = self.bindings[offset..]
            .iter()
            .enumerate()
            .filter_map(|(index, binding)| match binding.term.borrow().deref() {
                BindingTerm::Untyped(_) | BindingTerm::UntypedAndUninitialized => Some(index),
                _ => None,
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

    fn resolve_scope(&mut self) -> Result<()> {
        let scope = self.scopes.last().unwrap().clone();

        for item in scope.borrow().items.values() {
            self.resolve_item(*item)?;
        }

        Ok(())
    }

    fn resolve_item(&mut self, index: ItemId) -> Result<()> {
        let item = match &self.items[index.0] {
            Item::Unavailable => {
                // if this generates false positives, we might be calling `resolve_item` too early or
                // unnecessarily:
                return Err(anyhow!("infinite type detected"));
            }
            Item::Unresolved(item) => item.clone(),
            _ => return Ok(()),
        };

        self.items[index.0] = Item::Unavailable;

        // todo: type check method bodies (or else do that lazily elsewhere, e.g. on first invocation)
        #[allow(clippy::single_match)]
        match item.deref() {
            Item::Struct {
                parameters,
                fields,
                methods,
            } => {
                self.items[index.0] = Item::Struct {
                    parameters: parameters.clone(),
                    methods: methods.clone(),
                    fields: Rc::new(self.resolve_fields(fields, 0)?),
                }
            }

            Item::Enum {
                parameters,
                discriminant_type,
                variants,
                methods,
            } => {
                self.items[index.0] = Item::Enum {
                    parameters: parameters.clone(),
                    discriminant_type: *discriminant_type,
                    methods: methods.clone(),
                    variants: Rc::new(
                        self.resolve_variants(
                            variants,
                            discriminant_type
                                .as_ref()
                                .map(|type_| Type::Integer(*type_).size())
                                .unwrap_or(0),
                        )?,
                    ),
                }
            }

            Item::Type(_) | Item::Variant { .. } => (),

            Item::Unavailable | Item::Unresolved(_) => unreachable!(),
        }

        Ok(())
    }

    fn resolve_variants(
        &mut self,
        variants: &HashMap<NameId, Variant>,
        discriminant_size: usize,
    ) -> Result<HashMap<NameId, Variant>> {
        variants
            .iter()
            .map(
                |(
                    name,
                    Variant {
                        item,
                        fields,
                        discriminant,
                    },
                )| {
                    Ok((
                        *name,
                        Variant {
                            item: *item,
                            fields: Rc::new(self.resolve_fields(fields, discriminant_size)?),
                            discriminant: *discriminant,
                        },
                    ))
                },
            )
            .collect()
    }

    fn resolve_fields(
        &mut self,
        fields: &HashMap<NameId, Field>,
        mut next_offset: usize,
    ) -> Result<HashMap<NameId, Field>> {
        // Note that we use the IDs of names to order fields, which would not be ideal if we cared
        // about alignment.
        fields
            .iter()
            .collect::<BTreeMap<_, _>>()
            .into_iter()
            .map(|(name, Field { type_, .. })| {
                let type_ = self.resolve_type(type_)?;

                let offset = next_offset;

                next_offset += type_.size();

                Ok((*name, Field { type_, offset }))
            })
            .collect()
    }

    fn find_item_in_item(&mut self, item: ItemId, path: &[NameId]) -> Result<ItemId> {
        self.resolve_item(item)?;

        if path.is_empty() {
            Ok(item)
        } else {
            let item = match &self.items[item.0] {
                Item::Enum { variants, .. } => {
                    variants
                        .get(&path[0])
                        .ok_or_else(|| {
                            anyhow!("variant {} not present in enum", self.unintern(path[0]))
                        })?
                        .item
                }

                _ => todo!("find_item_in_item {:?}", self.items[item.0]),
            };

            self.find_item_in_item(item, &path[1..])
        }
    }

    fn find_item(&mut self, path @ Path { absolute, segments }: &Path) -> Result<ItemId> {
        if *absolute {
            todo!("absolute paths")
        } else if let Some(item) = self
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.borrow().items.get(&segments[0]).copied())
        {
            self.find_item_in_item(item, &segments[1..])
        } else {
            Err(anyhow!("item not found: {}", self.unintern_path(path)))
        }
    }

    fn resolve_type(&mut self, type_: &Type) -> Result<Type> {
        // todo: recursively resolve type parameters

        // todo: detect infinite types and return error

        match type_ {
            Type::Unresolved(path) => {
                let item = self.find_item(path)?;

                Ok(self.type_for_item(item))
            }

            Type::Reference { type_, unique } => Ok(Type::Reference {
                type_: Rc::new(self.resolve_type(type_)?),
                unique: *unique,
            }),

            _ => Ok(type_.clone()),
        }
    }

    fn type_for_item(&self, item: ItemId) -> Type {
        match &self.items[item.0] {
            Item::Type(type_) => type_.clone(),
            Item::Struct { fields, .. } => Type::Nominal {
                item,
                size: fields_size(fields, 0),
                arguments: Rc::new([]),
            },
            Item::Enum {
                discriminant_type,
                variants,
                ..
            } => {
                let discriminant_size = discriminant_type
                    .as_ref()
                    .map(|&type_| Type::Integer(type_).size())
                    .unwrap_or(0);

                Type::Nominal {
                    item,
                    size: variants
                        .values()
                        .map(|Variant { fields, .. }| fields_size(fields, discriminant_size))
                        .max()
                        .unwrap_or(discriminant_size),
                    arguments: Rc::new([]),
                }
            }
            item => unreachable!("type_for_item {:?}", item),
        }
    }

    fn typed_literal(
        &mut self,
        literal: &Literal,
        expected_type: Option<&Type>,
    ) -> Result<Literal> {
        // todo: if expected_type is a reference to (a reference to...) an integer type, use that since we may be
        // type checking a pattern literal
        Ok(if let Type::Integer(Integer::Unknown) = &literal.type_ {
            let string = str::from_utf8(self.load_slice(literal.offset))
                .unwrap()
                .to_owned();

            match expected_type.cloned() {
                Some(Type::Integer(integer_type)) => Literal {
                    offset: integer_type.parse(self, &string)?,
                    type_: Type::Integer(integer_type),
                },

                _ => Literal {
                    offset: self.store(string.parse::<i32>()?)?,
                    type_: Type::Integer(Integer::I32),
                },
            }
        } else {
            literal.clone()
        })
    }

    fn resolve_pattern(
        &mut self,
        path: &Path,
        parameters: &HashMap<NameId, Pattern>,
        complete: bool,
        scrutinee: &Term,
        default_binding_mode: BindingMode,
    ) -> Result<Pattern> {
        let item = self.find_item(path)?;

        match self.items[item.0].clone() {
            Item::Variant { item, name } => {
                let default_binding_mode = match (scrutinee.type_(), default_binding_mode) {
                    (
                        Type::Reference { unique: true, .. },
                        BindingMode::Move | BindingMode::MoveMut,
                    ) => BindingMode::RefMut,

                    (Type::Reference { unique: false, .. }, _) => BindingMode::Ref,
                    _ => default_binding_mode,
                };

                if let Item::Enum {
                    variants,
                    discriminant_type,
                    ..
                } = self.items[item.0].clone()
                {
                    if let Some(Variant {
                        fields,
                        discriminant,
                        ..
                    }) = variants.get(&name)
                    {
                        let missing_count =
                            fields.len().checked_sub(parameters.len()).ok_or_else(|| {
                                anyhow!(
                                    "too many parameters specified for variant {}",
                                    self.unintern(name)
                                )
                            })?;

                        let rest = parameters
                            .iter()
                            .find_map(|(name, pattern)| {
                                if matches!(pattern, Pattern::Rest) {
                                    Some(*name)
                                } else {
                                    None
                                }
                            })
                            .map(|name| self.unintern(name).parse::<usize>().unwrap());

                        let parameters = parameters
                            .iter()
                            .filter_map(|(name, pattern)| match pattern {
                                Pattern::Wildcard | Pattern::Rest => None,

                                _ => {
                                    let name = if let Some(rest) = rest {
                                        let index = self.unintern(*name).parse::<usize>().unwrap();

                                        if index > rest {
                                            self.intern(&(index + missing_count).to_string())
                                        } else {
                                            *name
                                        }
                                    } else {
                                        *name
                                    };

                                    Some(if let Some(field) = fields.get(&name) {
                                        self.resolve_known_field(&scrutinee.type_(), field)
                                            .and_then(|lens| {
                                                let pattern = self.type_check_pattern(
                                                    pattern,
                                                    &Term::Field {
                                                        base: Rc::new(scrutinee.clone()),
                                                        name,
                                                        lens,
                                                    },
                                                    default_binding_mode,
                                                )?;

                                                match_types_for_pattern(
                                                    &field.type_,
                                                    &pattern.type_(),
                                                )?;

                                                Ok((name, pattern))
                                            })
                                    } else {
                                        Err(anyhow!("unknown field: {}", self.unintern(name)))
                                    })
                                }
                            })
                            .collect::<Result<HashMap<_, _>>>()?;

                        if complete && !fields.keys().all(|name| parameters.contains_key(name)) {
                            return Err(anyhow!(
                                "missing fields in pattern: expected [{}], got [{}]",
                                fields
                                    .keys()
                                    .map(|&name| self.unintern(name))
                                    .collect::<Vec<_>>()
                                    .join(", "),
                                parameters
                                    .keys()
                                    .map(|&name| self.unintern(name))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ));
                        }

                        Ok(Pattern::Variant {
                            type_: self.type_for_item(item),
                            required_discriminant: *discriminant,
                            actual_discriminant: Term::Field {
                                base: Rc::new(scrutinee.clone()),
                                name: NameId(usize::MAX),
                                lens: self.resolve_known_field(
                                    &scrutinee.type_(),
                                    &Field {
                                        type_: Type::Integer(discriminant_type.unwrap()),
                                        offset: 0,
                                    },
                                )?,
                            },
                            parameters: parameters.into_values().collect(),
                        })
                    } else {
                        Err(anyhow!("unknown variant: {}", self.unintern(name)))
                    }
                } else {
                    unreachable!()
                }
            }

            item => todo!("resolve {item:?}"),
        }
    }

    fn type_check_pattern(
        &mut self,
        pattern: &Pattern,
        scrutinee: &Term,
        default_binding_mode: BindingMode,
    ) -> Result<Pattern> {
        match pattern {
            // todo: may need to deref scrutinee to match literal type
            Pattern::Literal { required, .. } => {
                let required = self.type_check(required, Some(&scrutinee.type_()))?;

                // todo: deduplicate this logic with respect to `match_types_for_pattern`
                let mut actual = scrutinee.clone();
                let required_type = required.type_();

                loop {
                    let actual_type = actual.type_();

                    if actual_type != Type::Never
                        && required_type != Type::Never
                        && actual_type != required_type
                    {
                        if let Type::Reference { .. } = actual_type {
                            actual = Term::UnaryOp(UnaryOp::Deref, Rc::new(actual.clone()))
                        } else {
                            return Err(anyhow!(
                                "pattern type mismatch: expected {:?}, got {required_type:?}",
                                scrutinee.type_()
                            ));
                        }
                    } else {
                        break;
                    }
                }

                Ok(Pattern::Literal { required, actual })
            }

            Pattern::Unresolved {
                path,
                parameters,
                complete,
            } => self.resolve_pattern(path, parameters, *complete, scrutinee, default_binding_mode),

            Pattern::Binding {
                binding_mode,
                name,
                subpattern,
                term,
            } => {
                let binding_mode = (*binding_mode).unwrap_or(default_binding_mode);

                let scrutinee = match binding_mode {
                    BindingMode::Move | BindingMode::MoveMut => scrutinee.clone(),
                    BindingMode::Ref | BindingMode::RefMut => {
                        let unique = matches!(binding_mode, BindingMode::RefMut);

                        if unique && !self.is_mutable(scrutinee) {
                            return Err(anyhow!("invalid unique reference to immutable term"));
                        }

                        Term::Reference(Rc::new(Reference {
                            unique,
                            term: scrutinee.clone(),
                        }))
                    }
                };

                let subpattern = subpattern
                    .as_ref()
                    .map(|subpattern| {
                        let subpattern =
                            self.type_check_pattern(subpattern, &scrutinee, default_binding_mode)?;

                        match_types_for_pattern(&scrutinee.type_(), &subpattern.type_())?;

                        Ok::<_, Error>(Rc::new(subpattern))
                    })
                    .transpose()?;

                *term.borrow_mut() = BindingTerm::Typed(scrutinee);

                self.bindings.push(Binding {
                    name: *name,
                    mutable: matches!(binding_mode, BindingMode::MoveMut),
                    term: term.clone(),
                });

                Ok(Pattern::Binding {
                    binding_mode: Some(binding_mode),
                    name: *name,
                    subpattern,
                    term: term.clone(),
                })
            }

            Pattern::Reference { unique, pattern } => {
                if let Type::Reference {
                    unique: type_unique,
                    ..
                } = scrutinee.type_()
                {
                    if *unique && !type_unique {
                        Err(anyhow!(
                            "attempt to match a unique reference pattern to a \
                             shared reference type: {:?}",
                            scrutinee.type_()
                        ))
                    } else {
                        self.type_check_pattern(
                            pattern,
                            &Term::UnaryOp(UnaryOp::Deref, Rc::new(scrutinee.clone())),
                            default_binding_mode,
                        )
                    }
                } else {
                    Err(anyhow!(
                        "attempt to match a reference pattern to a non-reference type: {:?}",
                        scrutinee.type_()
                    ))
                }
            }

            Pattern::Variant { .. } | Pattern::Wildcard | Pattern::Rest => Ok(pattern.clone()),
        }
    }

    fn stmt_to_term(&mut self, stmt: &Stmt) -> Result<Term> {
        let binding_count = self.bindings.len();

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

                                let term = Rc::new(RefCell::new(
                                    init.as_ref()
                                        .map(|(_, expr)| self.expr_to_term(expr))
                                        .transpose()?
                                        .map(BindingTerm::Untyped)
                                        .unwrap_or(BindingTerm::UntypedAndUninitialized),
                                ));

                                let index = self.bindings.len();

                                let result = self.sequence_for_temporaries(
                                    binding_count,
                                    Term::Let {
                                        name,
                                        mutable: mutability.is_some(),
                                        index,
                                        term: term.clone(),
                                    },
                                );

                                self.bindings.push(Binding {
                                    name,
                                    mutable: mutability.is_some(),
                                    term,
                                });

                                Ok(result)
                            }
                        }

                        _ => Err(anyhow!("pattern not yet supported: {pat:#?}")),
                    }
                }
            }

            _ => {
                let term = self.non_binding_stmt_to_term(stmt)?;

                Ok(self.sequence_for_temporaries(binding_count, term))
            }
        }
    }

    fn non_binding_stmt_to_term(&mut self, stmt: &Stmt) -> Result<Term> {
        match stmt {
            Stmt::Semi(expr, _) | Stmt::Expr(expr) => self.expr_to_term(expr),

            Stmt::Item(item) => match item {
                syn::Item::Struct(ItemStruct {
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
                }) => {
                    if !attrs.is_empty() {
                        Err(anyhow!("attributes not yet supported"))
                    } else if !params
                        .iter()
                        .all(|param| matches!(param, GenericParam::Lifetime(_)))
                    {
                        // todo: handle lifetimes
                        Err(anyhow!("generic parameters not yet supported"))
                    } else if where_clause.is_some() {
                        Err(anyhow!("where clauses not yet supported"))
                    } else if *vis != Visibility::Inherited {
                        Err(anyhow!("visibility not yet supported"))
                    } else {
                        let name = self.intern(&ident.to_string());

                        let fields = Rc::new(self.fields_to_fields(fields)?);

                        let item = self.add_item(Item::Unresolved(Rc::new(Item::Struct {
                            parameters: Rc::new([]),
                            fields,
                            methods: Rc::new([]),
                        })));

                        let items = &mut self.scopes.last().unwrap().borrow_mut().items;

                        if let Entry::Vacant(e) = items.entry(name) {
                            e.insert(item);

                            Ok(Term::Literal(self.unit.clone()))
                        } else {
                            Err(anyhow!("duplicate item identifier: {}", ident.to_string()))
                        }
                    }
                }

                syn::Item::Enum(ItemEnum {
                    ident,
                    generics:
                        Generics {
                            params,
                            where_clause,
                            ..
                        },
                    variants,
                    attrs,
                    vis,
                    ..
                }) => {
                    if !attrs.is_empty() {
                        Err(anyhow!("attributes not yet supported"))
                    } else if !params
                        .iter()
                        .all(|param| matches!(param, GenericParam::Lifetime(_)))
                    {
                        // todo: handle lifetimes
                        Err(anyhow!("generic parameters not yet supported"))
                    } else if where_clause.is_some() {
                        Err(anyhow!("where clauses not yet supported"))
                    } else if *vis != Visibility::Inherited {
                        Err(anyhow!("visibility not yet supported"))
                    } else {
                        let name = self.intern(&ident.to_string());

                        let mut default_discriminant = 0;
                        let mut min_discriminant = None;
                        let mut max_discriminant = None;

                        let variants = Rc::new(
                            variants
                                .iter()
                                .map(
                                    |syn::Variant {
                                         ident,
                                         fields,
                                         discriminant,
                                         attrs,
                                     }| {
                                        if !attrs.is_empty() {
                                            Err(anyhow!("attributes not yet supported"))
                                        } else {
                                            let discriminant = discriminant
                                                .as_ref()
                                                .map(|(_, expr)| {
                                                    let term = self.expr_to_term(expr)?;

                                                    self.eval_discriminant(&term)
                                                })
                                                .transpose()?
                                                .unwrap_or(default_discriminant);

                                            min_discriminant =
                                                Some(if let Some(min) = min_discriminant {
                                                    if min > discriminant {
                                                        discriminant
                                                    } else {
                                                        min
                                                    }
                                                } else {
                                                    discriminant
                                                });

                                            max_discriminant =
                                                Some(if let Some(max) = max_discriminant {
                                                    if max < discriminant {
                                                        discriminant
                                                    } else {
                                                        max
                                                    }
                                                } else {
                                                    discriminant
                                                });

                                            default_discriminant = discriminant + 1;

                                            let name = self.intern(&ident.to_string());

                                            Ok((
                                                name,
                                                Variant {
                                                    item: self.add_item(Item::Variant {
                                                        item: ItemId(usize::MAX),
                                                        name,
                                                    }),
                                                    fields: Rc::new(self.fields_to_fields(fields)?),
                                                    discriminant,
                                                },
                                            ))
                                        }
                                    },
                                )
                                .collect::<Result<HashMap<_, _>>>()?,
                        );

                        // todo: use #[repr(_)] attribute if present (but still check that bounds fit)

                        let discriminant_type =
                            if let (Some(min), Some(max)) = (min_discriminant, max_discriminant) {
                                Some(if min >= i8::MIN.into() && max <= i8::MAX.into() {
                                    Integer::I8
                                } else if min >= u8::MIN.into() && max <= u8::MAX.into() {
                                    Integer::U8
                                } else if min >= i16::MIN.into() && max <= i16::MAX.into() {
                                    Integer::I16
                                } else if min >= u16::MIN.into() && max <= u16::MAX.into() {
                                    Integer::U16
                                } else if min >= i32::MIN.into() && max <= i32::MAX.into() {
                                    Integer::I32
                                } else if min >= u32::MIN.into() && max <= u32::MAX.into() {
                                    Integer::U32
                                } else if min >= i64::MIN.into() && max <= i64::MAX.into() {
                                    Integer::I64
                                } else if min >= u64::MIN.into() && max <= u64::MAX.into() {
                                    Integer::U64
                                } else {
                                    Integer::I128
                                })
                            } else {
                                None
                            };

                        let item = self.add_item(Item::Unresolved(Rc::new(Item::Enum {
                            parameters: Rc::new([]),
                            discriminant_type,
                            variants: variants.clone(),
                            methods: Rc::new([]),
                        })));

                        for Variant {
                            item: variant_item, ..
                        } in variants.values()
                        {
                            if let Item::Variant {
                                item: variant_item, ..
                            } = &mut self.items[variant_item.0]
                            {
                                *variant_item = item;
                            }
                        }

                        let items = &mut self.scopes.last().unwrap().borrow_mut().items;

                        if let Entry::Vacant(e) = items.entry(name) {
                            e.insert(item);

                            Ok(Term::Literal(self.unit.clone()))
                        } else {
                            Err(anyhow!("duplicate item identifier: {}", ident.to_string()))
                        }
                    }
                }

                _ => Err(anyhow!("item not yet supported: {item:#?}")),
            },

            _ => Err(anyhow!("stmt not yet supported: {stmt:#?}")),
        }
    }

    fn eval_discriminant(&self, term: &Term) -> Result<i128> {
        match term {
            Term::Literal(Literal {
                type_: Type::Integer(integer_type),
                offset,
            }) => match integer_type {
                Integer::Unknown => {
                    let s = str::from_utf8(self.load_slice(*offset)).unwrap();

                    s.parse().map_err(|e: ParseIntError| {
                        if s.parse::<u128>().is_ok() {
                            anyhow!("u128 discriminants not yet supported")
                        } else {
                            e.into()
                        }
                    })
                }

                _ => Ok(integer_type.load_i128(self, *offset)),
            },

            Term::UnaryOp(UnaryOp::Neg, term) => Ok(-self.eval_discriminant(term)?),

            _ => Err(anyhow!("unable to evaluate {term:?} as enum discriminant")),
        }
    }

    fn expr_to_term(&mut self, expr: &Expr) -> Result<Term> {
        fn parse<T: ToBytes + FromStr>(
            env: &mut Env,
            value: &str,
            integer_type: Integer,
        ) -> Result<Term>
        where
            <T as FromStr>::Err: error::Error + Send + Sync + 'static,
        {
            Ok(Term::Literal(Literal {
                offset: env.store(value.parse::<T>()?)?,
                type_: Type::Integer(integer_type),
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
                                offset: self.store_slice(lit.base10_digits().as_bytes())?,
                                type_: Type::Integer(Integer::Unknown),
                            })),

                            suffix => integer_suffix_op!(parse, suffix, self, lit.base10_digits()),
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

            Expr::Path(ExprPath { path, qself, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if qself.is_some() {
                    Err(anyhow!("qualified paths not yet supported"))
                } else {
                    let path = self.path_to_path(path)?;

                    if !path.absolute && path.segments.len() == 1 {
                        Ok(Term::Variable {
                            index: self.find_binding(path.segments[0]).ok_or_else(|| {
                                anyhow!("symbol not found: {}", self.unintern(path.segments[0]))
                            })?,
                            type_: Type::Never,
                        })
                    } else {
                        Ok(Term::Unresolved(path))
                    }
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
                        pattern: Pattern::Literal {
                            required: Term::Literal(self.true_.clone()),
                            actual: Term::Literal(self.unit.clone()),
                        },
                        guard: None,
                        body: self.block_to_term(stmts)?,
                    };

                    let else_ = MatchArm {
                        pattern: Pattern::Literal {
                            required: Term::Literal(self.false_.clone()),
                            actual: Term::Literal(self.unit.clone()),
                        },
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
                    Ok(Term::Reference(Rc::new(Reference {
                        unique: mutability.is_some(),
                        term: self.expr_to_referenced_term(expr)?,
                    })))
                }
            }

            Expr::Struct(ExprStruct {
                path,
                fields,
                attrs,
                rest,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if rest.is_some() {
                    Err(anyhow!("move initialization not yet supported"))
                } else {
                    let type_ = Type::Unresolved(self.path_to_path(path)?);

                    let mut arguments = HashMap::new();

                    // todo: need to preserve evaluation order of fields since terms may have side-effects

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

                            if let Entry::Vacant(e) = arguments.entry(name) {
                                e.insert(self.expr_to_term(expr)?);
                            } else {
                                return Err(anyhow!(
                                    "duplicate field in struct initializer: {}",
                                    self.unintern(name)
                                ));
                            }
                        }
                    }

                    Ok(Term::Struct {
                        type_,
                        arguments: Rc::new(arguments),
                    })
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
                        base: Rc::new(self.expr_to_term(base)?),
                        name: self.intern_member(member),
                        lens: Lens::Unresolved,
                    })
                }
            }

            Expr::Call(ExprCall {
                func, args, attrs, ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Term::Application {
                        abstraction: Rc::new(self.expr_to_term(func)?),
                        arguments: args
                            .iter()
                            .map(|expr| self.expr_to_term(expr))
                            .collect::<Result<_>>()?,
                    })
                }
            }

            Expr::Match(ExprMatch {
                expr, arms, attrs, ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    let scrutinee = self.expr_to_referenced_term(expr)?;

                    let binding_count = self.bindings.len();

                    let term = Term::Match {
                        scrutinee: Rc::new(scrutinee),
                        arms: arms
                            .iter()
                            .map(
                                |Arm {
                                     pat,
                                     guard,
                                     body,
                                     attrs,
                                     ..
                                 }| {
                                    if !attrs.is_empty() {
                                        Err(anyhow!("attributes not yet supported"))
                                    } else {
                                        let result = Ok(MatchArm {
                                            pattern: self.pat_to_pattern(pat)?,
                                            guard: guard
                                                .as_ref()
                                                .map(|(_, expr)| self.expr_to_term(expr))
                                                .transpose()?,
                                            body: self.expr_to_term(body)?,
                                        });

                                        self.bindings.truncate(binding_count);

                                        result
                                    }
                                },
                            )
                            .collect::<Result<_>>()?,
                    };

                    Ok(self.sequence_for_temporaries(binding_count, term))
                }
            }

            Expr::Tuple(ExprTuple { elems, attrs, .. }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if elems.is_empty() {
                    Ok(Term::Literal(self.unit.clone()))
                } else {
                    Err(anyhow!("tuples not yet supported"))
                }
            }

            _ => Err(anyhow!("expr not yet supported: {expr:#?}")),
        }
    }

    fn expr_to_referenced_term(&mut self, expr: &Expr) -> Result<Term> {
        let mut term = self.expr_to_term(expr)?;

        if term.temporary_needs_binding() {
            let index = self.bindings.len();
            let name = self.intern(&index.to_string());

            self.bindings.push(Binding {
                name,
                mutable: true,
                term: Rc::new(RefCell::new(BindingTerm::Untyped(term))),
            });

            term = Term::Variable {
                index,
                type_: Type::Never,
            };
        }

        Ok(term)
    }

    fn pat_to_pattern(&mut self, pat: &Pat) -> Result<Pattern> {
        match pat {
            Pat::Path(PatPath { path, attrs, qself }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else if qself.is_some() {
                    Err(anyhow!("qualified paths not yet supported"))
                } else {
                    Ok(Pattern::Unresolved {
                        path: self.path_to_path(path)?,
                        parameters: Rc::new(HashMap::new()),
                        complete: true,
                    })
                }
            }

            Pat::TupleStruct(PatTupleStruct {
                path,
                pat:
                    PatTuple {
                        attrs: tuple_attrs,
                        elems,
                        ..
                    },
                attrs,
            }) => {
                if !attrs.is_empty() || !tuple_attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Pattern::Unresolved {
                        path: self.path_to_path(path)?,
                        parameters: Rc::new(
                            elems
                                .iter()
                                .enumerate()
                                .map(|(index, pat)| {
                                    Ok((self.intern(&index.to_string()), self.pat_to_pattern(pat)?))
                                })
                                .collect::<Result<_>>()?,
                        ),
                        complete: !elems
                            .iter()
                            .any(|pat| matches!(pat, Pat::Rest(_) | Pat::Wild(_))),
                    })
                }
            }

            Pat::Struct(PatStruct {
                path,
                fields,
                dot2_token,
                attrs,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Pattern::Unresolved {
                        path: self.path_to_path(path)?,
                        parameters: Rc::new(
                            fields
                                .iter()
                                .map(
                                    |FieldPat {
                                         member, pat, attrs, ..
                                     }| {
                                        if !attrs.is_empty() {
                                            Err(anyhow!("attributes not yet supported"))
                                        } else {
                                            Ok((
                                                self.intern_member(member),
                                                self.pat_to_pattern(pat)?,
                                            ))
                                        }
                                    },
                                )
                                .collect::<Result<_>>()?,
                        ),
                        complete: dot2_token.is_none(),
                    })
                }
            }

            Pat::Ident(PatIdent {
                by_ref,
                mutability,
                ident,
                subpat,
                attrs,
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    let name = self.intern(&ident.to_string());

                    let term = Rc::new(RefCell::new(BindingTerm::UntypedAndUninitialized));

                    self.bindings.push(Binding {
                        name,
                        mutable: mutability.is_some(),
                        term: term.clone(),
                    });

                    Ok(Pattern::Binding {
                        binding_mode: if by_ref.is_some() {
                            Some(if mutability.is_some() {
                                BindingMode::RefMut
                            } else {
                                BindingMode::Ref
                            })
                        } else if mutability.is_some() {
                            Some(BindingMode::MoveMut)
                        } else {
                            None
                        },
                        name,
                        subpattern: subpat
                            .as_ref()
                            .map(|(_, pat)| Ok::<_, Error>(Rc::new(self.pat_to_pattern(pat)?)))
                            .transpose()?,
                        term,
                    })
                }
            }

            Pat::Wild(PatWild { attrs, .. }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Pattern::Wildcard)
                }
            }

            Pat::Rest(PatRest { attrs, .. }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Pattern::Rest)
                }
            }

            Pat::Reference(PatReference {
                mutability,
                pat,
                attrs,
                ..
            }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Pattern::Reference {
                        unique: mutability.is_some(),
                        pattern: Rc::new(self.pat_to_pattern(pat)?),
                    })
                }
            }

            Pat::Lit(PatLit { expr, attrs }) => {
                if !attrs.is_empty() {
                    Err(anyhow!("attributes not yet supported"))
                } else {
                    Ok(Pattern::Literal {
                        required: self.expr_to_term(expr)?,
                        actual: Term::Literal(self.unit.clone()),
                    })
                }
            }

            _ => Err(anyhow!("pattern not yet supported: {pat:#?}")),
        }
    }

    fn path_to_path(
        &mut self,
        syn::Path {
            leading_colon,
            segments,
        }: &syn::Path,
    ) -> Result<Path> {
        Ok(Path {
            absolute: leading_colon.is_some(),
            segments: segments
                .iter()
                .map(|PathSegment { ident, arguments }| {
                    match arguments {
                        PathArguments::None => (),
                        PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                            args,
                            ..
                        }) if args
                            .iter()
                            .all(|arg| matches!(arg, GenericArgument::Lifetime(_))) =>
                            // todo: handle lifetimes
                            {}
                        _ => return Err(anyhow!("path arguments not yet supported")),
                    }

                    Ok(self.intern(&ident.to_string()))
                })
                .collect::<Result<_>>()?,
        })
    }

    fn sequence_for_temporaries(&mut self, binding_count: usize, term: Term) -> Term {
        if self.bindings.len() > binding_count {
            let terms = self
                .bindings
                .iter()
                .enumerate()
                .skip(binding_count)
                .map(
                    |(
                        index,
                        Binding {
                            name,
                            mutable,
                            term,
                        },
                    )| Term::Let {
                        name: *name,
                        mutable: *mutable,
                        term: term.clone(),
                        index,
                    },
                )
                // todo: store this term in a let binding, append drop calls for any temporaries whose lifetimes
                // should *not* be extended according to
                // https://doc.rust-lang.org/reference/destructors.html#temporary-lifetime-extension, and finally
                // end the sequence with the variable referencing the aformentioned binding
                .chain(iter::once(term))
                .collect();

            Term::Sequence(terms)
        } else {
            term
        }
    }

    fn block_to_term(&mut self, stmts: &[Stmt]) -> Result<Term> {
        let binding_count = self.bindings.len();

        self.scopes.push(Rc::new(RefCell::new(Scope::new())));

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

    fn fields_to_fields(&mut self, fields: &Fields) -> Result<HashMap<NameId, Field>> {
        let empty = Punctuated::new();

        match fields {
            Fields::Named(FieldsNamed { named, .. }) => named,
            Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => unnamed,
            Fields::Unit => &empty,
        }
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
                } else if *vis != Visibility::Inherited {
                    Err(anyhow!("visibility not yet supported"))
                } else {
                    Ok((
                        self.intern(
                            &ident
                                .as_ref()
                                .map(|ident| ident.to_string())
                                .unwrap_or_else(|| index.to_string()),
                        ),
                        Field {
                            type_: self.type_to_type(ty)?,
                            offset: 0,
                        },
                    ))
                }
            },
        )
        .collect()
    }

    fn type_to_type(&mut self, type_: &syn::Type) -> Result<Type> {
        match type_ {
            syn::Type::Path(TypePath { path, qself }) => {
                if qself.is_some() {
                    Err(anyhow!("qualified paths not yet supported"))
                } else {
                    Ok(Type::Unresolved(self.path_to_path(path)?))
                }
            }

            syn::Type::Reference(TypeReference {
                mutability, elem, ..
            }) => {
                // todo: handle lifetime
                self.type_to_type(elem).map(|type_| Type::Reference {
                    unique: mutability.is_some(),
                    type_: Rc::new(type_),
                })
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

        Ok(match Env::default().eval_line(line)? {
            Eval::Result(result) => T::from_bytes(&result.value),
            eval => return Err(anyhow!("expected Eval::Result, got {eval}")),
        })
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
    fn bad_struct_field_access() {
        assert!(eval::<()>("{ struct Foo { x: i64, y: i64 } let f: Foo; f.x }").is_err())
    }

    #[test]
    fn struct_field_mutation() {
        assert_eq!(
            56_i64,
            eval("{ struct Foo { x: i64, y: i64 } let mut f = Foo { x: 7, y: 14 }; f.y = 49; f.x + f.y }").unwrap()
        )
    }

    #[test]
    fn bad_immutable_struct_field_mutation() {
        assert!(eval::<()>(
            "{ struct Foo { x: i64, y: i64 } let f = Foo { x: 7, y: 14 }; f.y = 49; f.x + f.y }"
        )
        .is_err())
    }

    #[test]
    fn bad_uninitialized_struct_field_mutation() {
        assert!(
            eval::<()>("{ struct Foo { x: i64, y: i64 } let f: Foo; f.y = 49; f.x + f.y }")
                .is_err()
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
            484_i64,
            eval(
                "{ struct Foo { x: i64, y: i64 } \
                 let mut f = Foo { x: 7, y: 14 }; \
                 let y = &mut f.y; \
                 *y = 22; \
                 f.y * *y }"
            )
            .unwrap()
        )
    }

    #[test]
    fn bad_struct_field_unique_reference() {
        assert!(eval::<()>(
            "{ struct Foo { x: i64, y: i64 } \
             let f = Foo { x: 7, y: 14 }; \
             let y = &mut f.y; \
             *y = 22; \
             f.y * *y }"
        )
        .is_err())
    }

    #[test]
    fn struct_field_reference_chain() {
        assert_eq!(
            160034_i64,
            eval(
                "{ struct Foo<'a> { w: i64, x: &'a i64 } \
                 struct Bar<'a, 'b> { a: &'a Foo<'b> } \
                 struct Baz<'a, 'b> { w: i64, z: Bar<'a, 'b> } \
                 let y = 71; \
                 let f = Foo { w: 98, x: &y }; \
                 let b = Bar { a: &f }; \
                 let z = Baz { w: 23, z: b }; \
                 z.w * z.z.a.w * *z.z.a.x }"
            )
            .unwrap()
        )
    }

    #[test]
    fn reference_to_temporary() {
        assert_eq!(40_i32, eval("*&(33 + 7)").unwrap())
    }

    #[test]
    fn bound_reference_to_temporary() {
        assert_eq!(40_i32, eval("{ let x = &(33 + 7); *x }").unwrap())
    }

    #[test]
    fn simple_enum() {
        assert_eq!(
            87_i32,
            eval(
                "{ enum Foo { A, B } \
                 let f = Foo::A; \
                 match f { \
                 Foo::A => 87, \
                 Foo::B => 21, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple() {
        assert_eq!(
            12_u32,
            eval(
                "{ enum Foo { A, B(u32) } \
                 let f = Foo::B(12); \
                 match f { \
                 Foo::A => 87_u32, \
                 Foo::B(x) => x, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple_skip() {
        assert_eq!(
            12_u32,
            eval(
                "{ enum Foo { A, B(u32, u32, u32, u32, u32, u32) } \
                 let f = Foo::B(1, 2, 3, 4, 5, 6); \
                 match f { \
                 Foo::A => 87_u32, \
                 Foo::B(a, _, .., b, c) => a + b + c, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple_ref_scrutinee() {
        assert_eq!(
            12_u32,
            eval(
                "{ enum Foo { A, B(u32) } \
                 let f = Foo::B(12); \
                 match &f { \
                 Foo::A => 87_u32, \
                 Foo::B(x) => *x, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple_ref_scrutinee_deref() {
        assert_eq!(
            12_u32,
            eval(
                "{ enum Foo { A, B(u32) } \
                 let f = Foo::B(12); \
                 match &f { \
                 Foo::A => 87_u32, \
                 &Foo::B(x) => x, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple_ref_scrutinee_deref_ref() {
        assert_eq!(
            12_u32,
            eval(
                "{ enum Foo { A, B(u32) } \
                 let f = Foo::B(12); \
                 match &f { \
                 Foo::A => 87_u32, \
                 &Foo::B(ref x) => *x, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple_ref_field() {
        assert_eq!(
            12_u32,
            eval(
                "{ enum Foo { A, B(u32) } \
                 let f = Foo::B(12); \
                 match f { \
                 Foo::A => 87_u32, \
                 Foo::B(ref x) => *x, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple_mut_field() {
        assert_eq!(
            15_u32,
            eval(
                "{ enum Foo { A, B(u32) } \
                 let f = Foo::B(12); \
                 match f { \
                 Foo::A => 87_u32, \
                 Foo::B(mut x) => { \
                 x += 3; \
                 x \
                 } } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn enum_tuple_ref_mut_field() {
        assert_eq!(
            16_u32,
            eval(
                "{ enum Foo { A, B(u32) } \
                 let mut f = Foo::B(12); \
                 match f { \
                 Foo::A => (), \
                 Foo::B(ref mut x) => { \
                 *x += 4; \
                 } } \
                 match f { \
                 Foo::A => 87_u32, \
                 Foo::B(x) => { \
                 x \
                 } } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn bad_enum_tuple_ref_mut_field() {
        assert!(eval::<()>(
            "{ enum Foo { A, B(u32) } \
             let f = Foo::B(12); \
             match f { \
             Foo::A => (), \
             Foo::B(ref mut x) => { \
             *x += 4; \
             } } \
             match f { \
             Foo::A => 87_u32, \
             Foo::B(x) => { \
             x \
             } } }"
        )
        .is_err())
    }

    #[test]
    fn enum_named_fields() {
        assert_eq!(
            187_u64,
            eval(
                "{ enum Foo { A { x: u8, y: u64, z: u32 }, B(u32) } \
                 let f = Foo::A { x: 7, y: 187, z: 22 };
                 match f { \
                 Foo::A { y, .. } => y, \
                 Foo::B(_) => 91, \
                 } }"
            )
            .unwrap()
        )
    }

    #[test]
    fn match_reference_to_literal() {
        assert_eq!(
            7_i32,
            eval("{ let x = 42; match &x { 42 => 7, _ => 8 } }").unwrap()
        )
    }
}
