use serde::{Deserialize, Serialize};
use std::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

/// The id of a `T` in its table.
#[derive(PartialEq, Eq, Hash)]
pub struct Id<T>(pub(super) u32, PhantomData<fn() -> T>);

impl<T> Id<T> {
    pub(super) const fn new(i: u32) -> Self {
        Self(i, PhantomData)
    }

    /// The id as an index, for arrays sized by a table's `bound`.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Id<T> {}

impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

pub type NameId = Id<Name>;

pub type LevelId = Id<Level>;

pub type ExprId = Id<Expr>;

/// The universe levels of a constant, interned so that a `Const` node holds only an id.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Univs(pub Box<[LevelId]>);

pub type UnivsId = Id<Univs>;

/// The fields of a `let`, boxed to keep `Expr` at 16 bytes.
#[derive(Debug, Clone)]
pub struct LetNode(pub NameId, pub ExprId, pub ExprId, pub ExprId);

pub const ANON: NameId = Id::new(0);

pub const ZERO: LevelId = Id::new(0);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Name {
    Anon,
    Str(NameId, Box<str>),
    Num(NameId, u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Binder {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// Equality and hashing ignore binder names and annotations, matching Lean's `BEq Expr`,
/// so terms that differ only there share one id, as they do in lean4export.
///
/// The binder names and annotations of a shared node are those of the earliest module in
/// import order to have it. [`Const::binders`] has a constant's own.
#[derive(Debug, Clone)]
pub enum Expr {
    BVar(u64),
    Sort(LevelId),
    Const(NameId, UnivsId),
    App(ExprId, ExprId),
    Lam(NameId, ExprId, ExprId, Binder),
    Pi(NameId, ExprId, ExprId, Binder),
    Let(Box<LetNode>),
    Nat(Box<Box<str>>),
    Str(Box<Box<str>>),
    Proj(NameId, u32, ExprId),
}

const _: () = assert!(std::mem::size_of::<Expr>() == 16);

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::BVar(a), Self::BVar(b)) => a == b,
            (Self::Sort(a), Self::Sort(b)) => a == b,
            (Self::Const(n, us), Self::Const(m, vs)) => n == m && us == vs,
            (Self::App(f, a), Self::App(g, b)) => f == g && a == b,
            (Self::Lam(_, t, b, _), Self::Lam(_, u, c, _))
            | (Self::Pi(_, t, b, _), Self::Pi(_, u, c, _)) => t == u && b == c,
            (Self::Let(x), Self::Let(y)) => x.1 == y.1 && x.2 == y.2 && x.3 == y.3,
            (Self::Nat(a), Self::Nat(b)) | (Self::Str(a), Self::Str(b)) => a == b,
            (Self::Proj(n, i, x), Self::Proj(m, j, y)) => n == m && i == j && x == y,
            _ => false,
        }
    }
}

impl Eq for Expr {}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, h: &mut H) {
        let pack = |a: u32, b: u32| u64::from(a) << 32 | u64::from(b);
        match self {
            Self::BVar(i) => h.write_u64(*i),
            Self::Sort(l) => h.write_u32(l.0),
            Self::Const(n, us) => {
                h.write_u32(n.0);
                h.write_u32(us.0);
            }
            Self::App(f, a) => h.write_u64(pack(f.0, a.0)),
            Self::Lam(_, t, b, _) | Self::Pi(_, t, b, _) => h.write_u64(pack(t.0, b.0)),
            Self::Let(l) => {
                h.write_u64(pack(l.1 .0, l.2 .0));
                h.write_u32(l.3 .0);
            }
            Self::Nat(v) | Self::Str(v) => h.write(v.as_bytes()),
            Self::Proj(n, i, x) => {
                h.write_u64(pack(n.0, x.0));
                h.write_u64(u64::from(*i));
            }
        }
        h.write_u8(self.tag());
    }
}

impl Expr {
    const fn tag(&self) -> u8 {
        match self {
            Self::BVar(_) => 0,
            Self::Sort(_) => 1,
            Self::Const(..) => 2,
            Self::App(..) => 3,
            Self::Lam(..) => 4,
            Self::Pi(..) => 5,
            Self::Let(..) => 6,
            Self::Nat(_) => 7,
            Self::Str(_) => 8,
            Self::Proj(..) => 9,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Debug)]
pub struct Rule {
    pub ctor: NameId,
    pub nfields: u64,
    pub rhs: ExprId,
}

#[derive(Debug)]
pub struct Defn {
    pub value: ExprId,
    pub hints: Hints,
    pub all: Vec<NameId>,
}

/// The value of an opaque constant.
#[derive(Debug)]
pub struct Body {
    pub value: ExprId,
    pub all: Vec<NameId>,
}

/// A theorem. Its value is `None` when [`Env::load_cone`] did not need it.
#[derive(Debug)]
pub struct Theorem {
    pub value: Option<ExprId>,
    pub all: Vec<NameId>,
}

#[derive(Debug)]
pub struct Inductive {
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

#[derive(Debug)]
pub struct Ctor {
    pub induct: NameId,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

#[derive(Debug)]
pub struct Rec {
    pub all: Vec<NameId>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<Rule>,
    pub k: bool,
}

#[derive(Debug)]
pub enum Kind {
    Axiom,
    Defn(Defn),
    Thm(Theorem),
    Opaque(Body),
    Quot(QuotKind),
    Induct(Inductive),
    Ctor(Ctor),
    Rec(Rec),
}

/// A declaration the kernel would accept. Unsafe and partial ones are dropped at load time.
#[derive(Debug)]
pub struct Const {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
    /// The name and annotation of each leading `∀` of `ty`, as this constant's own olean has
    /// them. `ty` is shared with every type that differs only there, so its own may be
    /// another constant's.
    pub binders: Box<[(NameId, Binder)]>,
    pub kind: Kind,
}
