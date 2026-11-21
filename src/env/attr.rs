use super::term::{Id, NameId};
use std::ops::Index;

pub type ValueId = Id<Value>;

/// An object of an environment extension entry, read by its layout alone since the olean
/// does not say what type it has.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// Anything Lean keeps unboxed: a small `Nat`, a `Bool`, a constructor without fields
    /// by its index, or `Name.anonymous`.
    Scalar(u64),
    /// A `Nat` past 63 bits, in decimal.
    Nat(Box<str>),
    Str(Box<str>),
    /// A name other than `Name.anonymous`.
    Name(NameId),
    Array(Box<[ValueId]>),
    /// A `ByteArray` or `FloatArray`, as its bytes.
    Bytes(Box<[u8]>),
    /// Any other constructor. `scalars` is its scalar area, zero padded to whole words.
    Ctor {
        tag: u8,
        fields: Box<[ValueId]>,
        scalars: Box<[u8]>,
    },
}

/// Where an attribute applies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    Global,
    /// Only while this namespace is open.
    Scoped(NameId),
}

/// One entry a module exports for a whitelisted extension.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Attr {
    /// The extension, as an index into the whitelist.
    pub attr: usize,
    pub scope: Scope,
    /// The declaration the entry is about, where the entry is its name or leads with it.
    pub decl: Option<NameId>,
    /// The whole entry, in [`Attrs::values`].
    pub entry: ValueId,
}

/// Where one module keeps the entries of one extension asked for, for [`crate::Env::attrs_of`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Entries {
    /// The extension, as an index into the list asked for.
    pub attr: usize,
    /// How many entries there are.
    pub len: usize,
    /// The address of the entries array in the module's public part.
    pub(super) at: u64,
}

/// The entries one module exports for the whitelisted extensions, in the order the olean
/// holds them. For a module in the module system they are those of its public part.
#[derive(Debug, Clone, Default)]
pub struct Attrs {
    pub entries: Vec<Attr>,
    /// The objects the entries are made of, each once however often it is shared.
    pub values: Vec<Value>,
}

impl Attrs {
    /// The scope of `entry` and the declaration it is about, as far as its layout shows them.
    ///
    /// The scope is that of a `ScopedEnvExtension.Entry`, `global a` or `scoped ns a`, and
    /// anything else is global as a whole. The declaration is what is left where that is a
    /// name or a constructor leading with one, as a tag attribute's `Name` and a parametric
    /// attribute's `Name × α` are.
    pub(super) fn classify(&self, entry: ValueId) -> (Scope, Option<NameId>) {
        let name = |id: ValueId| match self[id] {
            Value::Name(n) => Some(n),
            _ => None,
        };
        let (scope, inner) = match &self[entry] {
            Value::Ctor {
                tag: 0,
                fields,
                scalars,
            } if fields.len() == 1 && scalars.is_empty() => (Scope::Global, fields[0]),
            Value::Ctor {
                tag: 1,
                fields,
                scalars,
            } if fields.len() == 2 && scalars.is_empty() => {
                name(fields[0]).map_or((Scope::Global, entry), |ns| (Scope::Scoped(ns), fields[1]))
            }
            _ => (Scope::Global, entry),
        };
        let decl = name(inner).or_else(|| match &self[inner] {
            Value::Ctor { fields, .. } => fields.first().and_then(|&f| name(f)),
            _ => None,
        });
        (scope, decl)
    }
}

impl Index<ValueId> for Attrs {
    type Output = Value;

    fn index(&self, id: ValueId) -> &Value {
        &self.values[id.index()]
    }
}
