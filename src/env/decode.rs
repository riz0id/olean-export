use super::{
    attr::{Attr, Attrs, Entries, Value, ValueId},
    escape,
    reload::Live,
    table::Tables,
    term::{
        Binder, Body, Const, Ctor, Defn, Expr, ExprId, Hints, Id, Inductive, Kind, LetNode, Level,
        LevelId, Name, NameId, QuotKind, Rec, Rule, Theorem, Univs, ANON, ZERO,
    },
    Env,
};
use crate::{
    error::{at, corrupt, Error, Result},
    inspect::Import,
    olean::{
        is_scalar, small_nat, Header, Image, Safety, Shape, AXIOM, CTOR, DEFN, INDUCT, OPAQUE,
        QUOT, REC, THM,
    },
};
use rayon::prelude::*;
use rustc_hash::FxHashMap;
use std::{
    ops::Range,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
};

/// What one module adds besides table entries.
pub(super) struct Module {
    pub(super) consts: Vec<Const>,
    pub(super) recursors: FxHashMap<NameId, Vec<NameId>>,
    pub(super) skipped: usize,
    pub(super) header: Header,
    pub(super) imports: Vec<Import>,
    pub(super) exported: Option<FxHashMap<NameId, bool>>,
    /// Theorems whose values were left in the olean, with the values' addresses.
    pub(super) pending: Vec<(NameId, u64)>,
    /// The entries of the extensions asked for.
    pub(super) attrs: Attrs,
    /// Where the entries of the extensions asked for are, when they are left in the olean.
    pub(super) index: Vec<Entries>,
}

impl Module {
    fn new(header: Header) -> Self {
        Self {
            consts: Vec::new(),
            recursors: FxHashMap::default(),
            skipped: 0,
            header,
            imports: Vec::new(),
            exported: None,
            pending: Vec::new(),
            attrs: Attrs::default(),
            index: Vec::new(),
        }
    }
}

fn decode(
    tables: &Tables,
    rank: u32,
    cursor: &mut Option<usize>,
    path: &Path,
    lazy: bool,
    attrs: &[&str],
    index: bool,
) -> Result<Module> {
    let img = Image::open_module(path)?;
    let mut dec = Decoder::new(&img, tables, rank, cursor, lazy);
    dec.run(attrs, index).map_err(at(path))?;
    dec.module.imports = img.imports().map_err(at(path))?;
    Ok(dec.module)
}

/// Decode the modules at `paths`, each with its rank in import order, on `jobs` threads,
/// along with the entries of the environment extensions named in `attrs`, or with only
/// where they are if `index`.
pub(super) fn decode_all(
    tables: &Tables,
    paths: &[(usize, &Path)],
    jobs: usize,
    progress: &(dyn Fn(usize, usize) + Sync),
    lazy: bool,
    attrs: &[&str],
    index: bool,
) -> Result<Vec<Module>> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs.max(1))
        .build()?;
    let (done, consts) = (AtomicUsize::new(0), AtomicUsize::new(0));
    pool.install(|| {
        paths
            .par_iter()
            .map_init(
                || None,
                |cursor, &(rank, path)| {
                    let rank = u32::try_from(rank).expect("module count");
                    let m = decode(tables, rank, cursor, path, lazy, attrs, index)?;
                    let n = consts.fetch_add(m.consts.len(), Relaxed) + m.consts.len();
                    progress(done.fetch_add(1, Relaxed) + 1, n);
                    Ok(m)
                },
            )
            .collect()
    })
}

impl Image {
    pub(crate) fn imports(&self) -> Result<Vec<Import>> {
        let imports = self.array(self.field(self.root, 0)?)?;
        imports
            .into_iter()
            .map(|i| {
                Ok(Import {
                    module: self.str_name(self.field(i, 0)?)?,
                    all: self.scalar_u8(i, 0)? != 0,
                    exported: self.scalar_u8(i, 1)? != 0,
                    meta: self.scalar_u8(i, 2)? != 0,
                })
            })
            .collect()
    }

    pub(crate) fn str_name(&self, o: u64) -> Result<String> {
        self.join_name(o, false)
    }

    /// The name at `o` as [`Env::display`] writes it.
    pub(crate) fn display_name(&self, o: u64) -> Result<String> {
        self.join_name(o, true)
    }

    /// Whether the name at `o` is `name` as [`Image::str_name`] writes it, without building
    /// the string.
    pub(crate) fn name_is(&self, mut o: u64, name: &str) -> Result<bool> {
        let mut rest = name;
        let mut last = true;
        while !is_scalar(o) && self.tag(o)? != 0 {
            if !last {
                let Some(r) = rest.strip_suffix('.') else {
                    return Ok(false);
                };
                rest = r;
            }
            last = false;
            let arg = self.field(o, 1)?;
            let cut = if self.tag(o)? == 1 {
                rest.strip_suffix(self.str(arg)?)
            } else {
                rest.strip_suffix(self.nat_decimal(arg)?.as_str())
            };
            let Some(r) = cut else { return Ok(false) };
            rest = r;
            o = self.field(o, 0)?;
        }
        Ok(rest.is_empty())
    }

    fn join_name(&self, mut o: u64, escaped: bool) -> Result<String> {
        let mut parts = Vec::new();
        while !is_scalar(o) && self.tag(o)? != 0 {
            parts.push(if self.tag(o)? == 1 {
                let s = self.str(self.field(o, 1)?)?;
                if escaped {
                    escape(s).into_owned()
                } else {
                    s.to_owned()
                }
            } else {
                self.nat_decimal(self.field(o, 1)?)?
            });
            o = self.field(o, 0)?;
        }
        parts.reverse();
        Ok(parts.join("."))
    }
}

/// Translates one module's objects into the shared tables, memoized by address since the
/// compactor already maximally shares structurally equal objects within a module.
struct Decoder<'a> {
    img: &'a Image,
    tables: &'a Tables,
    /// The module's position in import order.
    rank: u32,
    /// The expression chunk this thread is filling.
    cursor: &'a mut Option<usize>,
    module: Module,
    /// Table id plus one for each decoded object, by slot. An object is only ever decoded as
    /// one of name, level or expression, so the kinds can share it.
    memo: Vec<u32>,
    /// Leave theorem values in the olean.
    lazy: bool,
}

/// The memo mark of an expression whose subterms are still being decoded.
const PENDING: u32 = u32::MAX;

impl<'a> Decoder<'a> {
    fn new(
        img: &'a Image,
        tables: &'a Tables,
        rank: u32,
        cursor: &'a mut Option<usize>,
        lazy: bool,
    ) -> Self {
        Self {
            img,
            tables,
            rank,
            cursor,
            memo: vec![0; img.slots()],
            module: Module::new(img.header.clone()),
            lazy,
        }
    }

    /// A decoder for extension entries only, which need no memo of names, levels and
    /// expressions and so are spared allocating one the size of the image.
    fn values(
        img: &'a Image,
        tables: &'a Tables,
        rank: u32,
        cursor: &'a mut Option<usize>,
    ) -> Self {
        Self {
            img,
            tables,
            rank,
            cursor,
            memo: Vec::new(),
            module: Module::new(img.header.clone()),
            lazy: false,
        }
    }

    fn run(&mut self, attrs: &[&str], index: bool) -> Result<()> {
        let img = self.img;
        for c in img.array(img.field(img.root, 2)?)? {
            self.constant(c)?;
        }
        if img.parts.len() > 1 {
            self.exported()?;
        }
        if !attrs.is_empty() {
            if index {
                self.attr_index(attrs)?;
            } else {
                self.attrs(attrs)?;
            }
        }
        Ok(())
    }

    /// The extensions the module exports entries for that are named in `wanted`, each as its
    /// index there and the address of its entries array.
    fn extensions(&self, wanted: &[&str]) -> Result<Vec<(usize, u64)>> {
        let img = self.img;
        let mut found = Vec::new();
        for ext in img.array(img.field(img.public, 4)?)? {
            let name = img.field(ext, 0)?;
            for (i, w) in wanted.iter().enumerate() {
                if img.name_is(name, w)? {
                    found.push((i, img.field(ext, 1)?));
                    break;
                }
            }
        }
        Ok(found)
    }

    /// The entries the module exports for the environment extensions named in `wanted`.
    fn attrs(&mut self, wanted: &[&str]) -> Result<()> {
        let img = self.img;
        let (mut memo, mut names) = (FxHashMap::default(), FxHashMap::default());
        for (attr, entries) in self.extensions(wanted)? {
            for e in img.array(entries)? {
                self.entry(attr, e, &mut memo, &mut names)?;
            }
        }
        Ok(())
    }

    /// Where the module keeps the entries of the extensions named in `wanted`, decoding none.
    fn attr_index(&mut self, wanted: &[&str]) -> Result<()> {
        for (attr, at) in self.extensions(wanted)? {
            let len = usize::try_from(self.img.u64(at + 8)?).map_err(corrupt)?;
            self.module.index.push(Entries { attr, len, at });
        }
        Ok(())
    }

    /// Decode the entries in each range of its extension's entries, sharing values across
    /// them.
    fn attr_ranges(&mut self, want: &[(Entries, Range<usize>)]) -> Result<()> {
        let (mut memo, mut names) = (FxHashMap::default(), FxHashMap::default());
        for (e, range) in want {
            if range.end.checked_sub(range.start).is_none() || range.end > e.len {
                return Err(Error::Misuse("entry range past the extension's entries"));
            }
            for i in range.clone() {
                let o = self.img.u64(e.at + 24 + 8 * i as u64)?;
                self.entry(e.attr, o, &mut memo, &mut names)?;
            }
        }
        Ok(())
    }

    /// Decode the entry at `o` of the extension `attr` and add it to the module's.
    fn entry(
        &mut self,
        attr: usize,
        o: u64,
        memo: &mut FxHashMap<u64, u32>,
        names: &mut FxHashMap<u64, NameId>,
    ) -> Result<()> {
        let entry = self.value(o, memo, names)?;
        let (scope, decl) = self.module.attrs.classify(entry);
        self.module.attrs.entries.push(Attr {
            attr,
            scope,
            decl,
            entry,
        });
        Ok(())
    }

    /// The name at `o`, if it has the layout of a `Name` other than `Name.anonymous`: a
    /// chain of `Name.str` and `Name.num`, each two fields and a hash, down to `box(0)`.
    ///
    /// `names` has the names found so far by address. They stay out of the decoder's own
    /// memo, which holds for an object decoded by its type that it is of no other kind, and
    /// a layout cannot tell a name from, say, the level `max 0 0`.
    fn layout_name(&self, o: u64, names: &mut FxHashMap<u64, NameId>) -> Result<Option<NameId>> {
        let img = self.img;
        if is_scalar(o) {
            return Ok(None);
        }
        let mut chain = Vec::new();
        let mut at = o;
        let mut pre = loop {
            if at == 1 {
                break ANON;
            }
            if let Some(&id) = names.get(&at) {
                break id;
            }
            if is_scalar(at) {
                return Ok(None);
            }
            let shape = img.shape(at)?;
            if !matches!(shape, Shape::Ctor(1 | 2))
                || img.num_objs(at)? != 2
                || img.scalars(at)?.len() != 8
            {
                return Ok(None);
            }
            let arg = img.field(at, 1)?;
            let fits = if shape == Shape::Ctor(1) {
                !is_scalar(arg) && img.shape(arg)? == Shape::Str
            } else {
                is_scalar(arg)
            };
            if !fits {
                return Ok(None);
            }
            chain.push((at, shape, arg));
            at = img.field(at, 0)?;
        };
        for (at, shape, arg) in chain.into_iter().rev() {
            let n = if shape == Shape::Ctor(1) {
                Name::Str(pre, img.str(arg)?.into())
            } else {
                Name::Num(pre, small_nat(arg)?)
            };
            pre = self.tables.names.intern(n);
            names.insert(at, pre);
        }
        Ok(Some(pre))
    }

    /// Decode the object at `root` by its layout, parts first, on a worklist. `memo` has the
    /// index of each value already in the module's arena by address, or by itself if unboxed.
    fn value(
        &mut self,
        root: u64,
        memo: &mut FxHashMap<u64, u32>,
        names: &mut FxHashMap<u64, NameId>,
    ) -> Result<ValueId> {
        /// An object to decode, or one whose parts now are.
        enum Frame {
            Visit(u64),
            Build(u64, Shape, Vec<u64>),
        }
        let img = self.img;
        let mut work = vec![Frame::Visit(root)];
        while let Some(frame) = work.pop() {
            let (o, v) = match frame {
                Frame::Visit(o) => {
                    match memo.get(&o) {
                        None => {}
                        Some(&PENDING) => return Err(corrupt("cyclic value")),
                        Some(_) => continue,
                    }
                    let v = if is_scalar(o) {
                        Value::Scalar(o >> 1)
                    } else if let Some(n) = self.layout_name(o, names)? {
                        Value::Name(n)
                    } else {
                        match img.shape(o)? {
                            Shape::Str => Value::Str(img.str(o)?.into()),
                            Shape::Nat => Value::Nat(img.nat_decimal(o)?.into()),
                            Shape::Bytes => Value::Bytes(img.scalar_array(o)?.into()),
                            shape => {
                                let parts = match shape {
                                    Shape::Array => img.array(o)?,
                                    Shape::Thunk => vec![img.u64(o + 8)?],
                                    _ => (0..img.num_objs(o)?)
                                        .map(|i| img.field(o, i))
                                        .collect::<Result<_>>()?,
                                };
                                memo.insert(o, PENDING);
                                let at = work.len();
                                work.push(Frame::Visit(o));
                                work.extend(parts.iter().rev().map(|&p| Frame::Visit(p)));
                                work[at] = Frame::Build(o, shape, parts);
                                continue;
                            }
                        }
                    };
                    (o, v)
                }
                Frame::Build(o, shape, parts) => {
                    let ids = parts.iter().map(|p| ValueId::new(memo[p])).collect();
                    let v = match shape {
                        Shape::Array => Value::Array(ids),
                        Shape::Ctor(tag) => Value::Ctor {
                            tag,
                            fields: ids,
                            scalars: img.scalars(o)?.into(),
                        },
                        // a thunk is the value it was forced to
                        _ => {
                            memo.insert(o, memo[&parts[0]]);
                            continue;
                        }
                    };
                    (o, v)
                }
            };
            let values = &mut self.module.attrs.values;
            let id = u32::try_from(values.len())
                .ok()
                .filter(|&i| i != PENDING)
                .ok_or_else(|| corrupt("too many extension values"))?;
            values.push(v);
            memo.insert(o, id);
        }
        Ok(ValueId::new(memo[&root]))
    }

    /// The public part holds a hidden proof or body as an axiom over the same type.
    fn exported(&mut self) -> Result<()> {
        let img = self.img;
        let own: FxHashMap<NameId, usize> = (self.module.consts.iter().map(|c| c.name))
            .zip(0..)
            .collect();
        let mut exported = FxHashMap::default();
        for info in img.array(img.field(img.public, 2)?)? {
            if img.safety(info)? != Safety::Safe {
                continue;
            }
            let cv = img.field(img.field(info, 0)?, 0)?;
            let name = self.name(img.field(cv, 0)?)?;
            let Some(&i) = own.get(&name) else { continue };
            let ty = self.expr(img.field(cv, 2)?)?;
            let k = &self.module.consts[i];
            if ty != k.ty {
                return Err(corrupt("a constant is exported at another type"));
            }
            let hidden = img.tag(info)? == AXIOM && !matches!(k.kind, Kind::Axiom);
            exported.insert(name, hidden);
        }
        self.module.exported = Some(exported);
        Ok(())
    }

    /// The memo slot of `o`, and its id if it was already decoded.
    fn seen<T>(&self, o: u64) -> Result<(usize, Option<Id<T>>)> {
        let slot = self.img.slot(o)?;
        Ok((slot, self.memo[slot].checked_sub(1).map(Id::new)))
    }

    fn remember<T>(&mut self, slot: usize, id: Id<T>) -> Id<T> {
        self.memo[slot] = id.0 + 1;
        id
    }

    fn name(&mut self, o: u64) -> Result<NameId> {
        let img = self.img;
        if is_scalar(o) || img.tag(o)? == 0 {
            return Ok(ANON);
        }
        let (slot, seen) = self.seen(o)?;
        if let Some(id) = seen {
            return Ok(id);
        }
        let pre = self.name(img.field(o, 0)?)?;
        let arg = img.field(o, 1)?;
        let n = match img.tag(o)? {
            1 => Name::Str(pre, img.str(arg)?.into()),
            _ => Name::Num(pre, small_nat(arg)?),
        };
        let id = self.tables.names.intern(n);
        Ok(self.remember(slot, id))
    }

    fn names(&mut self, o: u64) -> Result<Vec<NameId>> {
        self.img
            .list(o)?
            .into_iter()
            .map(|n| self.name(n))
            .collect()
    }

    fn level(&mut self, o: u64) -> Result<LevelId> {
        let img = self.img;
        if is_scalar(o) || img.tag(o)? == 0 {
            return Ok(ZERO);
        }
        let (slot, seen) = self.seen(o)?;
        if let Some(id) = seen {
            return Ok(id);
        }
        let f = |i| img.field(o, i);
        let l = match img.tag(o)? {
            1 => Level::Succ(self.level(f(0)?)?),
            2 => Level::Max(self.level(f(0)?)?, self.level(f(1)?)?),
            3 => Level::IMax(self.level(f(0)?)?, self.level(f(1)?)?),
            4 => Level::Param(self.name(f(0)?)?),
            t => return Err(corrupt(format!("unexpected level tag {t}"))),
        };
        let id = self.tables.levels.intern(l);
        Ok(self.remember(slot, id))
    }

    /// Decode `root` after its subterms, on a worklist rather than the stack. A slot is
    /// [`PENDING`] while its subterms are queued, which catches cyclic images.
    fn expr(&mut self, root: u64) -> Result<ExprId> {
        let img = self.img;
        let mut work = vec![(root, false)];
        while let Some((o, ready)) = work.pop() {
            let slot = img.slot(o)?;
            let f = |i| img.field(o, i);
            let tag = img.tag(o)?;
            if !ready {
                match self.memo[slot] {
                    0 => {}
                    PENDING => return Err(corrupt("cyclic expression")),
                    _ => continue,
                }
                self.memo[slot] = PENDING;
                work.push((o, true));
                let subs: &[u64] = match tag {
                    5 => &[0, 1],
                    6 | 7 => &[1, 2],
                    8 => &[1, 2, 3],
                    10 => &[1],
                    11 => &[2],
                    _ => &[],
                };
                for &i in subs.iter().rev() {
                    work.push((f(i)?, false));
                }
                continue;
            }
            let binder = || {
                Ok::<_, Error>(match img.scalar_u8(o, 8)? {
                    0 => Binder::Default,
                    1 => Binder::Implicit,
                    2 => Binder::StrictImplicit,
                    _ => Binder::InstImplicit,
                })
            };
            let e = match tag {
                0 => Expr::BVar(small_nat(f(0)?)?),
                3 => Expr::Sort(self.level(f(0)?)?),
                4 => {
                    let us = img.list(f(1)?)?;
                    let us = us
                        .into_iter()
                        .map(|l| self.level(l))
                        .collect::<Result<_>>()?;
                    let us = self.tables.univs.intern(Univs(us));
                    Expr::Const(self.name(f(0)?)?, us)
                }
                5 => Expr::App(self.done(f(0)?)?, self.done(f(1)?)?),
                6 => Expr::Lam(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    binder()?,
                ),
                7 => Expr::Pi(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    binder()?,
                ),
                8 => Expr::Let(Box::new(LetNode(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    self.done(f(3)?)?,
                ))),
                9 => {
                    let lit = f(0)?;
                    let val = img.field(lit, 0)?;
                    if img.tag(lit)? == 0 {
                        Expr::Nat(Box::new(img.nat_decimal(val)?.into()))
                    } else {
                        Expr::Str(Box::new(img.str(val)?.into()))
                    }
                }
                10 => {
                    let id = self.done(f(1)?)?;
                    self.remember(slot, id);
                    continue;
                }
                11 => Expr::Proj(
                    self.name(f(0)?)?,
                    u32::try_from(small_nat(f(1)?)?)
                        .map_err(|_| corrupt("projection index past u32"))?,
                    self.done(f(2)?)?,
                ),
                t => {
                    return Err(corrupt(format!(
                        "unexpected expression tag {t} (free or meta variable in a declaration)"
                    )))
                }
            };
            let id = self.tables.exprs.intern(e, self.rank, self.cursor);
            self.remember(slot, id);
        }
        self.done(root)
    }

    /// The id of an already decoded subterm.
    fn done(&self, o: u64) -> Result<ExprId> {
        self.seen(o)?
            .1
            .ok_or_else(|| corrupt("subterm decoded out of order"))
    }

    fn constant(&mut self, info: u64) -> Result<()> {
        let img = self.img;
        let tag = img.tag(info)?;
        let val = img.field(info, 0)?;
        if img.safety(info)? != Safety::Safe {
            self.module.skipped += 1;
            return Ok(());
        }
        let f = |i| img.field(val, i);
        let nat = |i| small_nat(f(i)?);
        let cv = f(0)?;
        let name = self.name(img.field(cv, 0)?)?;
        let level_params = self.names(img.field(cv, 1)?)?;
        for &p in &level_params {
            self.tables.levels.intern(Level::Param(p));
        }
        let ty = self.expr(img.field(cv, 2)?)?;
        let kind = match tag {
            AXIOM => Kind::Axiom,
            DEFN => {
                let h = f(2)?;
                let hints = if !is_scalar(h) {
                    Hints::Regular(img.scalar_u32(h)?)
                } else if h >> 1 == 0 {
                    Hints::Opaque
                } else {
                    Hints::Abbrev
                };
                Kind::Defn(Defn {
                    value: self.expr(f(1)?)?,
                    hints,
                    all: self.names(f(3)?)?,
                })
            }
            THM => Kind::Thm(Theorem {
                value: if self.lazy {
                    self.module.pending.push((name, f(1)?));
                    None
                } else {
                    Some(self.expr(f(1)?)?)
                },
                all: self.names(f(2)?)?,
            }),
            OPAQUE => Kind::Opaque(Body {
                value: self.expr(f(1)?)?,
                all: self.names(f(2)?)?,
            }),
            QUOT => Kind::Quot(match img.scalar_u8(val, 0)? {
                0 => QuotKind::Type,
                1 => QuotKind::Ctor,
                2 => QuotKind::Lift,
                _ => QuotKind::Ind,
            }),
            INDUCT => Kind::Induct(Inductive {
                num_params: nat(1)?,
                num_indices: nat(2)?,
                all: self.names(f(3)?)?,
                ctors: self.names(f(4)?)?,
                num_nested: nat(5)?,
                is_rec: img.scalar_u8(val, 0)? != 0,
                is_reflexive: img.scalar_u8(val, 2)? != 0,
            }),
            CTOR => Kind::Ctor(Ctor {
                induct: self.name(f(1)?)?,
                cidx: nat(2)?,
                num_params: nat(3)?,
                num_fields: nat(4)?,
            }),
            REC => {
                let all = self.names(f(1)?)?;
                for &ind in &all {
                    self.module.recursors.entry(ind).or_default().push(name);
                }
                let mut rules = Vec::new();
                for r in img.list(f(6)?)? {
                    rules.push(Rule {
                        ctor: self.name(img.field(r, 0)?)?,
                        nfields: small_nat(img.field(r, 1)?)?,
                        rhs: self.expr(img.field(r, 2)?)?,
                    });
                }
                Kind::Rec(Rec {
                    all,
                    num_params: nat(2)?,
                    num_indices: nat(3)?,
                    num_motives: nat(4)?,
                    num_minors: nat(5)?,
                    rules,
                    k: img.scalar_u8(val, 0)? != 0,
                })
            }
            t => return Err(corrupt(format!("unexpected constant tag {t}"))),
        };
        self.module.consts.push(Const {
            name,
            level_params,
            ty,
            kind,
        });
        Ok(())
    }
}

/// Decode the entries `want` of the module at `path`, from its public part alone.
pub(super) fn decode_attr_ranges(
    tables: &Tables,
    path: &Path,
    rank: u32,
    want: &[(Entries, Range<usize>)],
) -> Result<Attrs> {
    let img = Image::open_public(path)?;
    let mut cursor = None;
    let mut dec = Decoder::values(&img, tables, rank, &mut cursor);
    dec.attr_ranges(want).map_err(at(path))?;
    Ok(dec.module.attrs)
}

impl Env {
    /// Decode the theorem values `due`, sorted by module, into the tables.
    pub(super) fn decode_values(
        &mut self,
        live: &mut Live,
        due: &[((usize, u64), NameId)],
    ) -> Result<Vec<(NameId, ExprId)>> {
        let tables = self.thaw(live);
        let groups: Vec<_> = due.chunk_by(|a, b| a.0 .0 == b.0 .0).collect();
        let loaded = &live.loaded;
        let decoded = rayon::ThreadPoolBuilder::new()
            .num_threads(live.jobs.max(1))
            .build()
            .map_err(Error::from)
            .and_then(|pool| {
                pool.install(|| {
                    groups
                        .par_iter()
                        .map_init(
                            || None,
                            |cursor, group| {
                                let path = &loaded[group[0].0 .0].path;
                                let img = Image::open_module(path)?;
                                let rank = u32::try_from(group[0].0 .0).expect("module count");
                                let mut dec = Decoder::new(&img, &tables, rank, cursor, false);
                                group
                                    .iter()
                                    .map(|&((_, o), n)| Ok((n, dec.expr(o)?)))
                                    .collect::<Result<Vec<_>>>()
                                    .map_err(at(path))
                            },
                        )
                        .collect::<Result<Vec<_>>>()
                })
            });
        self.freeze(tables, live);
        Ok(decoded?.into_iter().flatten().collect())
    }
}
