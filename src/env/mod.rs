mod attr;
mod decode;
mod reload;
mod table;
mod term;
mod walk;

pub use attr::{Attr, Attrs, Entries, OleanLevel, Scope, Value, ValueId};
pub use reload::Reload;
pub use table::{Exprs, Table};
pub use term::{
    Binder, Body, Const, Ctor, Defn, Expr, ExprId, Hints, Id, Inductive, Kind, LetNode, Level,
    LevelId, Name, NameId, QuotKind, Rec, Rule, Theorem, Univs, UnivsId, ANON, ZERO,
};
pub(crate) use walk::{Builtins, Dep, Depth, Family};

use self::{
    decode::{decode_all, decode_attr_ranges, Module},
    reload::{stamp, Live, Loaded, Stamp},
    table::{Shared, SharedExprs, Tables},
};
use crate::{
    error::{at, Error, Result},
    inspect::Import,
    olean::{Header, Image},
};
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    borrow::Cow,
    env, mem,
    ops::Range,
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicU64, Ordering::Relaxed},
        OnceLock,
    },
    thread,
};

static LINEAGE: AtomicU64 = AtomicU64::new(0);

/// What [`Env::attrs_of_many`] decodes of one module: the module, and for each `(k, range)`
/// that range of the entries at `env.entries[module][k]` (see [`Env::entries`]).
pub type AttrRequest = (usize, Vec<(usize, Range<usize>)>);

/// An [`AttrRequest`] checked against the index: the olean, the module's rank and the
/// entries asked for.
type Located = (PathBuf, u32, Vec<(Entries, Range<usize>)>);

/// How `Env::build` loads.
#[derive(Clone, Copy, Default)]
pub(super) struct Opts<'a> {
    /// Keep what [`Env::reload`] needs.
    pub(super) live: bool,
    /// Leave theorem values in their oleans.
    pub(super) lazy: bool,
    /// The environment extensions to read the entries of.
    pub(super) attrs: &'a [&'a str],
    /// Only find where their entries are, for [`Env::attrs_of`].
    pub(super) index: bool,
    /// Which part of each module to read the entries from.
    pub(super) level: OleanLevel,
}

/// Every constant reachable from a set of root modules, in import order.
#[derive(Debug)]
pub struct Env {
    pub names: Table<Name>,
    pub levels: Table<Level>,
    pub univs: Table<Univs>,
    pub exprs: Exprs,
    pub consts: FxHashMap<NameId, Const>,
    pub order: Vec<NameId>,
    pub recursors: FxHashMap<NameId, Vec<NameId>>,
    pub modules: Vec<String>,
    /// The direct imports of each module in `modules`.
    pub imports: Vec<Vec<Import>>,
    /// What each module in the module system exports, true where only the statement.
    pub exported: Vec<Option<FxHashMap<NameId, bool>>>,
    /// The extension entries of each module in `modules`, for an environment from
    /// [`Env::load_attrs`]. Any other has none, and so no element here.
    pub attrs: Vec<Attrs>,
    /// Where the extension entries of each module in `modules` are, for an environment from
    /// [`Env::load_attrs_lazy`], to decode with [`Env::attrs_of`]. Any other has none.
    pub entries: Vec<Vec<Entries>>,
    /// The olean and its stamp at load of each module, kept for [`Env::attrs_of`].
    sources: Vec<(PathBuf, Stamp)>,
    pub header: Header,
    pub skipped: usize,
    /// Where each module's constants end in `order`.
    ends: Vec<usize>,
    pub(crate) lineage: u64,
    live: Option<Box<Live>>,
    /// The threads [`Env::attrs_of_many`] decodes on, with how many there are, made on its
    /// first call to decode on more than one.
    pool: OnceLock<(usize, rayon::ThreadPool)>,
}

/// Identifier-shaped tokens of Lean's term and command syntax, which a name must not print
/// as. Universe syntax adds `max` and `imax`, which the statement printer escapes itself.
#[rustfmt::skip]
const KEYWORDS: &[&str] = &[
    "Prop", "Sort", "Type", "abbrev", "at", "attribute", "axiom", "by", "calc", "class", "def",
    "deriving", "do", "else", "end", "example", "export", "forall", "from", "fun", "have", "if",
    "import", "in", "inductive", "instance", "let", "local", "macro", "match", "mutual",
    "namespace", "noncomputable", "nofun", "nomatch", "opaque", "open", "partial", "private",
    "protected", "scoped", "section", "set_option", "show", "sorry", "structure", "suffices",
    "syntax", "then", "theorem", "this", "universe", "unsafe", "variable", "where", "with",
];
/// A name component in `«»` unless Lean would read it back as itself unescaped. Lean has no
/// way to write a `»` in a name, so `»` and `\` are written after a `\`, which no name Lean
/// can print contains.
pub(crate) fn escape(s: &str) -> Cow<'_, str> {
    let letter = |c: char| {
        let u = u32::from(c);
        c.is_ascii_alphabetic()
            || c == '_'
            || ((0x3b1..=0x3c9).contains(&u) && u != 0x3bb)
            || ((0x391..=0x3a9).contains(&u) && u != 0x3a0 && u != 0x3a3)
            || matches!(u, 0x3ca..=0x3fb | 0x1f00..=0x1ffe | 0x2100..=0x214f | 0x1d49c..=0x1d59f)
    };
    let rest = |c: char| {
        letter(c)
            || c.is_ascii_digit()
            || matches!(c, '\'' | '!' | '?')
            || matches!(u32::from(c), 0x2080..=0x2089 | 0x2090..=0x209c | 0x1d62..=0x1d6a | 0x2c7c)
    };
    let mut cs = s.chars();
    let plain = cs.next().is_some_and(letter) && cs.all(rest) && !KEYWORDS.contains(&s);
    if plain {
        Cow::Borrowed(s)
    } else if s.contains(['»', '\\']) {
        Cow::Owned(format!("«{}»", s.replace('\\', "\\\\").replace('»', "\\»")))
    } else {
        Cow::Owned(format!("«{s}»"))
    }
}

fn discover_all(search: &[PathBuf], roots: &[&str]) -> Result<Vec<(String, PathBuf)>> {
    let mut seen = FxHashSet::default();
    let mut found = Vec::new();
    for root in roots {
        discover(search, root, &mut seen, &mut found)?;
    }
    Ok(found)
}

/// Find `module` and its imports, appending them to `out` in import order.
fn discover(
    search: &[PathBuf],
    module: &str,
    seen: &mut FxHashSet<String>,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<()> {
    if !seen.insert(module.to_owned()) {
        return Ok(());
    }
    let path = resolve(search, module)?;
    let img = Image::open(&path)?;
    let imports = img.imports().map_err(at(&path))?;
    drop(img);
    for import in &imports {
        discover(search, &import.module, seen, out)?;
    }
    out.push((module.to_owned(), path));
    Ok(())
}

/// The `.olean` for a dotted module name such as `Init.Prelude`, from the first directory
/// of `search` that has it.
pub fn resolve(search: &[PathBuf], module: &str) -> Result<PathBuf> {
    let rel: PathBuf = module.split('.').collect();
    search
        .iter()
        .map(|dir| dir.join(&rel).with_extension("olean"))
        .find(|p| p.is_file())
        .ok_or_else(|| Error::ModuleNotFound(module.to_owned()))
}

#[must_use]
pub fn search_path() -> Vec<PathBuf> {
    let mut dirs: Vec<PathBuf> =
        env::var_os("LEAN_PATH").map_or_default(|p| env::split_paths(&p).collect());
    if let Some(root) = env::var_os("LEAN_SYSROOT") {
        dirs.push(Path::new(&root).join("lib").join("lean"));
    }
    dirs
}

impl Env {
    /// Load `roots` and their transitive imports, resolving modules against `search`.
    pub fn load(search: &[PathBuf], roots: &[&str]) -> Result<Self> {
        let jobs = thread::available_parallelism().map_or(1, usize::from);
        Self::load_with(search, roots, jobs, &|_, _| {})
    }

    /// Like [`Env::load`] on `jobs` threads, calling `progress` with the number of modules
    /// and constants decoded so far.
    ///
    /// Modules decode in parallel straight into shared tables, and the result is the same
    /// for any `jobs`.
    pub fn load_with(
        search: &[PathBuf],
        roots: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        Self::build(search, roots, jobs, progress, Opts::default())
    }

    /// Like [`Env::load_with`], also reading the entries each module exports for the
    /// environment extensions in `attrs`, into [`Env::attrs`]. Lean keeps an attribute's
    /// uses in such an extension, named in full as `inspect` lists it, for example
    /// `Lean.Meta.instanceExtension`. A name no module has entries for gives none. A module
    /// in the module system exports the entries of its public part, those a plain `import`
    /// of it sees.
    ///
    /// An olean does not say what type an extension's entries have, so each is read by its
    /// layout into a [`Value`], and its scope and declaration found where it has the layout
    /// the attributes Lean provides builders for use.
    pub fn load_attrs(
        search: &[PathBuf],
        roots: &[&str],
        attrs: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        let opts = Opts {
            attrs,
            ..Opts::default()
        };
        Self::build(search, roots, jobs, progress, opts)
    }

    /// Like [`Env::load_attrs`], reading the entries `level` sees. [`OleanLevel::Server`]
    /// adds what Lean keeps for the editor, such as `Lean.declRangeExt` and
    /// `Lean.docStringExt`, which a module in the module system leaves out of its public part.
    pub fn load_attrs_at(
        search: &[PathBuf],
        roots: &[&str],
        attrs: &[&str],
        level: OleanLevel,
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        let opts = Opts {
            attrs,
            level,
            ..Opts::default()
        };
        Self::build(search, roots, jobs, progress, opts)
    }

    /// Like [`Env::load_attrs_lazy`], finding the entries `level` sees.
    pub fn load_attrs_lazy_at(
        search: &[PathBuf],
        roots: &[&str],
        attrs: &[&str],
        level: OleanLevel,
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        let opts = Opts {
            attrs,
            index: true,
            level,
            ..Opts::default()
        };
        Self::build(search, roots, jobs, progress, opts)
    }

    /// Like [`Env::load_attrs`], but only finding where each module keeps the entries, into
    /// [`Env::entries`], to decode as needed with [`Env::attrs_of`]. That costs about as
    /// much as a load without them.
    pub fn load_attrs_lazy(
        search: &[PathBuf],
        roots: &[&str],
        attrs: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        let opts = Opts {
            attrs,
            index: true,
            ..Opts::default()
        };
        Self::build(search, roots, jobs, progress, opts)
    }

    /// Decode entries of `module` from its olean: for each `(k, range)` in `want`, that range
    /// of the entries at `self.entries[module][k]` (see [`Env::entries`]). Values shared
    /// between them are decoded once. Each call reads the olean afresh, so asking for a
    /// module's entries in one call costs less than in many.
    ///
    /// Fails if the olean changed since the load, or a range is past its entries.
    pub fn attrs_of(&mut self, module: usize, want: &[(usize, Range<usize>)]) -> Result<Attrs> {
        let mut attrs = self.attrs_of_many(&[(module, want.to_vec())], 1)?;
        Ok(attrs.pop().expect("one module asked for"))
    }

    /// Like [`Env::attrs_of`] for many modules at once, decoding them on `jobs` threads.
    /// `want` has each module with its `(k, range)` requests, and the result is in its
    /// order. Fails, decoding nothing, if any module or extension asked for is not there or
    /// any olean changed since the load.
    pub fn attrs_of_many(&mut self, want: &[AttrRequest], jobs: usize) -> Result<Vec<Attrs>> {
        let requests = want
            .iter()
            .map(|(m, ks)| self.request(*m, ks))
            .collect::<Result<Vec<_>>>()?;
        let tables = self.names_only();
        let decode = |(path, rank, w): &Located| decode_attr_ranges(&tables, path, *rank, w);
        let decoded = if jobs <= 1 || requests.len() <= 1 {
            // one thread's worth: no pool to start, or to hand the work to
            requests.iter().map(decode).collect::<Result<Vec<_>>>()
        } else {
            let run = |pool: &rayon::ThreadPool| {
                pool.install(|| requests.par_iter().map(decode).collect::<Result<Vec<_>>>())
            };
            let built = || {
                rayon::ThreadPoolBuilder::new()
                    .num_threads(jobs)
                    .build()
                    .map_err(Error::from)
            };
            match self.pool.get() {
                Some((n, pool)) if *n == jobs => run(pool),
                Some(_) => built().and_then(|pool| run(&pool)),
                None => built().and_then(|pool| {
                    let got = run(&pool);
                    let _ = self.pool.set((jobs, pool));
                    got
                }),
            }
        };
        self.names = tables.names.freeze();
        decoded
    }

    /// The olean, rank and located ranges of one request of [`Env::attrs_of_many`].
    fn request(&self, module: usize, want: &[(usize, Range<usize>)]) -> Result<Located> {
        let (Some((path, at_load)), Some(entries)) =
            (self.sources.get(module), self.entries.get(module))
        else {
            return Err(Error::Misuse(
                "attrs_of needs a module of an Env::load_attrs_lazy",
            ));
        };
        let want = want
            .iter()
            .map(|(k, r)| entries.get(*k).map(|&e| (e, r.clone())))
            .collect::<Option<Vec<_>>>()
            .ok_or(Error::Misuse(
                "attrs_of asked for an extension the module has no entries of",
            ))?;
        if stamp(path) != *at_load {
            return Err(at(path)(Error::Misuse(
                "olean changed since the environment was loaded",
            )));
        }
        let rank = u32::try_from(module).expect("module count");
        Ok((path.clone(), rank, want))
    }

    /// The names table in shared form, with empty tables for the rest, for decoding
    /// extension entries, which only add names. Freeze `names` back after.
    fn names_only(&mut self) -> Tables {
        Tables {
            names: mem::replace(&mut self.names, Table(Vec::new())).thaw(),
            levels: Shared::new(Level::Zero, 0),
            univs: Shared::new(Univs(Box::new([])), 0),
            exprs: SharedExprs::new(0),
        }
    }

    fn build(
        search: &[PathBuf],
        roots: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
        opts: Opts<'_>,
    ) -> Result<Self> {
        let found = discover_all(search, roots)?;
        let stamps: Vec<Stamp> = found.iter().map(|(_, p)| stamp(p)).collect();
        // Sizing the tables up front avoids rehashing them while they grow. Across Lean and
        // Mathlib there is about one expression per 64 bytes of olean and one name per 1200.
        let bytes: u64 = stamps.iter().flatten().map(|(len, _)| len).sum();
        let estimate = |per: u64| usize::try_from(bytes / per).unwrap_or(0);
        let tables = Tables {
            names: Shared::new(Name::Anon, estimate(1200)),
            levels: Shared::new(Level::Zero, 0),
            univs: Shared::new(Univs(Box::new([])), 0),
            exprs: SharedExprs::new(estimate(64)),
        };
        let paths: Vec<_> = found.iter().map(|(_, p)| p.as_path()).enumerate().collect();
        let decoded = decode_all(&tables, &paths, jobs, progress, opts);
        let (exprs, index, ranks) = tables.exprs.freeze();
        let kept = opts.live.then_some((index, ranks));
        let mut decoded = decoded?;
        let (entries, sources) = if opts.index {
            let entries = decoded
                .iter_mut()
                .map(|m| mem::take(&mut m.index))
                .collect();
            let sources = found
                .iter()
                .map(|(_, p)| p.clone())
                .zip(stamps.clone())
                .collect();
            (entries, sources)
        } else {
            (Vec::new(), Vec::new())
        };
        let attrs = if opts.attrs.is_empty() || opts.index {
            Vec::new()
        } else {
            (decoded.iter_mut().map(|m| mem::take(&mut m.attrs))).collect()
        };
        let mut env = Self {
            names: tables.names.freeze(),
            levels: tables.levels.freeze(),
            univs: tables.univs.freeze(),
            exprs,
            consts: FxHashMap::default(),
            order: Vec::new(),
            recursors: FxHashMap::default(),
            modules: Vec::new(),
            imports: Vec::new(),
            exported: Vec::new(),
            attrs,
            entries,
            sources,
            header: Header::default(),
            skipped: 0,
            ends: Vec::new(),
            lineage: LINEAGE.fetch_add(1, Relaxed),
            live: None,
            pool: OnceLock::new(),
        };
        let loaded: Vec<_> = found
            .into_iter()
            .zip(stamps)
            .zip(decoded)
            .map(|(((module, path), stamp), m)| env.add(module, path, stamp, m))
            .collect();
        env.index(&loaded);
        if let Some((index, ranks)) = kept {
            let pending = env.pending(&loaded);
            env.live = Some(Box::new(Live {
                search: search.to_vec(),
                roots: roots.iter().map(|&r| r.to_owned()).collect(),
                jobs,
                index,
                ranks,
                loaded,
                pending,
                spare: Vec::new(),
                pool: reload::Pool::default(),
            }));
        }
        Ok(env)
    }

    fn add(&mut self, module: String, path: PathBuf, stamp: Stamp, m: Module) -> Loaded {
        let consts = m.consts.iter().map(|c| c.name).collect();
        self.consts
            .extend(m.consts.into_iter().map(|c| (c.name, c)));
        Loaded {
            module,
            path,
            stamp,
            consts,
            recursors: m.recursors,
            skipped: m.skipped,
            header: m.header,
            imports: m.imports,
            exported: m.exported,
            pending: m.pending,
        }
    }

    /// Rebuild the load order and everything summed over modules.
    fn index(&mut self, loaded: &[Loaded]) {
        self.order = loaded
            .iter()
            .flat_map(|l| l.consts.iter().copied())
            .collect();
        self.recursors.clear();
        // two modules may both declare a type, as realized or independent copies
        for (ind, recs) in loaded.iter().flat_map(|l| &l.recursors) {
            let all = self.recursors.entry(*ind).or_default();
            for r in recs {
                if !all.contains(r) {
                    all.push(*r);
                }
            }
        }
        self.modules = loaded.iter().map(|l| l.module.clone()).collect();
        self.imports = loaded.iter().map(|l| l.imports.clone()).collect();
        self.exported = loaded.iter().map(|l| l.exported.clone()).collect();
        self.header = loaded.last().map_or_default(|l| l.header.clone());
        self.skipped = loaded.iter().map(|l| l.skipped).sum();
        self.ends = loaded
            .iter()
            .scan(0, |end, l| {
                *end += l.consts.len();
                Some(*end)
            })
            .collect();
    }

    /// The constants module `m` declares, in load order.
    #[must_use]
    pub fn module_consts(&self, m: usize) -> &[NameId] {
        let start = m.checked_sub(1).map_or(0, |p| self.ends[p]);
        &self.order[start..self.ends[m]]
    }

    /// The constants `lean4export` exports when given no explicit names.
    pub fn roots(&self) -> impl Iterator<Item = NameId> + '_ {
        self.order.iter().copied().filter(|&c| !self.is_internal(c))
    }

    /// Look up a name such as `Nat.add` or `Foo.«bar.baz»`, as [`Env::display`] writes it,
    /// without interning it.
    #[must_use]
    pub fn find_name(&self, dotted: &str) -> Option<NameId> {
        let (mut pre, mut rest) = (ANON, dotted);
        loop {
            let (n, tail) = if let Some(r) = rest.strip_prefix('«') {
                let (mut s, mut cs) = (String::new(), r.char_indices());
                let end = loop {
                    match cs.next()? {
                        (_, '\\') => s.push(cs.next()?.1),
                        (i, '»') => break i + '»'.len_utf8(),
                        (_, c) => s.push(c),
                    }
                };
                (Name::Str(pre, s.into()), &r[end..])
            } else {
                let (s, tail) = rest.split_at(rest.find('.').unwrap_or(rest.len()));
                let n = s
                    .parse()
                    .map_or_else(|_| Name::Str(pre, s.into()), |i| Name::Num(pre, i));
                (n, tail)
            };
            pre = self.names.get(&n)?;
            match tail.strip_prefix('.') {
                Some(t) => rest = t,
                None => return tail.is_empty().then_some(pre),
            }
        }
    }

    /// `n` as Lean reads it back: components that are not plain identifiers, or are
    /// keywords, go in `«»`.
    #[must_use]
    pub fn display(&self, n: NameId) -> String {
        self.join(n, true)
    }

    /// `n` with its components joined as they are, as `declRangeExt` keys it.
    pub(crate) fn dotted(&self, n: NameId) -> String {
        self.join(n, false)
    }

    fn join(&self, n: NameId, escaped: bool) -> String {
        let (pre, last) = match &self.names[n] {
            Name::Anon => return String::new(),
            Name::Str(p, s) if escaped => (*p, escape(s).into_owned()),
            Name::Str(p, s) => (*p, s.to_string()),
            Name::Num(p, i) => (*p, i.to_string()),
        };
        match pre {
            ANON => last,
            p => format!("{}.{last}", self.join(p, escaped)),
        }
    }

    #[must_use]
    pub fn is_internal(&self, n: NameId) -> bool {
        match &self.names[n] {
            Name::Anon => false,
            Name::Str(p, s) => s.starts_with('_') || self.is_internal(*p),
            Name::Num(p, _) => self.is_internal(*p),
        }
    }
}
