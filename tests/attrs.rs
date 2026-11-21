use olean_export::{Attrs, Env, Error, Exporter, Scope, Value, ValueId};
use std::{fmt::Write as _, path::PathBuf, slice};

const WANTED: &[&str] = &[
    "Lean.matchPatternAttr",
    "reducibilityCore",
    "Lean.Compiler.inlineAttrs",
    "Lean.classExtension",
    "Lean.Meta.instanceExtension",
    "No.such.extension",
];

fn build() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")
}

fn render(env: &Env, attrs: &Attrs, id: ValueId, out: &mut String) {
    let list = |ids: &[ValueId], out: &mut String| {
        for (i, &v) in ids.iter().enumerate() {
            out.push_str(if i == 0 { "" } else { " " });
            render(env, attrs, v, out);
        }
    };
    match &attrs[id] {
        Value::Scalar(n) => write!(out, "{n}").unwrap(),
        Value::Nat(n) => write!(out, "{n}n").unwrap(),
        Value::Str(s) => write!(out, "{s:?}").unwrap(),
        Value::Name(n) => write!(out, "`{}", env.display(*n)).unwrap(),
        Value::Bytes(b) => write!(out, "bytes{b:?}").unwrap(),
        Value::Array(vs) => {
            out.push_str("#[");
            list(vs, out);
            out.push(']');
        }
        Value::Ctor {
            tag,
            fields,
            scalars,
        } => {
            write!(out, "({tag}").unwrap();
            if !fields.is_empty() {
                out.push(' ');
                list(fields, out);
            }
            if !scalars.is_empty() {
                write!(out, " | {scalars:?}").unwrap();
            }
            out.push(')');
        }
    }
}

fn export(env: &Env) -> Vec<u8> {
    let mut ex = Exporter::new(env, Vec::new());
    ex.meta().unwrap();
    ex.all().unwrap();
    ex.finish().unwrap()
}

/// Every entry in `attrs`, which `module` exports.
fn show(env: &Env, module: &str, attrs: &Attrs, out: &mut String) {
    for a in &attrs.entries {
        let scope = match a.scope {
            Scope::Global => "global".to_owned(),
            Scope::Scoped(ns) => format!("scoped {}", env.display(ns)),
        };
        let decl = a.decl.map_or_else(|| "?".to_owned(), |d| env.display(d));
        write!(out, "{module} {} {scope} {decl}\n  ", WANTED[a.attr]).unwrap();
        render(env, attrs, a.entry, out);
        out.push('\n');
    }
}

/// Every entry of `WANTED` that `root` and its imports export, by module.
fn entries(root: &str) -> String {
    let build = build();
    let env = Env::load_attrs(slice::from_ref(&build), &[root], WANTED, 1, &|_, _| {}).unwrap();
    assert_eq!(env.attrs.len(), env.modules.len());
    let mut out = String::new();
    for (module, attrs) in env.modules.iter().zip(&env.attrs) {
        show(&env, module, attrs, &mut out);
    }
    out
}

/// The same as [`entries`], from a lazy load: each module's entries in one call if
/// `!split`, else each extension's first entry and the rest in calls of their own.
fn lazy_entries(root: &str, split: bool) -> String {
    let build = build();
    let mut env =
        Env::load_attrs_lazy(slice::from_ref(&build), &[root], WANTED, 1, &|_, _| {}).unwrap();
    assert_eq!(env.attrs.len(), 0);
    assert_eq!(env.entries.len(), env.modules.len());
    let mut fetched = Vec::new();
    for m in 0..env.modules.len() {
        let index = env.entries[m].clone();
        let calls: Vec<Vec<_>> = if split {
            (0..index.len())
                .flat_map(|k| {
                    let len = index[k].len;
                    [vec![(k, 0..len.min(1))], vec![(k, len.min(1)..len)]]
                })
                .collect()
        } else {
            vec![(0..index.len()).map(|k| (k, 0..index[k].len)).collect()]
        };
        for want in calls {
            fetched.push((m, env.attrs_of(m, &want).unwrap()));
        }
    }
    let mut out = String::new();
    for (m, attrs) in &fetched {
        show(&env, &env.modules[*m], attrs, &mut out);
    }
    out
}

#[test]
fn attrs() {
    insta::assert_snapshot!(entries("Attrs"));
}

/// A module in the module system gives the entries of its public part.
#[test]
fn public_part() {
    insta::assert_snapshot!(entries("ModA"));
}

#[test]
fn unasked() {
    let build = build();
    let search = slice::from_ref(&build);
    let plain = Env::load(search, &["Attrs"]).unwrap();
    assert_eq!(plain.attrs.len(), 0);
    let with = Env::load_attrs(search, &["Attrs"], WANTED, 1, &|_, _| {}).unwrap();
    assert_eq!(export(&plain), export(&with));
}

#[test]
fn lazy_matches_eager() {
    for root in ["Attrs", "ModA"] {
        let eager = entries(root);
        assert_ne!(eager, "");
        assert_eq!(lazy_entries(root, false), eager, "{root}");
        assert_eq!(lazy_entries(root, true), eager, "{root} in pieces");
    }
}

#[test]
fn lazy_misuse() {
    let build = build();
    let search = slice::from_ref(&build);
    let mut env = Env::load_attrs_lazy(search, &["Attrs"], WANTED, 1, &|_, _| {}).unwrap();
    let m = env.entries.iter().position(|e| !e.is_empty()).unwrap();
    let len = env.entries[m][0].len;
    let past = env.attrs_of(m, &[(0, 0..len + 1)]);
    assert!(
        matches!(past, Err(Error::File { .. } | Error::Misuse(_))),
        "{past:?}"
    );
    let k = env.entries[m].len();
    assert!(matches!(
        env.attrs_of(m, &[(k, 0..0)]),
        Err(Error::Misuse(_))
    ));
    let mut plain = Env::load(search, &["Attrs"]).unwrap();
    assert_eq!(plain.entries.len(), 0);
    assert!(matches!(plain.attrs_of(0, &[]), Err(Error::Misuse(_))));
}

#[test]
fn lazy_parallel_matches_serial() {
    let build = build();
    for root in ["Attrs", "ModA"] {
        let eager = entries(root);
        for jobs in [1, 4] {
            let mut env =
                Env::load_attrs_lazy(slice::from_ref(&build), &[root], WANTED, jobs, &|_, _| {})
                    .unwrap();
            let want: Vec<_> = (0..env.modules.len())
                .map(|m| {
                    let ks = env.entries[m]
                        .iter()
                        .enumerate()
                        .map(|(k, e)| (k, 0..e.len))
                        .collect();
                    (m, ks)
                })
                .collect();
            let fetched = env.attrs_of_many(&want, jobs).unwrap();
            assert_eq!(fetched.len(), want.len());
            let mut out = String::new();
            for ((m, _), attrs) in want.iter().zip(&fetched) {
                show(&env, &env.modules[*m], attrs, &mut out);
            }
            assert_eq!(out, eager, "{root} on {jobs} threads");
        }
    }
}

#[test]
fn lazy_parallel_error_keeps_env() {
    let build = build();
    let search = slice::from_ref(&build);
    let mut env = Env::load_attrs_lazy(search, &["Attrs"], WANTED, 4, &|_, _| {}).unwrap();
    let m = env.entries.iter().position(|e| !e.is_empty()).unwrap();
    let len = env.entries[m][0].len;
    let names = env.names.len();
    let bad = env.attrs_of_many(&[(m, vec![(0, 0..len)]), (m, vec![(0, 0..len + 1)])], 4);
    assert!(bad.is_err());
    assert!(env.names.len() >= names);
    let good = env.attrs_of(m, &[(0, 0..len)]).unwrap();
    assert_eq!(good.entries.len(), len);
}
