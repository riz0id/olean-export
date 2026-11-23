use olean_export::{Binder, Env, Expr};
use std::{path::PathBuf, slice};

fn build() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")
}

/// The binders of `name`, with their names displayed.
fn binders(env: &Env, name: &str) -> Vec<(String, Binder)> {
    let c = &env.consts[&env.find_name(name).unwrap()];
    c.binders
        .iter()
        .map(|&(n, bi)| (env.display(n), bi))
        .collect()
}

/// The binders of the leading `Pi`s of the type of `name`, as the shared term has them.
fn shared(env: &Env, name: &str) -> Vec<(String, Binder)> {
    let mut e = env.consts[&env.find_name(name).unwrap()].ty;
    let mut out = Vec::new();
    while let Expr::Pi(n, _, body, bi) = env.exprs[e] {
        out.push((env.display(n), bi));
        e = body;
    }
    out
}

fn named(bs: &[(&str, Binder)]) -> Vec<(String, Binder)> {
    bs.iter().map(|&(n, bi)| (n.to_owned(), bi)).collect()
}

/// Every constant has one binder for each leading `Pi` of its type.
fn assert_counts(env: &Env) {
    for (&n, c) in &env.consts {
        let mut e = c.ty;
        let mut pis = 0;
        while let Expr::Pi(_, _, body, _) = env.exprs[e] {
            pis += 1;
            e = body;
        }
        assert_eq!(c.binders.len(), pis, "{}", env.display(n));
    }
}

#[test]
fn a_shared_type_keeps_each_constants_binders() {
    let build = build();
    let env = Env::load(slice::from_ref(&build), &["Binders"]).unwrap();
    let ty = |name: &str| env.consts[&env.find_name(name).unwrap()].ty;
    assert_eq!(ty("bi1"), ty("bi2"));
    assert_eq!(ty("bi1"), ty("bi4"));
    let (b1, b2, b4) = (
        binders(&env, "bi1"),
        binders(&env, "bi2"),
        binders(&env, "bi4"),
    );
    assert_eq!(
        b1,
        named(&[("n", Binder::Implicit), ("h", Binder::Default)])
    );
    assert_eq!(
        b2,
        named(&[("n", Binder::Default), ("h", Binder::Implicit)])
    );
    assert_eq!(b4, named(&[("k", Binder::Default), ("h", Binder::Default)]));
    // the shared term has only those of whichever was decoded first
    let one = shared(&env, "bi1");
    assert!([&b1, &b2, &b4].contains(&&one), "{one:?}");
}

#[test]
fn every_binder_info() {
    let build = build();
    let env = Env::load(slice::from_ref(&build), &["Binders"]).unwrap();
    let infos: Vec<Binder> = binders(&env, "bi3").into_iter().map(|b| b.1).collect();
    assert_eq!(
        infos,
        [
            Binder::StrictImplicit,
            Binder::InstImplicit,
            Binder::Default
        ]
    );
}

#[test]
fn an_earlier_module_wins_the_shared_term_only() {
    let build = build();
    let env = Env::load(slice::from_ref(&build), &["Binders"]).unwrap();
    let ty = |name: &str| env.consts[&env.find_name(name).unwrap()].ty;
    assert_eq!(ty("bi0"), ty("N.add_zero"));
    let base = named(&[("m", Binder::Default)]);
    assert_eq!(shared(&env, "bi0"), base);
    assert_eq!(binders(&env, "N.add_zero"), base);
    assert_eq!(binders(&env, "bi0"), named(&[("k", Binder::Implicit)]));
}

#[test]
fn one_binder_for_each_leading_pi() {
    let build = build();
    let search = slice::from_ref(&build);
    for root in [
        "Base", "Top", "Extra", "Pinned", "Attrs", "Binders", "Hidden", "ModA",
    ] {
        assert_counts(&Env::load(search, &[root]).unwrap());
        assert_counts(&Env::load_statements(search, &[root], 1, &|_, _| {}).unwrap());
    }
}
