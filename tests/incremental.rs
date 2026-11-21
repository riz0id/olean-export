use olean_export::{
    accepted::{self, Section},
    blean,
    join::{self, join},
    key::Keys,
    ndjson::{self, Ndjson},
    Env, Exporter,
};
use std::{collections::HashMap, fs, path::PathBuf};

fn keys(bytes: &[u8]) -> HashMap<String, Option<[u8; 32]>> {
    let mut k = Keys::new();
    if blean::sniff(bytes) {
        blean::read(bytes, &mut k).unwrap();
    } else {
        ndjson::read(bytes, &mut k).unwrap();
    }
    k.into_keys().into_iter().map(|d| (d.name, d.key)).collect()
}

/// Joining the per-module files gives the whole export, internal constants aside, with the
/// same keys.
#[test]
fn per_module_join_is_the_whole_export() {
    let build = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build");
    let env = Env::load(&[build], &["Top", "Extra", "Pinned"]).unwrap();
    let mut ex = Exporter::new(&env, Vec::new());
    ex.meta().unwrap();
    ex.all().unwrap();
    let whole = ex.finish().unwrap();
    for blean in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let files = join::split(&env, dir.path(), blean).unwrap();
        assert_eq!(files.len(), env.modules.len());
        let mut bytes: Vec<Vec<u8>> = files.iter().map(|f| fs::read(f).unwrap()).collect();
        bytes.reverse();
        let refs: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
        let joined = join(&refs, Ndjson::new(Vec::new())).unwrap();
        let d = olean_export::compare(&joined, &whole).unwrap();
        assert!(d.only_b.is_empty() && d.differ.is_empty(), "{d:?}");
        assert!(d.dups.0.is_empty() && d.dups.1.is_empty(), "{d:?}");
        let (j, w) = (keys(&joined), keys(&whole));
        assert!(w.values().all(Option::is_some));
        assert!(w.iter().all(|(n, k)| j[n] == *k));
    }
}

/// Every file under `dir`, by its path from `dir`, with its bytes.
fn tree(dir: &std::path::Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut out = Vec::new();
    let mut todo = vec![dir.to_path_buf()];
    while let Some(d) = todo.pop() {
        for e in fs::read_dir(d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                todo.push(p);
            } else {
                out.push((
                    p.strip_prefix(dir).unwrap().to_path_buf(),
                    fs::read(&p).unwrap(),
                ));
            }
        }
    }
    out.sort();
    out
}

/// A per-module export writes the same files on any number of threads, including the
/// hashes each file's meta names of the files it imports.
#[test]
fn per_module_parallel_matches_serial() {
    let build = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build");
    let roots = [
        "Top", "Extra", "Pinned", "ModA", "ModB", "ModC", "ModD", "ModZ",
    ];
    let env = Env::load(&[build], &roots).unwrap();
    for interfaces in [false, true] {
        for blean in [false, true] {
            let trees: Vec<_> = [1, 4, 16]
                .into_iter()
                .map(|jobs| {
                    let dir = tempfile::tempdir().unwrap();
                    let files = join::split_each(&env, dir.path(), blean, interfaces, jobs, &|| {})
                        .unwrap();
                    assert_eq!(files.len(), env.modules.len());
                    tree(dir.path())
                })
                .collect();
            assert!(trees[0].len() >= env.modules.len());
            assert!(trees.iter().all(|t| *t == trees[0]));
        }
    }
}

#[test]
fn join_checks_imports() {
    let build = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build");
    let env = Env::load(&[build], &["Top"]).unwrap();
    let dir = tempfile::tempdir().unwrap();
    let files = join::split(&env, dir.path(), false).unwrap();
    let top = files
        .iter()
        .position(|f| f.ends_with("Top.ndjson"))
        .unwrap();
    let top = fs::read(&files[top]).unwrap();
    assert!(join(&[&top], Ndjson::new(Vec::new())).is_err());
    let base = fs::read(dir.path().join("Base.ndjson")).unwrap();
    let mut edited = base.clone();
    edited.extend_from_slice(b"\n");
    assert!(join(&[&top, &edited], Ndjson::new(Vec::new())).is_err());
    assert!(join(&[&top, &base], Ndjson::new(Vec::new())).is_ok());
}

#[test]
fn accepted_round_trip() {
    let a = [[1u8; 32], [3; 32]];
    let b = [[2u8; 32]];
    let sections = [
        Section {
            checker: "one",
            tag: [7; 32],
            keys: &a,
        },
        Section {
            checker: "two",
            tag: [8; 32],
            keys: &b,
        },
    ];
    let mut out = Vec::new();
    accepted::write(&mut out, &sections).unwrap();
    let back = accepted::parse(&out).unwrap();
    assert_eq!(back, sections);
    assert!(back[0].contains(&[3; 32]) && !back[0].contains(&[2; 32]));
    assert!(accepted::parse(&out[..out.len() - 1]).is_err());
}
