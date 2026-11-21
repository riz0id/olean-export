use olean_export::{Env, Error, Exporter, Result};
use std::{
    env, fs,
    path::PathBuf,
    process,
    time::{Duration, SystemTime},
};

fn build() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")
}

/// `thmC'` is proved by `thmB`, by `thmA`, one module each.
const THMS: [&str; 3] = ["thmC'", "thmB", "thmA"];
const ROOT: &str = "ModC";

fn export(env: &Env, name: &str) -> Result<Vec<u8>> {
    let mut ex = Exporter::new(env, Vec::new());
    ex.constant(env.find_name(name).unwrap())?;
    ex.finish()
}

fn lazy(search: &[PathBuf]) -> Env {
    Env::load_cone(search, &[ROOT], &[], 2, &|_, _| {}).unwrap()
}

#[test]
fn fetch_cone_matches_eager() {
    let search = [build()];
    let eager = Env::load(&search, &[ROOT]).unwrap();
    for name in THMS {
        let mut env = lazy(&search);
        assert!(matches!(export(&env, name), Err(Error::Unfetched(n)) if n == name));
        let c = env.find_name(name).unwrap();
        env.fetch_cone(&[c]).unwrap();
        let want = export(&eager, name).unwrap();
        assert_eq!(export(&env, name).unwrap(), want, "{name}");
        let cone = Env::load_cone(&search, &[ROOT], &[name], 2, &|_, _| {}).unwrap();
        assert_eq!(export(&cone, name).unwrap(), want, "{name}");
        env.fetch_cone(&[c]).unwrap();
        assert_eq!(export(&env, name).unwrap(), want, "{name} fetched twice");
    }
}

#[test]
fn fetch_proofs_decodes_only_those() {
    let mut env = lazy(&[build()]);
    let d = env.find_name("thmC'").unwrap();
    let got = env.fetch_proofs(&[d, d]).unwrap();
    assert_eq!(got.len(), 1);
    assert_eq!(got[0].0, d);
    assert_eq!(env.fetch_proofs(&[d]).unwrap().len(), 0);
    assert!(matches!(export(&env, "thmC'"), Err(Error::Unfetched(n)) if n == "thmB"));

    let rest: Vec<_> = THMS[1..]
        .iter()
        .map(|n| env.find_name(n).unwrap())
        .collect();
    assert_eq!(env.fetch_proofs(&rest).unwrap().len(), 2);
    let eager = Env::load(&[build()], &[ROOT]).unwrap();
    assert_eq!(
        export(&env, "thmC'").unwrap(),
        export(&eager, "thmC'").unwrap()
    );
}

#[test]
fn fetch_needs_a_cone_load() {
    let search = [build()];
    let mut eager = Env::load(&search, &[ROOT]).unwrap();
    let d = eager.find_name("thmC'").unwrap();
    assert_eq!(eager.fetch_proofs(&[d]).unwrap().len(), 0);
    eager.fetch_cone(&[d]).unwrap();

    let mut stmts = Env::load_statements(&search, &[ROOT], 2, &|_, _| {}).unwrap();
    let d = stmts.find_name("thmC'").unwrap();
    assert!(matches!(stmts.fetch_proofs(&[d]), Err(Error::Misuse(_))));
    assert!(matches!(stmts.fetch_cone(&[d]), Err(Error::Misuse(_))));
}

#[test]
fn fetch_refuses_a_changed_olean() {
    let dir = env::temp_dir().join(format!("olean-export-cone-{}", process::id()));
    fs::create_dir_all(&dir).unwrap();
    for e in fs::read_dir(build()).unwrap() {
        let p = e.unwrap().path();
        let name = p.file_name().unwrap().to_str().unwrap().to_owned();
        if name.starts_with("Mod") || name.starts_with("Extra") {
            fs::copy(&p, dir.join(name)).unwrap();
        }
    }
    let search = [dir.clone()];
    let mut env = lazy(&search);
    let c = env.find_name("thmB").unwrap();
    let later = SystemTime::now() + Duration::from_secs(60);
    fs::File::options()
        .write(true)
        .open(dir.join("ModB.olean"))
        .unwrap()
        .set_modified(later)
        .unwrap();
    let err = env.fetch_proofs(&[c]).unwrap_err();
    assert!(err.to_string().contains("changed since the load"), "{err}");
    assert!(matches!(export(&env, "thmB"), Err(Error::Unfetched(_))));

    assert_eq!(env.reload().unwrap().modules, ["ModB"]);
    let d = env.find_name("thmC'").unwrap();
    env.fetch_cone(&[d]).unwrap();
    let eager = Env::load(&search, &[ROOT]).unwrap();
    assert_eq!(
        export(&env, "thmC'").unwrap(),
        export(&eager, "thmC'").unwrap()
    );
    fs::remove_dir_all(&dir).unwrap();
}
