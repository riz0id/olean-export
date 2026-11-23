//! How `Env::fetch_proofs` scales: batch size, module spread, threads and call granularity,
//! plus `Env::fetch_cone` on a few theorems. Every case runs in a fresh process, since peak
//! RSS only rises, on an environment from `Env::load_cone` with every proof left pending.
//!
//! ```text
//! just bench-setup                 # once: fetch Mathlib's oleans into bench/
//! just bench [--quick] [--csv]     # all of Mathlib
//! just bench --only calls,cone      # cases starting with these
//! cargo bench --bench fetch_proofs -- --path tests/cases/build --root ModC --quick
//! ```
#![allow(
    unsafe_code,
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)]

use olean_export::{search_path, Env, Kind, NameId, Theorem};
use std::{
    env, mem,
    path::PathBuf,
    process::{exit, Command},
    thread,
    time::Instant,
};

/// Nodes per expression chunk, as in `src/env/table.rs`.
const CHUNK: usize = 1 << 14;

/// Theorems `fetch_cone` runs on by default; the first is the README's.
const CONES: [&str; 3] = [
    "Fin.insertNth_apply_succAbove",
    "Finset.sum_range_succ",
    "MeasureTheory.integral_add",
];

struct Args {
    paths: Vec<PathBuf>,
    root: String,
    quick: bool,
    csv: bool,
    cones: Vec<String>,
    /// Run only the cases starting with one of these.
    only: Vec<String>,
    case: Option<String>,
}

fn args() -> Args {
    let mut a = Args {
        paths: Vec::new(),
        root: "Mathlib".to_owned(),
        quick: false,
        csv: false,
        cones: Vec::new(),
        only: Vec::new(),
        case: None,
    };
    let mut it = env::args().skip(1);
    while let Some(arg) = it.next() {
        let mut val = || it.next().unwrap_or_else(|| die(&format!("{arg} needs a value")));
        match arg.as_str() {
            "--path" => a.paths.push(val().into()),
            "--root" => a.root = val(),
            "--cone" => a.cones.push(val()),
            "--case" => a.case = Some(val()),
            "--only" => a.only.extend(val().split(',').map(str::to_owned)),
            "--quick" => a.quick = true,
            "--csv" => a.csv = true,
            // cargo bench passes this to every bench binary
            "--bench" => {}
            _ => die(&format!("unknown argument {arg}")),
        }
    }
    if a.paths.is_empty() {
        a.paths = search_path();
    }
    if a.cones.is_empty() {
        a.cones = CONES.map(str::to_owned).to_vec();
    }
    a
}

fn die(msg: &str) -> ! {
    eprintln!("fetch_proofs: {msg}");
    exit(2)
}

fn ncpu() -> usize {
    thread::available_parallelism().map_or(1, usize::from)
}

/// The cases to run, each as `--case` takes it.
fn cases(a: &Args) -> Vec<String> {
    let mut out = Vec::new();
    let batches: &[&str] = if a.quick {
        &["1", "10", "100", "1000"]
    } else {
        &["1", "10", "100", "1000", "10000", "100000", "all"]
    };
    out.extend(batches.iter().map(|n| format!("batch:{n}")));
    if !a.quick {
        out.extend(["1", "10", "100", "all"].map(|m| format!("spread:{m}:10000")));
        let mut jobs = vec![1, 2, 4, 8];
        jobs.retain(|&j| j < ncpu());
        jobs.push(ncpu());
        out.extend(jobs.iter().map(|j| format!("jobs:{j}")));
    }
    let ks: &[usize] = if a.quick { &[1000] } else { &[1000, 10000] };
    for &k in ks {
        out.extend([k, 100, 1].map(|s| format!("calls:{k}:{s}")));
    }
    if !a.quick {
        out.extend(a.cones.iter().map(|c| format!("cone:{c}")));
    }
    if !a.only.is_empty() {
        out.retain(|c| a.only.iter().any(|p| c.starts_with(p.as_str())));
    }
    out
}

const COLS: [&str; 11] = [
    "case", "load_s", "calls", "thms", "secs", "thm_per_s", "nodes", "chunks", "fill",
    "rss_load", "rss_end",
];

fn main() {
    let a = args();
    if let Some(case) = &a.case {
        run(&a, case);
        return;
    }
    let exe = env::current_exe().unwrap_or_else(|e| die(&e.to_string()));
    eprintln!(
        "fetch_proofs on {} from {:?}, {} threads",
        a.root,
        a.paths,
        ncpu()
    );
    if a.csv {
        println!("{}", COLS.join(","));
    } else {
        println!(
            "{:<38} {:>7} {:>6} {:>7} {:>8} {:>9} {:>11} {:>7} {:>6} {:>9} {:>9}",
            COLS[0], COLS[1], COLS[2], COLS[3], COLS[4], COLS[5], COLS[6], COLS[7], COLS[8],
            COLS[9], COLS[10]
        );
    }
    let mut failed = false;
    for case in cases(&a) {
        let mut cmd = Command::new(&exe);
        cmd.args(["--case", &case, "--root", &a.root]);
        for p in &a.paths {
            cmd.arg("--path").arg(p);
        }
        if a.csv {
            cmd.arg("--csv");
        }
        let ok = cmd.status().is_ok_and(|s| s.success());
        if !ok {
            eprintln!("fetch_proofs: case {case} failed");
            failed = true;
        }
    }
    if failed {
        exit(1);
    }
}

/// splitmix64, so every run samples the same theorems.
struct Rng(u64);

impl Rng {
    const fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            v.swap(i, (self.next() % (i as u64 + 1)) as usize);
        }
    }
}

fn pending(env: &Env, c: NameId) -> bool {
    matches!(
        env.consts.get(&c),
        Some(olean_export::Const {
            kind: Kind::Thm(Theorem { value: None, .. }),
            ..
        })
    )
}

/// The theorems of each module whose values are still in their oleans.
fn pending_by_module(env: &Env) -> Vec<Vec<NameId>> {
    (0..env.modules.len())
        .map(|m| {
            env.module_consts(m)
                .iter()
                .copied()
                .filter(|&c| pending(env, c))
                .collect()
        })
        .collect()
}

fn count(n: &str, all: usize) -> usize {
    match n {
        "all" => all,
        _ => n.parse().unwrap_or_else(|_| die(&format!("bad count {n}"))),
    }
}

fn run(a: &Args, case: &str) {
    let parts: Vec<&str> = case.split(':').collect();
    let jobs = match parts.as_slice() {
        ["jobs", j] => count(j, ncpu()),
        _ => ncpu(),
    };
    let start = Instant::now();
    let mut env = Env::load_cone(&a.paths, &[&a.root], &[], jobs, &|_, _| {})
        .unwrap_or_else(|e| die(&format!("loading {}: {e}", a.root)));
    let load = start.elapsed().as_secs_f64();
    let rss_load = peak_rss();
    let by_module = pending_by_module(&env);
    let mut all: Vec<NameId> = by_module.iter().flatten().copied().collect();
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    rng.shuffle(&mut all);

    // The batches to fetch, in order, or the cone root.
    let (batches, cone): (Vec<Vec<NameId>>, Option<NameId>) = match parts.as_slice() {
        ["batch", n] => (vec![take(&all, count(n, all.len()))], None),
        ["jobs", _] => (vec![all.clone()], None),
        ["spread", m, n] => {
            let mut ranked: Vec<&Vec<NameId>> = by_module.iter().collect();
            ranked.sort_by_key(|v| std::cmp::Reverse(v.len()));
            let m = count(m, ranked.len()).min(ranked.len());
            // As many as the largest module holds, so every spread draws the same number.
            let n = count(n, all.len()).min(ranked.first().map_or(0, |v| v.len()));
            let mut pool: Vec<NameId> = ranked[..m].iter().copied().flatten().copied().collect();
            rng.shuffle(&mut pool);
            (vec![take(&pool, n)], None)
        }
        ["calls", k, s] => {
            let size = count(s, 1).max(1);
            let pick = take(&all, count(k, all.len()));
            (pick.chunks(size).map(<[_]>::to_vec).collect(), None)
        }
        ["cone", name] => {
            let Some(c) = env.find_name(name) else {
                eprintln!("fetch_proofs: {name} is not in {}, skipped", a.root);
                return;
            };
            (Vec::new(), Some(c))
        }
        _ => die(&format!("unknown case {case}")),
    };

    let (nodes0, bound0) = (env.exprs.len(), env.exprs.bound());
    let before = all.len();
    let t = Instant::now();
    let (calls, thms) = if let Some(c) = cone {
        env.fetch_cone(&[c])
            .unwrap_or_else(|e| die(&format!("{case}: {e}")));
        let left = by_module.iter().flatten().filter(|&&c| pending(&env, c)).count();
        (1, before - left)
    } else {
        let mut thms = 0;
        for b in &batches {
            thms += env
                .fetch_proofs(b)
                .unwrap_or_else(|e| die(&format!("{case}: {e}")))
                .len();
        }
        (batches.len(), thms)
    };
    let secs = t.elapsed().as_secs_f64();
    let nodes = env.exprs.len() - nodes0;
    let chunks = (env.exprs.bound() - bound0) / CHUNK;
    let fill = if chunks == 0 {
        0.0
    } else {
        nodes as f64 / (chunks * CHUNK) as f64
    };
    let row = [
        case.to_owned(),
        format!("{load:.2}"),
        calls.to_string(),
        thms.to_string(),
        format!("{secs:.3}"),
        format!("{:.0}", thms as f64 / secs.max(1e-9)),
        nodes.to_string(),
        chunks.to_string(),
        format!("{fill:.3}"),
        mib(rss_load),
        mib(peak_rss()),
    ];
    if a.csv {
        println!("{}", row.join(","));
    } else {
        println!(
            "{:<38} {:>7} {:>6} {:>7} {:>8} {:>9} {:>11} {:>7} {:>6} {:>9} {:>9}",
            row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8], row[9],
            row[10]
        );
    }
}

fn take(v: &[NameId], n: usize) -> Vec<NameId> {
    v[..n.min(v.len())].to_vec()
}

fn mib(b: Option<u64>) -> String {
    b.map_or_else(|| "-".to_owned(), |b| format!("{}M", b >> 20))
}

/// Peak resident set so far, as in `src/main.rs`.
#[cfg(unix)]
fn peak_rss() -> Option<u64> {
    // SAFETY: rusage is plain integers, for which zero is valid, and getrusage only writes it.
    let mut u: libc::rusage = unsafe { mem::zeroed() };
    if unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut u) } != 0 {
        return None;
    }
    let n = u64::try_from(u.ru_maxrss).ok()?;
    // bytes on macOS, KiB elsewhere
    Some(if cfg!(target_os = "macos") { n } else { n << 10 })
}

#[cfg(not(unix))]
const fn peak_rss() -> Option<u64> {
    None
}
