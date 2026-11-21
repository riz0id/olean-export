# Changelog

## Unreleased

- `--per-module` writes files on `--jobs` threads, in an order that respects import hashes; the files are unchanged.
- `join::split_each` takes a `jobs` count, and its callback must be `Sync`.
- Add `Visibility` and `Exporter::with_visibility`, for per-module exporters sharing one view of the modules.
- Add `Env::fetch_proofs` and `Env::fetch_cone`, to decode proofs `Env::load_cone` left in their oleans; both refuse an olean changed since the load.
- Exporting a proof still in its olean fails with `Error::Unfetched`, naming the theorem.
- Lazy loads (`load_statements`, `load_attrs_lazy`) and lazy theorem fetches read olean pages on demand rather than up front.

## 0.7.0 (2026-11-17)

- Add `--interfaces`, per-module exports that follow the module system.
- Add `join -m MODULE`, one module over its imports' interfaces.
- A view's meta marks where imported declarations end, in `view.imported`.
- `join` takes a `--per-module` directory in place of its files.
- `join -m` on a directory opens only the files under the module, and counts its imports in parallel.
- `--per-module` shows progress while writing.
- Per-module imports carry `all`, `public` and `meta`, so file hashes change.
- `Env::imports` holds `inspect::Import`, and `Env::exported` what a module exports.
- Expressions take 16 bytes in place of 24: `Expr::Const` holds an interned `UnivsId` (levels in `Env::univs`), `Expr::Let` boxes its fields in `LetNode`, literals are boxed, and `Expr::Proj` holds a `u32`.
- Big Nat literals convert to decimal in subquadratic time.

## 0.6.0 (2026-11-09)

- Add `--per-module` exports and `join` to merge them.
- Add `keys`, closure keys per declaration (`key::Keys`).
- Add `accepted` store format shared by external checkers.
- Fix duplicate recursors when two modules declare one type.
- Escape names with `«»` like Lean, also in `-c`.
- `statement` counts trusted theorems instead of listing them.
- Read big Nat literals from Lean builds without GMP.
- NDJSON reading is 30% faster and checks id keys.
- CI type-checks the statement cones with nano-lean.

## 0.5.0 (2026-11-07)

- Add `compare` to diff two exports up to ids.
- `compare` parses in parallel, 48s vs 176s on Mathlib.
- `-c` leaves theorem values outside the cone undecoded.
- `Kind::Thm` holds a `Theorem` with an optional value.
- Add `statement`, a theorem's proof-free trusted base.
- Add `--rss` to show peak memory.
- Test fixtures and a cone against lean4export output.
- `Sink::record` takes ids, so resumed exports continue them.
- `Error::Misuse` reports API misuse.
- Fix `Exporter::update` missing changed private constants.
- Fix NDJSON escapes differing from Lean's.
- Fix unchecked ids in `compare`.
- Fix broken pipes reported as errors.
- Refuse olean parts from a different Lean build.

## 0.4.0 (2026-10-29)

- Add `Env::open` and `Env::reload`, redecoding only changed modules.
- Add `Exporter::suspend`, `resume` and `update` for reload diffs.

## 0.3.0 (2026-10-12)

- Walk terms and dependencies on worklists, never overflowing stacks.
- Report cyclic object graphs as corrupt oleans.
- Remove `with_big_stack`, `Exporter` runs on any thread.

## 0.2.0 (2026-10-08)

- Add `inspect`, summarizing an olean's imports, constants and sections.
- Add `-f blean` binary export with per-expression hashes.
- Add `convert` between blean and NDJSON.

## 0.1.0 (2026-10-04)

- Read Lean 4.26 to 4.35 oleans, emit lean4export NDJSON.
- Export a module's whole closure, or `-c` constants only.
- Decode modules in parallel, identical output for any `-j`.
- Map oleans into memory and stream the export.
- Report malformed oleans and missing modules as typed errors.
- Add opt-in `mimalloc` feature for the global allocator.
