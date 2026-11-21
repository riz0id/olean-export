{
  description = "Read Lean 4 .olean files and emit lean4export-compatible NDJSON";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { self, nixpkgs }:
    let
      inherit (nixpkgs) lib;
      systems = [
        "aarch64-darwin"
        "x86_64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      manifest = (lib.importTOML ./Cargo.toml).package;
    in
    {
      packages = forAllSystems (pkgs: rec {
        olean-export = pkgs.rustPlatform.buildRustPackage {
          pname = manifest.name;
          inherit (manifest) version;
          src = lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions [
              ./Cargo.toml
              ./Cargo.lock
              ./src
              ./tests
              ./examples
            ];
          };
          cargoLock.lockFile = ./Cargo.lock;
          meta = {
            inherit (manifest) description;
            homepage = manifest.repository;
            license = lib.licenses.mit;
            mainProgram = manifest.name;
          };
        };
        olean-export-mimalloc = olean-export.overrideAttrs { buildFeatures = [ "mimalloc" ]; };
        default = olean-export;
      });

      checks = forAllSystems (pkgs: {
        # Builds the package and runs `cargo test`.
        package = self.packages.${pkgs.stdenv.hostPlatform.system}.default;
      });

      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [
            cargo
            rustc
            clippy
            rustfmt
            rust-analyzer
            dprint
            just
            pre-commit
          ];
          RUST_SRC_PATH = "${pkgs.rustPlatform.rustLibSrc}";
        };
      });

      formatter = forAllSystems (pkgs: pkgs.nixfmt);
    };
}
