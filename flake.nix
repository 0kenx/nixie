{
  description = "OxiZ - Pure-Rust SMT solver";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

    crane.url = "github:ipetkov/crane";

    flake-utils.url = "github:numtide/flake-utils";

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    advisory-db = {
      url = "github:rustsec/advisory-db";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    crane,
    flake-utils,
    rust-overlay,
    advisory-db,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [(import rust-overlay)];
      };
      inherit (pkgs) lib;
      srcRoot = ./.;

      rustToolchain = pkgs.rust-bin.stable."1.96.0".default.override {
        extensions = [
          "rust-src"
          "clippy"
          "llvm-tools-preview"
        ];
        targets = ["wasm32-unknown-unknown"];
      };
      craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
      cargoLockExists = builtins.pathExists ./Cargo.lock;
      src =
        if cargoLockExists
        then
          lib.cleanSourceWith {
            src = srcRoot;
            filter = path: type:
              craneLib.filterCargoSources path type
              || lib.hasSuffix "deny.toml" path
              || lib.hasSuffix "clippy.toml" path;
          }
        else srcRoot;

      nightlyRustfmt = let
        nightly = pkgs.rust-bin.nightly."2026-06-11".minimal.override {
          extensions = ["rustfmt"];
        };
      in
        pkgs.runCommand "nightly-rustfmt" {} ''
          mkdir -p $out/bin
          ln -s ${nightly}/bin/rustfmt $out/bin/rustfmt
          ln -s ${nightly}/bin/cargo-fmt $out/bin/cargo-fmt
        '';

      fuzzRustToolchain = pkgs.rust-bin.nightly."2026-06-11".default.override {
        extensions = [
          "rust-src"
          "llvm-tools-preview"
        ];
      };

      rustCommonArgs = {
        inherit src;
        pname = "oxiz-workspace";
        version = "0.3.2";
        strictDeps = true;
        cargoBuildCommand = "cargo build --release";
        cargoCheckCommand = "cargo check --release";
        cargoTestCommand = "cargo test --release";
        nativeBuildInputs =
          [
            pkgs.pkg-config
            pkgs.clang
          ]
          ++ lib.optionals pkgs.stdenv.isLinux [pkgs.mold];
        buildInputs = lib.optionals pkgs.stdenv.isDarwin [pkgs.libiconv];
        preBuild = ''
          unset RUSTC_WRAPPER
          unset SCCACHE_CACHE_SIZE
        '';
      };

      cargoArtifacts =
        if cargoLockExists
        then craneLib.buildDepsOnly rustCommonArgs
        else null;

      oxiz-cli =
        if cargoLockExists
        then
          craneLib.buildPackage (rustCommonArgs
            // {
              inherit cargoArtifacts;
              pname = "oxiz-cli";
              cargoExtraArgs = "--package oxiz-cli --bin oxiz";
            })
        else null;

      workspaceChecks = lib.optionalAttrs cargoLockExists {
        workspace-fmt = craneLib.cargoFmt {
          inherit src;
          pname = "oxiz";
          version = "0.3.2";
        };

        workspace-audit = craneLib.cargoAudit {
          inherit src advisory-db;
          pname = "oxiz";
          version = "0.3.2";
        };

        workspace-deny = craneLib.cargoDeny {
          inherit src;
          pname = "oxiz";
          version = "0.3.2";
        };
      };
    in {
      packages = lib.optionalAttrs cargoLockExists {
        default = oxiz-cli;
        inherit oxiz-cli;
      };

      apps = lib.optionalAttrs cargoLockExists {
        default = flake-utils.lib.mkApp {
          drv = oxiz-cli;
          name = "oxiz";
        };
      };

      checks = workspaceChecks;

      formatter = pkgs.nixfmt;

      devShells.default = craneLib.devShell {
        checks = workspaceChecks;

        shellHook = ''
          export PATH="${nightlyRustfmt}/bin:$PATH"
          if git rev-parse --show-toplevel >/dev/null 2>&1; then
            export OXIZ_REPO_ROOT="$(git rev-parse --show-toplevel)"
          else
            export OXIZ_REPO_ROOT="$PWD"
          fi
          export OXIZ_FUZZ_TOOLCHAIN_BIN="${fuzzRustToolchain}/bin"
          export OXIZ_SCCACHE_CACHE_HOME="''${OXIZ_SCCACHE_CACHE_HOME:-$HOME/.cache/oxiz}"

          case "''${TMPDIR:-}" in
            ""|/tmp/nix-shell.*)
              export TMPDIR=/tmp
              ;;
          esac

          export SCCACHE_DIR="$OXIZ_SCCACHE_CACHE_HOME/sccache"
          export SCCACHE_SERVER_UDS="$OXIZ_SCCACHE_CACHE_HOME/oxiz-sccache.sock"
          export SCCACHE_CACHE_SIZE="5G"
          case "''${OXIZ_USE_SCCACHE:-}" in
            1|true|yes)
              export RUSTC_WRAPPER="${pkgs.sccache}/bin/sccache"
              ;;
            *)
              unset RUSTC_WRAPPER
              ;;
          esac
        '';

        packages = [
          pkgs.pkg-config
          pkgs.rust-analyzer
          pkgs.cargo-edit
          pkgs.cargo-fuzz
          pkgs.cargo-watch
          pkgs.cargo-nextest
          pkgs.cargo-deny
          pkgs.cargo-audit
          pkgs.sccache
          pkgs.just
          pkgs.wasm-pack
          pkgs.binaryen
          pkgs.wasmtime
          pkgs.maturin
          pkgs.python3
          pkgs.bash
          pkgs.git
          pkgs.jq
          pkgs.ripgrep
          pkgs.coreutils
          pkgs.llvmPackages.llvm
        ];
      };
    });
}
