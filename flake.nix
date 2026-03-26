{
  description = "Scuttle: Multi-objective MaxSAT solver written in Rust";

  nixConfig = {
    extra-substituters = [
      "https://chrjabs.cachix.org"
    ];
    extra-trusted-public-keys = [
      "chrjabs.cachix.org-1:hnjWCdXP+IWya+Y+/xTwyfpNtwOlbR0X3/9OqyLoE1o="
    ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    flake-parts.url = "github:hercules-ci/flake-parts";

    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";

    nur-packages.url = "github:chrjabs/nur-packages";
    nur-packages.inputs.nixpkgs.follows = "nixpkgs";
    nur-packages.inputs.rust-overlay.follows = "rust-overlay";

    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } (_: {
      imports = [ inputs.treefmt-nix.flakeModule ];
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      perSystem =
        {
          system,
          pkgs,
          ...
        }:
        let
          lib = pkgs.lib;
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            config.allowUnfree = true;
            overlays =
              let
                toolchain-overlay = _: super: {
                  rust-toolchain = super.symlinkJoin {
                    name = "rust-toolchain";
                    paths = [
                      ((pkgs.extend (import inputs.rust-overlay)).rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
                    ];
                    buildInputs = [ super.makeWrapper ];
                    postBuild = ''
                      wrapProgram $out/bin/cargo --set LIBCLANG_PATH ${super.libclang.lib}/lib
                    '';
                  };
                };
                patch-veripb = _: super: {
                  veripb = super.veripb.overrideAttrs {
                    patches = [ ./patches/veripb-trivial-order-constraint.patch ];
                  };
                };
              in
              [
                toolchain-overlay
                inputs.nur-packages.overlays.default
                patch-veripb
              ];
          };

          devShells.default =
            let
              libs = with pkgs; [
                openssl
                xz
                bzip2
                gurobi
              ];
            in
            pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } rec {
              nativeBuildInputs = with pkgs; [
                llvmPackages.bintools
                pkg-config
                clang
                cmake
                rust-toolchain
                cargo-nextest
                veripb
              ];
              buildInputs = libs;
              LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
              LD_LIBRARY_PATH = lib.makeLibraryPath libs;
              PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
              VERIPB_CHECKER = lib.getExe pkgs.veripb;
              GUROBI_HOME = pkgs.gurobi;
            };

          treefmt = {
            settings.global = {
              on-unmatched = "error";
            };
            programs = {
              # Rust
              rustfmt = {
                enable = true;
                edition = "2024";
                package = pkgs.rust-toolchain;
              };
              # Nix
              deadnix.enable = true;
              nixfmt.enable = true;
              # Shell
              shellcheck = {
                enable = true;
                excludes = [ ".envrc" ];
              };
              shfmt.enable = true;
              # TOML
              taplo.enable = true;
            };
          };
        };
    });
}
