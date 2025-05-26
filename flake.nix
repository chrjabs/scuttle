{
  description = "Rust library for tools and encodings related to SAT solving library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    systems.url = "github:nix-systems/default-linux";

    nix-config.url = "github:chrjabs/nix-config";
    nix-config.inputs.nixpkgs.follows = "nixpkgs";

    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    systems,
    rust-overlay,
    nix-config,
  }: let
    lib = nixpkgs.lib;
    pkgsFor = lib.genAttrs (import systems) (system: (import nixpkgs {
      inherit system;
      overlays = [(import rust-overlay)] ++ builtins.attrValues nix-config.overlays;
      config.allowUnfree = true;
    }));
    forEachSystem = f: lib.genAttrs (import systems) (system: f pkgsFor.${system});
  in {
    devShells = forEachSystem (pkgs: {
      default = let
        libs = with pkgs; [openssl xz bzip2 gurobi];
      in
        pkgs.mkShell rec {
          nativeBuildInputs = with pkgs; [
            llvmPackages.bintools
            pkg-config
            clang
            cmake
            (rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
            cargo-nextest
            (veripb.overrideAttrs rec {
              version = "version2-250409";
              src = fetchFromGitLab {
                owner = "MIAOresearch";
                repo = "VeriPB";
                rev = "e70eaf1ba5654750ebe34bb4b3c4f89fe9c956b0";
                hash = "sha256-kSZLFukQpE/Pza4hRighlJ71YRXdvEe826WM6FexId4=";
              };
            })
          ];
          buildInputs = libs;
          LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath libs;
          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
          VERIPB_CHECKER = lib.getExe pkgs.veripb;
          GUROBI_HOME = pkgs.gurobi;
        };
    });

    packages = forEachSystem (pkgs: {
      tools = pkgs.callPackage ./tools {};
    });
  };
}
