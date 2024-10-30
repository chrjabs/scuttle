{
  lib,
  rustPlatform,
  openssl,
  pkg-config,
  cmake,
  fetchFromGitHub,
  srcOnly,
}: let
  manifest = (lib.importTOML ./Cargo.toml).package;
in
  rustPlatform.buildRustPackage {
    pname = manifest.name;
    version = manifest.version;

    src = lib.fileset.toSource {
      root = ./.;
      fileset = lib.fileset.unions [
        ./Cargo.lock
        ./Cargo.toml
        ./src
      ];
    };
    cargoLock.lockFile = ./Cargo.lock;

    buildInputs = [];
    nativeBuildInputs = [];

    meta = with lib; {
      description = manifest.description;
      homepage = manifest.homepage;
      license = licenses.mit;
      platforms = platforms.all;
    };
  }
