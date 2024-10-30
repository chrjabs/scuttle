{
  description = "A VeriPB checker focused on performance";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    systems.url = "github:nix-systems/default-linux";

    custom.url = "github:chrjabs/nix-config";
    custom.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = {
    self,
    nixpkgs,
    systems,
    custom,
  }: let
    forAllSystems = nixpkgs.lib.genAttrs (import systems);
    pkgsFor = nixpkgs.legacyPackages;
  in {
    devShells = forAllSystems (system: {
      default = pkgsFor.${system}.callPackage ./shell.nix {veripb = custom.packages.${system}.veripb;};
    });

    packages = forAllSystems (system: {
      default = pkgsFor.${system}.callPackage ./package.nix {};
    });
  };
}
