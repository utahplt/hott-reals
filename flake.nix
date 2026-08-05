{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    agda-mcp = {
      url = "github:broughjt/agda-mcp";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils, agda-mcp }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          libraries = [ pkgs.agdaPackages.cubical ];
          agda = pkgs.agda.withPackages libraries;
        in
          {
            devShells.default = pkgs.mkShell {
              buildInputs = [
                agda
                (agda-mcp.packages.${system}.default.withPackages libraries)
              ];
            };
          }
      );
}
