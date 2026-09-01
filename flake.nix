{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      url = "github:agda/cubical/6e6df4e74d4b03205c942c1574c6fea0b2cc213e";
      flake = false;
    };
    agda-mcp = {
      url = "github:broughjt/agda-mcp";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils, cubical, agda-mcp }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          cubical' = pkgs.agdaPackages.cubical.overrideAttrs (_: {
            version = "master-6e6df4e7";
            src = cubical;
          });
          libraries = [ cubical' ];
          agda = pkgs.agda.withPackages libraries;
          agda-mcp' = agda-mcp.packages.${system}.default.withPackages libraries;
        in
          {
            packages.agda-mcp = agda-mcp';

            devShells.default = pkgs.mkShell {
              buildInputs = [
                agda
                agda-mcp'
              ];
            };
          }
      );
}
