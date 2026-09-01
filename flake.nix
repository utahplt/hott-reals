{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      url = "github:broughjt/cubical/da4178930c94e0cbc6124d5547db8ff1758e4d09";
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
            version = "beans-da417893";
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
