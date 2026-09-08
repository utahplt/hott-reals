{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      url = "github:broughjt/cubical/16c158d20a45b055318887fc65dba3d609232b2b";
      flake = false;
    };
    agda-mcp = {
      url = "github:broughjt/agda-mcp/cli-daemon-fixes";
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
            version = "beans-16c158d20";
            src = cubical;
          });
          libraries = [ cubical' ];
          agda = pkgs.agda.withPackages libraries;
          agda-interact' = agda-mcp.packages.${system}.agda-interact.withPackages libraries;
        in
          {
            packages.agda-interact = agda-interact';

            devShells.default = pkgs.mkShell {
              buildInputs = [
                agda
                agda-interact'
              ];
            };
          }
      );
}
