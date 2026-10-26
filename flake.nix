{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      url = "github:agda/cubical/c37782bb4e382dc41035e0970409a0c17b55e6ce";
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
            version = "master-c37782bb";
            src = cubical;
          });
          hott-reals-order = pkgs.agdaPackages.mkDerivation {
            pname = "hott-reals-order";
            version = "0.1.0";
            src = ./libraries/hott-reals-order;
            buildInputs = [ cubical' ];
            meta = { };
          };
          libraries = [ cubical' ];
          agda = pkgs.agda.withPackages libraries;
          agda-interact' = agda-mcp.packages.${system}.agda-interact.withPackages libraries;
        in
          {
            packages = {
              inherit hott-reals-order;
              agda-interact = agda-interact';
            };

            devShells.default = pkgs.mkShell {
              buildInputs = [
                agda
                agda-interact'
                pkgs.typst
              ];
              TYPST_FONT_PATHS = "${pkgs.julia-mono}/share/fonts";
              TYPST_IGNORE_SYSTEM_FONTS = "true";
            };
          }
      );
}
