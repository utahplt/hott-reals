{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          agda = pkgs.agda.withPackages [ pkgs.agdaPackages.cubical ];
        in
          {
            devShells.default = pkgs.mkShell {
              buildInputs = [
                agda
              ];
            };
          }
      );
}
