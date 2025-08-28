{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    # cubical.url = "github:agda/cubical";
    # cubical.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          # cubical = cubical.packages.${system}.cubical;
          # gdacubical = cubical-packages.cubical;
          # agda = pkgs.agda.withPackages [ cubical ];
          agda = pkgs.agda.withPackages [ pkgs.agdaPackages.cubical ];
        in
          {
            # packages.${system} = {
            #   cubical = cublical;
            #   agda = agda;
            # };
            # defaultPackages.${system} = agda;
            devShells.default = pkgs.mkShell {
              buildInputs = [
                agda
                # agda.withPackages [ cubical ]
              ];
            };
          }
      );
}
