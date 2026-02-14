{
  description = "HoTT book reals in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    agda-mcp.url = "path:/home/jackson/repositories/agda-mcp";
    # agda-mcp.url = "github:broughjt/agda-mcp";
  };

  outputs = { self, nixpkgs, flake-utils, agda-mcp }:
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
                agda-mcp.packages.${system}.agda-mcp
              ];
            };
          }
      );
}
