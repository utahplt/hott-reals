{
  description = "HoTT book reals in Cubical Agda";

  nixConfig = {
    extra-substituters = [ "https://hott-reals.cachix.org" ];
    extra-trusted-public-keys = [ "hott-reals.cachix.org-1:rgyQbU9OCqP0UDpSktfNL4ogjZKb45Tq2ZhLpmfRP6I=" ];
  };

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      url = "github:utahplt/cubical/hott-reals";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, cubical }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          cubical' = pkgs.agdaPackages.cubical.overrideAttrs (_: {
            version = "hott-reals-${cubical.shortRev}";
            src = cubical;
          });
          library = pname: buildInputs: pkgs.agdaPackages.mkDerivation {
            inherit pname buildInputs;
            version = "0.1.0";
            src = ./libraries/${pname};
            meta = { };
          };
          libraries = rec {
            hott-reals-order = library "hott-reals-order" [ cubical' ];
            hott-reals-completion = library "hott-reals-completion" [ cubical' ];
            hott-reals = library "hott-reals" [ cubical' hott-reals-order ];
          };
        in
          {
            packages = libraries // {
              cubical = cubical';
            };

            checks = libraries;

            devShells.default = pkgs.mkShell {
              buildInputs = [ pkgs.agda.unwrapped ];
              shellHook = ''
                root=$(git rev-parse --show-toplevel)
                export AGDA_DIR="$root/.agda"
                mkdir -p "$AGDA_DIR"
                {
                  echo ${cubical'}/${cubical'.libraryFile}
                  for lib in "$root"/libraries/*/*.agda-lib; do echo "$lib"; done
                } > "$AGDA_DIR/libraries"
              '';
            };
          }
      );
}
