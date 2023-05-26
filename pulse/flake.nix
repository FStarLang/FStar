{
  inputs = {
    fstar.url = "github:fstarlang/fstar";
    flake-utils.follows = "fstar/flake-utils";
    nixpkgs.follows = "fstar/nixpkgs";
  };

  outputs = { self, fstar, flake-utils, nixpkgs }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        fstarPkgs = fstar.packages.${system};
        ocamlPackages = fstarPkgs.ocamlPackages;
        default = pkgs.stdenv.mkDerivation {
          name = "steel";
          src = ./.;
          nativeBuildInputs = [
            pkgs.dune_3
            fstarPkgs.fstar
            ocamlPackages.ocaml
            ocamlPackages.findlib
            ocamlPackages.ppx_deriving_yojson
            ocamlPackages.sedlex
            ocamlPackages.process
            ocamlPackages.pprint
            ocamlPackages.menhir
            ocamlPackages.menhirLib
            ocamlPackages.stdint
            ocamlPackages.batteries
            ocamlPackages.zarith
          ];
          installPhase = ''
            mkdir -p $out
            PREFIX=$out make install
          '';
          enableParallelBuilding = true;
        };
        steel =
          default.overrideAttrs (_: { buildFlags = [ "lib" "verify-steel" ]; });
      in {
        packages = {
          inherit default steel;
        };
        hydraJobs = { inherit default steel; };
      });
}
