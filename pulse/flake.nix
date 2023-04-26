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
        steel = pkgs.stdenv.mkDerivation {
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
      in {
        packages = {
          inherit steel;
          default = steel;
        };
        hydraJobs = { inherit steel; };
      });
}
