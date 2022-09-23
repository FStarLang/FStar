{

  description = "The F* language";

  inputs = {
    nixpkgs.url = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
  flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
    let
      pkgs = import nixpkgs { inherit system; };
      z3 = pkgs.callPackage ./z3.nix {};
      fstar-factory = pkgs.callPackage ./default.nix {
        inherit z3;
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_12;
      };
      src = ./.;
      fstar = fstar-factory.binary-of-fstar {
        inherit src;
        name = "fstar-master";
      };
      fstar-tests = fstar-factory.check-fstar {
        inherit src;
        name = "fstar-tests-master";
        existing-fstar = fstar;
      };
    in {
      packages = {
        inherit z3 fstar;
      };
      defaultPackage = fstar;
      checks = {
        inherit fstar-tests;
      };
      hydraJobs = {
        inherit fstar-tests;
        fstar-build = fstar;
        fstar-doc = pkgs.stdenv.mkDerivation {
          name = "fstar-book";
          src = ./doc/book;
          buildInputs = with pkgs; [ sphinx python39Packages.sphinx_rtd_theme ];
          installPhase = ''
            mkdir -p "$out"/nix-support
            echo "doc manual $out/book" >> $out/nix-support/hydra-build-products
            mv _build/html $out/book
          '';
        };
      };
    }
  );

}
