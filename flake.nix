{
  description = "F*";

  inputs = {
    flake-utils.url = "flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
        z3 = pkgs.callPackage (import ./.nix/z3.nix) { };
        version = self.rev or "dirty";
        fstar-dune = ocamlPackages.callPackage ./ocaml { inherit version; };
        fstar-ulib = pkgs.callPackage ./nix/ulib.nix { inherit fstar-dune version z3; };
        fstar = pkgs.callPackage ./.nix/fstar.nix {
          inherit fstar-dune fstar-ulib version z3;
        };
        fstar-ocaml-snapshot =
          pkgs.callPackage ./src { inherit fstar ocamlPackages version; };
        fstar-bootstrap = pkgs.callPackage ./.nix/bootstrap.nix {
          inherit fstar fstar-dune fstar-ocaml-snapshot fstar-ulib;
        };
        emacs = pkgs.writeScriptBin "emacs-fstar" ''
          #!${pkgs.stdenv.shell}
          export PATH="${fstar}/bin:$PATH"
          export EMACSLOADPATH=
          ${
            (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages
            (epkgs: with epkgs.melpaPackages; [ fstar-mode ])
          }/bin/emacs -q "$@"
        '';
      in rec {
        packages = {
          inherit z3 ocamlPackages;
          inherit fstar fstar-dune fstar-ocaml-snapshot fstar-bootstrap;
          inherit emacs;
          default = fstar;
        };
        apps.emacs = {
          type = "app";
          program = "${emacs}/bin/emacs-fstar";
        };
        devShells.default = pkgs.mkShell {
          name = "${fstar.name}-dev";
          inputsFrom = [ fstar fstar-dune ];
          shellHook = ''
            export FSTAR_SOURCES_ROOT="$(pwd)"
            export PATH="$FSTAR_SOURCES_ROOT/bin/:$PATH"
          '';
        };
      });
}
