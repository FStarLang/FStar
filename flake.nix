{
  description = "F*";

  inputs = {
    flake-utils.url = "flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
        z3 = pkgs.callPackage (import ./.nix/z3.nix) { };
        version = self.rev or "dirty";
        fstar = ocamlPackages.callPackage ./.nix/fstar.nix {
          inherit version z3;
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
          inherit z3 fstar emacs;
          default = fstar;
        };
        apps.emacs = {
          type = "app";
          program = "${emacs}/bin/emacs-fstar";
        };
        devShells.default = pkgs.mkShell {
          name = "${fstar.name}-dev";
          inputsFrom = [ fstar ];
          shellHook = ''
            export FSTAR_SOURCES_ROOT="$(pwd)"
            export PATH="$FSTAR_SOURCES_ROOT/bin/:$PATH"
          '';
        };
      });
}
