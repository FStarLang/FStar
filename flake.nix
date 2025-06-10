{
  description = "F*";

  inputs = {
    flake-utils.url = "flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
        # We need sedlex >= 3.5 for utf8 support.
        sedlex = ocamlPackages.sedlex.overrideDerivation (_: {
          src = pkgs.fetchFromGitHub {
            owner = "ocaml-community";
            repo = "sedlex";
            rev = "v3.5";
            sha256 = "sha256-TtxrlJtoKn7i2w8OVD3YDJ96MsmsFs4MA1CuNKpqSuU=";
          };
        });

        z3 = pkgs.callPackage (import ./.nix/z3.nix) { };
        version = self.rev or "dirty";
        fstar = ocamlPackages.callPackage ./.nix/fstar.nix {
          inherit version z3 sedlex;
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
      in
      {
        packages = {
          inherit z3 fstar emacs ocamlPackages;
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
