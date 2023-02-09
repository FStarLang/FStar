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
        ulib = pkgs.callPackage ./ulib { inherit z3 fstar-dune version; };
        fstar = pkgs.callPackage ./.nix/fstar.nix {
          inherit z3 fstar-dune version ulib;
        };
        fstar-ocaml-snapshot = pkgs.callPackage ./src {
          inherit ocamlPackages version;
          # extracting F* doesn't require ulib to be typechecked
          fstar = fstar.override (_: {
            ulib = pkgs.lib.sourceByRegex ./. [ "ulib.*" ];

          });
        };
        fstar-bootstrap = fstar.override (_:
          let
            fstar-dune-bootstrap =
              fstar-dune.overrideAttrs (_: { src = fstar-ocaml-snapshot; });
          in {
            fstar-dune = fstar-dune-bootstrap;
            ulib = ulib.override (_: { fstar-dune = fstar-dune-bootstrap; });
          });
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
          inherit fstar-dune fstar-ocaml-snapshot fstar fstar-bootstrap;
          inherit emacs;
          default = fstar;
        };
        apps.emacs = {
          type = "app";
          program = "${packages.emacs}/bin/emacs-fstar";
        };
        devShells.default = pkgs.mkShell {
          name = "${packages.fstar.name}-dev";
          inputsFrom = [ packages.fstar packages.fstar-dune ];
          shellHook = ''
            export FSTAR_SOURCES_ROOT="$(pwd)"
            export PATH="$FSTAR_SOURCES_ROOT/bin/:$PATH"
          '';
        };
      });
}
