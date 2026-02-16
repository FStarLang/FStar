{
  description = "F*";

  inputs = {
    flake-utils.url = "flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs =
    {
      flake-utils,
      nixpkgs,
      self,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_5_3;

        z3 = pkgs.callPackage (import ./.nix/z3.nix) { };
        version = self.rev or "dirty";

        # Create OCaml library path with .so files for CAML_LD_LIBRARY_PATH
        ocamlLibraryPath = pkgs.symlinkJoin {
          name = "ocaml-shared-libs";
          paths = [
            "${ocamlPackages.num}/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/num"
            "${ocamlPackages.zarith}/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/stublibs"
            "${ocamlPackages.stdint}/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/stublibs"
          ];
        };

        fstar = ocamlPackages.callPackage ./.nix/fstar.nix {
          inherit version z3;
        };

        emacs = pkgs.writeScriptBin "emacs-fstar" ''
          #!${pkgs.stdenv.shell}
          export PATH="${fstar}/bin:$PATH"
          export EMACSLOADPATH=
          ${
            (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (
              epkgs: with epkgs.melpaPackages; [ fstar-mode ]
            )
          }/bin/emacs -q "$@"
        '';
      in
      {
        packages = {
          inherit
            z3
            fstar
            emacs
            ocamlPackages
            ;
          default = fstar;
        };
        apps.emacs = {
          type = "app";
          program = "${emacs}/bin/emacs-fstar";
        };
        devShells.default = pkgs.mkShell {
          name = "${fstar.name}-dev";
          inputsFrom = [ fstar ];
          buildInputs = [ z3 ];
          shellHook = ''
            export CAML_LD_LIBRARY_PATH="${ocamlLibraryPath}"
            export FSTAR_SOURCES_ROOT="$(pwd)"
            export PATH="$FSTAR_SOURCES_ROOT/bin/:$PATH"
          '';
        };
      }
    );
}
