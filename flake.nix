{
  description = "F*";

  inputs = {
    flake-utils.url = "flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      flake-utils,
      nixpkgs,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        version = self.rev or "dirty";
      in
      {
        packages = rec {
          z3 = pkgs.z3_4_8_5;
          ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
          fstar-dune = ocamlPackages.callPackage .nix/dune.nix { inherit version; };
          fstar-ulib = pkgs.callPackage .nix/ulib.nix { inherit fstar-dune version z3; };
          fstar = pkgs.callPackage .nix/fstar.nix {
            inherit
              fstar-dune
              fstar-ulib
              ocamlPackages
              version
              z3
              ;
          };
          fstar-ocaml-snapshot = pkgs.callPackage .nix/ocaml-snapshot.nix {
            inherit fstar ocamlPackages version;
          };
          fstar-bootstrap = pkgs.callPackage .nix/bootstrap.nix {
            inherit
              fstar
              fstar-dune
              fstar-ocaml-snapshot
              fstar-ulib
              ;
          };
          emacs-fstar = pkgs.writeScriptBin "emacs-fstar" ''
            #!${pkgs.stdenv.shell}
            export PATH="${self.packages.${system}.fstar}/bin:$PATH"
            export EMACSLOADPATH=
            ${
              (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (
                epkgs: with epkgs.melpaPackages; [ fstar-mode ]
              )
            }/bin/emacs -q "$@"
          '';
          default = fstar;
        };

        apps.emacs = {
          type = "app";
          program = "${self.packages.${system}.emacs-fstar}/bin/emacs-fstar";
        };

        devShells.default = pkgs.mkShell {
          name = "${self.packages.${system}.fstar.name}-dev";
          inputsFrom = [ self.packages.${system}.fstar ];
          shellHook = ''
            export FSTAR_SOURCES_ROOT="$(pwd)"
            export PATH="$FSTAR_SOURCES_ROOT/bin/:$PATH"
          '';
        };
      }
    );
}
