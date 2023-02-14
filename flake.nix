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
        lib = pkgs.callPackage (import ./.nix/lib.nix) { inherit z3; };
        pname = "fstar";
        sourceByDenyRegex = src: regexes:
          let
            isFiltered = src ? _isLibCleanSourceWith;
            origSrc = if isFiltered then src.origSrc else src;
          in pkgs.lib.cleanSourceWith {
            filter = (path: type:
              let
                relPath = pkgs.lib.removePrefix (toString origSrc + "/")
                  (toString path);
              in pkgs.lib.all (re: builtins.match re relPath == null) regexes);
            inherit src;
          };
        src = sourceByDenyRegex ./. [
          # Markdown files at the root
          "^[a-zA-Z]+\\.md$"
          # Nix files
          "^flake\\.lock$"
          ".*\\.nix$"
        ];
      in rec {
        packages = {
          inherit z3 ocamlPackages;
          fstar = lib.binary-of-fstar {
            inherit src pname;
            version = "master-snap";
          };
          default = packages.fstar;
          emacs = pkgs.writeScriptBin "emacs-fstar" ''
            #!${pkgs.stdenv.shell}
            export PATH="${packages.fstar}/bin:$PATH"
            export EMACSLOADPATH=
            ${
              (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages
              (epkgs: with epkgs.melpaPackages; [ fstar-mode ])
            }/bin/emacs -q "$@"
          '';
        };
        apps.emacs = {
          type = "app";
          program = "${packages.emacs}/bin/emacs-fstar";
        };
        devShells.default = pkgs.mkShell {
          name = "${packages.fstar.name}-dev";
          inputsFrom = [ packages.fstar ];
          shellHook = ''
            export FSTAR_SOURCES_ROOT="$(pwd)"
            export PATH="$FSTAR_SOURCES_ROOT/bin/:$PATH"
          '';
        };
        inherit lib;
      });
}
