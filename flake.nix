{
  description = "F* flake";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.05";
    fstar-flake.url = "github:W95Psp/nix-flake-fstar";
  };
  
  outputs = { self, nixpkgs, flake-utils, fstar-flake }:
    flake-utils.lib.eachSystem [ "x86_64-darwin" "x86_64-linux"]
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          fstar = fstar-flake.defaultPackage.${system};
          lib = pkgs.lib;
        in  
          rec {
            packages = {
              fstar = fstar.override ({ name = "fstar-dev";
                                        src = pkgs.lib.cleanSource ./.;
                                      });
            };
            defaultPackage = packages.fstar;
            devShell = pkgs.mkShell {
              name = "dev-env-fstar-compiler";
              inputsFrom = [ packages.fstar ];
              buildInputs = [
                (pkgs.writeScriptBin "fstar.exe"
                  ''#!${pkgs.bash}/bin/bash
                      if test -f "$FSTAR_SOURCES_ROOT"/bin/fstar.exe; then
                         "$FSTAR_SOURCES_ROOT"/bin/fstar.exe "$@"
                      else
                        echo "WARNING: NOT USING LOCAL FSTAR.EXE"
                        ${fstar}/bin/fstar.exe "$@"
                      fi
                    '')
              ];
              shellHook = ''
                  export FSTAR_SOURCES_ROOT="$(pwd)"
                  echo "$DIR_LOCALS" > src/.dir-locals.el
                '';
              DIR_LOCALS = ''((fstar-mode
  (fstar-subp-sloppy . nil)
  (eval .
  (progn (defun my-fstar-compute-prover-args-using-make ()
             "Construct arguments to pass to F* by calling make."
             (with-demoted-errors "Error when constructing arg string: %S"
               (split-string
                (car (last (process-lines "make"
                             "-C" (concat (getenv "FSTAR_SOURCES_ROOT") "/src")
                             "-f" "Makefile.boot" "--quiet"
                             (concat (file-name-nondirectory buffer-file-name) "-in")
                           )
                     )
                )
               )
             )
         )
         (setq-local fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
  )
)))
'';
            };
          }
      );
}
