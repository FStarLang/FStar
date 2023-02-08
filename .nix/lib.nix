/* Provides derivations that operate on F* source trees.

    - [binary-of-fstar] builds fstar.exe, verifies ulib, and installs
      both of them.
*/
{ stdenv, lib, makeWrapper, installShellFiles, which, z3, ocamlPackages, sphinx, python39Packages, removeReferencesTo }:
let
  /* Following [https://github.com/FStarLang/FStar/blob/master/fstar.opam],
     `ocamlBuildInputs` is the list of OCaml packages necessary to build F* snapshots.
  */
  ocamlNativeBuildInputs = with ocamlPackages; [
    ocaml
    dune_3
    findlib
  ];
  ocamlBuildInputs = with ocamlPackages; [
    batteries
    zarith
    stdint
    yojson
    menhirLib
    pprint
    sedlex
    ppxlib
    ppx_deriving
    ppx_deriving_yojson
    process
  ];
  preBuild = { pname, version }: ''
    echo "echo ${lib.escapeShellArg pname}-${version}" > src/tools/get_commit
    patchShebangs ulib/install-ulib.sh
    substituteInPlace src/ocaml-output/Makefile --replace '$(COMMIT)' '${version}'
  '';
  # Default options. (camel case because those are injected as bash variables)
  defaults = {
    # FIXME: honor this option to compile ulibfs.dll, the F# bindings to F* ulib,
    # maybe with conditional dependencies
    compileUlibFs = false;
  };

  binary-of-fstar = { src, pname ? src.pname, version ? src.version, opts ? defaults }:
    let pkg =
      stdenv.mkDerivation (defaults // opts // {
        inherit pname version src;

        nativeBuildInputs = [ makeWrapper installShellFiles z3 removeReferencesTo ] ++ ocamlNativeBuildInputs;
        buildInputs = ocamlBuildInputs;
        strictDeps = true;
  
        preBuildPhases = [ "preparePhase" ];
        preparePhase = preBuild { inherit pname version; };
  
        # Triggers [make] rules according to [opts] contents
        buildPhase = ''
          MAKE_FLAGS="-j$NIX_BUILD_CORES"
          make $MAKE_FLAGS
        '';
  
        OCAML_VERSION = ocamlPackages.ocaml.version;
        Z3_PATH = lib.getBin z3;
        # Installs binaries and libraries according to [opts] contents
        installPhase = ''
          copyBin () { cp "bin/$1" $out/bin
                       # OCaml leaves it's full store path in produced binaries
                       # Thus we need to remove any reference to the path of OCaml in the store
                       remove-references-to -t '${ocamlPackages.ocaml}' $out/bin/$1
                       wrapProgram "$out/bin/$1" --prefix PATH ":" "$Z3_PATH/bin"
                     }
          mkdir -p $out/{bin,lib}
          copyBin fstar.exe
          cp -p -r lib/fstar $out/lib/fstar
          MAKE_FLAGS="-j$NIX_BUILD_CORES"
          make $MAKE_FLAGS -C ulib install PREFIX=$out
          # We need to provide fstar.lib to the OCaml library site
          # so that it can be seen by OCAMLPATH
          # However, it is easier to just do a symlink from the F* library
          # to the OCaml library site
          # FIXME: is there any way to avoid this step and append $out/lib to OCAMLPATH
          # whenever someone loads the fstar nix package?
          SITE_LIB="$out/lib/ocaml/$OCAML_VERSION/site-lib"
          mkdir -p "$SITE_LIB"
          rm -f "$SITE_LIB/fstar"
          ln -s "$out/lib/fstar" "$SITE_LIB/fstar"
          # Install shell completion
          installShellCompletion --bash .completion/bash/fstar.exe.bash
          installShellCompletion --fish .completion/fish/fstar.exe.fish
          installShellCompletion --zsh --name _fstar.exe .completion/zsh/__fstar.exe
        '';
  
        dontFixup = true;
  
        meta.mainProgram = "fstar.exe";
      });
    in pkg;

in {
  inherit binary-of-fstar;
  defaultOptions = defaults;
}
