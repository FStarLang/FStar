/* Provides derivations that operate on F* source trees.

   Those derivations realizes F* bootstraping. F* is bootsrapped via
   OCaml; F* source trees are assumed to provide an OCaml snapshot (in
   [src/ocaml-output]).

    - [ml-extraction-of-fstar]: given an F* source tree [src] and an
      existing F* binary [existing-fstar], [ml-extraction-of-fstar {src,
      existing-fstar, ...}] extracts F* sources (written in F*) as an
      OCaml snapshot.

    - [binary-of-ml-snapshot]: given an F* source tree [src] and a bunch
      of build options[1] [opts], [binary-of-ml-snapshot {src, opts, ...}]
      builds the OCaml snapshot [${src}/src/ocaml-output].

    - [binary-of-fstar] is basically the composition
      [binary-of-ml-snapshot ∘ ml-extraction-of-fstar ∘ binary-of-ml-snapshot],
      that is the full bootrapping of the compiler.

   [1]: Options are given as a set composed of the following keys:
    • [keep-sources]     (defaults to [false])
         Whether the folder [src] is kept during [installPhase]
         (keep in mind OCaml snapshots live under [src])
    • [compile-fstar]    (defaults to [true] )
         Wether [bin/fstar.exe] is built
    • [compile-bytecode] (defaults to [false])
         Wether [bin/fstar.ocaml] is built
    • [compile-tests]    (defaults to [true])
         Wether [bin/test.exe] is built
    • [compile-comp-lib]  (defaults to [true] )
         Wether F*'s compiler OCaml library is built & installed
    • [compile-ulib]     (defaults to [true] )
         Wether F*'s [ulib] OCaml library is built & installed
*/
{ stdenv, lib, makeWrapper, installShellFiles, which, z3, ocamlPackages, sphinx, python39Packages, removeReferencesTo }:
let
  /* Following [https://github.com/FStarLang/FStar/blob/master/fstar.opam],
     `ocamlBuildInputs` is the list of OCaml packages necessary to build F* snapshots.
  */
  ocamlNativeBuildInputs = with ocamlPackages; [
    ocaml
    ocamlbuild
    findlib
    menhir
  ];
  ocamlBuildInputs = with ocamlPackages; [
    batteries
    zarith
    stdint
    yojson
    fileutils
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
    patchShebangs src/tools ulib/gen_mllib.sh bin
    substituteInPlace src/ocaml-output/Makefile --replace '$(COMMIT)' '${version}'
  '';
  # Default options. (camel case because those are injected as bash variables)
  defaults = {
    keepSources = false;
    compileFStar = true;
    compileBytecode = false;
    compileTests = true;
    compileCompLib = true;
    compileUlib = true;
  };

  binary-of-ml-snapshot = { src, pname ? src.pname, version ? src.version, opts ? defaults }:
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
          [ -z "$compileFStar"    ] || make $MAKE_FLAGS -C src/ocaml-output ../../bin/fstar.exe
          [ -z "$compileBytecode" ] || make $MAKE_FLAGS -C src/ocaml-output ../../bin/fstar.ocaml
          [ -z "$compileTests"    ] || make $MAKE_FLAGS -C src/ocaml-output ../../bin/tests.exe
          [ -z "$compileCompLib"  ] || make $MAKE_FLAGS -C src/ocaml-output install-compiler-lib
          [ -z "$compileUlib"     ] || { make $MAKE_FLAGS -C ulib/ml && make $MAKE_FLAGS -C ulib; }
        '';
  
        OCAML_VERSION = ocamlPackages.ocaml.version;
        Z3_PATH = lib.getBin z3;
        # Installs binaries and libraries according to [opts] contents
        installPhase = ''
          SITE_LIB="$out/lib/ocaml/$OCAML_VERSION/site-lib"
          copyBin () { cp "bin/$1" $out/bin
                       # OCaml leaves it's full store path in produced binaries
                       # Thus we need to remove any reference to the path of OCaml in the store
                       remove-references-to -t '${ocamlPackages.ocaml}' $out/bin/$1
                       wrapProgram "$out/bin/$1" --prefix PATH ":" "$Z3_PATH/bin"
                     }
          instLib () { mkdir -p "$SITE_LIB"
                       cp -r "bin/$1" "$out/bin/$1"
                       ln -s "$out/bin/$1" "$SITE_LIB/$1"
                     }
          mkdir $out/{,ulib,bin}
          cp -r ./ulib/ $out/
          [ -z "$compileFStar"    ] || copyBin fstar.exe
          [ -z "$compileBytecode" ] || copyBin fstar.ocaml
          [ -z "$compileTests"    ] || copyBin tests.exe
          [ -z "$keepSources"     ] || cp -r ./src/ $out/
          [ -z "$compileUlib"     ] || { instLib fstarlib
                                         instLib fstar-tactics-lib ; }
          [ -z "$compileCompLib"  ] || { instLib fstar-compiler-lib; }

          # remove ocamlbuild artifacts
          find $out -name _build -type d | xargs -I{} rm -rf "{}"

          installShellCompletion --bash .completion/bash/fstar.exe.bash
          installShellCompletion --fish .completion/fish/fstar.exe.fish
          installShellCompletion --zsh --name _fstar.exe .completion/zsh/__fstar.exe
        '';
  
        dontFixup = true;
  
        meta.mainProgram = "fstar.exe";
      });
    in pkg;
    
  # Helper derivation that prepares an F* source tree with an existing F* binary/
  with-existing-fstar = { src, pname, version, existing-fstar, patches ? [ ], }:
    stdenv.mkDerivation {
      inherit src pname patches version;
      EXISTING_FSTAR = existing-fstar;
      nativeBuildInputs = [ z3 which existing-fstar ];
      preBuildPhases = [ "preparePhase" "copyBinPhase" ];
      preparePhase = preBuild { inherit pname version; };
      copyBinPhase = ''
        cd bin
        # Next line is required when building F* before commit [6dbcdc1bce]
        rm fstar-any.sh 2>/dev/null && ln -s "$EXISTING_FSTAR/bin/fstar.exe" fstar-any.sh
        for f in "$EXISTING_FSTAR"/bin/*; do
          file=$(basename -- "$f")
          test -f "$file" && rm "$file"
          ln -s "$f" ./
        done
        cd ..
      '';
      dontFixup = true;
    };
  ml-extraction-of-fstar = opts:
    (with-existing-fstar opts).overrideAttrs (o: {
      buildFlags = [ "ocaml" "-C" "src" ];
      installPhase = "cp -r . $out";
    });
  /* F* tests are twofold:
     - the binary [tests.exe] runs "internal" tests;
     - the folder [tests] holds number of test cases under the shape of F* modules.
     [check-fstar] runs both.

     TODO: the statement above is wrong, the [example] and [ucontrib] folders are also
           part of the F* tests.
  */
  check-fstar = opts:
    (with-existing-fstar opts).overrideAttrs (o: {
      buildPhase = ''
        ./bin/tests.exe
        substituteInPlace tests/machine_integers/Makefile --replace "/bin/echo" "echo"
        for file in ./ulib/gmake/Makefile.tmpl ./ulib/ml/Makefile.include; do
          # [OCAMLPATH] is already correctly set, disable override
          substituteInPlace "$file" --replace "OCAMLPATH=" "IGNOREME="
        done
        make -j$NIX_BUILD_CORES -C tests
      '';
      installPhase = "touch $out";
      nativeBuildInputs = o.nativeBuildInputs ++ ocamlNativeBuildInputs;
      buildInputs = ocamlBuildInputs;
    });
  binary-of-fstar = { src, pname, version, patches ? [ ], existing-fstar ?
      binary-of-ml-snapshot {
        inherit src version;
        pname = "${pname}-bin-of-snapshot";
        opts = {
          keepSources = false;
          compileFStar = true;
          compileBytecode = false;
          compileTests = false;
          compileCompLib = false;
          compileUlib = false;
        };
      }, opts ? defaults }:
        let
          extraction = ml-extraction-of-fstar {
            inherit src existing-fstar patches;
            pname = "${pname}-ml-extraction";
            inherit version;
          };
          bin = binary-of-ml-snapshot {
            inherit pname version opts;
            src = extraction;
          };
        in
          bin.overrideAttrs (old: {
            passthru = (old.passthru or {}) // {
              bootstrap.zero = existing-fstar;
              bootstrap.one = extraction;
              book = book-of-fstar {
                inherit src;
                pname = "${pname}-book";
              };
              tests = check-fstar {
                inherit src;
                pname = "${pname}-tests";
                rev = src.rev;
                existing-fstar = bin;
              };
            };
          });
  book-of-fstar = { src, pname }: stdenv.mkDerivation {
    name = "${pname}-book";
    src = src + "/doc/book";
    buildInputs = [ sphinx python39Packages.sphinx_rtd_theme ];
    installPhase = ''
      mkdir -p "$out"/nix-support
      echo "doc manual $out/book" >> $out/nix-support/hydra-build-products
      mv _build/html $out/book
    '';
  };
in {
  inherit binary-of-fstar ml-extraction-of-fstar binary-of-ml-snapshot check-fstar
    with-existing-fstar ocamlBuildInputs ocamlNativeBuildInputs;
  defaultOptions = defaults;
}
