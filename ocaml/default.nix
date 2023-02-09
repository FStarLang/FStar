{ batteries, buildDunePackage, includeBinaryAnnotations ? false
, installShellFiles, lib, makeWrapper, menhirLib, ocaml, pprint, ppxlib
, ppx_deriving, ppx_deriving_yojson, process, removeReferencesTo, sedlex, stdint
, version, yojson, zarith }:

buildDunePackage {
  pname = "fstar";
  inherit version;

  duneVersion = "3";

  src = lib.sourceByRegex ../. [ "ocaml.*" "version.txt" ];

  prePatch = ''
    cd ocaml
    patchShebangs fstar-lib/make_fstar_version.sh
  '';

  nativeBuildInputs = [ installShellFiles makeWrapper removeReferencesTo ];

  buildInputs = [
    batteries
    menhirLib
    pprint
    ppx_deriving
    ppx_deriving_yojson
    ppxlib
    process
    sedlex
    stdint
    yojson
    zarith
  ];

  postFixup = ''
    # OCaml leaves it's full store path in produced binaries
    # Thus we need to remove every reference to the path of OCaml
    for binary in $out/bin/*
    do
      remove-references-to -t '${ocaml}' $binary
    done
  '' + (if includeBinaryAnnotations then
    ""
  else ''
    # Binary annotations are useful only for nice IDE integration while developping OCaml programs that depend on the F* library
    # Meanwhile, they add a dependency to the OCaml compiler and are thus removed by default
    rm $out/lib/ocaml/${ocaml.version}/site-lib/fstar/lib/*.cmt
  '');
}
