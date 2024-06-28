{
  batteries,
  buildDunePackage,
  lib,
  memtrace,
  menhir,
  menhirLib,
  ocaml,
  pprint,
  ppx_deriving,
  ppx_deriving_yojson,
  ppxlib,
  process,
  sedlex,
  stdint,
  version,
  yojson,
  zarith,
}:
buildDunePackage {
  pname = "fstar";
  inherit version;

  duneVersion = "3";

  src = lib.sourceByRegex ./.. ["ocaml.*" "version.txt"];

  prePatch = ''
    patchShebangs ocaml/fstar-lib/make_fstar_version.sh
    cd ocaml
  '';

  FSTAR_COMMIT = version;

  nativeBuildInputs = [
    menhir
  ];

  buildInputs = [
    memtrace
  ];

  propagatedBuildInputs = [
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

  enableParallelBuilding = true;
}
