{ fstar-dune, lib, stdenv, version, z3 }:

stdenv.mkDerivation {
  pname = "fstar-ulib";
  inherit version;

  src = lib.sourceByRegex ./.. [ "ulib.*" ".common.mk" ];

  postPatch = ''
    mkdir -p bin
    cp ${fstar-dune}/bin/fstar.exe bin
    export PATH="$(pwd)/bin:${z3}/bin:$PATH"
    patchShebangs ulib/install-ulib.sh
    cd ulib
  '';

  enableParallelBuilding = true;

  preInstall = "export PREFIX=$out";
}
