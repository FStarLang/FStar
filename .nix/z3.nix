{ stdenv, callPackage, z3, python310 }:

let
  z3_python310 = z3.override { python = python310; };
  z3_4_8_5 = callPackage (import ./z3_4_8_5.nix) { };
  z3_4_13_3 = callPackage (import ./z3_4_13_3.nix) { z3 = z3_python310; };
in
stdenv.mkDerivation {
  pname = "fstar-z3";
  version = "1";

  dontUnpack = true;

  buildPhase = ''
    mkdir -p $out/bin
    ln -s ${z3_4_8_5}/bin/z3 $out/bin/z3-4.8.5
    ln -s ${z3_4_13_3}/bin/z3 $out/bin/z3-4.13.3
  '';
}
