{ stdenv, callPackage }:

let
  z3_4_8_5 = callPackage (import ./z3_4_8_5.nix) { };
  z3_4_13_3 = callPackage (import ./z3_4_13_3.nix) { };
  z3_4_15_3 = callPackage (import ./z3_4_15_3.nix) { };
in
stdenv.mkDerivation {
  pname = "fstar-z3";
  version = "1";

  dontUnpack = true;

  buildPhase = ''
    mkdir -p $out/bin
    ln -s ${z3_4_8_5}/bin/z3 $out/bin/z3-4.8.5
    ln -s ${z3_4_13_3}/bin/z3 $out/bin/z3-4.13.3
    ln -s ${z3_4_15_3}/bin/z3 $out/bin/z3-4.15.3
  '';
}
