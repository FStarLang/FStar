{ fstar-dune, lib, stdenv, version, z3 }:

stdenv.mkDerivation {
  pname = "fstar-ulib";
  inherit version;

  src = lib.cleanSourceWith {
    src = ./..;
    filter = path: _:
      let relPath = lib.removePrefix (toString ./.. + "/") (toString path);
      in lib.hasPrefix "ulib" relPath || lib.hasSuffix ".common.mk" relPath;
  };

  postPatch = ''
    mkdir -p bin
    cp ${fstar-dune}/bin/fstar.exe bin
    export PATH="$(pwd)/bin:${z3}/bin:$PATH"
    patchShebangs ulib/install-ulib.sh
  '';

  buildPhase = "make -C ulib -j $NIX_BUILD_CORES";

  installPhase = ''
    mkdir -p $out
    PREFIX=$out make -C ulib install
  '';
}
