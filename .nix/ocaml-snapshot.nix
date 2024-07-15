{
  fstar,
  lib,
  ocamlPackages,
  stdenv,
  version,
}:
stdenv.mkDerivation {
  pname = "fstar-ocaml-snapshot";
  inherit version;

  src = lib.cleanSourceWith {
    src = ./..;
    filter =
      path: _:
      let
        relPath = lib.removePrefix (toString ./.. + "/") (toString path);
      in
      lib.any (lib.flip lib.hasPrefix relPath) [
        "src"
        "ulib"
      ]
      || (
        lib.hasPrefix "ocaml" relPath
        && !(lib.hasInfix "/generated/" relPath)
        && !(lib.hasInfix "/dynamic/" relPath)
      )
      || lib.hasSuffix ".common.mk" relPath;
  };

  postPatch = ''
    mkdir -p bin
    cp ${fstar}/bin/fstar.exe bin
    cd src/ocaml-output
  '';

  nativeBuildInputs = with ocamlPackages; [
    ocaml
    menhir
  ];

  installPhase = "mv ../../ocaml $out";

  enableParallelBuilding = true;
}
