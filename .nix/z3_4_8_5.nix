 { stdenv, lib
, fetchzip
, autoPatchelfHook
}:

stdenv.mkDerivation rec {
  pname = "z3";
  version = "4.8.5";

  src = fetchzip {
    url = "https://github.com/Z3Prover/z3/releases/download/Z3-${version}/z3-${version}-x64-ubuntu-16.04.zip";
    hash = "sha256-dgG4L77Y3+g10tO2pygmJ+XeGOhJrzuDxIzuZyJvMf0=";
  };

  nativeBuildInputs = [
    autoPatchelfHook
  ];

  buildInputs = [
    stdenv.cc.cc.lib
  ];

  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r bin $out
    runHook postInstall
  '';

  meta = with lib; {
    description = "High-performance theorem prover and SMT solver";
    mainProgram = "z3";
    homepage = "https://github.com/Z3Prover/z3";
    platforms = platforms.linux;
  };
}
