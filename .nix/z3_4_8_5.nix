{
  autoPatchelfHook,
  fetchzip,
  fixDarwinDylibNames,
  lib,
  stdenv,
}:

let
  platform = if stdenv.isDarwin then "osx-10.14.2" else "ubuntu-16.04";
  hash =
    if stdenv.isDarwin then
      "sha256-Bz5Bsg+0Bsshne/VN0dGeesOibI6yUfh3s+wiDNhwHM="
    else
      "sha256-dgG4L77Y3+g10tO2pygmJ+XeGOhJrzuDxIzuZyJvMf0=";

in
stdenv.mkDerivation rec {
  pname = "z3";
  version = "4.8.5";

  src = fetchzip {
    inherit hash;
    url = "https://github.com/Z3Prover/z3/releases/download/Z3-${version}/z3-${version}-x64-${platform}.zip";
  };

  nativeBuildInputs =
    lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ]
    ++ lib.optionals stdenv.hostPlatform.isDarwin [ fixDarwinDylibNames ];

  buildInputs = [ stdenv.cc.cc.lib ];

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
    platforms = platforms.unix;
  };
}
