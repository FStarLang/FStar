{
  bash,
  batteries,
  buildDunePackage,
  callPackage,
  installShellFiles,
  lib,
  makeWrapper,
  memtrace,
  menhir,
  menhirLib,
  mtime,
  pprint,
  ppx_deriving,
  ppx_deriving_yojson,
  ppxlib,
  process,
  sedlex,
  stdint,
  version,
  yojson,
  z3,
  zarith,
}:

buildDunePackage {
  pname = "fstar";
  inherit version;

  duneVersion = "3";

  nativeBuildInputs = [
    installShellFiles
    makeWrapper
    menhir
  ];

  buildInputs = [
    batteries
    memtrace
    menhir
    menhirLib
    mtime
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

  prePatch = ''
    patchShebangs .scripts/*.sh
    patchShebangs ulib/ml/app/ints/mk_int_file.sh
  '';

  src = lib.sourceByRegex ./.. [
    "Makefile"
    "src.*"
    "mk.*"
    "stage..*"
    "ulib.*"
    "doc.*"
    "version.txt"
    ".scripts.*" # Mostly here for get_fstar_z3.sh
    "LICENSE.*"
    "README.md"
    "INSTALL.md"
  ];

  buildPhase = ''
    export PATH="${z3}/bin:$PATH"
    make -j$(nproc)
  '';

  installPhase = ''
    PREFIX=$out make install

    for binary in $out/bin/*
    do
      wrapProgram $binary --prefix PATH ":" ${z3}/bin
    done

    cd $out
    installShellCompletion --bash ${../.completion/bash/fstar.exe.bash}
    installShellCompletion --fish ${../.completion/fish/fstar.exe.fish}
    installShellCompletion --zsh --name _fstar.exe ${../.completion/zsh/__fstar.exe}
  '';
}
