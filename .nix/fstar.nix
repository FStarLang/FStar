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
  num,
  ocamlLibraryPath,
  pprint,
  ppx_deriving,
  ppx_deriving_yojson,
  ppxlib,
  process,
  python3,
  sedlex,
  stdint,
  util-linux,
  version,
  which,
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
    python3
    util-linux
    which
  ];

  buildInputs = [
    batteries
    memtrace
    menhir
    menhirLib
    mtime
    num
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
    "LICENSE.*"
    "README.md"
    "INSTALL.md"
    # Mostly here for get_fstar_z3.sh
    ".scripts.*"
    # Required for check phase
    "bare-tests.*"
    "bin.*"
    "contrib.*"
    "examples.*"
    "fsharp.*"
    "tests.*"
  ];

  # Disable dune cache to avoid sandbox permission warnings
  DUNE_CACHE = "disabled";

  buildPhase = ''
    export PATH="${z3}/bin:$PATH"
    make -j$(nproc)
  '';

  doCheck = false;

  # F# tests are not run as they require .NET 6 which is EOL
  # (nixpkgs has .NET 8 and global.json doesn't allow major version jumps)
  checkPhase = ''
    export PATH="${z3}/bin:$PATH"
    export CAML_LD_LIBRARY_PATH="${ocamlLibraryPath}"
    make test stage3-diff test-2-bare stage2-unit-tests
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
