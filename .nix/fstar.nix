{ callPackage, installShellFiles, lib, makeWrapper, buildDunePackage, version, z3, bash, python3,
    batteries,
    menhir,
    menhirLib,
    pprint,
    ppx_deriving,
    ppx_deriving_yojson,
    ppxlib,
    process,
    sedlex,
    stdint,
    yojson,
    zarith,
    memtrace,
    mtime } :

buildDunePackage {
  pname = "fstar";
  inherit version;

  duneVersion = "3";

  nativeBuildInputs = [ installShellFiles makeWrapper menhir python3 ];

  buildInputs = [
    batteries
    menhir
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
    memtrace
    mtime
  ];

  enableParallelBuilding = true;

  prePatch = ''
    patchShebangs .scripts/*.sh
    patchShebangs .scripts/*.py
    patchShebangs ulib/ml/app/ints/mk_int_file.sh
  '';

  src = lib.sourceByRegex ./.. [
    "dune"
    "dune-project"
    "dune-workspace"
    "fstar.opam"
    "package.json"
    "packaging.*"
    "src.*"
    "stage0.*"
    "ulib.*"
    "version.txt"
    ".scripts.*"
    "LICENSE.*"
    "README.md"
    "INSTALL.md"
  ];

  # Build using dune directly (multi-stage build)
  buildPhase = ''
    export PATH="${z3}/bin:$PATH"
    
    # Stage 0: Build bootstrap compiler from OCaml snapshot
    dune build @stage0
    
    # Extract: Generate stage1 ML files from F* sources
    dune build @extract-stage1
    
    # Stage 1: Build stage1 compiler library
    dune build @stage1
    
    # Stage 2: Build final compiler with plugins
    dune build @stage2
  '';

  installPhase = ''
    mkdir -p $out/bin $out/lib/fstar

    # Copy the fstar executable
    cp _build/default/src/stage2/fstar.exe $out/bin/fstar.exe

    # Copy ulib
    cp -r ulib $out/lib/fstar/

    # Wrap with Z3
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" ${z3}/bin

    # Install shell completions
    installShellCompletion --bash ${../.completion/bash/fstar.exe.bash}
    installShellCompletion --fish ${../.completion/fish/fstar.exe.fish}
    installShellCompletion --zsh --name _fstar.exe ${
      ../.completion/zsh/__fstar.exe
    }
  '';
}
