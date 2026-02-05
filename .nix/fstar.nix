{ callPackage, installShellFiles, lib, makeWrapper, buildDunePackage, version, z3, bash, python3, gnumake,
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

  nativeBuildInputs = [ installShellFiles makeWrapper menhir python3 gnumake ];

  buildInputs = [
    batteries
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
    "Makefile"
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

  # Use make for the multi-stage build instead of pure dune
  buildPhase = ''
    runHook preBuild
    export PATH="${z3}/bin:$PATH"
    export HOME=$TMPDIR
    make
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out/bin $out/lib/fstar

    # Copy the fstar executable
    cp _build/default/src/stage2/fstar.exe $out/bin/fstar.exe 2>/dev/null || \
      cp _build/default/src/stage2/fstar $out/bin/fstar

    # Copy ulib
    cp -r ulib $out/lib/fstar/

    # Wrap with Z3
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" ${z3}/bin 2>/dev/null || \
      wrapProgram $out/bin/fstar --prefix PATH ":" ${z3}/bin

    # Install shell completions if they exist
    if [ -d .completion ]; then
      installShellCompletion --bash .completion/bash/fstar.exe.bash 2>/dev/null || true
      installShellCompletion --fish .completion/fish/fstar.exe.fish 2>/dev/null || true
      installShellCompletion --zsh --name _fstar.exe .completion/zsh/__fstar.exe 2>/dev/null || true
    fi
    runHook postInstall
  '';
}
