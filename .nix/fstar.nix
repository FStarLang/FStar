{ callPackage, fstar-dune, fstar-ulib, installShellFiles, lib, makeWrapper
, stdenv, version, z3 }:

stdenv.mkDerivation {
  pname = "fstar";
  inherit version;

  buildInputs = [ installShellFiles makeWrapper ];

  src = lib.sourceByRegex ./.. [
    ".common.mk"
    "doc.*"
    "examples.*"
    "src(/ocaml-output(/Makefile)?)?"
    "ucontrib.*"
  ];

  dontBuild = true;

  installPhase = ''
    mkdir $out

    CP="cp -r --no-preserve=mode"
    $CP ${fstar-dune}/* $out
    $CP ${fstar-ulib}/* $out

    PREFIX=$out make -C src/ocaml-output install-sides

    for binary in $out/bin/*
    do
      chmod +x $binary
      wrapProgram $binary --prefix PATH ":" ${z3}/bin
    done

    cd $out
    installShellCompletion --bash ${../.completion/bash/fstar.exe.bash}
    installShellCompletion --fish ${../.completion/fish/fstar.exe.fish}
    installShellCompletion --zsh --name _fstar.exe ${
      ../.completion/zsh/__fstar.exe
    }
  '';
}
