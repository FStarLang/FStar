{ callPackage, fstar-dune, installShellFiles, makeWrapper, stdenv, ulib, version
, z3 }:

stdenv.mkDerivation {
  pname = "fstar";
  inherit version;

  buildInputs = [ installShellFiles makeWrapper ];

  src = ./..;

  buildPhase = "true";

  installPhase = ''
    mkdir $out

    CP="cp -r --no-preserve=mode"
    $CP ${fstar-dune}/* $out
    $CP ${ulib}/* $out

    PREFIX=$out make -C src/ocaml-output install-sides -j $NIX_BUILD_CORES

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
