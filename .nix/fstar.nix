{ callPackage, fstar-dune, installShellFiles, makeWrapper, stdenv, ulib, version
, z3 }:

stdenv.mkDerivation {
  pname = "fstar";
  inherit version;

  dontUnpack = true;

  buildInputs = [ installShellFiles makeWrapper ];

  installPhase = ''
    mkdir $out
    cd $out

    CP="cp -r --no-preserve=mode"
    $CP ${fstar-dune}/* .
    $CP ${ulib}/* .

    # FIXME: Why not use `make -C src/ocaml-output install-sides` ?
    # (after moving the ulib install command back to `install`)
    mkdir -p share/fstar/doc
    $CP ${../examples} share/fstar/examples
    $CP ${../ucontrib} share/fstar/contrib
    $CP ${../doc/Makefile.include} share/fstar/doc/Makefile.include
    $CP ${../doc/tutorial} share/fstar/doc/tutorial

    for binary in $out/bin/*
    do
      chmod +x $binary
      wrapProgram $binary --prefix PATH ":" ${z3}/bin
    done

    installShellCompletion --bash ${../.completion/bash/fstar.exe.bash}
    installShellCompletion --fish ${../.completion/fish/fstar.exe.fish}
    installShellCompletion --zsh --name _fstar.exe ${
      ../.completion/zsh/__fstar.exe
    }
  '';
}
