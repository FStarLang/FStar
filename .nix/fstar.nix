{
  fstar-dune,
  fstar-ulib,
  installShellFiles,
  lib,
  makeWrapper,
  ocamlPackages,
  stdenv,
  removeReferencesTo,
  version,
  z3,
}:
stdenv.mkDerivation {
  pname = "fstar";
  inherit version;

  buildInputs = [
    installShellFiles
    makeWrapper
    removeReferencesTo
  ];

  src = lib.sourceByRegex ./.. [
    ".common.mk"
    "doc.*"
    "examples.*"
    "src(/ocaml-output(/Makefile)?)?"
    "ucontrib.*"
  ];

  inherit (fstar-dune) propagatedBuildInputs;

  dontBuild = true;

  installPhase = ''
    mkdir $out

    CP="cp -r --no-preserve=mode"
    $CP ${fstar-dune}/* $out
    $CP ${fstar-ulib}/* $out

    PREFIX=$out make -C src/ocaml-output install-sides

    chmod +x $out/bin/fstar.exe
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" ${z3}/bin
    remove-references-to -t '${ocamlPackages.ocaml}' $out/bin/fstar.exe

    substituteInPlace $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/fstar/dune-package \
      --replace ${fstar-dune} $out

    installShellCompletion --bash ${../.completion/bash/fstar.exe.bash}
    installShellCompletion --fish ${../.completion/fish/fstar.exe.fish}
    installShellCompletion --zsh --name _fstar.exe ${../.completion/zsh/__fstar.exe}
  '';
}
