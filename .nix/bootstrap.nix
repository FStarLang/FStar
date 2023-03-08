{ fstar, fstar-dune, fstar-ocaml-snapshot, fstar-ulib, stdenv }:

let
  ocaml-src = stdenv.mkDerivation {
    name = "src";
    src = fstar-ocaml-snapshot;
    dontBuild = true;
    installPhase = ''
      mkdir -p $out/ocaml
      mv ./* $out/ocaml
      cp ${../version.txt} $out/version.txt
    '';
  };
  fstar-dune-bootstrap = fstar-dune.overrideAttrs (_: {
    pname = "fstar-bootstrap-dune";
    src = ocaml-src;
  });
  fstar-ulib-bootstrap = (fstar-ulib.override
    (_: { fstar-dune = fstar-dune-bootstrap; })).overrideAttrs
    (_: { pname = "fstar-bootstrap-ulib"; });

in (fstar.override (_: {
  fstar-dune = fstar-dune-bootstrap;
  fstar-ulib = fstar-ulib-bootstrap;
})).overrideAttrs (_: { pname = "fstar-bootstrap"; })
