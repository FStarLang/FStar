{ fetchFromGitHub, z3 }:

z3.overrideAttrs (old: rec {
  version = "4.15.3";
  src = fetchFromGitHub {
    owner = "z3prover";
    repo = "z3";
    rev = "z3-${version}";
    sha256 = "sha256-Lw037Z0t0ySxkgMXkbjNW5CB4QQLRrrSEBsLJqiomZ4=";
  };
})
