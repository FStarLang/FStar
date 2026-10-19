{ fetchFromGitHub, z3 }:

z3.overrideAttrs (old: rec {
  version = "5.3.0";
  src = fetchFromGitHub {
    owner = "z3prover";
    repo = "z3";
    rev = "z3-${version}";
    sha256 = "sha256-K0KTI8ZpvvYCF9ITxVTbdtqlalFFjtYcyog/Sy1kRV8=";
  };
})
