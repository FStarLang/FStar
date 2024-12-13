{ fetchFromGitHub, z3 }:

z3.overrideAttrs (old: rec {
  version = "4.8.5";
  src = fetchFromGitHub {
    owner = "z3prover";
    repo = "z3";
    rev = "Z3-${version}";
    sha256 = "ytG5O9HczbIVJAiIGZfUXC/MuYH7d7yLApaeTRlKXoc=";
  };
})
