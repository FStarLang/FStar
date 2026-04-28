{ fetchFromGitHub, z3 }:

z3.overrideAttrs (old: rec {
  version = "4.16.0";
  src = fetchFromGitHub {
    owner = "z3prover";
    repo = "z3";
    rev = "z3-${version}";
    sha256 = "sha256-DnhX3kxggnFmyYwXEPBsBA1rh4oor1oIJR5TMJk/jvc=";
  };
})
