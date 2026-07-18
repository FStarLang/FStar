{ fetchFromGitHub, z3 }:

z3.overrideAttrs (old: rec {
  version = "4.13.3";
  src = fetchFromGitHub {
    owner = "z3prover";
    repo = "z3";
    rev = "z3-${version}";
    sha256 = "sha256-odwalnF00SI+sJGHdIIv4KapFcfVVKiQ22HFhXYtSvA=";
  };
})
