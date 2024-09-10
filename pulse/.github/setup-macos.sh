#!/usr/bin/env bash

# Install OCaml and other GNU build tools
# coreutils: for the `install` command used in install-ulib.sh
export OPAMYES=1
brew install opam bash gnu-getopt coreutils gnu-sed make
opam init --compiler=4.14.0
eval $(opam env)

# Install Z3 and the opam package dependencies
# NOTE: on Mac OS, we cannot do `opam install --deps-only fstar.opam`
# because the z3 opam package is broken
# So, we rely on Everest instead.
# We assume an everest checkout in the same directory as this script.
# The GitHub Actions workflow should take care of cloning everest.
cwd=$(cd $(dirname $0); pwd -P)
cd $cwd/everest
./everest --yes z3 opam
