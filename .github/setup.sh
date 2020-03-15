#!/usr/bin/env bash

# This should be Fstar/.github/
cwd=$(cd $(dirname $0); pwd -P)

# The everest checkout should be next to FStar
cd $cwd/../../everest
export OPAMYES=1
brew install opam bash gnu-getopt
opam init
opam switch create 4.05.0
eval $(opam env)
./everest --yes z3 opam
