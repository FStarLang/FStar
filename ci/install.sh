#!/bin/bash

set -e

if [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
  brew install ocaml opam z3 gmp gnu-sed findutils;
fi
if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo apt-get install --yes libssl-dev opam libgmp-dev libsqlite3-dev g++-5 gcc-5;
  sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 200;
  sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 200;
fi

export OPAMYES=true
opam init
eval $(opam config env)
# Our Ubuntu build boxes come with an old version of OCaml, so start with an
# upgrade. The OSX boxes use brew, which is up-to-date.
if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  opam switch 4.02.3
  eval $(opam config env)
fi
opam install batteries sqlite3 fileutils stdint zarith

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  export Z3=z3-4.4.1-x64-ubuntu-14.04;
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/$Z3.zip;
  unzip $Z3.zip;
  export PATH=/home/travis/build/FStarLang/FStar/$Z3/bin:/home/travis/build/FStarLang/FStar/bin:$PATH;
fi

ocamlfind ocamlopt -config
