#!/bin/bash

eval $(opam config env)
export Z3=z3-4.4.1-x64-ubuntu-14.04;
export PATH=/home/travis/build/FStarLang/FStar/$Z3/bin:/home/travis/build/FStarLang/FStar/bin:$PATH;

echo -e "\e[31m=== Some info about the environment ===\e[0m"
ocamlfind ocamlopt -config

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo /etc/init.d/postgresql stop;
  for d in mysql ; do
    sudo rm -rf /var/lib/$d
    sudo mv /var/ramfs/$d /var/lib/
    sudo ln -s /var/lib/$d /var/ramfs/$d
  done
  free -h;
fi

echo -e "\e[31m=== Bootstrap cycle ===\e[0m"
make -C src
make -C src ocaml
make -C src/ocaml-output

echo -e "\e[31m=== Running tests ===\e[0m"
make -C examples/unit-tests
if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  make -C src regressions
else
  make -C src regressions OTHERFLAGS=--lax
fi
