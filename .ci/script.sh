#!/usr/bin/env bash

set -e

eval $(opam config env)
export Z3=z3-4.4.1-x64-ubuntu-14.04;
export PATH=/home/travis/build/FStarLang/FStar/$Z3/bin:/home/travis/build/FStarLang/FStar/bin:$PATH;

echo -e "\e[31m=== Some info about the environment ===\e[0m"
ocamlfind ocamlopt -config

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo /etc/init.d/postgresql stop;
  for d in postgresql ; do
    sudo rm -rf /var/lib/$d
    sudo mv /var/ramfs/$d /var/lib/
    sudo ln -s /var/lib/$d /var/ramfs/$d
  done
  free -h;
fi

.ci/corecryptotest_reduce_keysize.sh
make -C src test utest OTHERFLAGS=--lax
make -C examples/unit-tests
