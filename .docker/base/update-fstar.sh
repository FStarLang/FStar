#!/bin/sh
cd ~/FStar
git clean -fdx .
git pull
make -C src/ocaml-output
OTHERFLAGS='--admit_smt_queries true' make -C ulib #build .checked files
