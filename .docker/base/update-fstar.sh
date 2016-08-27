#!/bin/sh
cd ~/FStar
git pull
make ocaml -C src
make -C src/ocaml-output