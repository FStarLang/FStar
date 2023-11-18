#!/usr/bin/env bash
set -e
set -x

# Switch to the directory of this script
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if [[ -z "$CC" ]] ; then
   CC=cc
fi

dune build
if ! [[ -e appendix_a.json ]] ; then
    wget https://raw.githubusercontent.com/cbor/test-vectors/master/appendix_a.json
fi
_build/default/GenCBORTest.exe appendix_a.json > CBORTest.c
"$CC" -Werror -I $KRML_HOME/include -I $KRML_HOME/krmllib/dist/generic -I ../_output/ -c -o CBORTest.o CBORTest.c
"$CC" -o CBORTest.exe CBORTest.o ../_output/CBOR_Pulse.o ../dist/CBOR.o
./CBORTest.exe
