#!/usr/bin/env bash
set -e
set -x

# Switch to the directory of this script
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

dune build
if ! [[ -e appendix_a.json ]] ; then
    wget https://raw.githubusercontent.com/cbor/test-vectors/master/appendix_a.json
fi
_build/default/GenCBORTest.exe appendix_a.json > ../CBORTest.c
