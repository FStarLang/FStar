#!/bin/bash

PREFIX="$(realpath "$1")"
D="$(dirname "$0")"

mkdir -p "$PREFIX"/lib/fstar

TMP=$(mktemp -d)
$D/get_fstar_z3.sh --full "$TMP"

pushd "$TMP"

inst1 () {
	TGT="$PREFIX/lib/fstar/$1"
	mkdir -p "$(dirname "$TGT")"
	cp "$1" "$TGT"
}

inst1 ./z3-4.8.5/bin/z3
inst1 ./z3-4.8.5/LICENSE.txt
inst1 ./z3-4.13.3/bin/z3
inst1 ./z3-4.13.3/LICENSE.txt

popd

rm -r "$TMP"
