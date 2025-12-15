#!/bin/bash

PREFIX="$1"
mkdir -p "$PREFIX"
PREFIX="$(realpath "$PREFIX")"

D="$(dirname "$0")"

mkdir -p "$PREFIX"/lib/fstar

TMP=$(mktemp -d)
$D/get_fstar_z3.sh --full "$TMP"

pushd "$TMP" > /dev/null

inst1 () {
	TGT="$PREFIX/lib/fstar/$1"
	mkdir -p "$(dirname "$TGT")"
	cp "$1" "$TGT"
}

for dir in z3-4.8.5 z3-4.13.3 z3-4.15.3; do
  inst1 ./$dir/bin/z3
  inst1 ./$dir/LICENSE.txt
  for dll in ./$dir/bin/*dll; do
    # Needed for Windows packages.
    inst1 "$dll"
  done
done

popd > /dev/null

rm -r "$TMP"
