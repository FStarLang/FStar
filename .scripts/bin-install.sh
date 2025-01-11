#!/bin/bash

# This is called by the Makefile *after* an installation into the
# prefix, so we add the rest of the files that go into a binary pacakge.

set -eu

if [ $# -ne 1 ]; then
	echo "Usage: $0 <prefix>" >&2
	exit 1
fi

# $1 will usually exist, but mkdir it if not
PREFIX="$(realpath -m "$1")" # -m: leading dirs allowed to not exist

mkdir -p "${PREFIX}"

if ! [ -v FSTAR_PACKAGE_Z3 ] || ! [ "$FSTAR_PACKAGE_Z3" = false ]; then
  .scripts/package_z3.sh "$PREFIX"
fi

# License and extra files. Not there on normal installs, but present in
# package.
cp LICENSE* "$PREFIX"
cp README.md "$PREFIX"
cp INSTALL.md "$PREFIX"
cp version.txt "$PREFIX"
