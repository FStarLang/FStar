#!/usr/bin/env bash

set -e
set -x

# build a F* package
[[ -n "$FSTAR_HOME" ]]
fstar_package_dir=$FSTAR_HOME/src/ocaml-output/fstar
rm -rf "$fstar_package_dir"
make -C "$FSTAR_HOME" package "$@"

# assume current directory is $STEEL_HOME/src/ci
export STEEL_HOME=$(cd `dirname $0`/../.. && pwd)

# use the package to build Steel
export FSTAR_HOME="$fstar_package_dir"
OTHERFLAGS='--admit_smt_queries true' make -C "$STEEL_HOME" "$@"
make -C "$STEEL_HOME"/share/steel/examples/pulse lib "$@"

# install Steel into the package directory
export PREFIX="$FSTAR_HOME"
make -C "$STEEL_HOME" install "$@"
make -C "$STEEL_HOME"/share/steel/examples/pulse install-lib "$@"

# create the archive package
cd `dirname $0`
[[ ! -e steel ]]
mv "$PREFIX" steel
rm -rf steel/share/fstar
if [[ "$OS" = Windows_NT ]] ; then
  zip -r -9 steel.zip steel
else
  tar czf steel.tgz steel
fi
