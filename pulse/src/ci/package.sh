#!/usr/bin/env bash

set -e
set -x

cp0=$(which gcp >/dev/null 2>&1 && echo gcp || echo cp)
cp="$cp0 --preserve=mode,timestamps"

# make sure the package has not already been built
cd $(cd `dirname $0` && pwd)
[[ ! -e steel ]]

# download the z3 license file
if ! [[ -f LICENSE-z3.txt ]] ; then
    curl -o LICENSE-z3.txt https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt
fi

# build a F* package
[[ -n "$FSTAR_HOME" ]]
old_FSTAR_HOME="$FSTAR_HOME"
fstar_package_dir=$FSTAR_HOME/src/ocaml-output/fstar
rm -rf "$fstar_package_dir"
Z3_LICENSE=$(pwd)/LICENSE-z3.txt make -C "$FSTAR_HOME" package "$@"

# build Karamel and add it to the package
[[ -n "$KRML_HOME" ]]
make -C "$KRML_HOME" "$@"
$cp -L $KRML_HOME/krml $fstar_package_dir/bin/krml$exe
$cp -r $KRML_HOME/krmllib $fstar_package_dir/
$cp -r $KRML_HOME/include $fstar_package_dir/
$cp -r $KRML_HOME/misc $fstar_package_dir/

# assume current directory is $STEEL_HOME/src/ci
export STEEL_HOME=$(cd ../.. && pwd)

# use the package to build Steel
export FSTAR_HOME="$fstar_package_dir"
OTHERFLAGS='--admit_smt_queries true' make -C "$STEEL_HOME" "$@"
make -C "$STEEL_HOME"/share/steel/examples/pulse lib "$@"
mkdir -p "$old_FSTAR_HOME"/src/.cache.boot
FSTAR_HOME="$old_FSTAR_HOME" make -C "$STEEL_HOME"/pulse2rust "$@"

# install Steel into the package directory
export PREFIX="$FSTAR_HOME"
make -C "$STEEL_HOME" install "$@"
make -C "$STEEL_HOME"/share/steel/examples/pulse install-lib "$@"
mkdir -p "$PREFIX"/pulse2rust
$cp "$STEEL_HOME"/pulse2rust/main.exe "$PREFIX"/pulse2rust/

# create the archive package
mv "$PREFIX" steel
rm -rf steel/share/fstar
if [[ "$OS" = Windows_NT ]] ; then
  zip -r -9 steel.zip steel
else
  tar czf steel.tgz steel
fi
