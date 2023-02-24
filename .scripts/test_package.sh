#!/usr/bin/env bash

set -e
set -o pipefail
set -x

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOST_HOME is the former.
if [[ -z "$FSTAR_HOST_HOME" ]] ; then
  FSTAR_HOST_HOME=$(cd `dirname $0`/.. && pwd)
fi
cd "$FSTAR_HOST_HOME"

# Constants for showing color in output window
RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

diag () {
	echo -e "${YELLOW}$1${NC}"
}

diag "*** Make package (clean build directory first) ***"
git clean -ffdx src/ocaml-output release
make -j6 package
cd src/ocaml-output

if [[ -z "$CURRENT_VERSION" ]] ; then
  CURRENT_VERSION=$(cat fstar/version.txt | sed 's!^v!!' | sed 's!'"\r"'$!!')
fi

diag "*** Unzip and verify the Package  ***"
TIME_STAMP=$(date +%Y%m%d%H%M)
COMMIT=_$(git rev-parse --short HEAD)

mkdir "$FSTAR_HOST_HOME/release"

rm -rf /tmp/fstar_package
mkdir /tmp/fstar_package
cd /tmp/fstar_package
TYPE="_Windows_x64.zip"
BUILD_PACKAGE_FILENAME=fstar_$CURRENT_VERSION$TYPE
BUILD_PACKAGE="$FSTAR_HOST_HOME/src/ocaml-output/$BUILD_PACKAGE_FILENAME"
if [[ -f $BUILD_PACKAGE ]] ; then
  unzip -o $BUILD_PACKAGE
else
  echo -e "src/ocaml-output/make package did not create ${BUILD_PACKAGE_FILENAME}"
  TYPE="_Linux_x86_64.tar.gz"
  BUILD_PACKAGE_FILENAME=fstar_$CURRENT_VERSION$TYPE
  BUILD_PACKAGE="$FSTAR_HOST_HOME/src/ocaml-output/$BUILD_PACKAGE_FILENAME"
  if [[ -f $BUILD_PACKAGE ]] ; then
    tar xf $BUILD_PACKAGE
  else
    echo -e "src/ocaml-output/make package did not create ${BUILD_PACKAGE_FILENAME}"
    echo -e "* ${RED}FAIL!${NC}"
    exit 1
  fi
fi
NEW_BUILD_PACKAGE="$FSTAR_HOST_HOME/release/$BUILD_PACKAGE_FILENAME"
cp "$BUILD_PACKAGE" "$NEW_BUILD_PACKAGE"
BUILD_PACKAGE="$NEW_BUILD_PACKAGE"

diag "*** Test the binary package ***"

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOME is the latter.
cd fstar
export FSTAR_HOME="$PWD"

# Move doc and examples to the tmp directory.
# We move them elsewhere since we
# don't want to rely on relative paths in their Makefiles.
rm -rf /tmp/fstar_examples /tmp/fstar_doc
mv share/fstar/examples /tmp/fstar_examples
mv share/fstar/doc /tmp/fstar_doc

diag "-- Versions --"
bin/fstar.exe --version
bin/z3 --version

diag "-- Verify all examples --"
make -j6 -C /tmp/fstar_examples && make -j6 -C /tmp/fstar_doc/tutorial regressions
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for all examples - make returned $?"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for all examples"
fi

cd $FSTAR_HOST_HOME

# Cleanup
rm -rf /tmp/fstar_examples /tmp/fstar_doc

# From this point on, we should no longer need FSTAR_HOME.
export FSTAR_HOME=
