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
pushd "$FSTAR_HOST_HOME"

# Constants for showing color in output window
RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

diag () {
	echo -e "${YELLOW}$1${NC}"
}

diag "*** Check that the package was created  ***"
if [[ -z $OS ]] ; then
    OS=$(uname)
fi
if echo $OS | grep -i '^cygwin' ; then
    OS=Windows_NT
fi
if [[ $OS = Windows_NT ]] ; then
    ext=.zip
else
    ext=.tar.gz
fi
BUILD_PACKAGE="$FSTAR_HOST_HOME/src/ocaml-output/fstar$ext"
if ! [[ -f $BUILD_PACKAGE ]] ; then
  echo -e "src/ocaml-output/make package did not create ${BUILD_PACKAGE_FILENAME}"
  echo -e "* ${RED}FAIL!${NC}"
  exit 1
fi

diag "*** Unzip the binary package ***"
rm -rf /tmp/fstar_package
mkdir /tmp/fstar_package
popd
pushd /tmp/fstar_package
if [[ $ext = .zip ]] ; then
    unzip -o $BUILD_PACKAGE
else
    tar xf $BUILD_PACKAGE
fi
pushd fstar

diag "-- Versions --"
bin/fstar.exe --version
bin/z3 --version

diag "*** Test the binary package"
# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOME is the latter.
export FSTAR_HOME="$PWD"

# Move doc and examples to the tmp directory.
# We move them elsewhere since we
# don't want to rely on relative paths in their Makefiles.
rm -rf /tmp/fstar_examples /tmp/fstar_doc
mv share/fstar/examples /tmp/fstar_examples
mv share/fstar/doc /tmp/fstar_doc

diag "-- Verify all examples --"
make -j6 -C /tmp/fstar_examples && make -j6 -C /tmp/fstar_doc/tutorial regressions
if [ $? -ne 0 ]; then
    echo -e "* ${RED}FAIL!${NC} for all examples - make returned $?"
    exit 1
else
    echo -e "* ${GREEN}PASSED!${NC} for all examples"
fi

popd
popd
pushd $FSTAR_HOST_HOME

# Cleanup
rm -rf /tmp/fstar_examples /tmp/fstar_doc

# From this point on, we should no longer need FSTAR_HOME.
export FSTAR_HOME=
popd
