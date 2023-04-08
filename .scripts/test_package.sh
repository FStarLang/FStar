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

if [[ -z "$CURRENT_VERSION" ]] ; then
  CURRENT_VERSION=$(cat fstar/version.txt | sed 's!^v!!' | sed 's!'"\r"'$!!')
fi

diag "*** Make package (clean build directory first) ***"
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
TYPE="_${OS}_$(uname -m)"
PACKAGE_NAME=fstar_$CURRENT_VERSION$TYPE
BUILD_PACKAGE_FILENAME=$PACKAGE_NAME$ext
BUILD_PACKAGE="$FSTAR_HOST_HOME/src/ocaml-output/$BUILD_PACKAGE_FILENAME"
rm -rf "$BUILD_PACKAGE" src/ocaml-output/fstar
PACKAGE_NAME=$PACKAGE_NAME make -j6 package

diag "*** Check that the package was created  ***"
if ! [[ -f $BUILD_PACKAGE ]] ; then
  echo -e "src/ocaml-output/make package did not create ${BUILD_PACKAGE_FILENAME}"
  echo -e "* ${RED}FAIL!${NC}"
  exit 1
fi

diag "*** Unzip the binary package ***"
rm -rf /tmp/fstar_package
mkdir /tmp/fstar_package
cd /tmp/fstar_package
if [[ $ext = .zip ]] ; then
    unzip -o $BUILD_PACKAGE
else
    tar xf $BUILD_PACKAGE
fi
cd fstar

diag "-- Versions --"
bin/fstar.exe --version
bin/z3 --version

if [[ -z "$FSTAR_SKIP_PACKAGE_TEST" ]] ; then

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

fi

cd $FSTAR_HOST_HOME

# Cleanup
rm -rf /tmp/fstar_examples /tmp/fstar_doc src/ocaml-output/fstar

# From this point on, we should no longer need FSTAR_HOME.
export FSTAR_HOME=
