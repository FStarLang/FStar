#!/usr/bin/env bash

# This script is called from everest-ci/ci script for a weekly build of the FStar Binaries
# If ran separately, the starting directory should be the root directory of FStar.

# Creates a tag, if necessary
. "`dirname $0`/release-pre.sh"

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOST_HOME is the former.
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
cd src/ocaml-output
git clean -ffdx
make -j6 -C ../.. package

diag "*** Unzip and verify the Package  ***"
TIME_STAMP=$(date +%Y%m%d%H%M)
COMMIT=_$(git rev-parse --short HEAD)

mkdir "$FSTAR_HOST_HOME/release"

TYPE="_Windows_x64.zip"
MAJOR_ZIP_FILE=fstar_$CURRENT_VERSION$TYPE
if [[ -f $MAJOR_ZIP_FILE ]]; then
  unzip -o $MAJOR_ZIP_FILE
  BUILD_PACKAGE="$MAJOR_ZIP_FILE"
  cp $MAJOR_ZIP_FILE "$FSTAR_HOST_HOME/release/$BUILD_PACKAGE"
else
  TYPE="_Linux_x86_64.tar.gz"
  MAJOR_TAR_FILE=fstar_$CURRENT_VERSION$TYPE
  if [[ -f $MAJOR_TAR_FILE ]]; then
    tar -x -f $MAJOR_TAR_FILE
    BUILD_PACKAGE="$MAJOR_TAR_FILE"
    cp $MAJOR_TAR_FILE "$FSTAR_HOST_HOME/release/$BUILD_PACKAGE"
  else
    echo -e "* ${RED}FAIL!${NC} src/ocaml-output/make package did not create ${MAJOR_ZIP_FILE} or ${MAJOR_TAR_FILE}"
    exit 1
  fi
fi

diag "*** Test the binary package ***"
cd fstar

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOME is the latter. Most examples will
# anyway redefine and overwrite FSTAR_HOME according to their location
# within the package, *except* one: stringprinter in examples/tactics,
# which needs KaRaMeL, which needs some FSTAR_HOME defined. So we have
# to export it from here.
export FSTAR_HOME="$PWD"

# Copy tests and examples to the tmp directory, since they are no
# longer included in the package. We copy them elsewhere since we
# don't want to rely on relative paths in their Makefiles.
rm -rf /tmp/fstar_examples /tmp/fstar_doc
cp -r $FSTAR_HOST_HOME/examples /tmp/fstar_examples
cp -r $FSTAR_HOST_HOME/doc /tmp/fstar_doc

diag "-- Versions --"
bin/fstar.exe --version
bin/z3 --version

diag "-- Execute examples/hello via OCaml -- should output Hello F*! --"
make -C /tmp/fstar_examples/hello hello | tee HelloOcamlOutput.log
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello - make failed withexit code $?"
  exit 1
elif ! egrep -q 'Hello F\*!' HelloOcamlOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello - 'Hello F*!' was not found in HelloOcamlOutput.log"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello"
fi

diag "-- Rebuilding ulib (to make sure it works) --"
make -j6 dune-bootstrap
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for dune-bootstrap - make returned $?"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for dune-bootstrap"
fi

diag "-- Verify all examples --"
make -j6 -C /tmp/fstar_examples
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for all examples - make returned $?"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for all examples"
fi

# Cleanup
rm -rf /tmp/fstar_examples /tmp/fstar_doc

# From this point on, we should no longer need FSTAR_HOME.
export FSTAR_HOME=


# Push the binary package(s) to the release.
. "$FSTAR_HOST_HOME/.scripts/release-post.sh"

# Manual steps on major releases - use the major version number from make package ... this process creates binary builds and minor version
# 1) Update https://github.com/FStarLang/FStar/blob/master/version.txt
# 2) Create a new branch based on that version
# 3) Document the release
