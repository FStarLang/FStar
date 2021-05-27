#!/usr/bin/env bash

# This script is called from everest-ci/ci script for a weekly build of the FStar Binaries
# If ran separately, the starting directory should be the root directory of FStar.

# Sorry, everyone
if (( ${BASH_VERSION%%.*} < 4 )); then
  echo "This script requires Bash >= 4. On OSX, try: brew install bash"
  exit 1
fi

# Any error is fatal.
set -e
set -o pipefail

set -x

git_org=tahina-pro
git_remote=tahina-pro

# Check if the user has provided a GitHub authentication token
[[ -n $SATS_TOKEN ]]

# Switch to the F* directory (the parent of this script's directory)
cd `dirname $0`/..

# Make sure we are starting in the right place (F* repository)
if ! [[ -d ulib ]]; then
  echo "This script is intended to be run from the root of the F* repository"
  exit 1
fi

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOST_HOME is the former.
FSTAR_HOST_HOME=$PWD

# Constants for showing color in output window
RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

diag () {
	echo -e "${YELLOW}$1${NC}"
}

diag "test if the working copy is clean"
git diff --staged --exit-code
git diff --exit-code

# This script will not create a new tag. To this end, you should use
# release-linux.sh, which will create the release tag (currently only
# on Linux)

diag "there must be a tag to this version, let that tag override version.txt"
this_commit=$(git rev-parse HEAD)
my_tag=$(git describe --exact-match)
[[ $(echo $my_tag | wc -w) -eq 1 ]]
CURRENT_VERSION=$(echo $my_tag | sed 's!^v!!')
echo $CURRENT_VERSION > version.txt

diag "*** Make package (clean build directory first) ***"
cd src/ocaml-output
git clean -ffdx
make -j6 -C ../.. package

diag "*** Unzip and verify the Package  ***"
TIME_STAMP=$(date +%Y%m%d%H%M)
COMMIT=_$(git rev-parse --short HEAD)

TYPE="_Windows_x64.zip"
MAJOR_ZIP_FILE=fstar_$CURRENT_VERSION$TYPE
if [[ -f $MAJOR_ZIP_FILE ]]; then
  unzip -o $MAJOR_ZIP_FILE
  BINARY_PACKAGE="$MAJOR_ZIP_FILE"
else
  TYPE="_Linux_x86_64.tar.gz"
  MAJOR_TAR_FILE=fstar_$CURRENT_VERSION$TYPE
  if [[ -f $MAJOR_TAR_FILE ]]; then
    tar -x -f $MAJOR_TAR_FILE
    BINARY_PACKAGE="$MAJOR_TAR_FILE"
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
# which needs KreMLin, which needs some FSTAR_HOME defined. So we have
# to export it from here.
export FSTAR_HOME="$PWD"

diag "-- Versions --"
bin/fstar.exe --version
bin/z3 --version

diag "-- Verify micro benchmarks --"
make -C tests/micro-benchmarks
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for micro benchmarks - make returned $?"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for micro benchmarks"
fi

diag "-- Execute examples/hello via OCaml -- should output Hello F*! --"
make -C examples/hello hello | tee HelloOcamlOutput.log
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello - make failed withexit code $?"
  exit 1
elif ! egrep -q 'Hello F\*!' HelloOcamlOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello - 'Hello F*!' was not found in HelloOcamlOutput.log"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello"
fi

diag "-- Rebuilding ulib/ml (to make sure it works) --"
make -C ulib rebuild
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for install-fstarlib - make returned $?"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for install-fstarlib"
fi

diag "-- Verify all examples --"
make -j6 -C examples
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for all examples - make returned $?"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for all examples"
fi

# From this point on, we should no longer need FSTAR_HOME.
export FSTAR_HOME=

# Push the binary package(s) to the release.

pushd $FSTAR_HOST_HOME/src/ocaml-output
mkdir release
mv $BINARY_PACKAGE release
docker build -t fstar-release \
       --build-arg SATS_FILE=$BINARY_PACKAGE \
       --build-arg SATS_TAG=$my_tag \
       --build-arg SATS_COMMITISH=$this_commit \
       --build-arg SATS_TOKEN=$SATS_TOKEN \
       --build-arg SATS_SLUG=$git_org/FStar \
       -f "$FSTAR_HOST_HOME/.docker/release.Dockerfile" \
       release
docker image rm -f fstar-release
rm -rf release
popd

# Manual steps on major releases - use the major version number from make package ... this process creates binary builds and minor version
# 1) Update https://github.com/FStarLang/FStar/blob/master/version.txt
# 2) Create a new branch based on that version
# 3) Document the release
