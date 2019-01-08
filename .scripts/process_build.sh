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

# Make sure we are starting in the right place (F* repository)
if ! [[ -d ulib ]]; then
  echo "This script is intended to be run from the root of the F* repository"
  exit 1
fi

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOST_HOME is the former.
FSTAR_HOST_HOME=$PWD

# Expects to be called from $BN_BINARYSPATH_ROOT
function cp_to_binaries () {
  local file=$1
  echo "--" $FSTAR_HOST_HOME/src/ocaml-output/$file $BN_BINARYSPATH
  cp $FSTAR_HOST_HOME/src/ocaml-output/$file $BN_BINARYSPATH
  git add $BN_BINARYSPATH/$file
}

function cleanup_files () {
  pushd $BN_BINARYSPATH
  local suffix=$1
  local files=*.$suffix
  local file_count=$(ls -1 $files 2>/dev/null | wc -l)
  if (( $file_count > $BN_FILESTOKEEP )); then
    # git rm does not take absolute paths; since there are no subdirectories,
    # use basename
    local file_list=$(ls -t1 $files | xargs -n1 basename | tail -n +$(($BN_FILESTOKEEP+1)))
    git rm $file_list -f
  fi
  popd
}

# Constants for showing color in output window
RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

diag () {
	echo -e "${YELLOW}$1${NC}"
}

CURRENT_VERSION=$(head -n 1 version.txt | tr -d '\r')

diag "*** Clean up log files ***"
if [[ -f src/ocaml-output/fstar/HelloOcamlOutput.log ]]; then
  rm src/ocaml-output/fstar/HelloOcamlOutput.log
fi

diag "*** Make package (clean build directory first) ***"
cd src/ocaml-output
make package

# 'make package' makes the package using the major version from version.txt. This script is a weekly process to make minor versions so use timestamp in file name instead of major version
diag "*** Unzip and verify the Package  ***"
TIME_STAMP=$(date +%Y%m%d%H%M)
COMMIT=_$(git rev-parse --short HEAD)

TYPE="_Windows_x64.zip"
MAJOR_ZIP_FILE=fstar_$CURRENT_VERSION$TYPE
if [[ -f $MAJOR_ZIP_FILE ]]; then
  MINOR_ZIP_FILE=fstar_$TIME_STAMP$COMMIT$TYPE
  cp $MAJOR_ZIP_FILE $MINOR_ZIP_FILE
  unzip -o $MAJOR_ZIP_FILE
else
  TYPE="_Linux_x86_64.tar.gz"
  MAJOR_TAR_FILE=fstar_$CURRENT_VERSION$TYPE
  if [[ -f $MAJOR_TAR_FILE ]]; then
    MINOR_TAR_FILE=fstar_$TIME_STAMP$COMMIT$TYPE
    cp $MAJOR_TAR_FILE $MINOR_TAR_FILE
    tar -x -f $MAJOR_TAR_FILE
  else
    echo -e "* ${RED}FAIL!${NC} src/ocaml-output/make package did not create ${MAJOR_ZIP_FILE} or ${MAJOR_TAR_FILE}"
    exit 1
  fi
fi

diag "*** Make the examples ***"
cd fstar

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOME is the latter. Most examples will
# anyway redefine and overwrite FSTAR_HOME according to their location
# within the package, *except* one: stringprinter in examples/tactics,
# which needs KreMLin, which needs some FSTAR_HOME defined. So we have
# to export it from here.
export FSTAR_HOME="$PWD"

diag "-- Verify hello ocaml -- should output Hello F*! --"
make -C examples/hello ocaml | tee HelloOcamlOutput.log
if [ $? -ne 0 ]; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello ocaml - make failed withexit code $?"
  exit 1
elif ! egrep -q 'Hello F\*!' HelloOcamlOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello ocaml - 'Hello F*!' was not found in HelloOcamlOutput.log"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello ocaml"
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

# Got to this point, so know it passed - copy minor version out
diag "*** Upload the minor version of the package. Will only keep the most recent 4 packages ***"
BN_BINARYSPATH_ROOT=~/binaries
BN_BINARYSPATH=$BN_BINARYSPATH_ROOT/weekly
BN_FILESTOKEEP=4

if [[ ! -d $BN_BINARYSPATH_ROOT ]]; then
  git clone git@github.com:/FStarLang/binaries.git $BN_BINARYSPATH_ROOT
fi

cd $BN_BINARYSPATH_ROOT
git fetch
git checkout master
git reset --hard origin/master

diag "-- copy files and add to Github --"
if [[ -f $FSTAR_HOST_HOME/src/ocaml-output/$MINOR_ZIP_FILE ]]; then
  cp_to_binaries $MINOR_ZIP_FILE
fi
if [[ -f $FSTAR_HOST_HOME/src/ocaml-output/$MINOR_TAR_FILE ]]; then
  cp_to_binaries $MINOR_TAR_FILE
fi

# Now that latest package is added, remove the oldest one because only keeping most recent 4 packages
diag "-- Delete oldest ZIP file if more than 4 exist --"
cleanup_files "zip"
diag "-- Delete oldest TAR file if more than 4 exist --"
cleanup_files "gz"

# Commit and push - adding a new one and removing the oldest - commit with amend to keep history limited
diag "--- now commit it but keep history truncated ... then push --- "
git commit --amend -m "Adding new build package and removing oldest."
git push git@github.com:FStarLang/binaries.git master --force

# Manual steps on major releases - use the major version number from make package ... this process creates binary builds and minor version
# 1) Update https://github.com/FStarLang/FStar/blob/master/version.txt
# 2) Create a new branch based on that version
# 3) Document the release
