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

# Expects to be called from $BN_BINARYSPATH_ROOT
function cp_to_binaries () {
  local file=$1
  echo "--" $ORIG_PWD/src/ocaml-output/$file $BN_BINARYSPATH
  cp $ORIG_PWD/src/ocaml-output/$file $BN_BINARYSPATH
  git add $BN_BINARYSPATH/$file
}

function cleanup_files () {
  local suffix=$1
  local files=$BN_BINARYSPATH/*.$suffix
  local file_count=$(ls -1 $files 2>/dev/null | wc -l)
  if (( $file_count > $BN_FILESTOKEEP )); then
    # Windows git rm just needs the file name and fails if give path so just get file name
    local file_list=$(ls -t1 $files | xargs -n1 basename | tail -n +$(($BN_FILESTOKEEP+1)))
    git rm ${file_list} -f
#+++    for f in $file_list; do
#+++      git rm $f -f
#+++    done
  fi
}

BUILD_DIR=$(pwd)
if [[ -f ~/.bash_profile ]]; then
  source ~/.bash_profile
fi
cd "$BUILD_DIR"

# Constants for showing color in output window
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

CURRENT_VERSION=$(head -n 1 version.txt)

echo "*** Clean up log files ***"
if [[ -f src/ocaml-output/fstar/MicroBenchMarkOutput.log ]]; then
  rm src/ocaml-output/fstar/MicroBenchMarkOutput.log
fi
if [[ -f src/ocaml-output/fstar/HelloOcamlOutput.log ]]; then
  rm src/ocaml-output/fstar/HelloOcamlOutput.log
fi
if [[ -f src/ocaml-output/fstar/HelloFStarOutput.log ]]; then
  rm src/ocaml-output/fstar/HelloFStarOutput.log
fi
if [[ -f src/ocaml-output/fstar/AllExamples.log ]]; then
  rm src/ocaml-output/fstar/AllExamples.log
fi

# Need this to get back after unzip things
ORIG_PWD=$PWD

echo "*** Make package ***"
cd src/ocaml-output
make package

# 'make package' makes the package using the major version from version.txt. This script is a weekly process to make minor versions so use timestamp in file name instead of major version
echo "*** Unzip and verify the Package  ***"
TIME_STAMP=$(date +%s)

TYPE="_Windows_x64.zip"
MAJOR_ZIP_FILE=fstar_$CURRENT_VERSION$TYPE
if [[ -f $MAJOR_ZIP_FILE ]]; then
  MINOR_ZIP_FILE=fstar_$TIME_STAMP$TYPE
  cp $MAJOR_ZIP_FILE $MINOR_ZIP_FILE
  unzip -o $MAJOR_ZIP_FILE
else
  TYPE="_Linux_x86_64.tar.gz"
  MAJOR_TAR_FILE=fstar_$CURRENT_VERSION$TYPE
  if [[ -f $MAJOR_TAR_FILE ]]; then
    MINOR_TAR_FILE=fstar_$TIME_STAMP$TYPE
    cp $MAJOR_TAR_FILE $MINOR_TAR_FILE
    tar -x -f $MAJOR_TAR_FILE
  else
    echo -e "* ${RED}FAIL!${NC} src/ocaml-output/make package did not create ${MAJOR_ZIP_FILE} or ${MAJOR_TAR_FILE}"
    exit 1
  fi
fi

echo "*** Make the examples ***"
cd fstar
make -C examples/micro-benchmarks > MicroBenchMarkOutput.log
make -C examples/hello ocaml > HelloOcamlOutput.log
make -C examples/hello fs > HelloFStarOutput.log
make -j6 -C examples > AllExamples.log

echo "*** Verify the examples ***"
echo "-- Verify Micro-benchmarks -- should output 'Success:' *"
if ! egrep 'Success:' MicroBenchMarkOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/micro-benchmarks - Success: was not found in MicroBenchMarkOutput.log"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/micro-benchmarks"
fi

echo "-- Verify hello ocaml -- should output Hello F*! *"
if ! egrep 'F*!' HelloFStarOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello ocaml - F*! was not found in HelloOcamlOutput.log"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello ocaml"
fi

echo "-- Verify hello fs -- should output Hello F*!"
if ! egrep 'F*!' HelloFStarOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello fs - F*! was not found in HelloFStarOutput.log"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello fs"
fi

echo "-- Verify all examples -- Look for Success:"
if ! egrep 'Success:' AllExamples.log; then
  echo -e "* ${RED}FAIL!${NC} for all examples - Success: was not found in AllExamples.log"
  exit 1
else
  echo -e "* ${GREEN}PASSED!${NC} for all examples"
fi

# Got to this point, so know it passed - copy minor version out
echo "*** Upload the minor version of the package. Will only keep the most recent 4 packages ***"
cd $ORIG_PWD
BN_BINARYSPATH_ROOT=~/binaries
BN_BINARYSPATH=$BN_BINARYSPATH_ROOT/weekly
BN_FILESTOKEEP=4

if [[ ! -d $BN_BINARYSPATH_ROOT ]]; then
  cd ~
  git clone git@github.com:/FStarLang/binaries.git
fi

cd $BN_BINARYSPATH_ROOT
git checkout master
git reset --head HARD
git pull origin master

echo "-- copy files and add to Github --"
if [[ -f $ORIG_PWD/src/ocaml-output/$MINOR_ZIP_FILE ]]; then
  cp_to_binaries $MINOR_ZIP_FILE
  cd ..
fi
if [[ -f $ORIG_PWD/src/ocaml-output/$MINOR_TAR_FILE ]]; then
  cp_to_binaries $MINOR_TAR_FILE
fi

# Now that latest package is added, remove the oldest one because only keeping most recent 4 packages
cd $BN_BINARYSPATH
echo "-- Delete oldest ZIP file if more than 4 exist --"
cleanup_files ".zip"
echo "-- Delete oldest TAR file if more than 4 exist --"
cleanup_files ".gz"

# Commit and push - adding a new one and removing the oldest - commit with amend to keep history limited
echo "--- now commit it but keep history truncated ... then push --- "
git commit --amend -m "Adding new build package and removing oldest."
git push git@github.com:FStarLang/binaries.git master --force

# Manual steps on major releases - use the major version number from make package ... this process creates binary builds and minor version
# 1) Update https://github.com/FStarLang/FStar/blob/master/version.txt
# 2) Create a new branch based on that version
# 3) Document the release
