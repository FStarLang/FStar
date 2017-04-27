#!/usr/bin/env bash

# Sorry, everyone
if (( ${BASH_VERSION%%.*} < 4 )); then
  echo "This script requires Bash >= 4. On OSX, try: brew install bash"
  exit 1
fi

# Any error is fatal.
set -e
set -o pipefail

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
ORIG_PWD=$PWD  #+++++

echo "*** Make package ***"
cd src/ocaml-output
#cd src   #+++++ Just put in one line
#cd ocaml-output  #+++++ Just put in one line
make package

# For weekly build, we want to use TimeStamp since it is a minor release
echo "*** Unzip and verify the Package  ***"
TIME_STAMP=$(date +%s)

# make package makes the package using the major version from version.txt. This process is weekly process to make minor versions so use timestamp in file name
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
    echo -e "* ${RED}FAIL!${NC} src/ocaml-output/make package did not create "$MAJOR_ZIP_FILE" or "$MAJOR_TAR_FILE
    exit 1
  fi
fi

echo "*** Make the examples ***"
cd fstar
make -C examples/micro-benchmarks 1> MicroBenchMarkOutput.log
make -C examples/hello ocaml 1> HelloOcamlOutput.log
make -C examples/hello fs 1> HelloFStarOutput.log
make -j6 -C examples 1> AllExamples.log

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

# Got to this point, so know it passed - copy minor version out to see if it works
echo "*** Upload the minor version of the package. Will only keep the most recent 4 packages ***"
echo "+++PWD1"$PWD
echo "++ BASE"$ORIG_PWD
cd $ORIG_PWD  #++++ WILL THIS WORK???????
#++++  cd ../../..  # DELETE THIS PROBABLY .... gets back to FStar directory from the unzipped fstar dir ... can't assume ~/FStar as not that way for Windows
echo "+++PWD2"$PWD
#ORIG_PWD=$PWD  +++ DELETE
echo "+++ ORIG:"$ORIG_PWD
BN_BINARYSPATH_ROOT=~/binaries
BN_BINARYSPATH=$BN_BINARYSPATH_ROOT/weekly
#FSTAR_BIN_BRANCH="master"  #+++ DELETE Not really needed since not debugging any more on other branches
BN_FILESTOKEEP=4

if [[ ! -d $BN_BINARYSPATH_ROOT ]]; then
  cd ~
  git clone https://github.com/FStarLang/binaries.git
  #cd $BN_BINARYSPATH_ROOT  #+++++ DUPLICATE FROM LINE BELOW
fi

cd $BN_BINARYSPATH_ROOT
git checkout master #++++++ $FSTAR_BIN_BRANCH remove this and make master
git pull origin master

echo "-- copy files and add to Github --"
if [[ -f $ORIG_PWD/src/ocaml-output/$MINOR_ZIP_FILE ]]; then
  echo "-- "$ORIG_PWD/src/ocaml-output/$MINOR_ZIP_FILE $BN_BINARYSPATH
  cp $ORIG_PWD/src/ocaml-output/$MINOR_ZIP_FILE $BN_BINARYSPATH
  cd $BN_BINARYSPATH
  git add $MINOR_ZIP_FILE
  cd ..
echo "++++ Current PWD"$PWD  
fi
if [[ -f $ORIG_PWD/src/ocaml-output/$MINOR_TAR_FILE ]]; then
  echo "--" $ORIG_PWD/src/ocaml-output/$MINOR_TAR_FILE $BN_BINARYSPATH
  cp $ORIG_PWD/src/ocaml-output/$MINOR_TAR_FILE $BN_BINARYSPATH
  git add $BN_BINARYSPATH/$MINOR_TAR_FILE
fi

# Now that latest package is added, remove the oldest one so only keeping most recent 4 packages
cd $BN_BINARYSPATH
echo "-- Delete oldest ZIP file --"
BN_ZIP_FILES=$BN_BINARYSPATH/*.zip
ZIP_COUNT=`ls -1 $BN_ZIP_FILES 2>/dev/null | wc -l`
if [[ $ZIP_COUNT > $BN_FILESTOKEEP ]]; then
  # Windows git rm just needs the file name and fails if give path so just get file name
  ZIP_FILE_LIST=`ls -t1 $BN_ZIP_FILES | xargs -n1 basename | tail -n +$(($BN_FILESTOKEEP+1))`
  for ZIP_FILE in $ZIP_FILE_LIST
  do
     rm ${ZIP_FILE}
     git rm ${ZIP_FILE} -f  
  done
fi

echo "-- Delete oldest TAR file --"
BN_TAR_FILES=$BN_BINARYSPATH/*.gz
TAR_COUNT=`ls -1 $BN_TAR_FILES 2>/dev/null | wc -l`
if [[ $TAR_COUNT > $BN_FILESTOKEEP ]]; then
  TAR_FILE_LIST=`ls -t1 $BN_TAR_FILES | tail -n +$(($BN_FILESTOKEEP+1))`
  for TAR_FILE in $TAR_FILE_LIST
  do
     rm ${TAR_FILE}
     git rm ${TAR_FILE} -f
  done
fi

# Commit and push - adding a new one and removing the oldest - commit with amend to keep history limited
echo "--- now commit it but keep history truncated ... then push --- "
git commit --amend -m "Adding new build package and removing oldest."
git push git@github.com:FStarLang/binaries.git master --force  #+++++ REMOVED $FSTAR_BIN_BRANCH and just put master in there

# Manual steps on major releases - use the major version number from make package ... this process creates binary builds and minor version
# 1) Update https://github.com/FStarLang/FStar/blob/master/version.txt
# 2) Create a new branch based on that version
# 3) Document the release
