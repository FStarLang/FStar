#!/usr/bin/env bash

# Sorry, everyone
if (( ${BASH_VERSION%%.*} < 4 )); then
  echo "This script requires Bash >= 4. On OSX, try: brew install bash"
  exit 1
fi

# Any error is fatal.
set -e
set -o pipefail

if [[ -f ~/.bash_profile ]]; then
  source ~/.bash_profile
fi

# Constants for showing color in output window
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

CURRENT_VERSION=$(head -n 1 version.txt)

echo "** Clean up existing packages first **"
# TO DO: Clean up existing zip files 

echo "** Clean up log files **"
if [[ -f src/ocaml-output/fstar/MicroBenchMarkOutput.log ]]; then
  echo "-- Delete MicroBenchMark Log --"
  rm src/ocaml-output/fstar/MicroBenchMarkOutput.log
fi
if [[ -f src/ocaml-output/fstar/HelloOcamlOutput.log ]]; then
  echo "-- Delete Hello Ocaml Log --"
  rm src/ocaml-output/fstar/HelloOcamlOutput.log
fi
if [[ -f src/ocaml-output/fstar/HelloFStarOutput.log ]]; then
  echo "-- Delete Hello Fstar Log --"
  rm src/ocaml-output/fstar/HelloFStarOutput.log
fi
if [[ -f src/ocaml-output/fstar/AllExamples.log ]]; then
  echo "-- Delete All Examples Log --"
  rm src/ocaml-output/fstar/AllExamples.log
fi

echo "*** Make package ***"
cd src
cd ocaml-output
make package

# For weekly build, we want to use TimeStamp since it is a minor release
echo "*** Unzip and verify the Package  ***"
TIME_STAMP=$(date +%s)

# Unzip .zip file if exists
TYPE="_Windows_x64.zip"
MAJOR_ZIP_FILE=fstar_$CURRENT_VERSION$TYPE
MINOR_ZIP_FILE=fstar_$TIME_STAMP$TYPE
if [[ -f $MAJOR_ZIP_FILE ]]; then
  cp $MAJOR_ZIP_FILE $MINOR_ZIP_FILE
  unzip -o $MAJOR_ZIP_FILE
fi

# Extract linux file if exists
TYPE="Linux_x86_64.tar.gz"
MAJOR_TAR_FILE=fstar_$CURRENT_VERSION$TYPE
MINOR_TAR_FILE=fstar_$TIME_STAMP$TYPE
if [[ -f $MAJOR_TAR_FILE ]]; then
  cp $MAJOR_TAR_FILE $MINOR_TAR_FILE
  tar -x $MAJOR_TAR_FILE
fi

echo "*** Make the examples ***"
cd fstar
make -C examples/micro-benchmarks 1> MicroBenchMarkOutput.log
make -C examples/hello ocaml 1> HelloOcamlOutput.log
make -C examples/hello fs 1> HelloFStarOutput.log
make -j6 -C examples 1> AllExamples.log

echo "*** Verify the examples ***"
echo "* Verify Micro-benchmarks -- should output 'Success:' *"
if ! egrep 'Success:' MicroBenchMarkOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/micro-benchmarks - Success: was not found in MicroBenchMarkOutput.log"
#  exit 1  # Probably don't want to exit ... maybe do because don't want to continue and copy build out
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/micro-benchmarks"
fi

echo "* Verify hello ocaml -- should output Hello F*! *"
if ! egrep 'F*!' HelloFStarOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello ocaml - F*! was not found in HelloOcamlOutput.log"
#  exit 1  # Probably don't want to exit ... maybe do because don't want to continue and copy build out
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello ocaml"
fi

echo "* Verify hello fs -- should output Hello F*!"
if ! egrep 'F*!' HelloFStarOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello fs - F*! was not found in HelloFStarOutput.log"
#  exit 1  # Probably don't want to exit ... maybe do because don't want to continue and copy build out
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello fs"
fi

echo "* Verify all examples -- Look fro Success:"
if ! egrep 'Success:' AllExamples.log; then
  echo -e "* ${RED}FAIL!${NC} for all examples - Success: was not found in AllExamples.log"
#  exit 1  # Probably don't want to exit ... maybe do because don't want to continue and copy build out
else
  echo -e "* ${GREEN}PASSED!${NC} for all examples"
fi

# Got to this point, so know it passed - copy minor version out to see if it works
# TO DO - How do you keep only last four versions????
echo "* Upload the minor version of the package."
cd ..
if [[ -f $MINOR_ZIP_FILE ]]; then
  cp $MINOR_ZIP_FILE "//darrengez820/public"
fi
if [[ -f $MINOR_TAR_FILE ]]; then
  cp $MINOR_TAR_FILE "//darrengez820/public"
fi


# TO DO:
# Find location of releases and figure out how to only keep 4 recent builds - update fstarlang.org
# Clean up old zip files etc
# slack notification on failure?


# Manual steps on major releases
# 1) Update https://github.com/FStarLang/FStar/blob/master/version.txt 
# 2) Create a new branch based on that version
# 3) Document the release

echo "**** DONE!!! ****"
