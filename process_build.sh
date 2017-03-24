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
# TO DO: Clean up existing zip files etc

echo "** Clean up log files **"
if [ -f src/ocaml-output/fstar/MicroBenchMarkOutput.log ]; then
  echo "-- Delete MicroBenchMark Log --"
  rm src/ocaml-output/fstar/MicroBenchMarkOutput.log
fi
if [ -f src/ocaml-output/fstar/HelloOcamlOutput.log ]; then
  echo "-- Delete Hello Ocaml Log --"
  rm src/ocaml-output/fstar/HelloOcamlOutput.log
fi
if [ -f src/ocaml-output/fstar/HelloFStarOutput.log ]; then
  echo "-- Delete Hello Fstar Log --"
  rm src/ocaml-output/fstar/HelloFStarOutput.log
fi
if [ -f src/ocaml-output/fstar/AllExamples.log ]; then
  echo "-- Delete All Examples Log --"
  rm src/ocaml-output/fstar/AllExamples.log
fi

echo "*** Make package ***"
cd src
cd ocaml-output
make package

echo "*** Unzip and verify the Package  ***"
# Unzip .zip file if exists
TYPE="_Windows_x64.zip"
ZIP_FILE=fstar_$CURRENT_VERSION$WIN
if [ -f ZIP_FILE ]; then
  unzip -o ZIP_FILE
fi

# Extract linux file if exists
TYPE="Linux_x86_64.tar.gz"
TAR_FILE=fstar_$CURRENT_VERSION$TYPE
if [ -f TAR_FILE ]; then
  tar -x TAR_FILE
fi


echo "*** Make the examples ***"
cd fstar
make -C examples/micro-benchmarks 1> MicroBenchMarkOutput.log
make -C examples/hello ocaml 1> HelloOcamlOutput.log
make -C examples/hello fs 1> HelloFStarOutput.log
make -j6 -C examples 1> AllExamples.log # Takes a while - not sure if want to do it or not


echo "*** Verify the examples ***"
echo "* Verify Micro-benchmarks -- should output 'Success:' *"
if ! egrep 'Success:' MicroBenchMarkOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/micro-benchmarks - Success: was not found in MicroBenchMarkOutput.log"
#  exit 1  # Probably don't want to exit ...
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/micro-benchmarks"
fi

echo "* Verify hello ocaml -- should output Hello F*! *"
if ! egrep 'F*!' HelloFStarOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello ocaml - F*! was not found in HelloOcamlOutput.log"
#  exit 1  # Probably don't want to exit ...
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello ocaml"
fi

echo "* Verify hello fs -- should output Hello F*!"
if ! egrep 'F*!' HelloFStarOutput.log; then
  echo -e "* ${RED}FAIL!${NC} for examples/hello fs - F*! was not found in HelloFStarOutput.log"
#  exit 1  # Probably don't want to exit ...
else
  echo -e "* ${GREEN}PASSED!${NC} for examples/hello fs"
fi

echo "* Verify all examples -- Look fro Success:"
if ! egrep 'Success:' AllExamples.log; then
  echo -e "* ${RED}FAIL!${NC} for all examples - Success: was not found in AllExamples.log"
#  exit 1  # Probably don't want to exit ...
else
  echo -e "* ${GREEN}PASSED!${NC} for all examples"
fi

# TO DO:
#1) Figure out what to all verify in all examples
#2) Find out what actual binaries are (ulib directory?)
#3) Clean up existing packages first

# Push all changes to ocaml output -- handled by nightly build

# Push binaries to fstarlang.org (Sreekanth will have info on how to access)
# Save the last 4 builds there. Don't need more than that.

# Update Version.txt?? Probably not

# Create a new branch based on version (i.e. v0.9.x.y)

# Document the release

echo "**** DONE!!! ****"
