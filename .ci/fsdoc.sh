#!/bin/bash

# Script to run fsdoc on certain dirs in the FStar repo.
# Currently, gets called by the VSTF "FStar, Docs, Linux, CI" build. 
set -x

echo Running fsdoc in `pwd`

# SI: we assume F* has been built and is in the path.

# make the output dir
FSDOC_ODIR=fsdoc_odir
mkdir -p "$FSDOC_ODIR"

# fsdoc ulib/*.fst* 
pushd ulib
# Get fst, fsti files. Sorted by default. 
FST_FILES=(*.fst *.fsti)
../bin/fstar-any.sh --odir "../$FSDOC_ODIR" --doc ${FST_FILES[*]} 
popd

