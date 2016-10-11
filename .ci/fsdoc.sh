#!/bin/bash

# Script to run fsdoc on certain dirs in the FStar repo.
# Currently, gets called by the VSTF "FStar, Docs, Linux, CI" build. 
set -x

# Build F*. 
# SI: do I have to do this? Or can I assume it's there already?
make -C src 
# SI: should check that make succeeded.

# make the output dir
FSDOC_ODIR=fsdoc_odir
mkdir -p "$FSDOC_ODIR"

# fsdoc ulib/*.fst* 
pushd ulib
# SI: short sort the *.fst* files. 
SFILES=`ls *.fst *.fsti | sort`
../bin/fstar-any.sh --odir "../$FSDOC_ODIR" --doc *.fst *.fsti
popd

