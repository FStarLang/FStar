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

# pandoc : md -> html
# SI: no pandoc on machine yet.
PD=`which pandoc`
echo "Machine has pandoc $PD installed." 
# for 
#     pandoc $f -f markdown -t html -o $f.html
# exit

# push fstarlang.github.io with latest html
git clone https://fstarlang.github.io 
pushd fstarlang.github.io
pushd docs
cp "../../$FSDOC_ODIR"/*.html .
git commit -am "Automated doc refresh"
git push 
popd
popd
rm -rf fstarlang




