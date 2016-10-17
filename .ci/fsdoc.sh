#!/bin/bash

# Script to run fsdoc on certain dirs in the FStar repo.
# Currently, gets called by the VSTF "FStar, Docs, Linux, CI" Build Defn. 
# The $PAT value is stored in that Build Defn.  
set -x # debug on

echo Running fsdoc in `pwd`

# SI: we assume F* has been built and we are in it. 

# make the output dir
FSDOC_ODIR=fsdoc_odir
mkdir -p "$FSDOC_ODIR"

# fsdoc ulib/*.fst* 
pushd ulib
# Get fst, fsti files (files are sorted by default). 
FST_FILES=(*.fst *.fsti)
../bin/fstar-any.sh --odir "../$FSDOC_ODIR" --doc ${FST_FILES[*]} 
popd

# pandoc : md -> html
## FST_FILES
pushd $FSDOC_ODIR 
for f in "${FST_FILES[@]}"
do
    fe=`basename $f` # SI: should just be able to strip -s md if fsdoc outputs X.fst.md. 
    f="${fe%.*}"     #
    md="${f}.md"
    html="${f}.html"
    pandoc $md -f markdown -t html -o $html
done
## index.md 
pandoc index.md -f markdown -t html -o index.html
popd

# push fstarlang.github.io with latest html
mkdir fstarlang.github.io
pushd fstarlang.github.io
git init
git config user.name "fsdocbuild"
git config user.email "fsdocbuild@somewhereontheinternet.com"
git pull https://$PAT@github.com/FStarLang/fstarlang.github.io
pushd docs
mv "../../$FSDOC_ODIR"/*.html .
git add *.html 
git commit -m "Automated doc refresh"
git remote add origin https://$PAT@github.com/FStarLang/fstarlang.github.io
git push origin master
popd
popd
rm -rf fstarlang.github.io

# SI: could cleanup FSDOC_ODIR too.


