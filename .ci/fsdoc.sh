#!/bin/bash

# Script to run fsdoc on certain dirs in the FStar repo.
# Currently, this script gets called by the VSTF "FStar, Docs, Linux, CI"
# Build Defn. The $PAT env var is stored in that Build Defn.  
set -x # debug on

echo Running fsdoc in `pwd`

# SI: we assume F* has been built and we are in it. 

# make the output dir
FSDOC_ODIR=fsdoc_odir
mkdir -p "$FSDOC_ODIR"

# fsdoc the output dir.  
pushd ulib
# Get fst, fsti files (files are name-sorted by default). 
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
    pandoc $md -s --css=style.ccs -f markdown -t html -o $html
done
## index.md 
### Add html to the module names. 
sed -i '/[A-Za-z0-9]/s/\(.*\)/[\1](\1.html)/' index.md
### convert index.md to index.html.  
pandoc index.md -s --css=style.ccs -f markdown -t html -o index.html
popd
exit
# push fstarlang.github.io with latest html.
# The flow is described at https://github.com/blog/1270-easier-builds-and-deployments-using-git-over-https-and-oauth;
# $PAT is stored in the Build Defn. 
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


