#!/usr/bin/env bash

# Script to run fsdoc on certain dirs in the FStar repo.
# Currently, this script gets called by the VSTF "FStar, Docs, Linux, CI"
# Build Defn. 

# set -x # debug on
set -e

echo Running fsdoc in `pwd`

# SI: we assume F* has been built and we are in it. 

# un-set this if you won't push the htmls to fstarlang.
# Useful for local testing. 
FSTARLANG_PUSH=true

# 1. Run fstar --doc.

# make the output dir
FSDOC_ODIR=fsdoc_odir
mkdir -p "$FSDOC_ODIR"

# fsdoc ulib to the output dir.  
pushd ulib
# Get fst, fsti files (files are name-sorted by default) except: 
#  FStar.IndefiniteDescription.fst fails to parse;
#  prims.fst has a lower-case filename but an upper-case modulename
#    (pandoc looks for Prims.md but there's only a prims.md).
GLOBIGNORE="prims.fst:FStar.IndefiniteDescription.fst"
FST_FILES=(*.fst *.fsti)
unset GLOBIGNORE

../bin/fstar-any.sh --odir "../$FSDOC_ODIR" --doc ${FST_FILES[*]} 
popd

# 2. pandoc : md -> html
## pandoc the FST_FILES
pushd $FSDOC_ODIR 
for f in "${FST_FILES[@]}"
do
    fe=`basename $f` # SI: should just be able to strip -s md if fsdoc outputs X.fst.md. 
    f="${fe%.*}"     #
    md="${f}.md"
    html="${f}.html"
    pandoc $md -s --css=style.ccs -f markdown -t html -o $html
done
## pandoc the index.md 
### Add html to the module names
sed -i '/[A-Za-z0-9]/s/\(.*\)/[\1](\1.html)/' index.md
### convert index.md to index.html.  
pandoc index.md -s --css=style.ccs -f markdown -t html -o index.html
popd

# 3. push fstarlang.github.io with latest html.
if $FSTARLANG_PUSH; then 
    if [ ! -d fstarlang.github.io ]; then
	git clone git@github.com:FStarLang/fstarlang.github.io
    fi
    pushd fstarlang.github.io
    git config user.email "everbld@microsoft.com"
    git config user.name "Dzomo the everest Yak"

    pushd docs
    mv "../../$FSDOC_ODIR"/*.html .
    git add *.html
    if (git commit -m "Automated doc refresh"); then 
	echo git commit ok.
	git push git@github.com:FStarLang/fstarlang.github.io master 
	echo git push to fstarlang.github ok. 
    else 
	echo git did not commit. 
    fi
    popd # docs
    popd # fstarlang.github.io
# SI: `rm -rf fstarlang.github.io` sometimes fails when in a docker
#     container, so not tidying up after myself.
fi


