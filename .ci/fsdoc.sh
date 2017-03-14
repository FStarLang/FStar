#!/usr/bin/env bash

# Script to run fsdoc on certain dirs in the FStar repo.
# Currently, this script gets called by the VSTF "FStar, Docs, Linux, CI"
# Build Defn. 

# set -x # debug on
set -e

echo Running fsdoc in `pwd`

# SI: we assume F* has been built and we are in it. 

# un-set this if you won't push docs to fstarlang.
# Useful for local testing. 
FSTARLANG_PUSH=true

# 1. Run fstar --doc.

# make the output dir
FSDOC_ODIR=fsdoc_odir
mkdir -p "$FSDOC_ODIR"

# fsdoc ulib to the output dir.  
pushd ulib
# Get fst, fsti files (files are name-sorted by default). 
# SI: Used to be this:
#FST_FILES=(*.fst *.fsti)
#     but FStar.IndefiniteDescription.fst fails to parse;
#         prims.fst has a lower-case filename but an upper-case modulename
#           (pandoc looks for Prims.md but there's only a prims.md). 
FST_FILES=(
FStar.All.fst \
FStar.Array.fst \
FStar.Axiomatic.Array.fst \
FStar.BitVector.fst \
FStar.Buffer.fst \
FStar.Buffer.Quantifiers.fst \
FStar.Bytes.fst \
FStar.Classical.fst \
FStar.Constructive.fst \
FStar.Crypto.fst \
FStar.DependentMap.fst \
FStar.ErasedLogic.fst \
FStar.Fin.fst \
FStar.FunctionalExtensionality.fst \
FStar.Ghost.fst \
FStar.Heap.fst \
FStar.HyperHeap.fst \
FStar.HyperStack.fst \
FStar.Int.Cast.fst \
FStar.Int.fst \
FStar.Int128.fst \
FStar.Int16.fst \
FStar.Int31.fst \
FStar.Int32.fst \
FStar.Int63.fst \
FStar.Int64.fst \
FStar.Int8.fst \
FStar.Integers.fst \
FStar.List.fst \
FStar.List.Tot.Base.fst \
FStar.List.Tot.fst \
FStar.List.Tot.Properties.fst \
FStar.Map.fst \
FStar.MarkovsPrinciple.fst \
FStar.Math.Lemmas.fst \
FStar.Math.Lib.fst \
FStar.Monotonic.RRef.fst \
FStar.Monotonic.Seq.fst \
FStar.MRef.fst \
FStar.Mul.fst \
FStar.OrdMap.fst \
FStar.OrdMapProps.fst \
FStar.OrdSet.fst \
FStar.OrdSetProps.fst \
FStar.PredicateExtensionality.fst \
FStar.PropositionalExtensionality.fst \
FStar.Reader.fst \
FStar.Relational.Comp.fst \
FStar.Relational.Relational.fst \
FStar.Relational.State.fst \
FStar.Seq.Base.fst \
FStar.Seq.fst \
FStar.Seq.Properties.fst \
FStar.Set.fst \
FStar.Squash.fst \
FStar.SquashEffect.fst \
FStar.SquashProperties.fst \
FStar.ST.fst \
FStar.StrongExcludedMiddle.fst \
FStar.Struct.fst \
FStar.StructNG.fst \
FStar.Tcp.fst \
FStar.TSet.fst \
FStar.TwoLevelHeap.fst \
FStar.UInt.fst \
FStar.UInt128.fst \
FStar.UInt16.fst \
FStar.UInt31.fst \
FStar.UInt32.fst \
FStar.UInt63.fst \
FStar.UInt64.fst \
FStar.UInt8.fst \
FStar.Universe.fst \
FStar.Util.fst \
)

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


