#!/bin/bash
set -e
set -x
for f in *.fst *.fsti experimental/*.fst experimental/*.fsti .cache/*.checked ml/Makefile.realized ml/Makefile.include gmake/* legacy/*.fst legacy/*.fsti ; do
    if [[ -e $f ]] ; then
        "$INSTALL_EXEC" -m 644 -D -p $f $PREFIX/lib/fstar/$f
    fi
done
