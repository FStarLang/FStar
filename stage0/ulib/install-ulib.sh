#!/usr/bin/env bash
set -e
set -x

for f in fstar.include *.fst *.fsti experimental/*.fst experimental/*.fsti .cache/*.checked ml/Makefile.realized ml/Makefile.include gmake/* legacy/*.fst legacy/*.fsti Makefile.extract.fsharp fs/* fs/VS/* ; do
    if [[ -f $f ]] ; then
        "$INSTALL_EXEC" -m 644 -D -p $f $PREFIX/lib/fstar/$f
    fi
done
