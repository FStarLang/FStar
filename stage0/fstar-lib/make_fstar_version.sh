#!/usr/bin/env bash

VERSION=$(head -n 1 version.txt)
if [ "$OS" = "Windows_NT" ]
then
   if [ "$PROCESSOR_ARCHITECTURE" = "AMD64" ]
   then
     PLATFORM="Windows_x64"
   else
     PLATFORM="Windows_x86"
   fi
else
     PLATFORM="$(uname)_$(uname -m)"
fi
COMPILER="OCaml $(ocamlc -version)"
# If a system does not have git, or we are not in a git repo, fallback with "unset"
if [[ -z "$FSTAR_COMMIT" ]] ; then
   FSTAR_COMMIT=$(git describe --match="" --always --abbrev=40 --dirty 2>/dev/null || echo unset)
fi
COMMITDATE=$(git log --pretty=format:%ci -n 1 2>/dev/null || echo unset)

echo "let dummy () = ();;"
echo "FStarC_Options._version := \"$VERSION\";"
echo "FStarC_Options._platform := \"$PLATFORM\";;"
echo "FStarC_Options._compiler := \"$COMPILER\";;"
# We deliberately use commitdate instead of date, so that rebuilds are no-ops
echo "FStarC_Options._date := \"$COMMITDATE\";;"
echo "FStarC_Options._commit:= \"$FSTAR_COMMIT\";;"
