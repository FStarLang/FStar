#!/usr/bin/env bash

windows () {
  [[ "${OS:-}" = "Windows_NT" ]]
}

if [[ -z "$FSTAR_VERSION" ]]; then
  FSTAR_VERSION=$(head -n 1 version.txt)~dev
fi

if windows; then
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
   # NB: ^ has to be in-sync with src-install.sh
fi
if [[ -z "$FSTAR_COMMITDATE" ]] ; then
   FSTAR_COMMITDATE=$(git log --pretty=format:%ci -n 1 2>/dev/null || echo unset)
   # NB: ^ has to be in-sync with src-install.sh
fi

echo "let dummy () = ();;"
echo "FStarC_Options._version := \"$FSTAR_VERSION\";;"
echo "FStarC_Options._platform := \"$PLATFORM\";;"
echo "FStarC_Options._compiler := \"$COMPILER\";;"
# We deliberately use commitdate instead of date, so that rebuilds are no-ops
echo "FStarC_Options._date := \"$FSTAR_COMMITDATE\";;"
echo "FStarC_Options._commit:= \"$FSTAR_COMMIT\";;"
