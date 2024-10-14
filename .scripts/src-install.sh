#!/bin/bash

set -eu

BROOT="$(realpath "$1")"
PREFIX="$(realpath "$2")"

if [ -e "${PREFIX}" ]; then
  echo "Destination directory already exists: ${PREFIX}"
  exit 1
fi

mkdir "${PREFIX}"

# Note: we must exclude everything in the Dune build
# directories, since if some files "vanish" during this
# copy, rsync will fail. We could also copy everything
# over and then remove the leftovers, but cp -r will
# also abort if some file disappears just before it tries
# to copy it. This seems robust.
rsync -r --copy-links                   \
  --delete-excluded                     \
  --delete-after                        \
  --filter="- **/*.checked"             \
  --filter="- **/*.checked.lax"         \
  --filter="- **/_build"                \
  --filter="- **/*.o"                   \
  --filter="- **/*.a"                   \
  --filter="- **/*.exe"                 \
  --filter="- **/*.cm*"                 \
  --filter="- **/*.*depend*"            \
  --filter="- /out"                     \
  --filter="- /.gitignore"              \
  "${BROOT}/" "${PREFIX}/"

cp fstar.opam "${PREFIX}/fstar.opam"
cp mk/src_package_mk.mk "${PREFIX}/Makefile"
