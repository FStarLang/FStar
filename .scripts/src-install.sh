#!/bin/bash

set -eu

if [ $# -ne 2 ]; then
	echo "Usage: $0 <build_root> <prefix>" >&2
	exit 1
fi

if [ -e "${PREFIX}" ]; then
  echo "Destination directory already exists: ${PREFIX}"
  exit 1
fi

mkdir -p "${PREFIX}"

BROOT="$(realpath "$1")"
PREFIX="$(realpath "$2")"

# Note: we must exclude everything in the Dune build directories, since
# if some files "vanish" during this copy, rsync will fail (even if
# ignored). We could also copy everything over and then remove the
# leftovers, but cp -r will also abort if some file disappears just
# before it tries to copy it. This seems robust.
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

cp -H -r src "${PREFIX}/src"
cp .scripts/get_fstar_z3.sh "${PREFIX}/get_fstar_z3.sh"
cp fstar.opam "${PREFIX}/fstar.opam"
cp mk/src_package_mk.mk "${PREFIX}/Makefile"
mkdir "${PREFIX}/mk"
cp mk/lib.mk "${PREFIX}/mk/lib.mk"
cp mk/common.mk "${PREFIX}/mk/common.mk"
cp -H mk/fstar-12.mk "${PREFIX}/mk/fstar-12.mk"
