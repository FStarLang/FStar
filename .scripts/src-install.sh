#!/bin/bash

set -eu

if [ $# -ne 2 ]; then
	echo "Usage: $0 <build_root> <prefix>" >&2
	exit 1
fi

BROOT="$(realpath "$1")"

PREFIX="$2"
mkdir -p "$PREFIX"
PREFIX="$(realpath "$PREFIX")"

# The tests.ml directory may not exist after a build, and rsync
# in src-install will complain if so. Create it just in case.
mkdir -p "${BROOT}/tests.ml"

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

cp LICENSE* "${PREFIX}"
cp README.md "${PREFIX}"
cp INSTALL.md "${PREFIX}"
cp version.txt "${PREFIX}"

cp -H -r src "${PREFIX}/src"
cp .scripts/get_fstar_z3.sh "${PREFIX}/get_fstar_z3.sh"
cp fstar.opam "${PREFIX}/fstar.opam"
mkdir "${PREFIX}/mk"
cp mk/lib.mk "${PREFIX}/mk/lib.mk"
cp mk/common.mk "${PREFIX}/mk/common.mk"
cp -H mk/fstar-12.mk "${PREFIX}/mk/fstar-12.mk"
cp mk/generic-1.mk "${PREFIX}/mk/generic-1.mk"
mkdir "${PREFIX}/.scripts"
cp .scripts/bin-install.sh  "${PREFIX}/.scripts"
cp .scripts/mk-package.sh   "${PREFIX}/.scripts"
cp .scripts/get_fstar_z3.sh "${PREFIX}/.scripts"
cp .scripts/package_z3.sh   "${PREFIX}/.scripts"

cp mk/src_package_mk.mk "${PREFIX}/Makefile"

# Make sure the source package has a proper version.
FSTAR_COMMIT=$(git describe --match="" --always --abbrev=40 --dirty 2>/dev/null || echo unset)
FSTAR_COMMITDATE=$(git log --pretty=format:%ci -n 1 2>/dev/null || echo unset)
# NB: ^ has to be in-sync with make_fstar_version.sh
echo "## LINES BELOW ADDED BY src-install.sh" >> "${PREFIX}/Makefile"
echo "export FSTAR_COMMITDATE=$FSTAR_COMMITDATE" >> "${PREFIX}/Makefile"
echo "export FSTAR_COMMIT=$FSTAR_COMMIT" >> "${PREFIX}/Makefile"
if [[ -n "${FSTAR_VERSION:-}" ]]; then
  echo "export FSTAR_VERSION=$FSTAR_VERSION" >> "${PREFIX}/Makefile"
fi

# Remove extra ML files, rsync has resolved the links
# into the corresponding files already, and these would be
# duplicates.
rm -r "$PREFIX"/*.ml
rm -r "$PREFIX"/*.pluginml
