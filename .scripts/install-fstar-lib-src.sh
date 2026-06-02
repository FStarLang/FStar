#!/bin/bash

# Install the OCaml *sources* of the F* application library (fstar.lib)
# into <prefix>/lib/fstar/lib, together with a dune project, so that the
# user can build and install fstar.lib themselves.
#
# The binary package deliberately does not ship a precompiled fstar.lib:
# this avoids OCaml ABI mismatches between the package and the user's own
# OCaml toolchain. See mk/fstar-lib-src/README.md.

set -eu

if [ $# -ne 3 ]; then
  echo "Usage: $0 <prefix> <fstar_root> <ulib_ml_dir>" >&2
  exit 1
fi

PREFIX="$1"     # install prefix (we write into $PREFIX/lib/fstar/lib)
FSTAR_ROOT="$2" # root of the F* source tree
ULIB_ML="$3"    # directory holding the extracted ulib OCaml (stageN/ulib.ml)

DEST="$PREFIX/lib/fstar/lib"
rm -rf "$DEST"
mkdir -p "$DEST"

# Handwritten realizations (dereference symlinks with -L).
cp -L -p -r "$FSTAR_ROOT/ulib/ml/app"       "$DEST/app"
cp -L -p -r "$FSTAR_ROOT/ulib/ml/app-extra" "$DEST/app-extra"
# F*-extracted ulib modules.
cp -L -p -r "$ULIB_ML"                      "$DEST/ulib.ml"

# Drop any stale dependency files that may have ended up next to the sources.
# NB: we deliberately keep app/ints/dune, which generates the fixed-width
# integer modules (FStar_UInt16/32/64, FStar_Int8/16/32/64) at build time.
find "$DEST" -name '.depend' -delete 2>/dev/null || true

# dune project to build and install fstar.lib.
cp -p "$FSTAR_ROOT/mk/fstar-lib-src/dune"         "$DEST/dune"
cp -p "$FSTAR_ROOT/mk/fstar-lib-src/dune-project" "$DEST/dune-project"
cp -p "$FSTAR_ROOT/mk/fstar-lib-src/README.md"    "$DEST/README.md"
# Mediated installer: builds fstar.lib and installs it without clobbering the
# rest of the F* findlib metadata (compiler/pluginlib). See README.md.
cp -p "$FSTAR_ROOT/mk/fstar-lib-src/install.sh"   "$DEST/install.sh"
chmod +x "$DEST/install.sh"

echo "Installed fstar.lib sources + dune project into $DEST"
