#!/bin/bash

# This is called by the Makefile *after* an installation into the
# prefix, so we add the rest of the files that go into a binary package.

set -eu

windows () {
  # This seems portable enough and does not trigger an
  # undefined variable error (see set -u above) if $OS
  # is unset (like in linux/mac). Note: OSX's bash is usually
  # old and does not support '[ -v OS ]'.
  [[ "${OS:-}" = "Windows_NT" ]]
}

if [ $# -ne 1 ]; then
  echo "Usage: $0 <prefix>" >&2
  exit 1
fi

PREFIX="$1"
mkdir -p "$PREFIX"
PREFIX="$(realpath "$PREFIX")"

if ! [ -v FSTAR_PACKAGE_Z3 ] || ! [ "$FSTAR_PACKAGE_Z3" = false ]; then
  .scripts/package_z3.sh "$PREFIX"
fi

if windows; then
    # This dll is needed. It must be installed if we're packaging, as we
    # must have run F* already, but it should probably be obtained from
    # somewhere else... We also allow an external override.
    if [ -z "$LIBGMP" ]; then
      LIBGMP=$(which libgmp-10.dll)
    fi
    if ! [ -f "$LIBGMP" ]; then
      echo "error: libgmp-10.dll not found! Carrying on..." >&2
    fi
    cp "$LIBGMP" "$PREFIX/bin"
fi

# License and extra files. Not there on normal installs, but present in
# package.
cp LICENSE* "$PREFIX"
cp README.md "$PREFIX"
cp INSTALL.md "$PREFIX"
cp version.txt "$PREFIX"

# Save the megabytes! Strip binaries
STRIP=strip

if windows; then
  strip_prefix="$(cygpath -m "$PREFIX")"
else
  strip_prefix="$PREFIX"
fi

$STRIP "$strip_prefix"/bin/* || true
$STRIP "$strip_prefix"/lib/fstar/z3-*/bin/* || true
