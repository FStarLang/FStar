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

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  echo "Usage: $0 <prefix> [<ulib_ml_dir>]" >&2
  exit 1
fi

PREFIX="$1"
# Optional: directory holding the F*-extracted ulib OCaml sources
# (stageN/ulib.ml). When provided, we ship fstar.lib as sources instead of
# a precompiled library (see below).
ULIB_ML="${2:-}"
SCRIPTDIR="$(cd "$(dirname "$0")" && pwd)"
FSTAR_ROOT="$(dirname "$SCRIPTDIR")"
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

# fstar.lib: in a binary package we do NOT ship the precompiled library
# that `dune install` produced under lib/fstar/lib. Instead we replace it
# with its OCaml *sources* + a dune project, so the user builds fstar.lib
# against their own OCaml toolchain (avoiding ABI mismatches). A regular
# `make install` / `opam install fstar.opam` keeps the compiled fstar.lib.
if [ -n "$ULIB_ML" ]; then
  # Drop the precompiled fstar.lib advertised in META (the "lib" sub-package),
  # since the binary package ships sources only. The user's later
  # `dune install` of the shipped dune project re-adds it.
  META="$PREFIX/lib/fstar/META"
  if [ -f "$META" ]; then
    awk '
      /^package "lib" \(/ { skip=1 }
      skip { if ($0 ~ /^\)/) skip=0; next }
      { print }
    ' "$META" > "$META.tmp" && mv "$META.tmp" "$META"
  fi
  # Replace the compiled library directory with sources + dune project.
  "$FSTAR_ROOT/.scripts/install-fstar-lib-src.sh" "$PREFIX" "$FSTAR_ROOT" "$ULIB_ML"
fi
