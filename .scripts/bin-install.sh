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

# A binary package must NOT ship any precompiled OCaml/findlib packages.
# `dune install` produced, under lib/fstar/, the compiled findlib packages
# fstar.compiler (compiler/), fstar.pluginlib (pluginlib/) and fstar.lib
# (lib/), advertised by META (and dune-package). These only work if the
# recipient uses the *exact same* OCaml compiler and dependency package
# versions that built this package's fstar.exe -- impossible for someone who
# received fstar.exe as a binary -- so we remove them all. fstar.lib is then
# re-shipped as OCaml *sources* + a dune project, so the user builds it
# against their own OCaml toolchain via `fstar.exe --install_lib`.
#
# A regular `make install` / `opam install fstar.opam` does NOT run this
# script (it goes through mk/stage.mk's install rule), so it keeps shipping
# the compiled OCaml packages. Only this binary-package path strips them.
#
# Removing META also fixes findlib resolution of the user-built fstar.lib:
# fstar.exe's --ocamlopt/--ocamlenv prepend <exec>/../lib to OCAMLPATH; with
# no META there, ocamlfind falls through to the user's switch where
# --install_lib installed fstar.lib (with a proper META), instead of being
# shadowed by the package's own META.
if [ -n "$ULIB_ML" ]; then
  LIBDIR="$PREFIX/lib/fstar"
  rm -rf "$LIBDIR/compiler" "$LIBDIR/pluginlib"
  rm -f  "$LIBDIR/META" "$LIBDIR/dune-package"
  # Replace the compiled fstar.lib with sources + a dune project.
  "$FSTAR_ROOT/.scripts/install-fstar-lib-src.sh" "$PREFIX" "$FSTAR_ROOT" "$ULIB_ML"
fi
