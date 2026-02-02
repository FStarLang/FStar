#!/bin/bash

set -eu

# This will just create a tar.gz or zip out of a directory.
# You may want to look at src-install.sh and bin-install.sh
# that generate the layouts for a source and binary package,
# and are then packaged up with this script.

if [ $# -ne 2 ]; then
  exec >&2
  echo "usage: $0 <install_root> <package_basename>"
  echo "The archive format and command used depends on the system and installed tools,"
  echo "see script for details."
  echo "Optionally set FSTAR_PACKAGE_FORMAT to: "
  echo " - 'zip': create a .zip via 'zip' command"
  echo " - '7z': create a .zip via '7z' command"
  echo " - 'tar.gz': create a .tar.gz, via calling"
  echo "Output filename is <package_basename> + proper extension"
  echo "If FSTAR_RELEASE is non-empty, we use maximum compression."
  exit 1
fi

PREFIX="$1"
ARCHIVE="$2"

windows () {
  # This seems portable enough and does not trigger an
  # undefined variable error (see set -u above) if $OS
  # is unset (like in linux/mac). Note: OSX's bash is usually
  # old and does not support '[ -v OS ]'.
  [[ "${OS:-}" = "Windows_NT" ]]
}

release () {
  [[ -n "${FSTAR_RELEASE:-}" ]]
}

# Computes a (hopefully) sensible default for the current system
detect_format () {
  if windows; then
    # Github actions runner do not have 'zip'
    if which zip > /dev/null; then
      FSTAR_PACKAGE_FORMAT=zip
    elif which 7z > /dev/null; then
      FSTAR_PACKAGE_FORMAT=7z
    else
      echo "error: no zip or 7z command found." >&2
      exit 1
    fi
  else
    FSTAR_PACKAGE_FORMAT=tar.gz
  fi
}

# If unset, pick a default for the system.
if ! [ -v FSTAR_PACKAGE_FORMAT ]; then
  detect_format
fi

fixpath () {
    local result="$(realpath "$1")"
    if windows ; then
	result="$(cygpath -m "$result")"
    fi
    echo "$result"
}

case $FSTAR_PACKAGE_FORMAT in
  zip)
    TGT="$ARCHIVE.zip"
    ATGT="$(fixpath "$TGT")"
    pushd "$PREFIX" >/dev/null
    LEVEL=
    if release; then
      LEVEL=-9
    fi
    zip -q -r $LEVEL "$ATGT" .
    popd >/dev/null
    ;;
  7z)
    TGT="$ARCHIVE.zip"
    ATGT="$(fixpath "$TGT")"
    LEVEL=
    if release; then
      LEVEL=-mx9
    fi
    pushd "$PREFIX" >/dev/null
    7z $LEVEL a "$ATGT" .
    popd >/dev/null
    ;;
  tar.gz|tgz)
    # -h: resolve symlinks
    TGT="$ARCHIVE.tar.gz"
    tar cf "$ARCHIVE.tar" -h -C "$PREFIX" .
    LEVEL=
    if release; then
      LEVEL=-9
    fi
    gzip -f $LEVEL "$ARCHIVE.tar"
    ;;
  *)
    echo "unrecognized FSTAR_PACKAGE_FORMAT: $FSTAR_PACKAGE_FORMAT" >&2
    exit 1
    ;;
esac

if ! [ -f "$TGT" ] ; then
  echo "error: something seems wrong, archive '$TGT' not found?" >&2
  exit 1
fi

# bytes=$(stat -c%s "$TGT")
# echo "Wrote $TGT" ($bytes bytes)"
# ^ Does not work in Mac (no -c option for stat)

echo "Wrote $TGT"
ls -l "$TGT" || true
