#!/bin/bash

# This will just create a tar.gz or zip out of a directory.
# You may want to look at src-install.sh and bin-install.sh
# that generate the layouts for a source and binary package,
# and are then packaged up with this script.

if [ $# -ne 2 ]; then
	echo "usage: $0 <install_root> <package_basename>" >&2
	echo "Default format is tar.gz. Optionally set FSTAR_PACKAGE_FORMAT=zip to generate a zip instead." >&2
	echo "Output filename is <package_basename> + proper extension." >&2
	exit 1
fi

PREFIX="$1"
ARCHIVE="$2"

case $FSTAR_PACKAGE_FORMAT in
  zip)
    TGT="$ARCHIVE.zip"
    TGT="$(realpath "$TGT")"
    pushd "$PREFIX"
    zip -q -r -9 "$TGT" .
    popd
    ;;
  tar.gz|tgz|"")
    # -h: resolve symlinks
    tar czf "$ARCHIVE.tar.gz" -h -C "$PREFIX" .
    ;;
  *)
    echo "unrecognized FSTAR_PACKAGE_FORMAT: $FSTAR_PACKAGE_FORMAT" >&2
    exit 1
    ;;
esac
