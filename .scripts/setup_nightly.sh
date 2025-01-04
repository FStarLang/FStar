#!/bin/bash

set -euo pipefail

kernel="$(uname -s)"
case "$kernel" in
  CYGWIN*) kernel=Windows ;;
esac

arch="$(uname -m)"
case "$arch" in
  arm64) arch=aarch64 ;;
esac

URL="https://github.com/FStarLang/FStar/releases/download/nightly/fstar-$kernel-$arch.tar.gz"
FILE="$(basename "$URL")"

# Get artifact
wget "$URL" -O "$FILE"

# Warn if too old (over 48 hours)
S_NOW=$(date +%s)
S_FILE=$(stat "$FILE" -c '%Y')
if [[ $((S_NOW - S_FILE)) -gt $((48 * 60 * 60)) ]]; then
	echo "Warning: downloaded package seems old" >&2
	echo "Modification date: $(stat "$FILE" -c '%y')" >&2
fi

# Untar
rm -rf out
mkdir out
tar xzf "$FILE" -C out
rm "$FILE"

echo Done.
