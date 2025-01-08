#!/bin/bash

set -euo pipefail

NIGHTLY_REPO=FStarLang/FStar-nightly
NIGHTLY_REPO_URL=https://api.github.com/repos/$NIGHTLY_REPO/releases/latest

kernel="$(uname -s)"
case "$kernel" in
  CYGWIN*) kernel=Windows ;;
esac

arch="$(uname -m)"

# Get info about latest release
LATEST_CURL=$(curl -L -H "Accept: application/vnd.github+json" -H "X-GitHub-Api-Version: 2022-11-28" $NIGHTLY_REPO_URL)

# Find the asset that seems to match our architecture and OS
ASSET=$(echo "$LATEST_CURL" | jq -r '.assets[] | select(.name | contains("'$kernel'-'$arch'")) | .browser_download_url')

FILE="$(basename "$ASSET")"

# Get artifact
wget "$ASSET" -O "$FILE"

# Warn if too old (over 48 hours)
S_NOW=$(date +%s)
S_FILE=$(stat "$FILE" -c '%Y')
if [[ $((S_NOW - S_FILE)) -gt $((48 * 60 * 60)) ]]; then
	echo "Warning: downloaded package seems old" >&2
	echo "Modification date: $(stat "$FILE" -c '%y')" >&2
fi

# Untar
rm -rf nightly
mkdir nightly
tar xzf "$FILE" -C nightly
ln -Trsf nightly/fstar out
rm "$FILE"

echo Done.
