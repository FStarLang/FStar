#!/bin/bash

set -eu

BROOT="$(realpath "$1")"
PREFIX="$(realpath "$2")"

if [ -e "${PREFIX}" ]; then
  echo "Destination directory already exists: ${PREFIX}"
  exit 1
fi

mkdir "${PREFIX}"

# FIXME: use --release or similar?

dune install --prefix="${PREFIX}" --root="${BROOT}/full"
dune install --prefix="${PREFIX}" --root="${BROOT}/fstarlib"
dune install --prefix="${PREFIX}" --root="${BROOT}/bare" fstar-guts
dune install --prefix="${PREFIX}" --root="${BROOT}/fstar-pluginlib"
cp -r -L ulib "${PREFIX}/ulib"
cp -r -L "${BROOT}/ulib.checked" "${PREFIX}/ulib/.cache"
cp version.txt "${PREFIX}/version.txt"
