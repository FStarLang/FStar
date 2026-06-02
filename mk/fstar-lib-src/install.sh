#!/usr/bin/env bash

# Build and install fstar.lib into an opam switch (or any prefix) *without*
# clobbering the rest of the F* findlib metadata.
#
# Why this script (and not a plain `dune install`)?  `fstar.lib` is the `lib`
# sub-package of the findlib package `fstar`, which also provides `fstar.compiler`
# and `fstar.pluginlib` (used by `fstar.exe --ocamlopt_plugin`).  dune writes the
# package META at <libdir>/fstar/META and has no option to merge or skip it, so a
# bare `dune install` of this project would overwrite that file with a META that
# only mentions `lib`, silently dropping `compiler`/`pluginlib`.  This script runs
# the install and then merges the freshly generated `lib` stanza back into the
# pre-existing META, preserving every other sub-package.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$HERE"

PREFIX="${1:-$(opam var prefix)}"
LIBDIR="${2:-$(opam var lib 2>/dev/null || echo "$PREFIX/lib")}"
META="$LIBDIR/fstar/META"

# Preserve any pre-existing sub-package stanzas (compiler, pluginlib, ...) that
# `dune install` would otherwise clobber.
SAVED=""
if [ -f "$META" ]; then
  SAVED="$(mktemp)"
  cp "$META" "$SAVED"
fi

dune build
dune install --prefix "$PREFIX" --libdir "$LIBDIR"

# dune has just rewritten $META to contain ONLY the `lib` stanza.  If there were
# other stanzas before, merge: keep them and re-append the new `lib` stanza.
if [ -n "$SAVED" ] && [ -f "$META" ]; then
  NEWLIB="$(awk '
    /^package "lib" \(/ { p=1 }
    p { print }
    p && /^\)/ { exit }
  ' "$META")"
  if [ -n "$NEWLIB" ]; then
    # Drop any stale `lib` stanza from the saved META, keep all other stanzas,
    # then append the freshly generated one.
    awk '
      /^package "lib" \(/ { skip=1 }
      skip { if ($0 ~ /^\)/) skip=0; next }
      { print }
    ' "$SAVED" > "$META"
    printf '\n%s\n' "$NEWLIB" >> "$META"
  fi
  rm -f "$SAVED"
fi

echo "Installed fstar.lib into $LIBDIR/fstar (META preserved)."
