#!/usr/bin/env bash
FSTAR=$(cd "$(dirname "$0")" && pwd -P)/fstar.exe
if [ ! -f "$FSTAR" ]; then
  echo "fstar.exe not found"
  exit 1
elif [[ $OS != "Windows_NT" ]] && file "$FSTAR" | grep Mono >/dev/null 2>&1; then
  mono "$FSTAR" "$@" || exit 1
else
  "$FSTAR" "$@" || exit 1
fi
