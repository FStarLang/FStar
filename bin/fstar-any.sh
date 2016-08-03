#!/bin/bash
FSTAR=$(dirname $(stat -f $0))/fstar.exe
if (( $? != 0 )); then
  echo "fstar.exe not found"
  exit 1
elif file $FSTAR | grep Mono >/dev/null 2>&1; then
  mono --debug $FSTAR "$@" || exit 1
else
  $FSTAR "$@" || exit 1
fi
