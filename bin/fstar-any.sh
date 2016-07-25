#!/bin/bash
set -e
FSTAR=$(which fstar.exe)
if (( $? != 0 )); then
  echo "fstar.exe not found"
elif file $FSTAR | grep Mono >/dev/null 2>&1; then
 mono --debug $FSTAR "$@"
else
 $FSTAR "$@"
fi
