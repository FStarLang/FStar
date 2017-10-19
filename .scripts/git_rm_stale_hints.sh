#!/bin/bash

set -e
if [[ $(uname) != "Linux" ]]; then
  echo "This script must be run on a case-sensitive OS"
  exit 0
fi

hints=$(find . -iname '*.hints')
for h in $hints; do
  f="${h%.hints}"
  if ! [ -f "$f" ]; then
    echo "Hints file $h present but $f does not exist... git rm'ing it"
    if git ls-files --error-unmatch $h; then
      git rm "$h"
    fi
  fi
done
