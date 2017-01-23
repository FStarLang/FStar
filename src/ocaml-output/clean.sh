#!/usr/bin/env bash
if ! command -v git 2>&1 >/dev/null; then
  echo "Not cleaning because not in a development git checkout of F*"
  exit 0
fi

for f in *.ml; do
  if ! git ls-files | grep "$f" >/dev/null 2>&1; then
    echo $f is not under version control, removing
    rm "$f"
  fi
done
