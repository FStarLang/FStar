#!/bin/bash

set -eux

# Run from repo root

fail=
for fn in $(.scripts/remove_stale_hints.sh list); do
  echo "::error::Stale hint file: $fn"
  fail=1
done

if ! [ -z "$fail" ]; then exit 1; fi
