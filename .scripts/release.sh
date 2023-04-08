#!/usr/bin/env bash

# This script is called by the release.yml GitHub Actions workflow
# to create a release for Mac

set -e
set -x

# Switch to the F* root directory
if [[ -z "$FSTAR_HOST_HOME" ]] ; then
  FSTAR_HOST_HOME=$(cd `dirname $0`/.. && pwd)
fi
cd "$FSTAR_HOST_HOME"

# Build the package
make -j6 package

# Push the binary package to GitHub Releases
.scripts/publish_release.sh
