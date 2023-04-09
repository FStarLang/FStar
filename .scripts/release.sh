#!/usr/bin/env bash

# This script is called by the release.yml GitHub Actions workflow
# to build and upload a release artifact for Mac or Windows.

# This script MUST NOT be used to create a fresh new release from
# scratch, but only to upload Mac or Windows binaries, ASSUMING that
# a Linux release was already uploaded.
# To create a new release, you should first start with Linux, by
# building an image from .docker/release.Dockerfile

# Ideally, instead of invoking these Dockerfiles and scripts by
# yourself, you should be able to use the release.yaml GitHub Actions
# workflow, which should create a new Linux release and upload Mac and
# Windows binaries all at once.

set -e
set -x

# Switch to the F* root directory
if [[ -z "$FSTAR_HOST_HOME" ]] ; then
  FSTAR_HOST_HOME=$(cd `dirname $0`/.. && pwd)
fi
cd "$FSTAR_HOST_HOME"

# Strip the ~dev part of the version number
dev='~dev'
sed -i 's!'"$dev"'!!' version.txt

# Build the package
if [[ -z "$CI_THREADS" ]] ; then
    CI_THREADS=1
fi
make -j "$CI_THREADS" package

# Test the package if possible
if [[ -z "$FSTAR_SKIP_PACKAGE_TEST" ]] ; then
    .scripts/test_package.sh
fi

# Push the binary package to GitHub Releases
.scripts/publish_release.sh
