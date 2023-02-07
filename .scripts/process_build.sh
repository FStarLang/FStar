#!/usr/bin/env bash

# This script is called from everest-ci/ci script for a weekly build of the FStar Binaries
# If ran separately, the starting directory should be the root directory of FStar.

# Creates a tag, if necessary
. "`dirname $0`/release-pre.sh"

# Build and test the package
. "`dirname $0`/test_package.sh"

# Push the binary package(s) to the release.
. "$FSTAR_HOST_HOME/.scripts/release-post.sh"

# Manual steps on major releases - use the major version number from make package ... this process creates binary builds and minor version
# 1) Update https://github.com/FStarLang/FStar/blob/master/version.txt
# 2) Create a new branch based on that version
# 3) Document the release
