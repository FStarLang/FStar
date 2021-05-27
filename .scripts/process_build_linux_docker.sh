#!/usr/bin/env bash

# Creates a tag, if necessary
. "`dirname $0`/release-pre.sh"

# Build the package
docker build -t fstar-package -f "$FSTAR_HOST_HOME/.docker/package.Dockerfile" "$FSTAR_HOST_HOME"

# Extract the package from the image
mkdir "$FSTAR_HOST_HOME/release"
docker container create --name container-fstar-package fstar-package
docker cp container-fstar-package:/home/test/fstar.tar.gz "$FSTAR_HOST_HOME/release/fstar.tar.gz"
docker cp container-fstar-package:/home/test/version_platform.txt "$FSTAR_HOST_HOME/release/version_platform.txt"
docker container rm container-fstar-package
docker image rm -f fstar-package

# Rename the package to its intended name with version and platform
BUILD_PACKAGE=$(cat "$FSTAR_HOST_HOME/release/version_platform.txt")
mv "$FSTAR_HOST_HOME/release/fstar.tar.gz" "$FSTAR_HOST_HOME/release/$BUILD_PACKAGE"

# Push the release
. "$FSTAR_HOST_HOME/.scripts/release-post.sh"
