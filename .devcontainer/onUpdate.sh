#!/usr/bin/env bash

git submodule init
git submodule update

# Prebuild F* and library
make -j$(nproc) ADMIT=1 |& tee .devcontainer_build.log
