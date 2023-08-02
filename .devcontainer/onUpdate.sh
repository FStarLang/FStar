#!/usr/bin/env bash

# Prebuild F* and library
make -j$(nproc) ADMIT=1 |& tee .devcontainer_build.log
