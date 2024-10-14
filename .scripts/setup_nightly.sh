#!/bin/bash

set -eux

# Get latest run ID
# ID=$(gh run list --workflow nightly.yml -L1 --json databaseId | jq '.[0].databaseId')
ID=$(gh run list --workflow nightly.yml --json status,databaseId | jq '(.[] | select (.status == "completed") | .databaseId)' | head -n 1)
NAME=fstar-ci-stage1.tar.gz

# Download binary package
gh run download ${ID} -n ${NAME}

# Untar
rm -rf out
mkdir out
tar xzf ${NAME} -C out
rm -f ${NAME}

# Done?
echo DONE
