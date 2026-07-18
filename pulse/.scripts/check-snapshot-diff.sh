#!/bin/bash

set -eu

# This is run by CI to check that the snapshot has not changed after
# bootstrapping. Must run from the root of the Pulse git repo.

SUCCESS=true
DIR=src/ocaml/*/generated # globs are OK
export GIT_PAGER=cat

# If there's any output, i.e. any file not in HEAD, fail
if git ls-files --others --exclude-standard -- $DIR | grep -q . &>/dev/null; then
    SUCCESS=false
fi

# If there's a diff in existing files, fail
if ! git diff --exit-code $DIR &>/dev/null; then
    SUCCESS=false
fi

if ! $SUCCESS; then
    echo "*********************************************************"
    echo " *** SNAPSHOT DIFF:"
    echo ""
    echo "$ git status $DIR"
    git status $DIR
    echo ""
    echo "$ git diff -a $DIR"
    git diff -a $DIR
    echo "*********************************************************"
    exit 1
else
    echo "Snapshot seems clean"
    exit 0
fi
