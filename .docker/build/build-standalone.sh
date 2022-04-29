#!/usr/bin/env bash

set -x

set -e # abort on errors

target=$1
threads=$2
branchname=$3

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh

rootPath=$(pwd)
result_file="result.txt"
status_file="status.txt"
ORANGE_FILE="orange_file.txt"
build_fstar $target

. $status_file
