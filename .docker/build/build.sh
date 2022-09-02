#!/usr/bin/env bash

#set -x

set -e # abort on errors

target=$1
out_file=$2 # GM: This seems unused
threads=$3
branchname=$4

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh

cd FStar
rootPath=$(pwd)
result_file="../result.txt"
status_file="../status.txt"
ORANGE_FILE="../orange_file.txt"
build_fstar $target
cd ..
