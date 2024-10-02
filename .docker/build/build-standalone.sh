#!/usr/bin/env bash

set -x

set -e # abort on errors

threads=$1
branchname=$2

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh

rootPath=$(pwd)
result_file="result.txt"
status_file="status.txt"
ORANGE_FILE="orange_file.txt"
build_fstar ci

# If RESOURCEMONITOR is defined, then make an rmon/ directory with
# resource usage information
if [ -n "$RESOURCEMONITOR" ]; then
	echo "Saving runlim files into rmon/"
	mkdir -p rmon
	.scripts/res_summary.sh > rmon/res_summary.txt
	# Copy all .runlim files into a tar archive
	find . -name '*.runlim' | tar czf rmon/rmon.tgz -T -
fi
