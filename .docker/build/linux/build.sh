#!/usr/bin/env bash

target=$1
out_file=$2
threads=$3

tail -f $out_file &
tail_pd=$!
{ { { { { { stdbuf -e0 -o0 ./build_fstar.sh "$@" ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDERR]!' ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDOUT]!' ; } 2>&1 ; } >> $out_file
kill $tail_pd