#!/usr/bin/env bash

target=$1
out_file=$2
threads=$3
branchname=$4
fstarVersion=$5

# Add ssh identity
eval $(ssh-agent)
ssh-add .ssh/id_rsa

eval $(opam config env)

echo $(date -u "+%Y-%m-%d %H:%M:%S") >> $out_file
echo "FStar source version: $fstarVersion" >> $out_file

tail -f $out_file &
tail_pd=$!
{ { { { { { stdbuf -e0 -o0 ./build.sh "$@" ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDERR]!' ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDOUT]!' ; } 2>&1 ; } >> $out_file
kill $tail_pd

echo $(date -u "+%Y-%m-%d %H:%M:%S") >> $out_file

eval $(ssh-agent)
ssh-add -D

# Generate query-stats.
# List the hints that fail to replay.
FStar/.scripts/query-stats.py -f $out_file -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g

# Worst offenders (longest times)
FStar/.scripts/query-stats.py -f $out_file -F html -o log_worst.html -c -g -n 10