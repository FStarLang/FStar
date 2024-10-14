#!/bin/bash

set -eu
set -o pipefail

FSTAR=$1

grab_time () {
	sed -n 's/real \([0-9.]*\)/\1/p'
}

t_defs () {
	rm -f M.fst
	echo 'module M' >>M.fst
	for i in $(seq 1 $1); do
		echo "let x$i = 1" >>M.fst
	done
	/usr/bin/time -p ${FSTAR} M.fst 2>&1 | tee output
	T=$(cat output | grab_time)
	echo "::notice file=DEFS_$i::time = $T"
}

t_defs 100
t_defs 200
t_defs 400
t_defs 800
t_defs 1600
t_defs 3200
t_defs 6400
