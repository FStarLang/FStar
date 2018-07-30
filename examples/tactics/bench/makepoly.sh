#!/bin/bash

set -ue

make1 () {
	FILE=$1
	MODULENAME=${FILE/.fst/}
	BY=$2
	FACTOR=$3
	SEED=$4
	OPTS=$5

	FLATMODULE=$(echo $MODULENAME | tr -d '.')

	cat PolyStub.fst | sed "s/__MODULE__/${MODULENAME}/" \
			 | sed "s/__FACTOR__/${FACTOR}/" \
			 | sed "s/__SEED__/${SEED}/" \
			 | sed "s/__OPTS__/${OPTS}/" \
			 | sed "s/__SUFFIX__/${FLATMODULE}/" \
			 | sed "s/__BY__/${BY}/" > $FILE
}

abort () {
	echo "expected input Bench.Poly.(None/Canon/CanonNative).Factor(Factor).Seed(SIZE).fst" &>2
}

IFS='.' read -r -a array <<< "$1"

if ! [ x"${array[0]}" == x"Bench" ]; then
	abort
fi
if ! [ x"${array[1]}" == x"Poly" ]; then
	abort
fi

# Overriden by CanonNative

OPTS="--no_plugins"

if [ x"${array[2]}" == x"None" ]; then
	BY=""
elif [ x"${array[2]}" == x"Canon" ]; then
	BY="by (canon_semiring int_cr)"
elif [ x"${array[2]}" == x"CanonNative" ]; then
	BY="by (canon_semiring int_cr)"
	OPTS=""
else
	abort
fi

FACTOR="${array[3]}"
FACTOR="${FACTOR/Factor/}"

SEED="${array[4]}"
SEED="${SEED/Seed/}"

make1 "$1" "$BY" "$FACTOR" "$SEED" "$OPTS"
