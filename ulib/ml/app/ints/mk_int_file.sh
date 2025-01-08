#!/bin/bash

set -eu

SIGN=$1
WIDTH=$2

if [ "$SIGN" == "U" ]; then
	cat << EOF
	module M = Stdint.Uint${WIDTH}
	type uint${WIDTH} = M.t
	let n = Prims.of_int ${WIDTH}

	let uint_to_t x = M.of_string (Z.to_string x)
	let __uint_to_t = uint_to_t
EOF
elif [ "$SIGN" == "S" ]; then
	cat << EOF
	module M = Stdint.Int${WIDTH}
	type int${WIDTH} = M.t
	let n = Prims.of_int ${WIDTH}

	let int_to_t x = M.of_string (Z.to_string x)
	let __int_to_t = int_to_t
EOF
else
	echo "Bad usage" &>2
	exit 1
fi

cat ./FStar_Ints.ml.body
exit 0
