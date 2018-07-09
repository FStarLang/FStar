#!/bin/bash

set -ue

make () {
	REPR=$1
	use_nbe=$2
	use_eager=$3
	LEN=$4
	use_load=$5
	FILE=$6

	STEPS=
               
	if $use_nbe; then
		STEPS="${STEPS} nbe;"
	fi

	MODULE=${FILE/.fst/}
	MODULE_PLAIN=${MODULE//./_}

	(
	exec 1> $FILE;
	echo "\
module $MODULE
open Imp.$REPR
module R = Registers.$REPR
module L = FStar.List.Tot

[@unfold_defs]
let long_zero x : prog =
	let l = x_times_42 x in"

	for i in $(seq 1 $LEN); do
		echo '	let l = l `L.append` l in'
	done
	echo '	l `L.append` [Const 0 (reg 0); Const 0 (reg 1); Const 0 (reg 2)]'
	echo
	echo -n '
unfold
let normal #a (e:a) =
  FStar.Pervasives.norm [zeta; iota;
                         delta_only [`%eval; `%eval'"'"'; `%R.upd; `%R.sel; `%R.eta_map; `%L.append; `%FStar.Mul.op_Star];
                         delta_attr [`%unfold_defs]; '"$STEPS"'
                         primops] e

let norm_assert (p:Type) : Lemma (requires (normal p)) (ensures True) = ()

#set-options "--no_smt"
[@tcdecltime]
let test_'"$MODULE_PLAIN"' = norm_assert (forall x y. equiv_norm (long_zero x) (long_zero y))'
	)
}

abort () {
	echo "expected input Bench.(REPR).(NBE/Norm).(Eager/Lazy).Size(SIZE).(Load/Interpret).fst" &>2
	echo " (the Load is only used for the module name and file, otherwise ignored)" &>2

}

IFS='.' read -r -a array <<< "$1"

if ! [ x"${array[0]}" == x"Bench" ]; then
	abort
fi
REPR=${array[1]}

if [ x"${array[2]}" == x"NBE" ]; then
	use_nbe=true
elif [ x"${array[2]}" == x"Norm" ]; then
	use_nbe=false
else
	abort
fi

if ! [ x"${array[3]}" == x"Eager" ]; then
	use_eager=true
elif ! [ x"${array[3]}" == x"Lazy" ]; then
	use_eager=false
else
	abort
fi

LEN=${array[4]}
LEN=${LEN/Size/}

if ! [ x"${array[5]}" == x"Load" ]; then
	use_load=true
elif ! [ x"${array[5]}" == x"Interpret" ]; then
	use_load=false
else
	abort
fi

make $REPR $use_nbe $use_eager $LEN $use_load "$1"
