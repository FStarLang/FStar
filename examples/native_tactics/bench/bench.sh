#!/bin/bash

set -ue

# Benchmarking script

# All functions below share this calling convention:
# $1: List/Fun
# $2: true (for NBE) / false (for interpreter)
# $3: true for eager embeddings
# $4: size of test (careful: super-exponential runtime)
# $5: use --load (only meaningful for `run`)

modulename () {
	REPR=$1
	use_nbe=$2
	use_eager=$3
	LEN=$4

	NBE=
	EAGER=
               
	if $use_nbe; then
		NBE=NBE
	fi
	if $use_eager; then
		EAGER=Eager
	fi
	echo "Imp.${REPR}.${EAGER}Driver${NBE}.Size${LEN}"
}

make () {
	REPR=$1
	use_nbe=$2
	use_eager=$3
	LEN=$4
	_LOAD=$5

	STEPS=
               
	if $use_nbe; then
		STEPS="${STEPS} nbe;"
	fi

	MODULE=$(modulename "$@")
	MODULE_PLAIN=${MODULE//./_}

	(
	exec 1> $MODULE.fst;
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
                         delta_attr unfold_defs; '"$STEPS"'
                         primops] e

let norm_assert (p:Type) : Lemma (requires (normal p)) (ensures True) = ()

#set-options "--no_smt"
[@tcdecltime]
let test_'"$MODULE_PLAIN"' = norm_assert (forall x y. equiv_norm (long_zero x) (long_zero y))'
	)
}

test () {
	make "$@"
	run "$@"
}

run () {
	MODULE=$(modulename "$@")
	use_load=$5
	LOAD=
	if $use_load; then
		LOAD="${LOAD} --load Registers.$REPR"
	fi
	EAGER=
	if $use_eager; then
		EAGER=--eager_embedding
	fi
	echo ../../../bin/fstar.exe ${LOAD} ${EAGER} ${MODULE}.fst --include ..
	../../../bin/fstar.exe ${LOAD} ${EAGER} ${MODULE}.fst --include ..
}

bench_all () {
	for repr  in List Fun   ; do
	for nbe   in true false ; do
	for eager in false ; do
	for load  in true false ; do
	for len   in $(seq 5 7) ; do
		# NOTE! We use parentheses to run in a subshell and not
		# leak the global variables across invocations. Do NOT delete them.
		(test $repr $nbe $eager $len $load)
	done; done; done; done; done
}

for BASE in Imp.List Imp.Fun Registers.List Registers.Fun; do
	../../../bin/fstar.exe ../${BASE}.fst --codegen Plugin --extract ${BASE} --include ..
done

bench_all
