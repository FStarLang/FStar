#!/bin/bash

D=$(dirname $0)
for arity in $(seq 2 14); do
    $D/mk_tuple.sh false $arity > ulib/FStar.Tuple$arity.fst
done

for arity in $(seq 3 5); do
    $D/mk_tuple.sh true $arity > ulib/FStar.DTuple$arity.fst
done
