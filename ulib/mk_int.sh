#!/bin/bash

for i in 8 16 31 32 63 64; do
  f=FStar.Int$i.fst
  cat > $f <<EOF
module FStar.Int$i

let n = $i

EOF
  cat FStar.IntN.fstp >> $f
done
