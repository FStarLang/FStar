#!/usr/bin/env bash

for i in 8 16 31 32 63 64 128; do
  f=FStar.Int$i.fst
  cat > $f <<EOF
module FStar.Int$i
(* This module generated automatically using [mk_int.sh] *)

unfold let n = $i

EOF
  cat FStar.IntN.fstp >> $f
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

abstract
val mul_wide: a:Int64.t -> b:Int64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Int64.v a * Int64.v b))
let mul_wide a b = 
  assume (size (Int64.v a * Int64.v b) n);
  Mk ((Int64.v a) * (Int64.v b))
EOF
  fi
done

for i in 8 16 31 32 63 64; do
  f=FStar.UInt$i.fst
  cat > $f <<EOF
module FStar.UInt$i
(* This module generated automatically using [mk_int.sh] *)

unfold let n = $i

EOF
  cat FStar.UIntN.fstp >> $f
  if [ $i -eq 8 ]; then
    echo "unfold inline_for_extraction type byte = t" >> $f
  fi
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

abstract
val mul_wide: a:UInt64.t -> b:UInt64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = UInt64.v a * UInt64.v b))
let mul_wide a b = 
  assume (size (UInt64.v a * UInt64.v b) n);
  Mk ((UInt64.v a) * (UInt64.v b))
EOF
  fi
done

sed -i.bak 's/UInt32.//g' FStar.UInt32.fst
