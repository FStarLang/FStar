#!/usr/bin/env bash

for i in 8 16 31 32 63 64 128; do
  # generate interface
  f=FStar.Int$i.fsti
  cat > $f <<EOF
module FStar.Int$i
(* This module generated automatically using [mk_int.sh] *)

let n = $i

EOF
  cat FStar.IntN.fstip >> $f
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

val mul_wide: a:Int64.t -> b:Int64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Int64.v a * Int64.v b))
EOF
  fi

  # generate implementation
  f=FStar.Int$i.fst
  cat > $f <<EOF
module FStar.Int$i
(* This module generated automatically using [mk_int.sh] *)

EOF
  cat FStar.IntN.fstp >> $f
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

let mul_wide a b =
  assume (size (Int64.v a * Int64.v b) n);
  Mk ((Int64.v a) * (Int64.v b))
EOF
  fi
done

for i in 8 16 31 32 63 64; do
  # generate interface
  f=FStar.UInt$i.fsti
  cat > $f <<EOF
module FStar.UInt$i
(* This module generated automatically using [mk_int.sh] *)

let n = $i

EOF
  cat FStar.UIntN.fstip >> $f
  if [ $i -eq 8 ]; then
      cat >> $f <<EOF
unfold inline_for_extraction let byte = t
// workaround for issue #1088
val __dummy: unit
EOF
  fi

  # generate implementation
  f=FStar.UInt$i.fst
  cat > $f <<EOF
module FStar.UInt$i
(* This module generated automatically using [mk_int.sh] *)

EOF
  cat FStar.UIntN.fstp >> $f
  if [ $i -eq 8 ]; then
      cat >> $f <<EOF
let __dummy = ()
EOF
  fi
done

sed -i.bak 's/UInt32\.//g' FStar.UInt32.fst
sed -i.bak 's/UInt32\.//g' FStar.UInt32.fsti
