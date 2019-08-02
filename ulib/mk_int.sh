#!/usr/bin/env bash

for i in 8 16 31 32 63 64 128; do
  f=FStar.Int$i.fst
  cat > $f <<EOF
(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
