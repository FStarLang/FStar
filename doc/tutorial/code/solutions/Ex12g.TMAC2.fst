(*
   Copyright 2008-2018 Microsoft Research

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
module Ex12g.TMAC2

open FStar.Seq
open Ex12.Pad
open FStar.Mul 
//allows to use * for op_Multiply as long as it's not needed for tuples

module BMAC = Ex12.BMAC

// BEGIN: TMAC2
type text2 = b:bytes { length b <=  blocksize } 

let keysize = 2 * BMAC.keysize
let macsize = BMAC.macsize
noeq type key = | Keys: k0:BMAC.key -> k1:BMAC.key -> key
type tag = BMAC.tag

type bspec0 (spec: (text2 -> Type)) (b:block) =
  (forall (t:text). equal b (encode t) ==> spec t)

type bspec1 (spec: (text2 -> Type)) (b:block) = 
  spec b

assume type key_prop : key -> text2 -> Type

type pkey (p:(text2 -> Type)) = 
  k:key{ key_prop k == p
      /\ BMAC.key_prop (Keys?.k0 k) == bspec0 p
      /\ BMAC.key_prop (Keys?.k1 k) == bspec1 p }

val keygen: p:(text2 -> Type) -> pkey p
val mac:    p:(text2 -> Type) -> k:pkey p -> t:text2{p  t} -> tag
val verify: p:(text2 -> Type) -> k:pkey p -> t:text2 -> tag -> b:bool{b ==> p t}


let keygen (spec: text2 -> Type) = 
  let k0 = BMAC.keygen (bspec0 spec) in
  let k1 = BMAC.keygen (bspec1 spec) in
  let k = Keys k0 k1 in
  assert (BMAC.key_prop k0 == bspec0 spec);
  assert (BMAC.key_prop k1 == bspec1 spec);
  assume (key_prop k == spec);
  k
 

let mac p (Keys k0 k1) t = 
  if length t < blocksize 
  then BMAC.mac k0 (encode t)
  else BMAC.mac k1 t

let verify p (Keys k0 k1) t tag =   
  if length t < blocksize
  then BMAC.verify k0 (encode t) tag
  else BMAC.verify k1 t tag
// END: TMAC2
