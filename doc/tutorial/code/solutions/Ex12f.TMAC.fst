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
module Ex12f.TMAC

open FStar.Seq

open Ex12.Pad 

module BMAC = Ex12.BMAC


let keysize = BMAC.keysize
let macsize = BMAC.macsize
type key = BMAC.key
type tag = BMAC.tag

type bspec (spec: (text -> Type)) (b:block) = 
  (forall (t:text). equal b (encode t) ==> spec t)


assume type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = 
  k:key{key_prop k == p /\ BMAC.key_prop k == bspec p}
  

val keygen: p:(text -> Type) -> pkey p
val mac:    p:(text -> Type) -> k:pkey p -> t:text{p t} -> tag
val verify: p:(text -> Type) -> k:pkey p -> t:text -> tag -> b:bool{b ==> p t}

// BEGIN: TMAC
let keygen (spec: text -> Type) = 
  let k = BMAC.keygen (bspec spec) in
  assume (key_prop k == spec);
  k

let mac (p:text -> Type) k t = BMAC.mac k (encode t)

let verify p k t tag = BMAC.verify k (encode t) tag
// END: TMAC
