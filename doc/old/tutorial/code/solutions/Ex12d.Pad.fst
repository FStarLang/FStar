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
module Ex12d.Pad

open FStar.UInt8
open FStar.Seq


type uint8 = FStar.UInt8.t

(* a coercion; avoid it? *)
assume val n2b: n:nat {( n < 256 )} -> Tot uint8
assume val b2n: b:uint8 -> Tot (n:nat { (n < 256) /\ n2b n = b })

type bytes = seq byte (* concrete byte arrays *) 
type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32 
type block = nbytes blocksize
type text = b:bytes {(length b < blocksize)}

// BEGIN: CreatePaddingT
val pad: n:nat { 1 <= n /\ n <= blocksize } -> Tot (nbytes n)
// END: CreatePaddingT

let pad n = 
  Seq.create n (n2b (n-1))  

(* pad 1 = [| 0 |]; pad 2 = [| 1; 1 |]; ... *)

// BEGIN: EncodePaddingT
val encode: a: text -> Tot block
// END: EncodePaddingT
let encode a = append a (pad (blocksize - length a))

// BEGIN: DecodePaddingT
val decode: b:block -> option (t:text { equal b (encode t) })
// END: DecodePaddingT
let decode (b:block) = 
  let padsize = b2n(index b (blocksize - 1)) + 1 in
  if op_LessThan padsize blocksize then 
    let (plain,padding) = split b (blocksize - padsize) in
    if  Seq.eq padding (pad padsize)
    then Some plain
    else None   
  else None
