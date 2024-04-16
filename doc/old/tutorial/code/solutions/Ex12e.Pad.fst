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
module Ex12e.Pad

//#set-options "--z3timeout 20"
open FStar.UInt8
open FStar.Seq


type uint8 = FStar.UInt8.t

let n2b = uint_to_t
let b2n = v

type bytes = seq byte (* concrete byte arrays *) 
type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32 
type block = nbytes blocksize
type text = b:bytes {(length b < blocksize)}

val pad: n:nat { 1 <= n /\ n <= blocksize } -> Tot (nbytes n)

let pad n = 
  Seq.create n (n2b (n-1))  

(* pad 1 = [| 0 |]; pad 2 = [| 1; 1 |]; ... *)

val encode: a: text -> Tot block 
let encode a = append a (pad (blocksize - length a))

// BEGIN: PaddingInj
val inj: a: text -> b: text -> Lemma (requires (equal (encode a) (encode b)))
                                     (ensures (equal a b))
                                     [SMTPat (encode a); SMTPat (encode b)]

val lemma_append_inj: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a 
                      {length s1 = length t1 \/ length s2 = length t2}
  -> Lemma (requires (equal (append s1 s2) (append t1 t2)))
           (ensures (equal s1 t1 /\ equal s2 t2))
           [SMTPat (append s1 s2); SMTPat (append t1 t2)]
           //good example to explain patterns.
let lemma_append_inj #a s1 s2 t1 t2 = Seq.lemma_append_inj #a s1 s2 t1 t2

let inj a b = 
  if length a = length b
  then () 
       //lemma_append_inj a (pad (blocksize - length a)) b  (pad (blocksize - length a))
       //no longer needed because of pattern
  else let aa = encode a in
       let bb = encode b in
       cut (index aa 31 <> index bb 31)
// END: PaddingInj

       
val decode: b:block -> option (t:text { equal b (encode t) })
let decode (b:block) = 
  let padsize = b2n(index b (blocksize - 1)) + 1 in
  if op_LessThan padsize blocksize then 
    let (plain,padding) = split b (blocksize - padsize) in
    if  Seq.eq padding (pad padsize)
    then Some plain
    else None   
  else None
