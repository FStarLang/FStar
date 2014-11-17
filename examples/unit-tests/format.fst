(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module Format
open Prims.PURE
open String
open Array

type message = seq byte
type msg (l:nat) = m:message{length m==l}

(* Here's a small proof that append is injective. 
   To use this property, you have to explicitly call append_inj yourself (with an implicit first arg) *)
val append_inj: #l:nat
               -> b1:msg l -> b2:message
               -> c1:msg l -> c2:message{append b1 b2==append c1 c2}
               -> Lemma
                      (ensures (Equal b1 c1 /\ Equal b2 c2))
let rec append_inj l b1 b2 c1 c2 = match l with
  | 0 -> ()
  | _ -> append_inj #(l - 1) (slice b1 1 l) b2 (slice c1 1 l) c2


(* The same proof again, 
   But, if you give it a "Lemma" type the solver 
   will use the lemma as needed to prove other goals. *)
val append_inj_lemma: l:nat (* NS: should eventually be able to drop this argument, once we have a syntax for decreases clause; for now, we need it to prove termination. *)
               -> b1:message -> b2:message
               -> c1:message -> c2:message
               -> Lemma (requires (length b1==l /\ length b1==length c1 /\ append b1 b2==append c1 c2))
                        (ensures (Equal b1 c1 /\ Equal b2 c2))
                 //(*[ SMTPat (append b1 b2); SMTPat (append c1 c2)] once we remove l:nat, adding these patterns will improve solver performance *)
let rec append_inj_lemma l b1 b2 c1 c2 (* {decreases (length b1)} *) = 
  match length b1 with
  | 0 -> ()
  | _ -> append_inj_lemma (l - 1) (slice b1 1 l) b2 (slice c1 1 l) c2

let tag0 = create 1 0uy
let tag1 = create 1 1uy

logic type UInt16 (i:int) = (0 <= i /\ i < 65536)
type uint16 = i:int{UInt16 i}

assume val utf8: s:string -> Tot (m:message{length m <= strlen s}) (* this spec is accurate for ASCII strings *)
assume UTF8_inj: forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}  Equal (utf8 s0) (utf8 s1) ==> s0==s1

assume val uint16_to_bytes: uint16 -> Tot (msg 2)
assume UINT16_inj: forall s0 s1. Equal (uint16_to_bytes s0) (uint16_to_bytes s1)
                             ==> s0==s1

type string16 = s:string{UInt16 (length (utf8 s))}

val request : string -> Tot message
let request s = append tag0 (utf8 s)

val response: string16 -> string -> Tot message
let response s t =
  let lb = uint16_to_bytes (length (utf8 s)) in
  append tag1 (append lb
                      (append (utf8 s)
                              (utf8 t)))

val req_resp_distinct: s:string -> s':string16 -> t':string
                     -> Lemma (ensures (~(Equal (request s) (response s' t'))))
let req_resp_distinct s s' t' = ()

val req_inj: s1:string -> s2:string{request s1=request s2} -> Lemma (ensures (s1==s2))
let req_inj s1 s2 = ()

val resp_components_corr: s1:string16 
                       -> t1:string 
                       -> s2:string16
                       -> t2:string
                       -> Lemma (requires (response s1 t1 == response s2 t2))
                                (ensures  (s1==s2 /\ t1==t2))
                                [SMTPat (response s1 t1); SMTPat (response s2 t2)]
let resp_components_corr s1 t1 s2 t2 = ()

val req_components_corr: s1:string
                      -> s2:string
                      -> Lemma (requires (request s1 == request s2))
                               (ensures  (s1==s2))
                               [SMTPat (request s1); SMTPat (request s2)]
let req_components_corr s1 s2 = ()
