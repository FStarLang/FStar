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

(* ----- two lemmas on array append *) 

(* Here's a small proof that append is injective. 
   To use this property, you have to explicitly call 
   append_inj yourself (with an implicit first arg) *)

val append_inj: #l:nat
               -> b1:msg l -> b2:message
               -> c1:msg l -> c2:message{append b1 b2==append c1 c2}
               -> Lemma (ensures (Equal b1 c1 /\ Equal b2 c2))
let rec append_inj l b1 b2 c1 c2 = match l with
  | 0 -> ()
  | _ -> append_inj #(l - 1) (slice b1 1 l) b2 (slice c1 1 l) c2

(* The same proof again, 
   But, if you give it a "Lemma" type the solver 
   will use the lemma as needed to prove other goals. *)

val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 /\ append b1 b2==append c1 c2))
                            (ensures (Equal b1 c1 /\ Equal b2 c2))
                            (decreases (length b1))
                            [SMTPat (append b1 b2); SMTPat (append c1 c2)] 

let rec append_inj_lemma b1 b2 c1 c2 =
  let l = length b1 in 
  match l with
  | 0 -> ()
  | _ -> append_inj_lemma (slice b1 1 l) b2 (slice c1 1 l) c2


(* ----- from strings to bytestring and back *)

logic type UInt16 (i:int) = (0 <= i /\ i < 65536)
type uint16 = i:int{UInt16 i}

assume val utf8:
  s:string  -> Tot (m:message{length m <= strlen s}) 
  (* this spec is accurate for ASCII strings *)

assume val iutf8: m:message -> s:string{utf8 s == m}

assume UTF8_inj: 
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    Equal (utf8 s0) (utf8 s1) ==> s0==s1

assume val uint16_to_bytes: uint16 -> Tot (msg 2)
assume UINT16_inj: forall s0 s1. Equal (uint16_to_bytes s0) (uint16_to_bytes s1) ==> s0==s1

type string16 = s:string{UInt16 (length (utf8 s))} (* up to 65K *)


(* ----- the formatting we use for authenticated RPCs *) 

let tag0 = create 1 0uy
let tag1 = create 1 1uy

val request : string -> Tot message
let request s = append tag0 (utf8 s)

val response: string16 -> string -> Tot message
let response s t =
  let lb = uint16_to_bytes (length (utf8 s)) in
  append tag1 (append lb (append (utf8 s) (utf8 t)))


(* ------- 3 lemmas on message formats: 

   - requests are injective on their argument
   - responses are injective on both their arguments
   - requests and responses are distinct 

   Note that we do not export a "spec" of the request and response
   functions---they just return messages---so these three lemmas are
   sufficient *) 

val req_resp_distinct: 
  s:string -> s':string16 -> t':string -> 
  Lemma (requires True)
        (ensures (request s <> response s' t'))
        [SMTPat (request s); SMTPat (response s' t')]
(*prove this lemma*)        

val req_components_corr: 
  s0:string -> s1:string -> 
  Lemma (requires (request s0 == request s1))
        (ensures  (s0==s1))
(*prove this lemma*)
        
val resp_components_corr: 
  s0:string16 -> t0:string -> s1:string16 -> t1:string -> 
  Lemma (requires (response s0 t0 == response s1 t1))
        (ensures  (s0==s1 /\ t0==t1))
(*prove this lemma*)
