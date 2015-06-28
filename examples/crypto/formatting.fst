(*--build-config
    options:--admit_fsi Set --verify_module Formatting;
    variables:LIB=../../lib;
    other-files:../../lib/list.fst
      ../../lib/string.fst
      ../../lib/partialmap.fst
--*)

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

module Formatting
open Prims.PURE
open String
open Array

type message = seq byte
type msg (l:nat) = m:message{length m==l}

(* ----- a lemma on array append *)
val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 /\ equal (append b1 b2) (append c1 c2)))
                            (ensures (equal b1 c1 /\ equal b2 c2))
                            [SMTPat (append b1 b2); SMTPat (append c1 c2)] (* given to the SMT solver *)
let rec append_inj_lemma b1 b2 c1 c2 = ()

(* ----- from strings to bytestring and back *)

logic type UInt16 (i:int) = (0 <= i /\ i < 65536)
type uint16 = i:int{UInt16 i}

val utf8:
  s:string  -> Tot (m:message{length m <= strlen s})
  (* this spec is accurate for ASCII strings *)
let utf8 s = magic()

val iutf8: m:message -> s:string{utf8 s == m}
let iutf8 m = magic()

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    equal (utf8 s0) (utf8 s1) ==> s0==s1

val uint16_to_bytes: uint16 -> Tot (msg 2)
let uint16_to_bytes u = magic()
assume UINT16_inj: forall s0 s1. equal (uint16_to_bytes s0) (uint16_to_bytes s1) ==> s0==s1

type string16 = s:string{UInt16 (length (utf8 s))} (* up to 65K *)


(* =============== the formatting we use for authenticated RPCs *)

val request : string -> Tot message
val response: string16 -> string -> Tot message

(* -------- implementation *)

let tag0 = create 1 0uy
let tag1 = create 1 1uy

let request s = append tag0 (utf8 s)

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
        (ensures (not (Array.equal (request s) (response s' t'))))
        [SMTPat (request s); SMTPat (response s' t')]

val req_components_corr:
  s0:string -> s1:string ->
  Lemma (requires (Array.equal (request s0) (request s1)))
        (ensures  (s0==s1))

val resp_components_corr:
  s0:string16 -> t0:string -> s1:string16 -> t1:string ->
  Lemma (requires (Array.equal (response s0 t0) (response s1 t1)))
        (ensures  (s0==s1 /\ t0==t1))

let req_resp_distinct s s' t' = cut (Array.index tag0 0 == 0uy)
let req_components_corr s0 s1 = ()
let resp_components_corr s0 t0 s1 t1 = ()
