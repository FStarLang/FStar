(*--build-config
    options:--z3timeout 10 --verify_module Formatting --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:MITLS=../../../mitls-fstar/libs/fst/;
    other-files:
            FStar.FunctionalExtensionality.fst FStar.Classical.fst
            FStar.Set.fsi FStar.Set.fst
            FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.String.fst FStar.List.fst
            seq.fsi FStar.SeqProperties.fst
            ../../contrib/Platform/fst/Bytes.fst
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
open FStar.String
open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes

type message = bytes
type msg (l:nat) = lbytes l

(* ----- a lemma on array append *)
val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 /\ Seq.Eq (b1 @| b2) (c1 @| c2)))
                            (ensures (Seq.Eq b1 c1 /\ Seq.Eq b2 c2))
                            [SMTPat (b1 @| b2); SMTPat (c1 @| c2)] (* given to the SMT solver *)
let rec append_inj_lemma b1 b2 c1 c2 =
  lemma_append_len_disj b1 b2 c1 c2;
  Classical.forall_intro (lemma_append_inj_l b1 b2 c1 c2);
  Classical.forall_intro (lemma_append_inj_r b1 b2 c1 c2)


(* ----- from strings to bytestring and back *)

logic type UInt16 (i:int) = (0 <= i /\ i < 65536)
type uint16 = i:int{UInt16 i}

(*val utf8:
  s:string  -> Tot (m:message{length m <= strlen s})
  (* this spec is accurate for ASCII strings *)
let utf8 s = magic()*)

(*val iutf8: m:message -> s:string{utf8 s == m}
let iutf8 m = Platform.Bytes.iutf8 m*)

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    Seq.Eq (utf8 s0) (utf8 s1) ==> s0==s1

val uint16_to_bytes: u:uint16{repr_bytes u <= 2} -> Tot (msg 2)

let uint16_to_bytes u = bytes_of_int 2 u

assume UINT16_inj: forall s0 s1. Seq.Eq (uint16_to_bytes s0) (uint16_to_bytes s1) ==> s0==s1

type string16 = s:string{UInt16 (length (utf8 s))} (* up to 65K *)


(* =============== the formatting we use for authenticated RPCs *)

val request : string -> Tot message
val response: string16 -> string -> Tot message

(* -------- implementation *)

let tag0 = createBytes 1 0uy
let tag1 = createBytes 1 1uy

let request s = tag0 @| (utf8 s)

let response s t =
  lemma_repr_bytes_values (length (utf8 s));
  let lb = uint16_to_bytes (length (utf8 s)) in
  tag1 @| (lb @| ( (utf8 s) @| (utf8 t)))


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
        (ensures (not( (request s) = (response s' t'))))
        [SMTPat (request s); SMTPat (response s' t')]
let req_resp_distinct s s' t' =
  lemma_repr_bytes_values (length (utf8 s));
  lemma_repr_bytes_values (length (utf8 s'));
  (*lemma_repr_bytes_values (length (utf8 t'));*)
  cut (Seq.index tag0 0 == 0uy)

val req_components_corr:
  s0:string -> s1:string ->
  Lemma (requires (Seq.Eq (request s0) (request s1)))
        (ensures  (s0==s1))
        (*[SMTPat (request s0); SMTPat (request s1)]*)
let req_components_corr s0 s1 = ()

val resp_components_corr:
  s0:string16 -> t0:string -> s1:string16 -> t1:string ->
  Lemma (requires (Seq.Eq (response s0 t0) (response s1 t1)))
        (ensures  (s0==s1 /\ t0==t1))
        [SMTPat (response s0 t0); SMTPat (response s1 t1)]
let resp_components_corr s0 t0 s1 t1 =
  lemma_repr_bytes_values (length (utf8 s0));
  lemma_repr_bytes_values (length (utf8 s1))
