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
module Ex12b2.Format

open FStar.String
open Platform.Bytes         //This shadows length, index etc. from FStar.Seq, for no good reason?
open FStar.Seq              //It's really important for FStar.Seq.index to have precedence for proper use of the lemmas in FStar.Seq
open FStar.Classical

// BEGIN: FormatMsg
type message = bytes
type msg (l:nat) = lbytes l
// END: FormatMsg

(* ----- a lemma on array append *)
// BEGIN: FormatAppend
val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 /\ b2t (Seq.eq (b1 @| b2) (c1 @| c2))))
                            (ensures (b2t (Seq.eq b1 c1) /\ b2t (Seq.eq b2 c2)))
                            [SMTPat (b1 @| b2); SMTPat (c1 @| c2)] (* given to the SMT solver *)
// END: FormatAppend
let append_inj_lemma b1 b2 c1 c2 =
  lemma_append_len_disj b1 b2 c1 c2;
  Classical.forall_intro #_ #(fun (x:(i:nat{i < length b1})) -> index b1 x == index c1 x) (lemma_append_inj_l b1 b2 c1 c2); //sadly, the 2nd implicit argument has to be provided explicitly
  Classical.forall_intro #_ #(fun (x:(i:nat{i < length b2})) -> index b2 x == index c2 x) (lemma_append_inj_r b1 b2 c1 c2)  //should fix this soon (NS)

abstract val lemma_eq_intro: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (Seq.length s1 = Seq.length s2
               /\ (forall (i:nat{i < Seq.length s1}).{:pattern (Seq.index s1 i); (Seq.index s2 i)} (Seq.index s1 i == Seq.index s2 i))))
     (ensures (Seq.equal s1 s2))
     [SMTPat (Seq.equal s1 s2)]
let lemma_eq_intro #a s1 s2 = ()

(* ----- from strings to bytestring and back *)

type uInt16 (i:int) = (0 <= i /\ i < 65536)
type uint16 = i:int{uInt16 i}

(*val utf8:
  s:string  -> Tot (m:message{length m <= strlen s})
  (* this spec is accurate for ASCII strings *)
let utf8 s = magic()*)

(*val iutf8: m:message -> s:string{utf8 s == m}
let iutf8 m = Platform.Bytes.iutf8 m*)

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    b2t (Seq.eq (utf8 s0) (utf8 s1)) ==> s0==s1

val uint16_to_bytes: u:uint16{repr_bytes u <= 2} -> Tot (msg 2)

let uint16_to_bytes u = bytes_of_int 2 u

assume UINT16_inj: forall s0 s1. b2t (Seq.eq (uint16_to_bytes s0) (uint16_to_bytes s1)) ==> s0==s1

type string16 = s:string{uInt16 (length (utf8 s))} (* up to 65K *)


(* =============== the formatting we use for authenticated RPCs *)

// BEGIN: FormatReqRes
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
// END: FormatReqRes

(* ------- 3 lemmas on message formats:

   - requests and responses are distinct
   - requests are injective on their argument
   - responses are injective on both their arguments

   Note that we do not export a "spec" of the request and response
   functions---they just return messages---so these three lemmas are
   sufficient *)

// BEGIN: FormatLemmas
val req_resp_distinct:
  s:string -> s':string16 -> t':string ->
  Lemma (requires True)
        (ensures (request s <> response s' t'))
        [SMTPat (request s); SMTPat (response s' t')]

val req_injective:
  s0:string -> s1:string ->
  Lemma (requires (b2t (Seq.eq (request s0) (request s1))))
        (ensures  (s0==s1))
        (*[SMTPat (request s0); SMTPat (request s1)]*)

val resp_injective:
  s0:string16 -> t0:string -> s1:string16 -> t1:string ->
  Lemma (requires (b2t (Seq.eq (response s0 t0) (response s1 t1))))
        (ensures  (s0==s1 /\ t0==t1))
        [SMTPat (response s0 t0); SMTPat (response s1 t1)]
// END: FormatLemmas

// BEGIN: FormatProofs
let req_resp_distinct s s' t' = 
  lemma_repr_bytes_values (length (utf8 s));
  lemma_repr_bytes_values (length (utf8 s'));
  assert (Seq.index (request s) 0 == 0uy);
  assert (Seq.index (response s' t') 0 == 1uy)

let req_injective s0 s1 = ()

let resp_injective s0 t0 s1 t1 =
  lemma_repr_bytes_values (length (utf8 s0));
  lemma_repr_bytes_values (length (utf8 s1))
// END: FormatProofs
