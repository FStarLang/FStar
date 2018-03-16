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
open FStar.Bytes            //This shadows length, index etc. from FStar.Seq, for no good reason?
open FStar.Seq              //It's really important for FStar.Seq.index to have precedence for proper use of the lemmas in FStar.Seq
open FStar.Classical

type message = bytes
type msg (l:nat) = lbytes l

(* ----- a lemma on array append *)
val append_inj_lemma: b1:message -> b2:message {UInt.fits (Bytes.length b1 + Bytes.length b2) 32}
                   -> c1:message -> c2:message {UInt.fits (Bytes.length c1 + Bytes.length c2) 32}
                   -> Lemma (requires (Bytes.length b1==Bytes.length c1 /\ b2t ((Bytes.append b1 b2) = (Bytes.append c1 c2))))
                            (ensures (Bytes.equal b1 c1 /\ Bytes.equal b2 c2))
                            [SMTPat (Bytes.append b1 b2); SMTPat (Bytes.append c1 c2)] (* given to the SMT solver *)
let append_inj_lemma b1 b2 c1 c2 =
  lemma_append_len_disj (reveal b1) (reveal b2) (reveal c1) (reveal c2);
  Classical.forall_intro #_ #(fun (x:(i:nat{i < Bytes.length b1})) -> Bytes.index b1 x == Bytes.index c1 x) (lemma_append_inj_l (reveal b1) (reveal b2) (reveal c1) (reveal c2)); //sadly, the 2nd implicit argument has to be provided explicitly
  Classical.forall_intro #_ #(fun (x:(i:nat{i < Bytes.length b2})) -> Bytes.index b2 x == Bytes.index c2 x) (lemma_append_inj_r (reveal b1) (reveal b2) (reveal c1) (reveal c2))  //should fix this soon (NS)

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
let iutf8 m = FStar.Bytes.iutf8 m*)

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8_encode s0); (utf8_encode s1)}
    Bytes.equal (utf8_encode s0) (utf8_encode s1) ==> s0==s1

val uint16_to_bytes: u:uint16{repr_bytes u <= 2} -> Tot (msg 2)

let uint16_to_bytes u = bytes_of_int 2 u

assume UINT16_inj: forall s0 s1. Bytes.equal (uint16_to_bytes s0) (uint16_to_bytes s1) ==> s0==s1

type string16 = s:string{uInt16 (String.length s)} (* up to 65K *)
type string30 = (s:string{UInt.fits (String.length s) 30}) 

(* =============== the formatting we use for authenticated RPCs *)

val request : string30 -> Tot message
val response: (s:string16{UInt.fits (String.length s) 16}) -> string30 -> Tot message

(* -------- implementation *)

let tag0 = Bytes.create 1ul 0uy
let tag1 = Bytes.create 1ul 1uy

let request s = Bytes.append tag0 (utf8_encode s)

let response s t =
  let us = utf8_encode s in
  let lus = min (Bytes.length us) 65535 in
  lemma_repr_bytes_values lus;
  let lb = uint16_to_bytes lus in
  let us = utf8_encode s in
  let ut = utf8_encode t in
  assume (UInt.fits (Bytes.length us + Bytes.length ut) 30);
  Bytes.append tag1 (Bytes.append lb (Bytes.append us ut))


(* ------- 3 lemmas on message formats:

   - requests and responses are distinct
   - requests are injective on their argument
   - responses are injective on both their arguments

   Note that we do not export a "spec" of the request and response
   functions---they just return messages---so these three lemmas are
   sufficient *)


val req_resp_distinct:
  s:string30 -> s':string16 -> t':string30 ->
  Lemma (requires True)
        (ensures (request s <> response s' t'))
        [SMTPat (request s); SMTPat (response s' t')]

val req_injective:
  s0:string30 -> s1:string30 ->
  Lemma (requires (Bytes.equal (request s0) (request s1)))
        (ensures  (s0==s1))
        (*[SMTPat (request s0); SMTPat (request s1)]*)

val resp_injective:
  s0:string16 -> t0:string30 -> s1:string16 -> t1:string30 ->
  Lemma (requires (Bytes.equal (response s0 t0) (response s1 t1)))
        (ensures  (s0==s1 /\ t0==t1))
        [SMTPat (response s0 t0); SMTPat (response s1 t1)]


// BEGIN: FormatProofsEx
let req_resp_distinct s s' t' = admit()

let req_injective s0 s1 = admit()

let resp_injective s0 t0 s1 t1 = admit()
// END: FormatProofsEx
