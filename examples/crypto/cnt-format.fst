(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module Format --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:LIB=../../lib;
    other-files:
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst $LIB/all.fst
            $LIB/string.fst $LIB/list.fst
            $LIB/seq.fsi $LIB/seqproperties.fst
            $LIB/io.fsti
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

module Format
open Prims.PURE
open FStar.String
open FStar.Seq
open FStar.SeqProperties

type message = seq byte
type msg (l:nat) = m:message{length m==l}

(* ----- a lemma on array append *)
val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 /\  Seq.Eq (append b1 b2) (append c1 c2)))
                            (ensures (Seq.Eq b1 c1 /\ Seq.Eq b2 c2))
                            [SMTPat (append b1 b2); SMTPat (append c1 c2)] (* given to the SMT solver *)
let append_inj_lemma b1 b2 c1 c2 =
    lemma_append_len_disj b1 b2 c1 c2;
    erase (Classical.forall_intro (lemma_append_inj_l b1 b2 c1 c2));
    erase (Classical.forall_intro (lemma_append_inj_r b1 b2 c1 c2));
    ()

(* ----- from strings to bytestring and back *)
type uint = i:int{0 <= i}
type pint = i:int{1 <= i}
(*assume *)
val max_int : i:pint -> Tot uint
let rec max_int i =
  if i > 1 then
    256 * max_int (i-1)
  else 256

logic type UInt (len:pint) (i:int) = (0 <= i /\ i < max_int len)
type ulint (len:pint) = i:int{UInt len i}
type uint16 = i:int{UInt 2 i}
let uint16_max = (max_int 2) - 1
type uint32 = i:int{UInt 4 i}

assume val utf8:
  s:string  -> Tot (m:message{length m <= strlen s})
  (* this spec is accurate for ASCII strings *)

assume val iutf8: m:message -> s:string{utf8 s == m}
assume val iutf8T: m:message -> Tot (s:string{utf8 s == m})

(* val iutf8T: m:message -> s:option string{match s with *)
(* 					 | Some s' -> iutf8 s' = m *)
(* 					 | None -> true} *)
(* let iutf8T m = *)
(*   try Some (iutf8 m) *)
(*   with _ -> None *)

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
     Seq.Eq (utf8 s0) (utf8 s1) ==> s0==s1

assume val ulint_to_bytes: len:pint -> ulint len -> Tot (msg len)
assume val bytes_to_ulint: len:pint -> x:msg len -> Tot (y:ulint len{ulint_to_bytes len y == x})
assume UINT_inj: forall len s0 s1. Seq.Eq (ulint_to_bytes len s0) (ulint_to_bytes len s1) ==> s0==s1

let uint16_to_bytes = ulint_to_bytes 2
let uint32_to_bytes = ulint_to_bytes 4
let bytes_to_uint16 = bytes_to_ulint 2
let bytes_to_uint32 = bytes_to_ulint 4

type string16 = s:string{UInt 16 (length (utf8 s))} (* up to 65K *)


(* =============== the formatting we use for authenticated RPCs *)

val request : string -> Tot message
val response: string16 -> string -> Tot message

(* -------- implementation *)

let tag0 = create 1 0uy
let tag1 = create 1 1uy
let tag2 = create 1 2uy

let request s = append tag0 (utf8 s)

val response: s:string{ length (utf8 s) < max_int 2} -> string -> Tot message
let response s t =
  let lb = uint16_to_bytes (length (utf8 s)) in
  append tag1 (append lb (append (utf8 s) (utf8 t)))

val signal_size: int
let signal_size = 7 (* Bytes *)

val signal : uint32 -> uint16 -> Tot (msg signal_size)
let signal s c =
  let s_b = uint32_to_bytes s in
  let c_b = uint16_to_bytes c in
  append tag2 (append s_b c_b)

val signal_split : m:msg signal_size -> Tot (x:option (uint32 * uint16)
    { is_Some x ==> m = signal (fst (Some.v x)) (snd (Some.v x))})
let signal_split m =
  let (t, sc) = split_eq m 1 in
  if t = tag2 then
    let (s_b, c_b) = split_eq sc 4 in
    let (s, c) = (bytes_to_ulint 4 s_b, bytes_to_ulint 2 c_b) in
    Some (s, c)
  else
    None

val signal_components_corr:
  s0:uint32 -> c0:uint16 -> s1:uint32 -> c1:uint16 ->
  Lemma (requires (Seq.Eq (signal s0 c0) (signal s1 c1)))
        (ensures  (s0 = s1 /\ c0 = c1))
        [SMTPat (signal s0 c0); SMTPat (signal s1 c1)]
let signal_components_corr s0 c0 s1 c1 = ()

(* ------- 3 lemmas on message formats:

   - requests are injective on their argument
   - responses are injective on both their arguments
   - requests and responses are distinct

   Note that we do not export a "spec" of the request and response
   functions---they just return messages---so these three lemmas are
   sufficient *)

val req_resp_distinct:
  s:string -> s':string16{ length (utf8 s') < max_int 2} -> t':string ->
  Lemma (requires True)
        (ensures ( ( (request s) <> (response s' t'))))
        [SMTPat (request s); SMTPat (response s' t')]
let req_resp_distinct s s' t' = cut (index tag0 0 == 0uy)

val req_components_corr:
  s0:string -> s1:string ->
  Lemma (requires (Seq.Eq (request s0) (request s1)))
        (ensures  (s0==s1))
let req_components_corr s0 s1 = ()

val resp_components_corr:
  s0:string16{ length (utf8 s0) < max_int 2} -> t0:string -> s1:string16{ length (utf8 s1) < max_int 2} -> t1:string ->
  Lemma (requires (Seq.Eq (response s0 t0) (response s1 t1)))
        (ensures  (s0==s1 /\ t0==t1))
let resp_components_corr s0 t0 s1 t1 = ()
