(*--build-config
    options:--z3timeout 10 --verify_module CntFormat --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    other-files:
            ext.fst classical.fst
            set.fsi set.fst
            heap.fst st.fst all.fst
            string.fst list.fst
            seq.fsi seqproperties.fst
            ../../contrib/Platform/fst/Bytes.fst
            io.fsti
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

module CntFormat
open Prims.PURE
open FStar.Bytes
open FStar.String
open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes

type message = bytes
type msg (l:nat) = m:message{length m==l}

(* ----- a lemma on array append *)
val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 /\  Seq.Eq (append b1 b2) (append c1 c2)))
                            (ensures (Seq.Eq b1 c1 /\ Seq.Eq b2 c2))
                            [SMTPat (append b1 b2); SMTPat (append c1 c2)] (* given to the SMT solver *)
let append_inj_lemma b1 b2 c1 c2 =
    lemma_append_len_disj b1 b2 c1 c2;
    Classical.forall_intro (lemma_append_inj_l b1 b2 c1 c2);
    Classical.forall_intro (lemma_append_inj_r b1 b2 c1 c2)

(* ----- from strings to bytestring and back *)
type uint = i:int{0 <= i}
type pint = i:int{1 <= i}

type uint16 = i:nat{repr_bytes i <= 2}
type uint32 = i:nat{repr_bytes i <= 4}

(*assume val utf8:
  s:string  -> Tot (m:message{length m <= strlen s})*)

  (* this spec is accurate for ASCII strings *)

(*assume val iutf8: m:message -> s:string{utf8 s == m}*)
(*assume val iutf8T: m:message -> Tot (s:string{utf8 s == m})*)

(* val iutf8T: m:message -> s:option string{match s with *)
(* 					 | Some s' -> iutf8 s' = m *)
(* 					 | None -> true} *)
(* let iutf8T m = *)
(*   try Some (iutf8 m) *)
(*   with _ -> None *)

let uint16_to_bytes = bytes_of_int 2
let uint32_to_bytes = bytes_of_int 4
let bytes_to_uint16 (x:msg 2) = int_of_bytes x
let bytes_to_uint32 (x:msg 4) = int_of_bytes x

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
     Seq.Eq (utf8 s0) (utf8 s1) ==> s0==s1

type string16 = s:string{repr_bytes (length (utf8 s)) <= 2} (* up to 65K *)


(* =============== the formatting we use for authenticated RPCs *)

val request : string -> Tot message
val response: string16 -> string -> Tot message

(* -------- implementation *)

let tag0 = createBytes 1 0uy
let tag1 = createBytes 1 1uy
let tag2 = createBytes 1 2uy

let request s = tag0 @| (utf8 s)

val response: s:string{ repr_bytes (length (utf8 s)) <= 2} -> string -> Tot message
let response s t =
  let lb = uint16_to_bytes (length (utf8 s)) in
  tag1 @| (lb @| ( (utf8 s) @| (utf8 t)))

val signal_size: int
let signal_size = 6 (* Bytes *)

val signal : uint32 -> uint16 -> Tot (msg signal_size)
let signal s c =
  let s_b = uint32_to_bytes s in
  let c_b = uint16_to_bytes c in
  (s_b @| c_b)

val signal_split : m:msg signal_size -> Tot (x:(uint32 * uint16)
    { m = signal (fst x) (snd x)})
let signal_split sc =
    let (s_b, c_b) = split_eq sc 4 in
    (bytes_to_uint32 s_b, bytes_to_uint16 c_b)

assume val signal_components_corr:
  s0:uint32 -> c0:uint16 -> s1:uint32 -> c1:uint16 ->
  Lemma (requires (Eq (signal s0 c0) (signal s1 c1)))
        (ensures  (s0 = s1 /\ c0 = c1))
        [SMTPat (signal s0 c0); SMTPat (signal s1 c1)]
(*let signal_components_corr s0 c0 s1 c1 = ()*)
