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
module Bloom.Format

open FStar.Seq

type uint = i:int{0 <= i}
type pint = i:int{1 <= i}

type message = seq byte
type msg (i:pint) = m:message{length m = i}

val max_int : i:pint -> Tot uint
let rec max_int i =
  if i > 1 then
    256 * max_int (i-1)
  else 256

type UInt (len:pint) (i:int) = (0 <= i /\ i < max_int len)
type ulint (len:pint) = i:int{UInt len i}
type uint16 = i:int{UInt 2 i}
let uint16_max = (max_int 2) - 1
type uint32 = i:int{UInt 4 i}

assume val ulint_to_bytes: len:pint -> ulint len -> Tot (msg len)
assume val bytes_to_ulint: len:pint -> x:msg len -> Tot (y:ulint len{ulint_to_bytes len y == x})
assume UINT_inj: forall len s0 s1. Seq.Eq (ulint_to_bytes len s0) (ulint_to_bytes len s1) ==> s0==s1

val uint16_to_bytes: uint16 -> Tot (msg 2)
let uint16_to_bytes = ulint_to_bytes 2
let uint32_to_bytes = ulint_to_bytes 4
val bytes_to_uint16: msg 2 -> Tot uint16
let bytes_to_uint16 = bytes_to_ulint 2
let bytes_to_uint32 = bytes_to_ulint 4

let tag0 = create 1 0uy

val signal_size: int
let signal_size = 7 (* Bytes *)

val signal : uint32 -> uint16 -> Tot (msg signal_size)
let signal s c =
  let s_b = uint32_to_bytes s in
  let c_b = uint16_to_bytes c in
  append tag0 (append s_b c_b)

val signal_split : m:msg signal_size -> Tot (x:option (uint32 * uint16)
    { Some? x ==> m = signal (fst (Some.v x)) (snd (Some.v x))})
let signal_split m =
  let (t, sc) = split_eq m 1 in
  if t = tag0 then
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
