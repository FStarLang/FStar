(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Hash

(* The Cherry implementation.  Like the OCaml one (FStarC.Hash-ocaml.fst), a
   hash code is a 63-bit two's complement integer, here the low 63 bits of a
   [U64.t] with the top bit clear: wrapping 64-bit arithmetic agrees with
   63-bit arithmetic on the low 63 bits, so masking after each multiplication
   is all it takes.  [mix], [cmp_hash] and [of_int] on integers below 2^62 in
   magnitude agree with the OCaml build; [of_string] and [of_int] on larger
   integers do not, so hash codes (and the Tm_inner_let_rec_... SMT symbols
   named after them) differ between the two builds. *)

open FStarC.Effect
module U64 = FStar.UInt64

type hash_code = U64.t

let mask63 (x:U64.t) : U64.t = U64.logand x 0x7fffffffffffffffUL

let to_int (h:hash_code) : int =
  let n = U64.v h in
  if n >= 0x4000000000000000 then n - 0x8000000000000000 else n

let cmp_hash (x y:hash_code) : int = to_int (mask63 (U64.sub_mod x y))

let mix_ (a b:hash_code) : hash_code =
  let c = 0x1bd1e9955bd1e995UL in
  let k = mask63 (U64.mul_mod b c) in
  let k = U64.logxor k (U64.shift_right k 31ul) in
  let k = mask63 (U64.mul_mod k c) in
  mask63 (U64.mul_mod (U64.logxor a k) c)

(* The 63-bit chunks of [n], least significant first, mixed into [acc]. *)
let rec mix_chunks (acc:hash_code) (n:nat) : Tot hash_code (decreases n) =
  if n = 0 then acc
  else mix_chunks (mix_ acc (U64.uint_to_t (n % 0x8000000000000000)))
                  (n / 0x8000000000000000)

(* Integers that fit are their own hash code, as in the OCaml build. *)
let of_int (i:int) : hash_code =
  if -0x4000000000000000 <= i && i < 0x4000000000000000 then
    U64.uint_to_t (i % 0x8000000000000000)
  else if i < 0 then mix_chunks 2UL (-i)
  else mix_chunks 1UL i

(* 64-bit FNV-1a over the UTF-8 bytes, in ulib/c/cherry.c. *)
[@@custard_extern "cherry_str_fnv1a"]
private assume val str_fnv1a : string -> U64.t

let of_string (s:string) : hash_code = mask63 (str_fnv1a s)

(* See FStarC.Hash-ocaml.fst. *)
let mix (a b:hash_code) : hash_code = mix_ a b

let string_of_hash_code (h:hash_code) : string = string_of_int (to_int h)
