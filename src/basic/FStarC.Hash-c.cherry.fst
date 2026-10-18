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

(* The Cherry implementation.  It computes the same hash codes as the OCaml
   one (FStarC.Hash-ocaml.fst), since they are observable: they name symbols
   in SMT queries (Tm_inner_let_rec_...) and are printed by the unit tests.

   A hash code is an OCaml [int], i.e. a 63-bit two's complement integer.  We
   keep its bit pattern in the low 63 bits of a [U64.t], with the top bit
   clear.  Wrapping 64-bit arithmetic agrees with OCaml's on the low 63 bits,
   so masking after each multiplication is all it takes. *)

open FStarC.Effect
module U32 = FStar.UInt32
module U64 = FStar.UInt64

type hash_code = U64.t

let mask63 (x:U64.t) : U64.t = U64.logand x 0x7fffffffffffffffUL

let to_int (h:hash_code) : int =
  let n = U64.v h in
  if n >= 0x4000000000000000 then n - 0x8000000000000000 else n

let cmp_hash (x y:hash_code) : int = to_int (mask63 (U64.sub_mod x y))

(* OCaml's MurmurHash3 steps (runtime/hash.c), on 32 bits. *)
let rotl32 (x:U32.t) (n:U32.t{0 < U32.v n /\ U32.v n < 32}) : U32.t =
  U32.logor (U32.shift_left x n) (U32.shift_right x (U32.sub 32ul n))

let caml_hash_mix_uint32 (h d:U32.t) : U32.t =
  let d = U32.mul_mod d 0xcc9e2d51ul in
  let d = rotl32 d 15ul in
  let d = U32.mul_mod d 0x1b873593ul in
  let h = U32.logxor h d in
  let h = rotl32 h 13ul in
  U32.add_mod (U32.mul_mod h 5ul) 0xe6546b64ul

let caml_final_mix (h:U32.t) : U32.t =
  let h = U32.logxor h (U32.shift_right h 16ul) in
  let h = U32.mul_mod h 0x85ebca6bul in
  let h = U32.logxor h (U32.shift_right h 13ul) in
  let h = U32.mul_mod h 0xc2b2ae35ul in
  U32.logxor h (U32.shift_right h 16ul)

(* [Hashtbl.hash] of a value whose hash mixes in the single word [d] (a
   custom block's hash, or a string's [caml_hash_mix_string]), folded to 30
   bits. *)
let caml_hash_result (h:U32.t) : hash_code =
  FStar.Int.Cast.uint32_to_uint64 (U32.logand (caml_final_mix h) 0x3FFFFFFFul)

(* Zarith's custom hash (ml_z_custom_hash in caml_z.c): the 64-bit limbs of
   the magnitude, least significant first, each as two 32-bit halves, plus
   one if negative. *)
let rec zarith_limbs_hash (acc:U32.t) (n:nat) : Tot U32.t (decreases n) =
  if n = 0 then acc
  else
    let limb = U64.uint_to_t (n % 0x10000000000000000) in
    let lo = FStar.Int.Cast.uint64_to_uint32 limb in
    let hi = FStar.Int.Cast.uint64_to_uint32 (U64.shift_right limb 32ul) in
    let acc = caml_hash_mix_uint32 (caml_hash_mix_uint32 acc lo) hi in
    zarith_limbs_hash acc (n / 0x10000000000000000)

(* Small integers are immediate in Zarith and are their own hash code; the
   others are custom blocks, hashed with [Z.hash]. *)
let of_int (i:int) : hash_code =
  if -0x4000000000000000 <= i && i < 0x4000000000000000 then
    U64.uint_to_t (i % 0x8000000000000000)
  else
    let acc = zarith_limbs_hash 0ul (if i < 0 then -i else i) in
    let acc = if i < 0 then U32.add_mod acc 1ul else acc in
    caml_hash_result (caml_hash_mix_uint32 0ul acc)

(* caml_hash_mix_string over the UTF-8 bytes, in ulib/c/cherry.c. *)
[@@custard_extern "cherry_str_caml_hash_mix"]
private assume val caml_hash_mix_string : U32.t -> string -> U32.t

let of_string (s:string) : hash_code =
  caml_hash_result (caml_hash_mix_string 0ul s)

(* See FStarC.Hash-ocaml.fst. *)
let mix (a b:hash_code) : hash_code =
  let c = 0x1bd1e9955bd1e995UL in
  let k = mask63 (U64.mul_mod b c) in
  let k = U64.logxor k (U64.shift_right k 31ul) in
  let k = mask63 (U64.mul_mod k c) in
  mask63 (U64.mul_mod (U64.logxor a k) c)

let string_of_hash_code (h:hash_code) : string = string_of_int (to_int h)
