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
module FStarC.SmallInt

(* The Cherry implementation: a 64-bit two's complement integer, stored in a
   [U64.t].  Addition and subtraction wrap; the signed comparisons flip the
   sign bit and compare unsigned.  (The OCaml build has 63 bits.) *)

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module IA = FStar.ImmutableArray.Base

type t = U64.t

(* Defined before this module's [<] shadows the one on [int]. *)
private let int_cmp (a b:int) : int = if a < b then -1 else if a = b then 0 else 1

(* Wraps modulo 2^64 if the argument does not fit. *)
let of_int x = U64.uint_to_t (x % 0x10000000000000000)

let to_int x =
  let n = U64.v x in
  if n >= 0x8000000000000000 then n - 0x10000000000000000 else n

let of_char c = Cast.uint32_to_uint64 (FStar.Char.u32_of_char c)

let zero = 0UL

let one = 1UL

let minus_one = 0xffffffffffffffffUL

let ( + ) a b = U64.add_mod a b

let ( - ) a b = U64.sub_mod a b

let flip (a:t) : t = U64.logxor a 0x8000000000000000UL

let ( < ) a b = U64.lt (flip a) (flip b)

let ( <= ) a b = U64.lte (flip a) (flip b)

let ( > ) a b = U64.gt (flip a) (flip b)

let ( >= ) a b = U64.gte (flip a) (flip b)

let max a b = if a >= b then a else b

let min a b = if a <= b then a else b

let show x = string_of_int (to_int x)

let array_length arr = of_int (IA.length arr)

(* The interface leaves the bounds to the caller. *)
let array_index arr i =
  assume (U64.v i < IA.length arr);
  IA.index arr (U64.v i)

let int_compare a b = of_int (int_cmp a b)

let string_compare a b = of_int (FStar.String.compare a b)
