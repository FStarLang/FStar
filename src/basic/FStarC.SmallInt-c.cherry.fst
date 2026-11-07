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
   sign bit and compare unsigned, and are C's signed comparisons in Cherry,
   which the C compiler can bound an array index with.  (The OCaml build has
   63 bits.) *)

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module IA = FStar.ImmutableArray.Base

type t = U64.t

(* Defined before this module's [<] shadows the one on [int].  A three-way
   comparison as a [t] directly, without going through [of_int]. *)
private let int_cmp (a b:int) : U64.t =
  if a < b then 0xffffffffffffffffUL else if a = b then 0UL else 1UL

(* Wraps modulo 2^64 if the argument does not fit.  A negative argument is
   negated rather than reduced modulo 2^64, which would make it a big
   integer in Cherry. *)
[@@custard_extern "cherry_smallint_of_int"]
let of_int x =
  if x >= 0 then U64.uint_to_t (x % 0x10000000000000000)
  else U64.sub_mod 0UL (U64.uint_to_t ((- x) % 0x10000000000000000))

(* Likewise, no arithmetic on integers beyond 2^62 unless the result is. *)
[@@custard_extern "cherry_smallint_to_int"]
let to_int x =
  if U64.gte x 0x8000000000000000UL then - (U64.v (U64.sub_mod 0UL x))
  else U64.v x

let of_char c = Cast.uint32_to_uint64 (FStar.Char.u32_of_char c)

let zero = 0UL

let one = 1UL

let minus_one = 0xffffffffffffffffUL

let ( + ) a b = U64.add_mod a b

let ( - ) a b = U64.sub_mod a b

let flip (a:t) : t = U64.logxor a 0x8000000000000000UL

[@@custard_extern "cherry_smallint_lt"]
let ( < ) a b = U64.lt (flip a) (flip b)

[@@custard_extern "cherry_smallint_le"]
let ( <= ) a b = U64.lte (flip a) (flip b)

[@@custard_extern "cherry_smallint_gt"]
let ( > ) a b = U64.gt (flip a) (flip b)

[@@custard_extern "cherry_smallint_ge"]
let ( >= ) a b = U64.gte (flip a) (flip b)

let max a b = if a >= b then a else b

let min a b = if a <= b then a else b

let show x = string_of_int (to_int x)

let array_length arr = of_int (IA.length arr)

(* The interface leaves the bounds to the caller. *)
let array_index arr i =
  let j = to_int i in
  assume (0 <= j /\ j < IA.length arr);
  IA.index arr j

let int_compare a b = int_cmp a b

(* In ulib/c/cherry.c: -1, 0 or 1 as a [t], with no [int] in between. *)
[@@custard_extern "cherry_str_compare_u64"]
private assume val str_compare_u64 : string -> string -> U64.t

let string_compare a b = str_compare_u64 a b
