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

(* The Cherry implementation: a 64-bit two's complement integer, an
   [I64.t].  Addition and subtraction wrap, by going through [U64.t]; the
   comparisons are [I64]'s, which C compiles to signed comparisons that the C
   compiler can bound an array index with.  (The OCaml build has 63 bits.) *)

module I64 = FStar.Int64
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module IA = FStar.ImmutableArray.Base

type t = I64.t

[@@custard_inline]
private let of_u (x:U64.t) : t = Cast.uint64_to_int64 x
[@@custard_inline]
private let to_u (x:t) : U64.t = Cast.int64_to_uint64 x

(* Defined before this module's [<] shadows the one on [int].  A three-way
   comparison as a [t] directly, without going through [of_int]. *)
private let int_cmp (a b:int) : t =
  if a < b then -1L else if a = b then 0L else 1L

(* Wraps modulo 2^64 if the argument does not fit.  A negative argument is
   negated rather than reduced modulo 2^64, which would make it a big
   integer in Cherry. *)
[@@custard_extern "cherry_smallint_of_int"]
let of_int x =
  if x >= 0 then of_u (U64.uint_to_t (x % 0x10000000000000000))
  else of_u (U64.sub_mod 0UL (U64.uint_to_t ((- x) % 0x10000000000000000)))

[@@custard_extern "cherry_smallint_to_int"]
let to_int x = I64.v x

let of_char c = Cast.uint32_to_int64 (FStar.Char.u32_of_char c)

let zero = 0L

let one = 1L

let minus_one = -1L

let ( + ) a b = of_u (U64.add_mod (to_u a) (to_u b))

let ( - ) a b = of_u (U64.sub_mod (to_u a) (to_u b))

let ( < ) a b = I64.lt a b

let ( <= ) a b = I64.lte a b

let ( > ) a b = I64.gt a b

let ( >= ) a b = I64.gte a b

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
[@@custard_extern "cherry_str_compare_i64"]
private assume val str_compare_i64 : string -> string -> t

let string_compare a b = str_compare_i64 a b
