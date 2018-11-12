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
#light "off"
module FStar.BigInt
open FStar.All

type bigint
    = FSharp.Compatibility.OCaml.Big_int.big_int // JUST FSHARP
type t = bigint

val zero : bigint
val one : bigint
val two : bigint

val succ_big_int : (bigint -> bigint)
val pred_big_int : (bigint -> bigint)
val minus_big_int : (bigint -> bigint)
val abs_big_int : (bigint -> bigint)

val add_big_int : (bigint -> bigint -> bigint)
val mult_big_int : (bigint -> bigint -> bigint)
val sub_big_int : (bigint -> bigint -> bigint)
val div_big_int : (bigint -> bigint -> bigint)
val mod_big_int : (bigint -> bigint -> bigint)

val eq_big_int : (bigint -> bigint -> bool)
val le_big_int : (bigint -> bigint -> bool)
val lt_big_int : (bigint -> bigint -> bool)
val ge_big_int : (bigint -> bigint -> bool)
val gt_big_int : (bigint -> bigint -> bool)

val logand_big_int: bigint -> bigint -> bigint
val logor_big_int: bigint -> bigint -> bigint
val logxor_big_int: bigint -> bigint -> bigint
val lognot_big_int: bigint -> bigint

val shift_left_big_int: bigint -> bigint -> bigint
val shift_right_big_int: bigint -> bigint -> bigint

val sqrt_big_int : (bigint -> bigint)

val string_of_big_int : (bigint -> string)
val big_int_of_string : (string -> bigint)

val of_int : (int -> bigint)
val to_int : (bigint -> int)

val of_int_fs: (int -> bigint)
val to_int_fs: (bigint -> int)

val of_hex: string -> bigint
