(*
   Copyright 2020 Microsoft Research

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
module Integers

irreducible
let mark_for_norm = ()

unfold
let norm (#a:Type) (x:a) = norm [iota; delta_attr [`%mark_for_norm]] x

type width =
  | W8
  | Winfinite

[@@mark_for_norm]
let nat_of_width = function
  | W8   -> Some 8
  | Winfinite -> None

let fixed_width = w:width{w <> Winfinite}

type signed_width =
  | Signed of width
  | Unsigned of fixed_width //We don't support (Unsigned WInfinite); use nat instead

[@@mark_for_norm]
let width_of_sw = function
  | Signed w -> w
  | Unsigned w -> w

[@@mark_for_norm]
inline_for_extraction
let int_t sw : Tot Type0 =
  match sw with
  | Unsigned W8 -> FStar.UInt8.t
  | Signed Winfinite -> int
  | Signed W8 -> FStar.Int8.t

[@@mark_for_norm; strict_on_arguments [0]]
unfold
let within_bounds' sw (x:int) =
  match sw, nat_of_width (width_of_sw sw) with
  | Signed _,   None   -> True
  | Signed _,   Some n -> FStar.Int.size x n
  | Unsigned _, Some n -> FStar.UInt.size x n

unfold
let within_bounds sw x = norm (within_bounds' sw x)

// Extracted code contains unsafe_coerce
[@@mark_for_norm; strict_on_arguments [0]]
unfold
let v #sw (x:int_t sw)
  : Tot (y:int_t (Signed Winfinite){within_bounds sw y})
  = match sw with
    | Unsigned w ->
      (match w with
       | W8 -> FStar.UInt8.v x)
    | Signed w ->
      (match w with
       | Winfinite -> x
       | W8 -> FStar.Int8.v x)

// Extracted code contains unsafe_coerce
[@@mark_for_norm; strict_on_arguments [0]]
unfold
let op_Subtraction #sw
                   (x:int_t sw)
                   (y:int_t sw{within_bounds sw (v x - v y)})
    : Tot          (int_t sw)
  = match sw with
    | Signed Winfinite -> x - y
    | Unsigned W8 -> FStar.UInt8.(x -^ y)
    | Signed W8 -> FStar.Int8.(x -^ y)
    
// This line fails at extractions
// TODO: Minimize
//let fails_at_extraction (x:Prims.int) (y:Prims.nat) = x - y