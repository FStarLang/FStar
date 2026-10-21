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
module FStarC.Int.Extra

(* The Cherry implementation, on [int] itself, with Zarith's semantics: an
   integer is an infinite two's complement bit string, so a negative one has
   infinitely many leading ones.  The bitwise operations work 32 bits at a
   time, lowest first; [/] and [%] by a positive divisor round towards minus
   infinity, so the high part of a negative number stays negative and ends at
   [-1], whose bits are all ones. *)

open FStarC.Effect
module U32 = FStar.UInt32

let base : int = 0x100000000

let rec bitwise (f:U32.t -> U32.t -> U32.t) (x y:int)
  : Tot int (decreases (FStar.Math.Lib.abs x + FStar.Math.Lib.abs y)) =
  if (x = 0 || x = -1) && (y = 0 || y = -1) then
    (* Both are uniform from here on: so is the result, by its low bit. *)
    (if U32.v (f (U32.uint_to_t (x % base)) (U32.uint_to_t (y % base))) = 0 then 0 else -1)
  else
    let lo = U32.v (f (U32.uint_to_t (x % base)) (U32.uint_to_t (y % base))) in
    bitwise f (x / base) (y / base) * base + lo

let logand x y = bitwise U32.logand x y

let logor x y = bitwise U32.logor x y

let logxor x y = bitwise U32.logxor x y

let lognot x = -x - 1

let rec pow2_int (n:int) : Tot pos (decreases (if n <= 0 then 0 else n)) =
  if n <= 0 then 1 else 2 * pow2_int (n - 1)

(* Zarith rejects a negative shift; here it shifts the other way. *)
let shift_left x n = if n >= 0 then x * pow2_int n else x / pow2_int (-n)

let shift_right x n = if n >= 0 then x / pow2_int n else x * pow2_int (-n)
