(*
   Copyright 2008-2020 Microsoft Research

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
module FStarC.Const
open FStarC.Effect

open FStar.Char
open FStar.Mul

let eq_const c1 c2 =
    match c1, c2 with
    | Const_int (s1, o1), Const_int(s2, o2) ->
      FStarC.Util.ensure_decimal s1 = FStarC.Util.ensure_decimal s2 &&
      o1=o2
    | Const_string(a, _), Const_string(b, _) -> a=b
    | Const_reflect l1, Const_reflect l2 -> Ident.lid_equals l1 l2
    | Const_reify _, Const_reify _ -> true
    | _ -> c1=c2

let rec pow2 (x : int) : int =
  if x = 0
  then 1
  else 2 * pow2 (x - 1)

let bounds signedness width =
    let n =
        match width with
        | Int8  -> 8
        | Int16 -> 16
        | Int32 -> 32
        | Int64 -> 64
        | Sizet -> 16
    in
    let lower, upper =
      match signedness with
      | Unsigned ->
        0, pow2 n - 1
      | Signed ->
        let upper = pow2 (n - 1) in
        - upper, upper - 1
    in
    lower, upper

let within_bounds repr signedness width =
  let lower, upper = bounds signedness width in
  let value = Util.int_of_string (FStarC.Util.ensure_decimal repr) in
  lower <= value && value <= upper
