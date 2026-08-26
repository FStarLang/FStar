(*
   Copyright 2017-2024 Microsoft Research

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
module FStarC.Real

open FStarC.Effect
open FStarC.Order

module RL = FStar.RealLiteral
module RLP = FStar.RealLiteral.Parse

(* The representation of real literals lives in ulib (FStar.RealLiteral) so
that the reflection API can expose the very same type. This module is just a
thin wrapper over it, adding the compiler-specific bits. *)

let mantissa (r : real) : int = r.RL.mantissa
let exponent (r : real) : int = r.RL.exponent

let mk = RL.mk
let of_int = RL.of_int
let of_string = RLP.of_string
let to_string = RL.to_string

let to_smt_string (r : real) : string =
  if mantissa r < 0
  then "(- " ^ to_string (mk (- (mantissa r)) (exponent r)) ^ ")"
  else to_string r

let cmp (r1 r2 : real) : order =
  compare_int (RL.compare r1 r2) 0
