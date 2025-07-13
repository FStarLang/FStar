(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.Range.Type

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Ord

[@@ PpxDerivingYoJson; PpxDerivingShow]
new val rng : Type0

[@@ PpxDerivingYoJson; PpxDerivingShow]
new val range : Type0

(* So we can write Range.t *)
type t = range

[@@ PpxDerivingYoJson; PpxDerivingShow]
new val pos : Type0

instance val deq_pos : deq pos
instance val ord_pos : ord pos

val dummy_rng : rng
val mk_rng : string -> pos -> pos -> rng

val dummyRange: range
val use_range: range -> rng
val def_range: range -> rng
val range_of_rng: def_rng:rng -> use_rng:rng -> range
val set_use_range: range -> rng -> range
val set_def_range: range -> rng -> range
val mk_pos: int -> int -> pos
val mk_range: string -> pos -> pos -> range

val json_of_pos: pos -> FStarC.Json.json
val json_of_rng: rng -> FStarC.Json.json
val json_of_range: range -> FStarC.Json.json
