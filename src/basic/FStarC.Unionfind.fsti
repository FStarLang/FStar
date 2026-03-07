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
module FStarC.Unionfind

open FStarC.Effect

type puf 'a
type p_uvar 'a
val puf_empty: unit -> ML (puf 'a)
val puf_fresh: puf 'a -> 'a -> ML (p_uvar 'a)
val puf_id: puf 'a -> p_uvar 'a -> ML int
val puf_fromid: puf 'a -> int -> ML (p_uvar 'a)
val puf_find: puf 'a -> p_uvar 'a -> ML 'a
val puf_union: puf 'a -> p_uvar 'a -> p_uvar 'a -> ML (puf 'a)
val puf_equivalent: puf 'a -> p_uvar 'a -> p_uvar 'a -> ML bool
val puf_change: puf 'a -> p_uvar 'a -> 'a -> ML (puf 'a)
val puf_test: unit -> ML unit

//
// Returns the unique id of the input uvar
// This is different from puf_id, that returns the
//   unique id of the root of the uf tree that the input
//   uvar belongs to
//
val puf_unique_id: p_uvar 'a -> int
