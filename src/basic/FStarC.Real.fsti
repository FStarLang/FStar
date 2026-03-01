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

(* A type for embedded real constants. This allows to write embeddings for them
(see FStarC.Syntax.Embeddings and FStarC.TypeChecker.NBETerm). *)

type real = | Real of string

(* Compares two reals, may return None if unknown. *)
val cmp (r1 r2 : real) : option order
