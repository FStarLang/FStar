(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or impliedmk_
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: N. Swamy
*)
module FStarC.Syntax.Hash

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax

module H = FStarC.Hash
open FStarC.Class.Hashable

val ext_hash_term (t:term) : H.hash_code
val ext_hash_term_no_memo (t:term) : H.hash_code
val equal_term (t0 t1:term) : bool

(* uses ext_hash_term (with memo) *)
instance val hashable_term : hashable term
