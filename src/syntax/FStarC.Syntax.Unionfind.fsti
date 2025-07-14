(*
   Copyright 2008-2014 Microsoft Research

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

module FStarC.Syntax.Unionfind

(* This module offers a transactional interface specialized for terms and
 * universes on top of the existing union-find implementation. *)

open FStarC.Effect
module Range = FStarC.Range.Type
module S = FStarC.Syntax.Syntax

val uf : Type0
val get : unit -> uf
val set : uf -> unit
val reset : unit -> unit

(* Set read-only mode *)
val set_ro : unit -> unit

(* Set read-write mode *)
val set_rw : unit -> unit

(* Run a function with rw mode enabled *)
val with_uf_enabled : (unit -> 'a) -> 'a

val tx : Type0
val new_transaction    : (unit -> tx)
val rollback           : tx -> unit
val commit             : tx -> unit
val update_in_tx       : ref 'a -> 'a -> unit

val fresh              : S.uvar_decoration -> Range.t -> S.uvar
val uvar_id            : S.uvar -> int
val uvar_unique_id     : S.uvar -> int
val find               : S.uvar -> option S.term
val find_decoration    : S.uvar -> S.uvar_decoration
val change             : S.uvar -> S.term -> unit
val change_decoration  : S.uvar -> S.uvar_decoration -> unit
val equiv              : S.uvar -> S.uvar -> bool
val union              : S.uvar -> S.uvar -> unit

val univ_fresh         : Range.t -> S.universe_uvar
val univ_uvar_id       : S.universe_uvar -> int
val univ_find          : S.universe_uvar -> option S.universe
val univ_change        : S.universe_uvar -> S.universe -> unit
val univ_equiv         : S.universe_uvar -> S.universe_uvar -> bool
val univ_union         : S.universe_uvar -> S.universe_uvar -> unit
