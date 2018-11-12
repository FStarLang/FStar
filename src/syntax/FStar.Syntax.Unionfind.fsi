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
module FStar.Syntax.Unionfind

(* This module offers a transactional interface specialized for terms and
 * universes on top of the existing union-find implementation. *)

open FStar.All
module S = FStar.Syntax.Syntax

type uf
val get : unit -> uf
val set : uf -> unit
val reset : unit -> unit

type tx
val new_transaction: (unit -> tx)
val rollback       : tx -> unit
val commit         : tx -> unit
val update_in_tx   : ref<'a> -> 'a -> unit

val fresh  : unit -> S.uvar
val uvar_id: S.uvar -> int
val from_id : int -> S.uvar
val find   : S.uvar -> option<S.term>
val change : S.uvar -> S.term -> unit
val equiv  : S.uvar -> S.uvar -> bool
val union  : S.uvar -> S.uvar -> unit

val univ_fresh  : unit -> S.universe_uvar
val univ_uvar_id: S.universe_uvar -> int
val univ_from_id : int -> S.universe_uvar
val univ_find   : S.universe_uvar -> option<S.universe>
val univ_change : S.universe_uvar -> S.universe -> unit
val univ_equiv  : S.universe_uvar -> S.universe_uvar -> bool
val univ_union  : S.universe_uvar -> S.universe_uvar -> unit
