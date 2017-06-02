#light "off"
module FStar.Syntax.Unionfind
open FStar.All
module S = FStar.Syntax.Syntax

type uf
val get : unit -> uf
val set : uf -> unit

type tx
val new_transaction: (unit -> tx)
val rollback       : tx -> unit
val commit         : tx -> unit
val update_in_tx   : ref<'a> -> 'a -> unit

val fresh  : unit -> S.uvar
val uvar_id: S.uvar -> int
val find   : S.uvar -> option<S.term>
val change : S.uvar -> S.term -> unit
val equiv  : S.uvar -> S.uvar -> bool
val union  : S.uvar -> S.uvar -> unit

val univ_uvar_id: S.universe_uvar -> int
val univ_fresh  : unit -> S.universe_uvar
val univ_find   : S.universe_uvar -> option<S.universe>
val univ_change : S.universe_uvar -> S.universe -> unit
val univ_equiv  : S.universe_uvar -> S.universe_uvar -> bool
val univ_union  : S.universe_uvar -> S.universe_uvar -> unit
