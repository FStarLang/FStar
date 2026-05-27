module FStar.Tactics.MApply0

open FStar.Stubs.Reflection.Types
open FStar.Tactics.Effect

(* Used by mapply, must be exposed, but not to be used directly *)
private val push1 : (#p:prop) -> (#q:prop) ->
                        squash (p ==> q) ->
                        squash p ->
                        squash q
private val push1' : (#p:prop) -> (#q:prop) ->
                         squash (p ==> q) ->
                         squash p ->
                         squash q

(* `m` is for `magic` *)
[@@plugin]
val mapply0 (t : term) : Tac unit
