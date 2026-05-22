module FStar.Tactics.MApply0

open FStar.Stubs.Reflection.Types
open FStar.Tactics.Effect

(* Used by mapply, must be exposed, but not to be used directly *)
private val push1 : (#p:prop) -> (#q:prop) ->
                        (p ==> q) ->
                        p ->
                        q
private val push1' : (#p:prop) -> (#q:prop) ->
                         (p ==> q) ->
                         p ->
                         q

(* `m` is for `magic` *)
[@@plugin]
val mapply0 (t : term) : Tac unit
