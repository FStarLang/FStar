module FStar.Tactics.MApply

open FStar.Reflection.V2
open FStar.Tactics.Effect
open FStar.Tactics.Typeclasses
open FStar.Tactics.V2.SyntaxCoercions

(* Used by mapply, must be exposed, but not to be used directly *)
private val push1 : (#p:Type) -> (#q:Type) ->
                        squash (p ==> q) ->
                        squash p ->
                        squash q
private val push1' : (#p:Type) -> (#q:Type) ->
                         (p ==> q) ->
                         squash p ->
                         squash q

class termable (a : Type) = {
  to_term : a -> Tac term
}

instance termable_term : termable term = {
  to_term = (fun t -> t);
}

instance termable_binding : termable binding = {
  to_term = (fun b -> binding_to_term b);
}

(* `m` is for `magic` *)
[@@plugin]
val mapply0 (t : term) : Tac unit

let mapply (#ty:Type) {| termable ty |} (x : ty) : Tac unit =
  let t = to_term x in
  mapply0 t
