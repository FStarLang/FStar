module Pulse.Simplify

(* Some functions to simplify terms and slprops *)

open FStar.Reflection.V2
module T       = FStar.Tactics.V2

val is_tuple2__1 (t:term) : T.Tac (option term)

val is_tuple2__2 (t:term) : T.Tac (option term)

val is_tuple2 (t:term) : T.Tac (option (term & term))

(* This is a huge hack to work around the lack of reduction of projectors in F*.
Note that we cannot simply unfold the projects willy-nilly, we only want to do so
when they are applied to a constructed value. *)
val _simpl_proj (t:term) : T.Tac (option term)

val simpl_proj (t:term) : T.Tac term

val simplify (t:term) : T.Tac term
