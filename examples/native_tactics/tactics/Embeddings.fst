module Embeddings

(* Tests for generating bindings to native tactics with correct calls to the
   embedding and unembedding functions for the types supported in tactic compilaton.
   Tactics should be generated without warnings and compile without errors.
*)

open FStar.Reflection
open FStar.Tactics

(* Simple types *)
let int_tac: int -> Tac int = fun n -> admit ()

let bool_tac: bool -> Tac bool = fun n -> admit ()

let unit_tac: unit -> Tac unit = fun n -> admit ()

let string_tac: string -> Tac string = fun n -> admit ()

let binder_tac: binder -> Tac binder = fun n -> admit ()

let term_tac: term -> Tac term = fun n -> admit ()

let fv_tac: fv -> Tac fv = fun n -> admit ()

(* Higher-order types *)
let list_tac: list int -> Tac (list int) = fun n -> admit ()

let option_tac: option int -> Tac (option int) = fun n -> admit ()
