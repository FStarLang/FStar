module Embeddings

(* Tests for generating bindings to native tactics with correct calls to the
   embedding and unembedding functions for the types supported in tactic compilaton.
   Tactics should be generated without warnings and compile without errors.
*)

open FStar.Reflection
open FStar.Tactics

(* Simple types *)
[@plugin]
let int_tac: int -> Tac int = fun n -> magic ()

[@plugin]
let bool_tac: bool -> Tac bool = fun n -> magic ()

[@plugin]
let unit_tac: unit -> Tac unit = fun n -> magic ()

[@plugin]
let string_tac: string -> Tac string = fun n -> magic ()

[@plugin]
let term_tac: term -> Tac term = fun n -> magic ()

[@plugin]
let binder_tac: binder -> Tac binder = fun n -> magic ()

[@plugin]
let binders_tac: binders -> Tac binders = fun n -> magic ()

[@plugin]
let norm_step_tac: norm_step -> Tac norm_step = fun n -> magic ()

[@plugin]
let fv_tac: fv -> Tac fv = fun n -> magic ()

(* Higher-order types *)
[@plugin]
let list_tac: list int -> Tac (list int) = fun n -> magic ()

[@plugin]
let option_tac: option int -> Tac (option term) = fun n -> magic ()

[@plugin]
let tuple_tac: (int * bool) -> Tac (string * term) = fun n -> magic ()

[@plugin]
let any_tac (#a: Type) (l: list a): Tac (list a) = l
