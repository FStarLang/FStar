module Plugins

(* Tests for generating bindings to native plugins with correct calls to the
   embedding and unembedding functions for the types supported in tactic compilaton.
   Tactics should be generated without warnings and compile without errors.
*)

open FStar.Reflection
open FStar.Tactics

[@plugin]
let int_plugin: int -> int = id

[@plugin]
let bool_plugin: bool -> bool = id

[@plugin]
let unit_plugin: unit -> bool = fun _ -> true

[@plugin]
let string_plugin: string -> string = id

[@plugin]
let term_plugin: term -> term = id

[@plugin]
let binder_plugin: binder -> binder = id

[@plugin]
let binders_plugin: binders -> binders = id

[@plugin]
let norm_step_plugin: norm_step -> norm_step = id

[@plugin]
let fv_plugin: fv -> fv = id

[@plugin]
let list_plugin: list int -> (list int) = id

[@plugin]
let option_plugin: option term -> (option term) = id

[@plugin]
let tuple_plugin: int -> bool -> (int * bool) = fun x y -> (x,y)

[@plugin]
let any_plugin (#a: Type) (l: list a): list a = l
