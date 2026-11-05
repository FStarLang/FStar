module Fundeps

[@@Tactics.Typeclasses.fundeps [0]]
class setlike (e:Type) (s:Type) = {
  empty : s;
  add : e -> s -> s;
  remove : e -> s -> s;
  contains : e -> s -> bool;
  size : s -> int;
}

assume val set (a:Type) : Type

assume
instance val setlike_set (a:Type) : setlike a (set a)

let test (s : set int) = size s

(* The meta-arg for [showable (list ?e)] must wait for [setlike ?e (set int)],
   which determines ?e through the fundep, regardless of the order in which
   the two constraints are generated. *)
class showable (a:Type) = { show : a -> string }
instance showable_int : showable int = { show = (fun _ -> "int") }
instance showable_list (a:Type) {| showable a |} : showable (list a) = { show = (fun _ -> "list") }

assume val to_list (#e #s : Type) {| setlike e s |} (x : s) : list e

let test_show (s : set int) : string = show (to_list s)

let test_show_inst (a:Type) {| showable a |} (s : set a) : string = show (to_list s)
