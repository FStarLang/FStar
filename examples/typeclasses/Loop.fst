module Loop

(* Making sure typeclass resolution does not loop *)

open FStar.Tactics.Typeclasses

(* two classes for inhabitation *)
class c a = { x : a }
class d a = { y : a }

instance cd (dict : c 'a) : d 'a = { y = dict.x }
instance dc (dict : d 'a) : c 'a = { x = dict.y }

(* This should fail... in finite time *)
[@expect_failure]
let f (a:Type) : a = x
