module Loop2

open FStar.Tactics.Typeclasses

(* two classes for inhabitation, with an integer index *)
class c (n:nat) a = { x : a }
class d (n:nat) a = { y : a }

instance cd  (#n:nat) (_ : c n 'a) : d (n + 1) 'a = { y = x }

instance dc  (#n:nat) (_ : d n 'a) : c (n + 1) 'a = { x = y }
instance dc' (#n:nat) (_ : d n 'a) : c (n + 1) 'a = { x = y }

(* This should fail... in finite time *)
[@expect_failure]
let f (a:Type) : a = x
