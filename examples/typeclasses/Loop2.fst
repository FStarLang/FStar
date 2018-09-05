module Loop2

open FStar.Tactics.Typeclasses

(* two classes for inhabitation, with an integer index *)
class c (n:int) a = { x : a }
class d (n:int) a = { y : a }

instance cd  #n (dict : c n 'a) : d (n+1) 'a = { y = dict.x }
instance dc  #n (dict : d n 'a) : c (n+1) 'a = { x = dict.y }
instance dc' #n (dict : d n 'a) : c (n+1) 'a = { x = dict.y }

(* This should fail... in finite time *)
[@expect_failure]
let f (a:Type) : a = x
