module Erased

(* Misc tests about erased *)

open FStar.Ghost

let aux (t1 t2 : Type{t1 == t2}) (x : erased t1)
  : Lemma (hide #t2 (reveal #t1 x) == x)
  = ()

let aux2 (t1 : Type) (x : erased t1)
  : Lemma (hide #t1 (reveal #t1 x) == x)
  = ()
