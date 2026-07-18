module UnrefineAttr

assume val eq2 (#[@@@unrefine] a:Type) (x y : a) : Type0

(* Actually enable it. *)
#set-options "--ext __unrefine"

let test0 (x y : nat) = eq2 #int x y
let test1 (x y : nat) = eq2 x y (* this implicit should be solved to int *)
let test2 (x y : int) = eq2 x y

let _ = assert (forall x y. test0 x y == test2 x y)
let _ = assert (forall x y. test1 x y == test2 x y)
let _ = assert_norm (forall x y. test0 x y == test2 x y)
let _ = assert_norm (forall x y. test1 x y == test2 x y)
