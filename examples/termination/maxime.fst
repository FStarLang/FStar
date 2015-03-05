module Maxime

type foo = | C : (p:Type -> p -> Tot p) -> foo

(* Maxime is worried that this fixpoint will be accepted if we were to add
   f x < f *)

val bad : x:foo -> Tot False (decreases x)
let rec bad (x:foo) : False =
  match x with
  | C f -> bad (f foo x)

(* Current error message:
   Error maxime.fst(9,0-15,0): The following problems were found:
	Subtyping check failed; expected type _12724:foo{(%[_12724] << %[x])}; got type foo (maxime.fst(11,15-11,24)) *)
