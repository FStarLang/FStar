module Maxime

type foo = | C : (p:Type -> p -> p) -> foo

(* Maxime is worried that this fixpoint will be accepted if we were to add
   f x < f *)

val bad : x:foo -> Tot False (decreases x)
let rec bad (x:foo) : False =
  match x with
  | C f -> bad (f foo x)

(* Computed type "False" and effect "ALL" is not compatible with the
   annotated type "False" effect "PURE" *)
