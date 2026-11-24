module ClearlyInhabited

(* The normalizer simplifies [exists (x:t). True] to [True] when
   [clearly_inhabited t]. A singleton [x:t{x == e}] is clearly inhabited
   only if [t] is a type constant: [x:(y:int{y == 0}){x == 1}] is empty. *)

[@@expect_failure [19]]
let empty () : Lemma (exists (x:(y:int{y == 0}){x == 1}). True) = ()

(* The singleton refinement of [int] is still simplified away. *)
#push-options "--no_smt"
let singleton () : Lemma (exists (x:int{x == 1}). True) = ()
#pop-options
