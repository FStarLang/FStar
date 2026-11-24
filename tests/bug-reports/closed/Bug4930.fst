module Bug4930

(* FStarLang/FStar#4930: [clearly_inhabited] took a singleton refinement
   [x:t{x == e}] to be inhabited by [e] whenever [t] is, but [e] need not have
   type [t] when [t] is itself a refinement: below, the equality is at [int],
   and [1] is not in [y:int{y == 0}]. *)

[@@expect_failure [19]]
let inhabited () : Lemma (exists (x:(y:int{y == 0}){x == 1}). True) = ()

[@@expect_failure [19]]
let bad_nonempty () : Lemma (nonempty (x:(y:int{y == 0}){x == 1})) = ()

[@@expect_failure [19]]
let bad_arrow () : Lemma (exists (f:int -> (y:(z:int{z == 0}){y == 1})). True) = ()

(* Singletons over a base type are still inhabited. *)
let ok_exists () : Lemma (exists (x:int{x == 1}). True) = ()
let ok_nonempty () : Lemma (nonempty (x:int{x == 1})) = ()
let ok_arrow () : Lemma (nonempty (int -> x:int{x == 1})) = ()
