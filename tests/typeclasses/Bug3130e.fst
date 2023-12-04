module Bug3130e

class ord_leq (a:eqtype) =
  { leq: a -> a -> bool
  ; trans: (x:a) -> (y:a) -> (z:a) -> Lemma (x `leq` y /\ y `leq` z ==> x `leq` z)
  }

let transitivity {| ord_leq 'a |} (x y z : 'a)
  : Lemma (x `leq` y /\ y `leq` z ==> x `leq` z)
  [SMTPat (x `leq` y); SMTPat (x `leq` z)]
  = trans x y z

(* Currently fails since the type of the uu binder is undefined,
and tcresolve won't run *)
[@@expect_failure [66]]
let transitivity_forall #a {| ord_leq a |} uu
  : Lemma (forall (x y z : a). x `leq` y /\ y `leq` z ==> x `leq` z )
= ()

let transitivity_forall2 #a {| ord_leq a |}
  : Lemma (forall (x y z : a). x `leq` y /\ y `leq` z ==> x `leq` z )
= ()

let transitivity_forall3 #a #b {| ord_leq a |} (unit:b)
  : Lemma (forall (x y z : a). x `leq` y /\ y `leq` z ==> x `leq` z )
= ()
