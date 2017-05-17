module B

//

unfold let squash (a:Type) = u:unit{a}

val l1 : (a : Type) -> Lemma (a ==> squash a)
let l1 a = assert_norm (a ==> squash a)

(* val l2 : (a : Type) -> Lemma (squash a ==> a) *)
(* let l2 a = assert_norm (squash a ==> a) *)
