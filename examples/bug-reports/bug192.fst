module Bug192

assume type deduce : int -> Type

type pred = int -> Tot int

type hoare_c (p:pred) : Type = (h:int -> deduce (p h))
  (* adding Tot to deduce causes Unexpected error: Ill-formed substitution *)

val hoare_while : p:pred -> Tot (hoare_c p)
let rec hoare_while p' h = (* commenting out the rec makes this work *)
    magic()  (* Unexpected error: Bound term variable not found: p'"
