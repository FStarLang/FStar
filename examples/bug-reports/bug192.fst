module Bug192

assume type deduce : int -> Type

type pred = int -> Tot int

type hoare_c (q:pred) : Type = (hh:int -> Tot (deduce (q hh)))

val hoare_while : p:pred -> Tot (hoare_c p)
let rec hoare_while p' h =    (* commenting out the rec makes this work *)
    magic () (* (deduce (p' h)) ()  (\* Unexpected error: Bound term variable not found: p'" *\) *)
