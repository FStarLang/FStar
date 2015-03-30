module Bug192

assume type deduce : int -> Type

type pred = int -> Tot int

type hoare_c (p:pred) : Type = (h:int -> Tot (deduce (p h)))

val hoare_while : p:pred -> Tot (hoare_c p)
let rec hoare_while p' h = (* commenting out the rec makes this work *)
    magic (deduce (p' h)) ()  (* Unexpected error: Bound term variable not found: p'" *)



(* val hoare_while : p:pred -> h:int -> Tot (deduce (p h)) *)
(* let rec hoare_while p' h = (\* commenting out the rec makes this work *\) *)
(*     magic (deduce (p' h)) ()  (\* Unexpected error: Bound term variable not found: p'" *)
