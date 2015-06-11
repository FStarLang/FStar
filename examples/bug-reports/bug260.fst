module Bug260

type pnat =
  | O : pnat
  | S : pnat -> pnat

type validity : n:pnat -> Type =
  | VSucc : n:pnat -> Tot (validity (S n))

val bad : t:pnat -> Tot (validity (S (S t))) (* wrong type: *)
(* val tot_ret_weakest : t:pnat -> Tot (validity (S t)) -- right type: *)
let bad t = VSucc t
