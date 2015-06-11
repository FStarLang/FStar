module Bug260

type typ =
  | TVar : typ
  | TImpl : typ -> typ

type validity : t:typ -> Type =
  | V_impl_intro : t:typ -> Tot (validity (TImpl t))

val tot_ret_weakest : t:typ -> Tot (validity (TImpl (TImpl t))) (* wrong type: *)
(* val tot_ret_weakest : t:typ -> Tot (validity (TImpl t)) -- right type: *)
let tot_ret_weakest t = V_impl_intro t
