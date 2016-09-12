module EtM.Ideal

val ind_cpa : bool

val uf_cma : b:bool{ ind_cpa ==> b }

let ind_cpa_rest_adv = uf_cma
(* well typed adversaries only submit ciphertext obtained using encrypt *)

let conf = ind_cpa

let auth = uf_cma
