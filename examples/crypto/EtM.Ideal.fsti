module EtM.Ideal


val ind_cpa : bool

val uf_cma : b:bool{ ind_cpa ==> b }

let ind_cpa_rest_adv = uf_cma
(* well typed adversaries only submit ciphertext obtained using encrypt *)

let conf = ind_cpa && uf_cma

let auth =  uf_cma

//A negative test, if you only have ind_cpa but not uf_cma security you should not be able to proof confidentiality

(* let ind_cpa = true *)
(* let uf_cma = false *)
(* let ind_cpa_rest_adv = uf_cma *)
(* let conf = true *)
(* let auth = false *)
