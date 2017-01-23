module HyE.Ideal


val ind_cca : bool

val int_ctxt : b:bool{ ind_cca ==> b }

val int_cpa : b:bool{ ind_cca ==> b }

let conf = ind_cca
