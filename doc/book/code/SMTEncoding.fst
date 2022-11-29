module SMTEncoding
#push-options "--log_queries"

let false_boolean = false
let true_boolean = true


#push-options "--smtencoding.nl_arith_repr wrapped --smtencoding.elim_box true"
open FStar.Mul
let test (x:int) = x * 1 * 2

let force_a_query (b:bool { b = true }) = assert b
