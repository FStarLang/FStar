module SMTEncoding
open FStar.Mul
#push-options "--log_queries"
let false_boolean = false
let true_boolean = true

let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n - 1)

let id (x:Type0) = x
let force_a_query = assert (id True)



