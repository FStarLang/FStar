module Bug2894

#set-options "--warn_error -328" // unused let rec

type comparator_for (t:Type) = x:t -> y:t -> int

val term_eq : comparator_for int
let rec term_eq t1 t2 = 0

let t = term_eq
