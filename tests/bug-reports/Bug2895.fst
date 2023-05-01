module Bug2895

// let rec not used
#set-options "--warn_error -328"

type foo (t:Type) = t -> bool

val f : foo string
let rec f (u : string) : bool = false

let test = f "123"

type comparator_for (t:Type) = t -> t -> bool

val univ_eq : comparator_for int
let rec univ_eq (u1 u2 : int) : bool = false
