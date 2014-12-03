module Bug62

type env 'a = int -> Tot (option 'a)

val empty : env 'a
let empty x = None
