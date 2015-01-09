module Bug62

type env 'a = int -> Tot (option 'a)
val empty : env 'a
let empty x = None


val empty2 : a:Type -> Tot (env a)
let empty2 x = None
