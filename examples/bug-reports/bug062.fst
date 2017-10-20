module Bug062

type env 'a = int -> Tot (option 'a)

val empty : env 'a
let empty x = fun y -> None

val empty2 : a:Type -> Tot (env a)
let empty2 x = fun u -> None
