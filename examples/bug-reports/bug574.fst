module Bug574

type t (b:bool) =
  | T: t b

val foo: t true
let foo = T
