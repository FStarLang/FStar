module Test
assume new type t : int -> Type0
assume val empty : t 0

val f : x:int -> Tot (t (op_Multiply 2 x))
let f x = empty
