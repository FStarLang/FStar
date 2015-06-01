module Bug250

val foo : int -> Tot int (ensures (fun _ -> false))
let foo x = x

val bar : int -> Tot int (ensures (42 "is the the answer"))
let bar x = x
