module Bug131

val id : a:Type -> a -> Tot a
let id x = x

let temp = id _ 42

val foo : unit -> Tot unit
let foo () = ()

let temp' = foo _
