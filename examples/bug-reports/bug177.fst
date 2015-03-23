module Bug177

val foo : #y:nat{false} -> x:nat -> Tot unit (ensures false)
let foo y x = ()

val bar : x:unit -> Tot unit (ensures false)
let bar _ = foo 42
