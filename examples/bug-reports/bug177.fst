module Bug177

val foo : #y:nat{false} -> x:nat ->
             Pure unit (requires true) (ensures (fun _ -> false))
let foo y x = ()

val bar : x:unit -> Pure unit (requires true) (ensures (fun _ -> false))
let bar _ = foo 42
