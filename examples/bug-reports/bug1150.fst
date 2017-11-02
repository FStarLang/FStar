module Bug1150

let positive' (s:int) : Type0 = s > 0
let positive : p:(int->Type0){p 42} = positive'

assume val witness : p:(int -> Type) -> Pure unit (requires (p 43)) (ensures (fun _ -> True))

val foo : unit -> Tot unit
let foo () = witness positive
