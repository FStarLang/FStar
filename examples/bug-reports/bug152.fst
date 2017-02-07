module Bug152

val f : option (unit -> Tot unit) -> unit
let f x = if Some? x then Some?.v x () else ()
