module Fail 

val f : option (unit -> Tot unit) -> unit
let f x = Some.v x ()
