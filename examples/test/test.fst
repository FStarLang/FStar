module Test

assume val f : x:int -> #r:range_of x -> unit -> Pure int 
  (requires (labeled r "Pre-condition of f" (x >= 0)))
  (ensures (fun y -> x = y))

val test : nat -> Tot nat
let test x = f x ()
