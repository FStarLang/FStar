module Bug21 

val constfun : 'a -> 'b -> Tot 'a
let constfun x k = x

val ftrue : 'b -> Tot bool
let ftrue = constfun true 

val my_override : ('a -> Tot 'b) -> 'a -> 'b -> Tot ('a -> Tot 'b)
let my_override f k x k' = if k = k' then x else f k'

val fmostlytrue : int -> Tot bool
let fmostlytrue x = my_override (my_override ftrue 1 false) 3 false x

val override_example1 : unit -> Fact unit
      (ensures (fmostlytrue 0 = true))
let override_example1 () = ()

(* val override_example2 : unit -> Fact unit *)
(*       (ensures (fmostlytrue 1 = false)) *)
(* let override_example2 () = () *)

(* val override_example3 : unit -> Fact unit *)
(*       (ensures (fmostlytrue 2 = true)) *)
(* let override_example3 () = () *)

(* val override_example4 : unit -> Fact unit *)
(*       (ensures (fmostlytrue 3 = false)) *)
(* let override_example4 () = () *)
